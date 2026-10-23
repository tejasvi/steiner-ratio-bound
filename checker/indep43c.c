/* indep43c.c: C + arb port of indep43.py, for full-size runs of the certificate layer of the Steiner-ratio bound
 * of Ke, Huang, Shu, He, Gai, Wang (arXiv:2601.22365; record format of github keyisi2006/Steiner-Ratio certificate/, commit 8f19604).
 * Semantics = indep43.py (see its docstring): per record, rho L(T*) + L(S+) - L(S-) must be certainly <= 0 at every box vertex
 * with finite coordinates; lemma conditions must hold certainly there; d_steiner symmetry skip; f <= d subcase skip; f >= d needs
 * f monotone (f := d); |S+| <= 3 in f <= d; an infinite upper end needs a monotone variable and lemma 0.
 * Splits: splits2num.py output. Ball arithmetic: arb at 128 bits; rho = P/Q exactly.
 * usage: indep43c FAMILY SUBCASE SPLITS.num CERT.bin RHO_P RHO_Q START COUNT     (COUNT = 0: to the end)
 * prints one JSON line: {"start", "count", "ok", "skip_sym", "skip_sub", "fail", "fails": [...]}
 * Build with -DID64 for certificates with 64-bit record ids (gen43f -DID64).
 * v2 (2026-10-22, for the rho >= 2141/2500 certificate):
 *  - subcase "f_ge_dv" (d_regular only): f >= d with f a genuine box coordinate (no f := d); boxes with sup f < inf d are skipped;
 *  - Lemma Y2: in f_ge_dv a T* edge D-Y may use |DY| <= max(|DP|, |DQ|) if Psi > 0 certainly at the vertex,
 *    Psi = 1 + b + s + 3d + 2c + e - smt3(A,B,D) - smt3(D,Q,Q*) - |QR|, Q* = Q + (2d + c - f) dir0 (smt3 = an upper bound), and only
 *    on boxes bounded in every variable;
 *  - Lemma X2: lemma 5's condition e < (2/sqrt3 - 1)c is extended by "e < c and Phi_X > 0",
 *    Phi_X = c + e + f - sqrt(e^2 + ef + f^2) - (sqrt3/2)(c + e) (f := d in f_ge_d; Phi_X is non-decreasing in f);
 *  - with NET4 (default) a 4-point S+ is accepted in every subcase (explicit network = upper bound for any f);
 *  - in f_ge_dv an unbounded f side is accepted for a split without a Y edge whose S+ contains Q only if PQ is in S- (case
 *    reduction, extension argument: F(f) <= F(f0) for f >= f0), whatever its other lemma; Y splits never on unbounded boxes.
 * v3 (2026-10-22, after an audit): a record with an unbounded c side and an A-X edge is rejected (lemma 0's condition c <= 1 cannot
 *    hold on such a box; earlier versions tested it only at the finite vertex c = lo_c); every lower end must be finite and every
 *    box must have at least one finite vertex evaluated (fail closed instead of vacuous acceptance).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <flint/arb.h>

#define PREC 128
#ifndef NET4_ITV
#define NET4_ITV 300   /* Weiszfeld steps for the explicit 4-point network (any count gives an upper bound; >= the generator's 60
                           steps from the same start, so the network is at least as short as the generator's) */
#endif
#ifdef ID64
#define IDB 8
#else
#define IDB 4
#endif
#define MAXV 8
#define MAXS 4096
#define MAXT 16

static int STEINER, NV, FVAL, NB;
static int NET4 = 1;                /* 1 = 4-point S+ by an explicit network for the lemma's pairing (no topology lemma); 0 = lemma formula */
static int nA, nB, nD, nU, nV, nP, nQ, nR, nS, nr, nX, nY;
static int vb, vc, vd, vs, vu, vv, ve, vf;

typedef struct { int nsm, sm[16], nsp, sp[8], nt, ta[MAXT], tb[MAXT]; unsigned mono; } Split;
static Split SPL[MAXS]; static int NSPL;

typedef struct { arb_t x, y; } pt;
static pt PT[12];
static arb_t VAR[MAXV], SQ3, HALF, RHO, ONE;
static arb_t w1, w2, w3, w4, w5, w6, w7, w8;      /* scratch for lemma code */

static void sqrt_nn(arb_t z, const arb_t x) { arb_t y; arb_init(y); arb_nonnegative_part(y, x); arb_sqrt(z, y, PREC); arb_clear(y); }
static void norm2v(arb_t z, const arb_t x, const arb_t y) { arb_t t; arb_init(t); arb_mul(t, x, x, PREC); arb_addmul(t, y, y, PREC); arb_swap(z, t); arb_clear(t); }
static void dist(arb_t z, const pt *a, const pt *b) {
  arb_t dx, dy, s; arb_init(dx); arb_init(dy); arb_init(s);
  arb_sub(dx, a->x, b->x, PREC); arb_sub(dy, a->y, b->y, PREC); norm2v(s, dx, dy); sqrt_nn(z, s);
  arb_clear(dx); arb_clear(dy); arb_clear(s);
}
static int angle_le_120_vec(const arb_t ux, const arb_t uy, const arb_t vx, const arb_t vy) {
  arb_t d, a, b, c; int r; arb_init(d); arb_init(a); arb_init(b); arb_init(c);
  arb_mul(d, ux, vx, PREC); arb_addmul(d, uy, vy, PREC);
  if (arb_is_nonnegative(d)) r = 1;
  else { arb_mul(a, d, d, PREC); arb_mul_ui(a, a, 4, PREC); norm2v(b, ux, uy); norm2v(c, vx, vy); arb_mul(b, b, c, PREC); r = arb_le(a, b); }
  arb_clear(d); arb_clear(a); arb_clear(b); arb_clear(c); return r;
}
static int angle_le_120(const pt *a, const pt *b, const pt *c) {   /* certainly angle ABC <= 120 deg */
  arb_t ux, uy, vx, vy; int r; arb_init(ux); arb_init(uy); arb_init(vx); arb_init(vy);
  arb_sub(ux, a->x, b->x, PREC); arb_sub(uy, a->y, b->y, PREC); arb_sub(vx, c->x, b->x, PREC); arb_sub(vy, c->y, b->y, PREC);
  r = angle_le_120_vec(ux, uy, vx, vy);
  arb_clear(ux); arb_clear(uy); arb_clear(vx); arb_clear(vy); return r;
}
static void smt3(arb_t z, const pt *a, const pt *b, const pt *c) {   /* upper bound of the 3-point Steiner minimal tree length */
  arb_t x, y; arb_init(x); arb_init(y);
  if (!angle_le_120(a, b, c)) { dist(x, a, b); dist(y, b, c); arb_add(z, x, y, PREC); }
  else if (!angle_le_120(b, c, a)) { dist(x, b, c); dist(y, c, a); arb_add(z, x, y, PREC); }
  else if (!angle_le_120(c, a, b)) { dist(x, c, a); dist(y, a, b); arb_add(z, x, y, PREC); }
  else {
    arb_t ux, uy, vx, vy, S, q, t; arb_init(ux); arb_init(uy); arb_init(vx); arb_init(vy); arb_init(S); arb_init(q); arb_init(t);
    arb_sub(ux, b->x, a->x, PREC); arb_sub(uy, b->y, a->y, PREC); arb_sub(vx, c->x, a->x, PREC); arb_sub(vy, c->y, a->y, PREC);
    arb_mul(S, ux, vy, PREC); arb_submul(S, uy, vx, PREC); arb_abs(S, S); arb_mul(S, S, HALF, PREC);
    norm2v(q, ux, uy); norm2v(t, vx, vy); arb_add(q, q, t, PREC);
    arb_sub(ux, b->x, c->x, PREC); arb_sub(uy, b->y, c->y, PREC); norm2v(t, ux, uy); arb_add(q, q, t, PREC);
    arb_mul(q, q, HALF, PREC);
    arb_mul(S, S, SQ3, PREC); arb_mul_ui(S, S, 2, PREC); arb_add(q, q, S, PREC);
    sqrt_nn(z, q);
    arb_clear(ux); arb_clear(uy); arb_clear(vx); arb_clear(vy); arb_clear(S); arb_clear(q); arb_clear(t);
  }
  arb_clear(x); arb_clear(y);
}
/* dst = src + t * dir, dir1 = (1/2, sqrt3/2) (sgn1 = +1), dir2 = (1/2, -sqrt3/2) (sgn1 = -1); scale = +1 or -1 on t */
static void add_dir(pt *dst, const pt *src, const arb_t t, int sgn1, int scale) {
  arb_t h, k; arb_init(h); arb_init(k);
  arb_mul(h, t, HALF, PREC); arb_mul(k, h, SQ3, PREC);
  if (scale < 0) { arb_neg(h, h); arb_neg(k, k); }
  arb_add(dst->x, src->x, h, PREC);
  if (sgn1 > 0) arb_add(dst->y, src->y, k, PREC); else arb_sub(dst->y, src->y, k, PREC);
  arb_clear(h); arb_clear(k);
}
static void coords(void) {
  arb_zero(PT[nA].x); arb_zero(PT[nA].y);
  arb_one(PT[nS].x); arb_zero(PT[nS].y);
  add_dir(&PT[nB], &PT[nS], VAR[vb], +1, +1);          /* B = s + b dir1 */
  add_dir(&PT[nr], &PT[nS], VAR[vs], -1, +1);          /* r = s + s dir2 */
  add_dir(&PT[nP], &PT[nr], VAR[vc], +1, -1);          /* P = r - c dir1 */
  arb_add(PT[nD].x, PT[nr].x, VAR[vd], PREC); arb_set(PT[nD].y, PT[nr].y);   /* D = r + d dir0 */
  if (STEINER) {
    add_dir(&PT[nU], &PT[nD], VAR[vu], +1, +1);        /* U = D + u dir1 */
    add_dir(&PT[nV], &PT[nD], VAR[vv], -1, +1);        /* V = D + v dir2 */
  }
  add_dir(&PT[nQ], &PT[nP], VAR[vf], -1, +1);          /* Q = P + f dir2 */
  arb_sub(PT[nR].x, PT[nP].x, VAR[ve], PREC); arb_set(PT[nR].y, PT[nP].y);   /* R = P - e dir0 */
}
static void maxdist(arb_t z, int w, const int *lst, int m) {
  arb_t d; arb_init(d);
  dist(z, &PT[w], &PT[lst[0]]);
  for (int i = 1; i < m; i++) { dist(d, &PT[w], &PT[lst[i]]); arb_max(z, z, d, PREC); }
  arb_clear(d);
}
#define C_ VAR[vc]
#define D_ VAR[vd]
#define S_ VAR[vs]
#define E_ VAR[ve]
#define B_ VAR[vb]

/* key kinds */
enum { K_AX = 1, K_UX, K_VX, K_DX, K_Y, K_ADQR, K_BDQR };

/* Lemma Y2 condition (d_regular, f a box variable): Psi > 0 certainly; smt3 below returns an upper bound, so Psi is a lower bound */
static int psi_y2_pos(void) {
  arb_t psi, t; pt Qs; arb_init(psi); arb_init(t); arb_init(Qs.x); arb_init(Qs.y);
  arb_one(psi); arb_add(psi, psi, VAR[vb], PREC); arb_add(psi, psi, VAR[vs], PREC); arb_addmul_ui(psi, VAR[vd], 3, PREC);
  arb_addmul_ui(psi, VAR[vc], 2, PREC); arb_add(psi, psi, VAR[ve], PREC);
  smt3(t, &PT[nA], &PT[nB], &PT[nD]); arb_sub(psi, psi, t, PREC);
  arb_mul_ui(t, VAR[vd], 2, PREC); arb_add(t, t, VAR[vc], PREC); arb_sub(t, t, VAR[vf], PREC);          /* 2d + c - f */
  arb_add(Qs.x, PT[nQ].x, t, PREC); arb_set(Qs.y, PT[nQ].y);                                           /* Q* = Q + (2d + c - f) dir0 */
  smt3(t, &PT[nD], &PT[nQ], &Qs); arb_sub(psi, psi, t, PREC);
  dist(t, &PT[nQ], &PT[nR]); arb_sub(psi, psi, t, PREC);
  int r = arb_is_positive(psi);
  arb_clear(psi); arb_clear(t); arb_clear(Qs.x); arb_clear(Qs.y); return r;
}

/* lemma 5 condition e < kc (kc = (2/sqrt3 - 1) c), extended by Lemma X2: e < c and Phi_X > 0 certainly */
static int x2_cond(const arb_t kc) {
  if (arb_lt(VAR[ve], kc)) return 1;
  if (!arb_lt(VAR[ve], VAR[vc])) return 0;
  arb_t phi, t, u; arb_init(phi); arb_init(t); arb_init(u);
  arb_mul(t, VAR[ve], VAR[ve], PREC); arb_addmul(t, VAR[ve], VAR[vf], PREC); arb_addmul(t, VAR[vf], VAR[vf], PREC); sqrt_nn(t, t);
  arb_add(phi, VAR[vc], VAR[ve], PREC); arb_add(phi, phi, VAR[vf], PREC); arb_sub(phi, phi, t, PREC);
  arb_add(u, VAR[vc], VAR[ve], PREC); arb_mul(u, u, SQ3, PREC); arb_mul(u, u, HALF, PREC); arb_sub(phi, phi, u, PREC);
  int r = arb_is_positive(phi);
  arb_clear(phi); arb_clear(t); arb_clear(u); return r;
}

/* lemma entry for (lemma L, key kind K): returns -1 = no such entry; 0 = condition fails; 1 = ok with bound in z */
static int lemma_entry(int L, int K, arb_t z) {
  arb_t a, b, c, d; int r = -1; arb_init(a); arb_init(b); arb_init(c); arb_init(d);
  if (K == K_Y) {                                              /* every lemma set carries the lemma-0 Y bound */
    if (FVAL == 3 && !STEINER) {                               /* Lemma Y2: Psi > 0 => |DY| <= max(|DP|, |DQ|) at the actual f */
      if (!psi_y2_pos()) { r = 0; goto out; }
      int l[2] = {nP, nQ}; maxdist(z, nD, l, 2); r = 1; goto out;
    }
    if (FVAL != 1) { r = 0; goto out; }
    if (STEINER) { int l[3] = {nr, nP, nQ}; maxdist(z, nV, l, 3); }
    else { int l[2] = {nP, nQ}; maxdist(z, nD, l, 2); }
    r = 1; goto out;
  }
  if (K == K_AX) {
    switch (L) {
      case 0:                                                  /* c <= 1 ; max(|Ar|, |AP|) */
        if (!arb_le(C_, ONE)) { r = 0; goto out; }
        { int l[2] = {nr, nP}; maxdist(z, nA, l, 2); } r = 1; goto out;
      case 1: case 2:
        if (L == 1) {                                          /* e < 1 - c + (2/sqrt3) s  and  c + e >= 1 */
          arb_div(a, S_, SQ3, PREC); arb_mul_ui(a, a, 2, PREC); arb_sub(a, a, C_, PREC); arb_add(a, a, ONE, PREC);
        } else {                                               /* e < 1 + (2/sqrt3 - 1) c  and  c + e >= 1 */
          arb_ui_div(a, 2, SQ3, PREC); arb_sub(a, a, ONE, PREC); arb_mul(a, a, C_, PREC); arb_add(a, a, ONE, PREC);
        }
        arb_add(b, C_, E_, PREC);
        if (!(arb_lt(E_, a) && arb_ge(b, ONE))) { r = 0; goto out; }
        { int l[4] = {nS, nr, nP, nR}; maxdist(z, nA, l, 4); }
        arb_sub(b, b, ONE, PREC); arb_mul(b, b, SQ3, PREC); arb_mul(b, b, HALF, PREC); arb_max(z, z, b, PREC);
        r = 1; goto out;
      case 5:                                                  /* e < (2/sqrt3 - 1) c or X2 ; max(|Ar|, |AP|, |AR|) */
        arb_ui_div(a, 2, SQ3, PREC); arb_sub(a, a, ONE, PREC); arb_mul(a, a, C_, PREC);
        if (!x2_cond(a)) { r = 0; goto out; }
        { int l[3] = {nr, nP, nR}; maxdist(z, nA, l, 3); } r = 1; goto out;
      case 8:                                                  /* e < s + 1 ; max(|Ar|, |AP|, |AR|, e + c - 1) */
        arb_add(a, S_, ONE, PREC);
        if (!arb_lt(E_, a)) { r = 0; goto out; }
        { int l[3] = {nr, nP, nR}; maxdist(z, nA, l, 3); }
        arb_add(b, E_, C_, PREC); arb_sub(b, b, ONE, PREC); arb_max(z, z, b, PREC);
        r = 1; goto out;
      default: r = -1; goto out;
    }
  }
  if (K == K_UX || K == K_VX || K == K_DX) {                   /* lemma 5 only: (U,X), (V,X) [steiner], (D,X) [regular] */
    if (L != 5) { r = -1; goto out; }
    if ((K == K_DX) == (STEINER != 0)) { r = -1; goto out; }
    arb_ui_div(a, 2, SQ3, PREC); arb_sub(a, a, ONE, PREC); arb_mul(a, a, C_, PREC);
    if (!x2_cond(a)) { r = 0; goto out; }
    int W = K == K_UX ? nU : (K == K_VX ? nV : nD);
    /* H = R - ((c - e)/2) dir2 = (R.x - (c-e)/4, R.y + (c-e) sqrt3/4) */
    pt H; arb_init(H.x); arb_init(H.y);
    arb_sub(b, C_, E_, PREC); arb_mul(b, b, HALF, PREC);              /* (c - e)/2 */
    arb_mul(c, b, HALF, PREC); arb_sub(H.x, PT[nR].x, c, PREC);       /* - (c-e)/2 * 1/2 */
    arb_mul(d, c, SQ3, PREC); arb_add(H.y, PT[nR].y, d, PREC);        /* - (c-e)/2 * (-sqrt3/2) */
    { int l[3] = {nr, nP, nR}; maxdist(z, W, l, 3); }
    dist(a, &PT[W], &H); arb_max(z, z, a, PREC);
    arb_clear(H.x); arb_clear(H.y);
    r = 1; goto out;
  }
  if (K == K_ADQR) {
    if (L == 3) {
      /* c + e >= 1, e <= s + c + d + 2, e >= 2 - c - d + s, e (2 + c + 3d + s) <= 2 + c^2 + 3d + 2s + 3cs + 3ds + 2s^2, e <= 3s,
         angle(D - R, Q - A) <= 120, angle(A, R, V') <= 120, angle(R, A, V') <= 120 with V' = D + rot60(Q - D) */
      arb_add(a, C_, E_, PREC); if (!arb_ge(a, ONE)) { r = 0; goto out; }
      arb_add(a, S_, C_, PREC); arb_add(a, a, D_, PREC); arb_add_ui(a, a, 2, PREC); if (!arb_le(E_, a)) { r = 0; goto out; }
      arb_set_ui(a, 2); arb_sub(a, a, C_, PREC); arb_sub(a, a, D_, PREC); arb_add(a, a, S_, PREC); if (!arb_ge(E_, a)) { r = 0; goto out; }
      arb_set_ui(a, 2); arb_add(a, a, C_, PREC); arb_addmul_ui(a, D_, 3, PREC); arb_add(a, a, S_, PREC); arb_mul(a, a, E_, PREC);
      arb_set_ui(b, 2); arb_addmul(b, C_, C_, PREC); arb_addmul_ui(b, D_, 3, PREC); arb_addmul_ui(b, S_, 2, PREC);
      arb_mul(c, C_, S_, PREC); arb_addmul_ui(b, c, 3, PREC); arb_mul(c, D_, S_, PREC); arb_addmul_ui(b, c, 3, PREC);
      arb_mul(c, S_, S_, PREC); arb_addmul_ui(b, c, 2, PREC);
      if (!arb_le(a, b)) { r = 0; goto out; }
      arb_mul_ui(a, S_, 3, PREC); if (!arb_le(E_, a)) { r = 0; goto out; }
      {
        arb_t ux, uy, vx, vy; arb_init(ux); arb_init(uy); arb_init(vx); arb_init(vy);
        arb_sub(ux, PT[nD].x, PT[nR].x, PREC); arb_sub(uy, PT[nD].y, PT[nR].y, PREC);
        arb_sub(vx, PT[nQ].x, PT[nA].x, PREC); arb_sub(vy, PT[nQ].y, PT[nA].y, PREC);
        int okang = angle_le_120_vec(ux, uy, vx, vy);
        /* V' = D + rot60(Q - D); rot60(u) = (u.x/2 - sqrt3/2 u.y, sqrt3/2 u.x + u.y/2) */
        pt Vp; arb_init(Vp.x); arb_init(Vp.y);
        arb_sub(ux, PT[nQ].x, PT[nD].x, PREC); arb_sub(uy, PT[nQ].y, PT[nD].y, PREC);
        arb_mul(vx, ux, HALF, PREC); arb_mul(a, uy, SQ3, PREC); arb_mul(a, a, HALF, PREC); arb_sub(vx, vx, a, PREC);
        arb_mul(vy, ux, SQ3, PREC); arb_mul(vy, vy, HALF, PREC); arb_mul(a, uy, HALF, PREC); arb_add(vy, vy, a, PREC);
        arb_add(Vp.x, PT[nD].x, vx, PREC); arb_add(Vp.y, PT[nD].y, vy, PREC);
        okang = okang && angle_le_120(&PT[nA], &PT[nR], &Vp) && angle_le_120(&PT[nR], &PT[nA], &Vp);
        arb_clear(ux); arb_clear(uy); arb_clear(vx); arb_clear(vy); arb_clear(Vp.x); arb_clear(Vp.y);
        if (!okang) { r = 0; goto out; }
      }
      /* sqrt(X^2 + Y^2), X = (1 + e + 3d + 2s + 3c)/2, Y = -sqrt3 (c + d + e - 1)/2 */
      arb_one(a); arb_add(a, a, E_, PREC); arb_addmul_ui(a, D_, 3, PREC); arb_addmul_ui(a, S_, 2, PREC); arb_addmul_ui(a, C_, 3, PREC);
      arb_mul(a, a, HALF, PREC);
      arb_add(b, C_, D_, PREC); arb_add(b, b, E_, PREC); arb_sub(b, b, ONE, PREC); arb_mul(b, b, SQ3, PREC); arb_mul(b, b, HALF, PREC);
      norm2v(c, a, b); sqrt_nn(z, c); r = 1; goto out;
    }
    if (L == 4) {                                              /* c >= 1, e >= 1 ; S = 1 + s + c + e + 2d, sqrt(S^2 - S + 1) */
      if (!(arb_ge(C_, ONE) && arb_ge(E_, ONE))) { r = 0; goto out; }
      arb_one(a); arb_add(a, a, S_, PREC); arb_add(a, a, C_, PREC); arb_add(a, a, E_, PREC); arb_addmul_ui(a, D_, 2, PREC);
      arb_mul(b, a, a, PREC); arb_sub(b, b, a, PREC); arb_add(b, b, ONE, PREC); sqrt_nn(z, b); r = 1; goto out;
    }
    if (L == 7) {
      /* d(c + e - 1) + e(s + c) >= 0, e >= (sqrt(k^2 + 4d) - k)/2 (k = c + s + 2d), -(2 + s - c + d)(c + 2e + 2d) + 3c(s + c + d) >= 0,
         s + e >= 1, c <= 1 + d + (s + e)/2 ; S = 2d + s + c + e, sqrt(S^2 + S + 1) */
      arb_add(a, C_, E_, PREC); arb_sub(a, a, ONE, PREC); arb_mul(a, a, D_, PREC); arb_add(b, S_, C_, PREC); arb_addmul(a, E_, b, PREC);
      if (!arb_is_nonnegative(a)) { r = 0; goto out; }
      arb_add(a, C_, S_, PREC); arb_addmul_ui(a, D_, 2, PREC);                     /* k */
      arb_mul(b, a, a, PREC); arb_addmul_ui(b, D_, 4, PREC); sqrt_nn(b, b); arb_sub(b, b, a, PREC); arb_mul(b, b, HALF, PREC);
      if (!arb_ge(E_, b)) { r = 0; goto out; }
      arb_set_ui(a, 2); arb_add(a, a, S_, PREC); arb_sub(a, a, C_, PREC); arb_add(a, a, D_, PREC);
      arb_set(b, C_); arb_addmul_ui(b, E_, 2, PREC); arb_addmul_ui(b, D_, 2, PREC); arb_mul(a, a, b, PREC); arb_neg(a, a);
      arb_add(b, S_, C_, PREC); arb_add(b, b, D_, PREC); arb_mul(b, b, C_, PREC); arb_addmul_ui(a, b, 3, PREC);
      if (!arb_is_nonnegative(a)) { r = 0; goto out; }
      arb_add(a, S_, E_, PREC); if (!arb_ge(a, ONE)) { r = 0; goto out; }
      arb_add(a, S_, E_, PREC); arb_mul(a, a, HALF, PREC); arb_add(a, a, D_, PREC); arb_add(a, a, ONE, PREC);
      if (!arb_le(C_, a)) { r = 0; goto out; }
      arb_mul_ui(a, D_, 2, PREC); arb_add(a, a, S_, PREC); arb_add(a, a, C_, PREC); arb_add(a, a, E_, PREC);
      arb_mul(b, a, a, PREC); arb_add(b, b, a, PREC); arb_add(b, b, ONE, PREC); sqrt_nn(z, b); r = 1; goto out;
    }
    r = -1; goto out;
  }
  if (K == K_BDQR) {
    if (L != 6) { r = -1; goto out; }
    if (!arb_ge(D_, B_)) { r = 0; goto out; }               /* d >= b ; sqrt(t1^2 + 3 t2^2)/2 */
    arb_set(b, C_); arb_addmul_ui(b, D_, 2, PREC); arb_add(b, b, E_, PREC); arb_add(b, b, S_, PREC);     /* t2 */
    arb_set(a, b); arb_addmul_ui(a, B_, 2, PREC);                                                        /* t1 */
    arb_mul(c, a, a, PREC); arb_mul(d, b, b, PREC); arb_addmul_ui(c, d, 3, PREC); sqrt_nn(z, c); arb_mul(z, z, HALF, PREC);
    r = 1; goto out;
  }
out:
  arb_clear(a); arb_clear(b); arb_clear(c); arb_clear(d); return r;
}

/* length of the network p1-x, p2-x, x-y, p3-y, p4-y with Steiner points x, y optimised in double precision (Weiszfeld
   alternation from the pair midpoints); the length is evaluated exactly in balls, so it is an upper bound of the minimum over x, y. */
static void net4(arb_t z, const pt *p1, const pt *p2, const pt *p3, const pt *p4) {
  double P[4][2]; const pt *pp[4] = {p1, p2, p3, p4};
  for (int i = 0; i < 4; i++) { P[i][0] = arf_get_d(arb_midref(pp[i]->x), ARF_RND_NEAR); P[i][1] = arf_get_d(arb_midref(pp[i]->y), ARF_RND_NEAR); }
  double x[2] = {(P[0][0] + P[1][0]) / 2, (P[0][1] + P[1][1]) / 2}, y[2] = {(P[2][0] + P[3][0]) / 2, (P[2][1] + P[3][1]) / 2};
  for (int it = 0; it < NET4_ITV; it++) {
    double nb[3][2], *Z = x; int idx[2] = {0, 1};
    for (int side = 0; side < 2; side++) {
      Z = side ? y : x; idx[0] = side ? 2 : 0; idx[1] = side ? 3 : 1;
      double *O = side ? x : y;
      nb[0][0] = P[idx[0]][0]; nb[0][1] = P[idx[0]][1]; nb[1][0] = P[idx[1]][0]; nb[1][1] = P[idx[1]][1]; nb[2][0] = O[0]; nb[2][1] = O[1];
      double ws = 0, sx = 0, sy = 0;
      for (int k = 0; k < 3; k++) { double d = hypot(Z[0] - nb[k][0], Z[1] - nb[k][1]); if (d < 1e-15) d = 1e-15; ws += 1 / d; sx += nb[k][0] / d; sy += nb[k][1] / d; }
      Z[0] = sx / ws; Z[1] = sy / ws;
    }
  }
  pt X, Y; arb_init(X.x); arb_init(X.y); arb_init(Y.x); arb_init(Y.y);
  arb_set_d(X.x, x[0]); arb_set_d(X.y, x[1]); arb_set_d(Y.x, y[0]); arb_set_d(Y.y, y[1]);
  arb_t t; arb_init(t);
  dist(z, p1, &X); dist(t, p2, &X); arb_add(z, z, t, PREC); dist(t, &X, &Y); arb_add(z, z, t, PREC);
  dist(t, p3, &Y); arb_add(z, z, t, PREC); dist(t, p4, &Y); arb_add(z, z, t, PREC);
  arb_clear(t); arb_clear(X.x); arb_clear(X.y); arb_clear(Y.x); arb_clear(Y.y);
}

static int edge_key(int a, int b) {     /* T* edge touching X or Y -> key kind (0 = none) */
  int o = (a == nX || a == nY) ? b : a, imp = (a == nX || a == nY) ? a : b;
  if (imp == nX) { if (o == nA) return K_AX; if (STEINER && o == nU) return K_UX; if (STEINER && o == nV) return K_VX; if (!STEINER && o == nD) return K_DX; return 0; }
  if (imp == nY) { if (o == (STEINER ? nV : nD)) return K_Y; return 0; }
  return 0;
}

/* value at the current VAR; returns 1 = certainly <= 0, 0 = not certified (cond fails / value not <= 0) */
static int eval_vertex(const Split *sp, int L, const char **why) {
  arb_t t, z, sm, spl, v; int ok = 0; arb_init(t); arb_init(z); arb_init(sm); arb_init(spl); arb_init(v);
  coords();
  arb_zero(t);
  for (int i = 0; i < sp->nt; i++) {
    int a = sp->ta[i], b = sp->tb[i];
    if (a == nX || b == nX || a == nY || b == nY) {
      int K = edge_key(a, b);
      int r = K ? lemma_entry(L, K, z) : -1;
      if (r != 1) { *why = r < 0 ? "missing lemma entry" : "lemma condition fails"; goto out; }
      arb_add(t, t, z, PREC);
    } else { dist(z, &PT[a], &PT[b]); arb_add(t, t, z, PREC); }
  }
  arb_zero(sm);
  for (int i = 0; i < sp->nsm; i++) { if (sp->sm[i] == 0) arb_add(sm, sm, ONE, PREC); else arb_add(sm, sm, VAR[sp->sm[i] - 1], PREC); }
  if (sp->nsp <= 1) arb_zero(spl);
  else if (sp->nsp == 2) dist(spl, &PT[sp->sp[0]], &PT[sp->sp[1]]);
  else if (sp->nsp == 3) smt3(spl, &PT[sp->sp[0]], &PT[sp->sp[1]], &PT[sp->sp[2]]);
  else {
    int K = 0;
    if (sp->nsp == 4) {
      int adqr[4] = {nA, nD, nQ, nR}, bdqr[4] = {nB, nD, nQ, nR}, s1[4], s2[4];
      for (int i = 0; i < 4; i++) { s1[i] = adqr[i]; s2[i] = bdqr[i]; }
      for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) { if (s1[j] < s1[i]) { int x = s1[i]; s1[i] = s1[j]; s1[j] = x; } if (s2[j] < s2[i]) { int x = s2[i]; s2[i] = s2[j]; s2[j] = x; } }
      if (!memcmp(s1, sp->sp, sizeof s1)) K = K_ADQR; else if (!memcmp(s2, sp->sp, sizeof s2)) K = K_BDQR;
    }
    if (NET4 && K) {
      /* lemma-free: the pairing the lemma's closed form uses (L3: AR|DQ, L4 and L7: AD|QR, L6: BD|QR); length of an explicit
         network with numerically optimised Steiner points, evaluated in ball arithmetic: an upper bound of the pairing's minimal
         network length, which is convex in w (the convexity argument replaces the topology lemma and the Shape Constraint). */
      int a1, a2, b1, b2;
      if (K == K_ADQR && L == 3) { a1 = nA; a2 = nR; b1 = nD; b2 = nQ; }
      else if (K == K_ADQR && (L == 4 || L == 7)) { a1 = nA; a2 = nD; b1 = nQ; b2 = nR; }
      else if (K == K_BDQR && L == 6) { a1 = nB; a2 = nD; b1 = nQ; b2 = nR; }
      else { *why = "missing S+ lemma entry"; goto out; }
      net4(spl, &PT[a1], &PT[a2], &PT[b1], &PT[b2]);
    } else {
      int r = K ? lemma_entry(L, K, spl) : -1;
      if (r != 1) { *why = r < 0 ? "missing S+ lemma entry" : "S+ lemma condition fails"; goto out; }
    }
  }
  arb_mul(v, RHO, t, PREC); arb_add(v, v, spl, PREC); arb_sub(v, v, sm, PREC);
  ok = arb_is_nonpositive(v);
  if (!ok) *why = "vertex value not <= 0";
out:
  arb_clear(t); arb_clear(z); arb_clear(sm); arb_clear(spl); arb_clear(v); return ok;
}

static void setup(const char *fam, const char *sub) {
  STEINER = !strcmp(fam, "d_steiner");
  if (!STEINER && strcmp(fam, "d_regular")) { fprintf(stderr, "family\n"); exit(2); }
  FVAL = !strcmp(sub, "f_ge_d") ? 2 : !strcmp(sub, "f_ge_dv") ? 3 : 1;
  if (FVAL == 1 && strcmp(sub, "f_le_d")) { fprintf(stderr, "subcase\n"); exit(2); }
  if (FVAL == 3 && STEINER) { fprintf(stderr, "f_ge_dv is for d_regular only\n"); exit(2); }
  if (STEINER) { /* A B D U V P Q R s r X Y */
    nA = 0; nB = 1; nD = 2; nU = 3; nV = 4; nP = 5; nQ = 6; nR = 7; nS = 8; nr = 9; nX = 10; nY = 11;
    vb = 0; vc = 1; vd = 2; vs = 3; vu = 4; vv = 5; ve = 6; vf = 7; NV = 8;
  } else {       /* A B D P Q R s r X Y */
    nA = 0; nB = 1; nD = 2; nU = -1; nV = -1; nP = 3; nQ = 4; nR = 5; nS = 6; nr = 7; nX = 8; nY = 9;
    vb = 0; vc = 1; vd = 2; vs = 3; vu = -1; vv = -1; ve = 4; vf = 5; NV = 6;
  }
  NB = FVAL == 2 ? NV - 1 : NV;
  for (int i = 0; i < 12; i++) { arb_init(PT[i].x); arb_init(PT[i].y); }
  for (int i = 0; i < MAXV; i++) arb_init(VAR[i]);
  arb_init(SQ3); arb_sqrt_ui(SQ3, 3, PREC); arb_init(HALF); arb_set_d(HALF, 0.5); arb_init(ONE); arb_one(ONE); arb_init(RHO);
}

static void read_splits(const char *path) {
  FILE *f = fopen(path, "r"); if (!f) { perror("splits"); exit(2); }
  NSPL = 0;
  while (NSPL < MAXS) {
    Split *s = &SPL[NSPL];
    if (fscanf(f, "%d", &s->nsm) != 1) break;
    for (int i = 0; i < s->nsm; i++) if (fscanf(f, "%d", &s->sm[i]) != 1) exit(3);
    if (fscanf(f, "%d", &s->nsp) != 1) exit(3);
    for (int i = 0; i < s->nsp; i++) if (fscanf(f, "%d", &s->sp[i]) != 1) exit(3);
    if (fscanf(f, "%d", &s->nt) != 1 || s->nt > MAXT) exit(3);
    for (int i = 0; i < s->nt; i++) if (fscanf(f, "%d %d", &s->ta[i], &s->tb[i]) != 2) exit(3);
    if (fscanf(f, "%u", &s->mono) != 1) exit(3);
    NSPL++;
  }
  fclose(f);
}

int main(int argc, char **argv) {
  if (argc != 9) { fprintf(stderr, "usage: indep43c FAMILY SUBCASE SPLITS.num CERT.bin RHO_P RHO_Q START COUNT\n"); return 2; }
  setup(argv[1], argv[2]); read_splits(argv[3]);
  if (getenv("NET4") && !strcmp(getenv("NET4"), "0")) NET4 = 0;
  { fmpz_t p, q; fmpz_init(p); fmpz_init(q); fmpz_set_str(p, argv[5], 10); fmpz_set_str(q, argv[6], 10);
    arb_set_fmpz(RHO, p); arb_div_fmpz(RHO, RHO, q, PREC); fmpz_clear(p); fmpz_clear(q); }
  int fd = open(argv[4], O_RDONLY); if (fd < 0) { perror("cert"); return 2; }
  struct stat st; fstat(fd, &st);
  size_t rs = IDB + 16 * (size_t)NB + 8;
  if (st.st_size % rs) { printf("{\"error\": \"size not a multiple of the record size\"}\n"); return 1; }
  uint64_t R = st.st_size / rs, start = strtoull(argv[7], 0, 10), cnt = strtoull(argv[8], 0, 10);
  if (start > R) start = R;
  if (cnt == 0 || start + cnt > R) cnt = R - start;
  unsigned char *m = mmap(NULL, st.st_size ? st.st_size : 1, PROT_READ, MAP_SHARED, fd, 0);
  uint64_t ok = 0, ssym = 0, ssub = 0, fail = 0; int nf = 0;
  char fails[8192]; fails[0] = 0; size_t fl = 0;
  for (uint64_t k = start; k < start + cnt; k++) {
    const unsigned char *p = m + k * rs;
    uint64_t id = 0; int32_t sid, lid; double lo[MAXV], hi[MAXV];
    memcpy(&id, p, IDB);
    for (int i = 0; i < NB; i++) { memcpy(&lo[i], p + IDB + 16 * i, 8); memcpy(&hi[i], p + IDB + 8 + 16 * i, 8); }
    memcpy(&sid, p + IDB + 16 * NB, 4); memcpy(&lid, p + IDB + 4 + 16 * NB, 4);
    const char *why = 0;
    if (STEINER && fmax(lo[vu], lo[vv]) > fmax(hi[vb], 1.0)) { ssym++; continue; }
    if (FVAL == 1 && lo[vf] > hi[vd]) { ssub++; continue; }
    if (FVAL == 3 && hi[vf] < lo[vd]) { ssub++; continue; }             /* box entirely in f < d */
    int good = 1;
    if (sid < 1 || sid > NSPL || lid < 0 || lid > 8) { good = 0; why = "bad split or lemma id"; }
    const Split *sp = good ? &SPL[sid - 1] : 0;
    if (good && FVAL == 2 && !((sp->mono >> vf) & 1)) { good = 0; why = "f >= d but f not monotone"; }
    if (good && FVAL != 2 && sp->nsp > 3 && !NET4) { good = 0; why = "|S+| > 3 away from f = d needs NET4"; }
    int hasY = 0, extok = 1, unb = 0;
    if (good) {
      for (int i = 0; i < sp->nt; i++) if (sp->ta[i] == nY || sp->tb[i] == nY) hasY = 1;
      int qin = 0, pq = 0;
      for (int i = 0; i < sp->nsp; i++) if (sp->sp[i] == nQ) qin = 1;
      for (int i = 0; i < sp->nsm; i++) if (sp->sm[i] == vf + 1) pq = 1;            /* edge id vf + 1 = PQ (length f) */
      extok = !qin || pq;
    }
    for (int i = 0; good && i < NB; i++) {
      if (!(lo[i] <= hi[i])) { good = 0; why = "empty box"; }
      else if (isinf(hi[i])) {
        unb = 1;
        if (FVAL == 3 && i == vf) {                                     /* extension argument (case reduction, f >= f0) */
          if (hasY || !extok) { good = 0; why = "unbounded f needs a split without a Y edge and with Q in S+ => PQ in S-"; }
        } else if (!((sp->mono >> i) & 1) || lid > 0) { good = 0; why = "infinite end without monotonicity / lemma 0"; }
      }
    }
    if (good && FVAL == 3 && hasY && unb) { good = 0; why = "Y2 split on an unbounded box"; }
    if (good) {                                                          /* v3: lower ends finite; no A-X edge with c unbounded */
      for (int i = 0; i < NB; i++) if (!isfinite(lo[i])) { good = 0; why = "lower end not finite"; }
      int hasAX = 0;
      for (int i = 0; i < sp->nt; i++) if ((sp->ta[i] == nX && sp->tb[i] == nA) || (sp->ta[i] == nA && sp->tb[i] == nX)) hasAX = 1;
      if (good && hasAX && isinf(hi[vc])) { good = 0; why = "A-X edge on a box with c unbounded (lemma 0 needs c <= 1)"; }
    }
    int nfin = 0;
    for (uint64_t mask = 0; good && mask < (1ull << NB); mask++) {
      int finite = 1;
      for (int i = 0; i < NB; i++) { double x = (mask >> i) & 1 ? hi[i] : lo[i]; if (isinf(x)) { finite = 0; break; } arb_set_d(VAR[i], x); }
      if (!finite) continue;
      nfin++;
      if (FVAL == 2) arb_set(VAR[vf], VAR[vd]);
      if (!eval_vertex(sp, lid, &why)) good = 0;
    }
    if (good && nfin == 0) { good = 0; why = "no finite vertex"; }
    if (good) ok++;
    else {
      fail++;
      if (nf < 10 && fl < sizeof(fails) - 300) {
        fl += snprintf(fails + fl, sizeof(fails) - fl, "%s{\"rec\": %llu, \"id\": %llu, \"split\": %d, \"lemma\": %d, \"why\": \"%s\"}",
                       nf ? ", " : "", (unsigned long long)k, (unsigned long long)id, sid, lid, why ? why : "?");
        nf++;
      }
    }
  }
  printf("{\"start\": %llu, \"count\": %llu, \"ok\": %llu, \"skip_sym\": %llu, \"skip_sub\": %llu, \"fail\": %llu, \"fails\": [%s]}\n",
         (unsigned long long)start, (unsigned long long)cnt, (unsigned long long)ok, (unsigned long long)ssym,
         (unsigned long long)ssub, (unsigned long long)fail, fails);
  return fail ? 1 : 0;
}
