/* cover43.c: independent coverage check of a Steiner-ratio partition (PKU certificate format, arXiv:2601.22365).
 * Written independently of the generator; top-down, unlike the original bottom-up verify_partition.py.
 *
 * Inputs: the certificate file (records: uint32 id, n x (double lo, double hi), int32 split_id, int32 lemma_id; any order) and
 * the child file (for id = N down to 1: uint32 left, uint32 right; 0 0 = leaf), as written by the generator plot_f_*.cpp.
 * Claim checked: starting from the 2^n root boxes (id = mask + 1; variable i in [1, inf] if bit i of mask is set, else [0, 1]),
 * and splitting every internal node into two halves along ONE axis (finite side: at the midpoint; infinite side [lo, inf]: at 2 lo),
 * every leaf is a certificate record whose box equals the computed box exactly, every record is such a leaf exactly once, and every
 * internal node's two children are distinct unused ids. The split axis is recomputed with the generator's rule (widest side; an
 * infinite side [lo, inf] counts as 1/lo; first maximum); a different axis in the generator would show up as a leaf mismatch, so the
 * check fails closed. Together: the leaves tile the union of the root boxes, i.e. the case domain [0, inf)^n.
 * usage: cover43 CERT.bin CHILD.bin n      (prints OK COVER or the first failure; exit code 0/1)
 * Build with -DID64 for the 64-bit-id variant written by gen43f -DID64 (uint64 ids in records and child pairs).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#define MAXN 8
#ifdef ID64
typedef uint64_t idt;
#else
typedef uint32_t idt;
#endif
#define IDB ((size_t)sizeof(idt))
typedef struct { double lo[MAXN], hi[MAXN]; idt id; } Node;

static void die(const char *m) { fprintf(stderr, "FAIL: %s\n", m); printf("FAIL: %s\n", m); exit(1); }

int main(int argc, char **argv) {
  if (argc != 4) die("usage: cover43 CERT.bin CHILD.bin n");
  int n = atoi(argv[3]); if (n < 1 || n > MAXN) die("bad n");
  size_t rs = IDB + 16 * (size_t)n + 8;
  int fc = open(argv[1], O_RDONLY), fh = open(argv[2], O_RDONLY);
  if (fc < 0 || fh < 0) die("open");
  struct stat sc, sh; fstat(fc, &sc); fstat(fh, &sh);
  if (sc.st_size % rs) die("certificate size not a multiple of the record size");
  if (sh.st_size % (2 * IDB)) die("child file size not a multiple of the pair size");
  uint64_t R = sc.st_size / rs, N = sh.st_size / (2 * IDB);
  unsigned char *cert = mmap(NULL, sc.st_size ? sc.st_size : 1, PROT_READ, MAP_SHARED, fc, 0);
  idt *ch = mmap(NULL, sh.st_size ? sh.st_size : 1, PROT_READ, MAP_SHARED, fh, 0);
  if (cert == MAP_FAILED || ch == MAP_FAILED) die("mmap");
  printf("records %llu, nodes %llu, n %d, id bytes %d\n", (unsigned long long)R, (unsigned long long)N, n, (int)IDB);
  if (IDB == 4 && N >= 0xFFFFFFFFull) die("too many nodes for 32-bit ids");
  /* index: id -> record number + 1 (0 = none) */
  uint64_t *pos = calloc(N + 1, sizeof(uint64_t));
  unsigned char *seen = calloc(N + 1, 1);
  if (!pos || !seen) die("alloc");
  for (uint64_t r = 0; r < R; r++) {
    idt id = 0; memcpy(&id, cert + r * rs, IDB);
    if (id == 0 || id > N) die("record id out of range");
    if (pos[id]) die("duplicate record id");
    pos[id] = r + 1;
  }
  /* child of id k is at index (N - k) in the file (written for k = N down to 1) */
  uint64_t nroot = 1ull << n, leaves = 0, internal = 0, maxdepth = 0;
  Node *stack = malloc(sizeof(Node) * 4096); int *depth = malloc(sizeof(int) * 4096);
  for (uint64_t mask = 0; mask < nroot; mask++) {
    int sp = 0;
    Node rt; rt.id = (idt)(mask + 1);
    for (int i = 0; i < n; i++) { if ((mask >> i) & 1) { rt.lo[i] = 1; rt.hi[i] = INFINITY; } else { rt.lo[i] = 0; rt.hi[i] = 1; } }
    stack[sp] = rt; depth[sp] = 0; sp++;
    while (sp) {
      Node b = stack[--sp]; int dp = depth[sp];
      if ((uint64_t)dp > maxdepth) maxdepth = dp;
      if (b.id == 0 || b.id > N) die("node id out of range");
      if (seen[b.id]) die("node id reached twice");
      seen[b.id] = 1;
      idt L = ch[2 * (N - b.id)], Rr = ch[2 * (N - b.id) + 1];
      if (L == 0 && Rr == 0) {                       /* leaf: must be a record with exactly this box */
        if (!pos[b.id]) { fprintf(stderr, "leaf id %llu has no record\n", (unsigned long long)b.id); die("leaf without record"); }
        const unsigned char *p = cert + (uint64_t)(pos[b.id] - 1) * rs + IDB;
        for (int i = 0; i < n; i++) {
          double lo, hi; memcpy(&lo, p + 16 * i, 8); memcpy(&hi, p + 16 * i + 8, 8);
          if (lo != b.lo[i] || hi != b.hi[i]) {
            fprintf(stderr, "leaf id %llu axis %d: record [%.17g, %.17g] computed [%.17g, %.17g]\n", (unsigned long long)b.id, i, lo, hi, b.lo[i], b.hi[i]);
            die("leaf box mismatch");
          }
        }
        leaves++;
        continue;
      }
      if (L == 0 || Rr == 0 || L == Rr) die("bad child pair");
      if (pos[b.id]) die("internal node also has a record");
      internal++;
      int dim = 0; double best = -1;
      for (int i = 0; i < n; i++) {
        double sep = isinf(b.hi[i]) ? 1.0 / b.lo[i] : b.hi[i] - b.lo[i];
        if (sep > best) { best = sep; dim = i; }       /* first maximum */
      }
      Node l = b, r = b; l.id = L; r.id = Rr;
      double m = isinf(b.hi[dim]) ? 2 * b.lo[dim] : (b.lo[dim] + b.hi[dim]) / 2;
      if (!(m > b.lo[dim] && m < b.hi[dim])) die("degenerate split");
      l.hi[dim] = m; r.lo[dim] = m;
      if (sp + 2 >= 4096) die("stack overflow");
      stack[sp] = r; depth[sp] = dp + 1; sp++;
      stack[sp] = l; depth[sp] = dp + 1; sp++;
    }
  }
  if (leaves != R) { fprintf(stderr, "leaves %llu records %llu\n", (unsigned long long)leaves, (unsigned long long)R); die("records not all reached"); }
  uint64_t unseen = 0;
  for (uint64_t k = 1; k <= N; k++) if (!seen[k]) unseen++;
  printf("leaves %llu (= records), internal %llu, max depth %llu, ids not in the tree %llu\n",
         (unsigned long long)leaves, (unsigned long long)internal, (unsigned long long)maxdepth, (unsigned long long)unseen);
  if (unseen) die("ids not reached from the roots");
  printf("OK COVER: the %llu record boxes tile the %llu root boxes (the domain [0,inf)^%d)\n",
         (unsigned long long)R, (unsigned long long)nroot, n);
  return 0;
}
