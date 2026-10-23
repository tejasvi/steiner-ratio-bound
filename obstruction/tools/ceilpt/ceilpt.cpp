// ceilpt.cpp: pointwise ceiling of the published split/lemma family of arXiv:2601.22365 at given points, in double
// precision with the authors' own generated formulas (certificate/d_regular/formulas F0..F8, unchanged; MIT licence, Copyright (c)
// 2025-2026 Yisi Ke and Yankai Shu, notice in LICENSE_PKU_MIT.txt). Diagnostic, not rigorous: an independent second evaluation of
// way 1 of obstruction.py. Each generated function is one (split, lemma) pair and is affine in rho (rho * L_t + L_S+ - L_S-); it
// returns INF when its lemma condition fails. Evaluating at rho = 0 and 1 gives the critical rho_k = (L_S- - L_S+) / L_t of every
// usable pair; the ceiling is max_k rho_k.
// Build: g++ ceilpt.cpp -O2 -std=c++23 -DFAM_STEINER=0 -DF_VAL=2 -o ceilpt   (formulas/ next to this file)
// usage: ceilpt b c d s e [b c d s e ...]   (d_regular, subcase f >= d with f := d)
# include <bits/stdc++.h>
using namespace std;
using ld = double;
using ull = unsigned long long;
thread_local ld rho = 0;
const ld INF = 1e18, eps = 1e-6, sqrt3 = sqrt(3.0l);
#if FAM_STEINER
const int NV = 8;
#else
const int NV = 6;
#endif
const int n = F_VAL == 2 ? NV - 1 : NV;

template<typename... Args>
ld max(ld a, ld b, ld c, Args... args) { return max({a, b, c, args...}); }

// -ffast-math makes isinf() unreliable; test the bit pattern (as the original generator does)
constexpr bool isinfinity(ld x) { return bit_cast<ull>(x) == bit_cast<ull>(numeric_limits<ld>::infinity()); }

static inline void fullargs(const ld *p, ld *x)
{
	for(int i = 0; i < n; i++) x[i] = p[i];
	if(F_VAL == 2) x[NV - 1] = p[2];
}
static inline bool glob_cond(const ld *x)
{
#if FAM_STEINER
	bool ok = max(x[4], x[5]) <= max(x[0], (ld)1);
#else
	bool ok = true;
#endif
	if(F_VAL == 1) ok = ok && x[NV - 1] <= x[2];
	if(F_VAL == 3) ok = ok && x[NV - 1] >= x[2];   // f >= d with f a box variable (no f := d reduction)
	return ok;
}

template<int>
struct F;
# include "formulas/F0"
# include "formulas/F1"
# include "formulas/F2"
# include "formulas/F3"
# include "formulas/F4"
# include "formulas/F5"
# include "formulas/F6"
# include "formulas/F7"
# include "formulas/F8"
const int m = M8;
using Fn = ld (*)(ull, const ld *);
template<int I>
ld callF(ull mono_mask, const ld *x)
{
#if FAM_STEINER
	return F<I>{}(mono_mask, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]);
#else
	return F<I>{}(mono_mask, x[0], x[1], x[2], x[3], x[4], x[5]);
#endif
}
template<int... I>
constexpr array<Fn, sizeof...(I)> make_ftab(integer_sequence<int, I...>) { return {&callF<I>...}; }
const auto ftab = make_ftab(make_integer_sequence<int, m>{});
template<int... I>
constexpr array<int, sizeof...(I)> make_sid(integer_sequence<int, I...>) { return {F<I>::split_id...}; }
constexpr auto split_ids = make_sid(make_integer_sequence<int, m>{});
template<int... I>
constexpr array<int, sizeof...(I)> make_lid(integer_sequence<int, I...>) { return {F<I>::lemma_id...}; }
constexpr auto lemma_ids = make_lid(make_integer_sequence<int, m>{});

// pointwise ceiling at box point p (n coordinates); -1 if outside the case domain; also the best split index
static double ceil_at(const ld *p, int &best)
{
	ld x[NV]; fullargs(p, x); best = -1;
	if(!glob_cond(x)) return -1;
	double r = -1e300;
	for(int k = 0; k < m; k++)
	{
		rho = 0; ld f0 = ftab[k](0, x);
		if(!(f0 < INF / 2)) continue;
		rho = 1; ld f1 = ftab[k](0, x);
		ld lt = f1 - f0;
		if(!(lt > 0)) continue;
		double rk = -f0 / lt;
		if(rk > r) { r = rk; best = k; }
	}
	return r;
}

struct Rec { int depth; array<array<double, 2>, n> box; double g; int arg; };
struct Res { int depth; double c_centre, c_min; array<double, n> pmin; int split; array<array<double, 2>, n> box; bool orig_cert; int nans; };

int main(int argc, char **argv)
{
	if(argc < 6 || (argc - 1) % n) { fprintf(stderr, "usage: ceilpt b c d s e [...]\n"); return 2; }
	for(int a = 1; a + n <= argc; a += n)
	{
		ld p[NV], x[NV];
		for(int i = 0; i < n; i++) p[i] = strtod(argv[a + i], 0);
		fullargs(p, x);
		vector<tuple<double, int>> rows; int usable = 0;
		for(int k = 0; k < m; k++)
		{
			rho = 0; ld f0 = ftab[k](0, x);
			if(!(f0 < INF / 2)) continue;
			rho = 1; ld f1 = ftab[k](0, x);
			ld lt = f1 - f0;
			if(!(lt > 0)) continue;
			usable++; rows.push_back({-f0 / lt, k});
		}
		sort(rows.rbegin(), rows.rend());
		printf("point (b,c,d,s,e) =");
		for(int i = 0; i < n; i++) printf(" %s", argv[a + i]);
		printf(", f := d: %d generated (split, lemma) functions, %d usable; ceiling rho* = %.12f at function %d (split %d, lemma %d)\n",
		       m, usable, get<0>(rows[0]), get<1>(rows[0]), split_ids[get<1>(rows[0])], lemma_ids[get<1>(rows[0])]);
		for(int t = 0; t < 8 && t < (int)rows.size(); t++)
			printf("  %.12f  function %d  split %d  lemma %d\n", get<0>(rows[t]), get<1>(rows[t]), split_ids[get<1>(rows[t])], lemma_ids[get<1>(rows[t])]);
	}
	return 0;
}
