#!/usr/bin/env python3
"""identities.py: exact symbolic checks of the algebraic identities and coordinate facts used in the proofs of
Sections 2-3 of the paper (coordinates of Lemma 2.5, w = e^{i pi/3}). Every check prints OK or FAIL; the summary line
counts them. Needs sympy.  usage: python3 -I -B identities.py"""
import sympy as sp

b, s, c, d, e, f, g, u, v, a5 = sp.symbols("b s c d e f g u v a5", positive=True)
I = sp.I
r3 = sp.sqrt(3)
w = sp.Rational(1, 2) + r3 / 2 * I          # e^{i pi/3}
wb = sp.conjugate(w)
A = sp.Integer(0); X = sp.Integer(1)
B = X + b * w; Y = X + s * wb; D = Y + d; Z = Y - c * w; R = Z - e; Q = Z + f * wb
U = D + u * w; V = D + v * wb
res = []


def zero(name, expr):
    ok = sp.simplify(sp.expand(sp.nsimplify(expr))) == 0
    res.append(ok)
    print(("OK   " if ok else "FAIL ") + name)


def n2(z):                                   # |z|^2
    return sp.expand(sp.re(z) ** 2 + sp.im(z) ** 2)


def lam(p, p0, delta):                       # signed distance to the left of the line through p0 with unit direction delta
    return sp.im(sp.expand((p - p0) * sp.conjugate(delta)))


def tpar(p, p0, delta):                      # coordinate of the foot of p along the line
    return sp.re(sp.expand((p - p0) * sp.conjugate(delta)))


# Lemma 2.5: directions and the 120-degree angles (unit edge vectors at each Steiner point sum to 0)
zero("X: (A-X)/1 + (B-X)/b + (Y-X)/s = 0", (A - X) + (B - X) / b + (Y - X) / s)
zero("Y: (X-Y)/s + (D-Y)/d + (Z-Y)/c = 0", (X - Y) / s + (D - Y) / d + (Z - Y) / c)
zero("Z: (Y-Z)/c + (R-Z)/e + (Q-Z)/f = 0", (Y - Z) / c + (R - Z) / e + (Q - Z) / f)
zero("D (d_steiner): (Y-D)/d + (U-D)/u + (V-D)/v = 0", (Y - D) / d + (U - D) / u + (V - D) / v)
zero("|AY|^2 = 1 + s + s^2", n2(Y) - (1 + s + s ** 2))
zero("|AZ|^2 = 1 + s + s^2 - c + cs + c^2", n2(Z) - (1 + s + s ** 2 - c + c * s + c ** 2))

# l5: line through R with direction w^2
d5 = w ** 2
W = 1 - c - e
zero("W = 1-c-e lies on l5", lam(W, R, d5))
zero("|RW|^2 = (s+c)^2", n2(W - R) - (s + c) ** 2)
zero("W - R = (s+c) w^2 (W beyond R along l5)", sp.expand(W - R - (s + c) * d5))
zero("lambda5(A3) = -(sqrt3/2) e", lam(Z, R, d5) + r3 / 2 * e)
zero("lambda5(A1) = -(sqrt3/2)(c+e)", lam(X, R, d5) + r3 / 2 * (c + e))
zero("lambda5(A2) = -(sqrt3/2)(c+e)", lam(Y, R, d5) + r3 / 2 * (c + e))
zero("lambda5(A) = -(sqrt3/2)(c+e-1)", lam(A, R, d5) + r3 / 2 * (c + e - 1))
zero("foot of A on l5 at distance (1+2s+c-e)/2 from R", tpar(A, R, d5) - (1 + 2 * s + c - e) / 2)
H0 = R + tpar(A, R, d5) * d5
zero("foot H of A on l5 = -(c+e-1)(3/4 + sqrt3/4 i)", sp.expand(H0 + (c + e - 1) * (sp.Rational(3, 4) + r3 / 4 * I)))
zero("Lemma 3.5 (c=1): foot at distance 1+s-e/2 from R", (tpar(A, R, d5) - (1 + s - e / 2)).subs(c, 1))
zero("|AR|^2 - e^2 = (1+s)(1+s-e) at c=1", (n2(R) - e ** 2 - (1 + s) * (1 + s - e)).subs(c, 1))
x3 = 1 + (s - c) / 2
zero("Re A3 = 1 + (s-c)/2", sp.re(Z) - x3)
zero("|AA4|^2 = |AA3|^2 - e(2 x3 - e)", n2(R) - (n2(Z) - e * (2 * x3 - e)))
zero("4 x3^2 - |AA3|^2 = 3(1+s)(1-c)", 4 * x3 ** 2 - n2(Z) - 3 * (1 + s) * (1 - c))
zero("Pi: W -> A1 is real (W < 1 since c + e > 0)", sp.im(X - W))
zero("Pi: A1 -> A2 = s wb", sp.expand(Y - X - s * wb))
zero("Pi: A2 -> A3 = c (-w)", sp.expand(Z - Y + c * w))
zero("Pi: A3 -> A4 = e (-1)", sp.expand(R - Z + e))
zero("Pi: A4 -> W = (s+c) w^2 (turns of -60 deg at every vertex: convex, clockwise)", sp.expand(W - R - (s + c) * d5))

# Lemma 3.6 (L1, L2): T1 margins and T4 for sigma_3
zero("L1: (1+2s+c-e) - (2c + (2-2/sqrt3)s) = 1 - c - e + (2/sqrt3)s", (1 + 2 * s + c - e) - (2 * c + (2 - 2 / r3) * s) - (1 - c - e + 2 / r3 * s))
zero("L2: (1+2s+c-e) - (2s + (2-2/sqrt3)c) = 1 + (2/sqrt3 - 1)c - e", (1 + 2 * s + c - e) - (2 * s + (2 - 2 / r3) * c) - (1 + (2 / r3 - 1) * c - e))
P3 = Y + (1 + 2 * s) * w
zero("Y + (1+2s) w lies on the line through A and H (direction 3/4 + sqrt3/4 i)", sp.im(sp.expand(P3 * sp.conjugate(sp.Rational(3, 4) + r3 / 4 * I))))
zero("Y + (1+2s) w lies on the line of sigma_3 (Y - t w), at t = -(1+2s) < 0", sp.im(sp.expand((P3 - Y) * sp.conjugate(w))))

# Lemma 3.7 (L5) and Lemma 3.12 (X2): H = R - ((c-e)/2) wb is the foot of Y on l5
H5 = R - (c - e) / 2 * wb
zero("H5 = R + ((c-e)/2) w^2", sp.expand(H5 - (R + (c - e) / 2 * d5)))
zero("foot of Y on l5 at distance (c-e)/2 from R", tpar(Y, R, d5) - (c - e) / 2)
zero("H5 lies on l5", lam(H5, R, d5))
zero("|YH5|^2 = (3/4)(c+e)^2", n2(H5 - Y) - sp.Rational(3, 4) * (c + e) ** 2)
zero("lambda5(Y) = -(sqrt3/2)(c+e)", lam(Y, R, d5) + r3 / 2 * (c + e))
zero("door Y->H5 has direction 210 deg (H5 - Y is a positive multiple of e^{i 7pi/6})",
     sp.im(sp.expand((H5 - Y) * sp.conjugate(-r3 / 2 - I / 2))))
zero("door Y->H5: real part of (H5-Y)/e^{i7pi/6} = (sqrt3/2)(c+e) > 0",
     sp.re(sp.expand((H5 - Y) * sp.conjugate(-r3 / 2 - I / 2))) - r3 / 2 * (c + e))
zero("sigma_3 leaves Y in direction 240 deg (Z - Y = -c w)", sp.expand(Z - Y + c * w))
zero("|AH5|^2 - |AZ|^2 = ((3/4)(c+e)^2 - c^2) - c/2 - 3e/2 - cs",
     n2(H5) - n2(Z) - ((sp.Rational(3, 4) * (c + e) ** 2 - c ** 2) - c / 2 - 3 * e / 2 - c * s))
zero("|AR|^2 - |AH5|^2 = (1/4)(c-e)(2+4s+c-e)", n2(R) - n2(H5) - sp.Rational(1, 4) * (c - e) * (2 + 4 * s + c - e))
zero("height of H5 above the line ZR = (sqrt3/4)(c-e)", sp.im(H5 - Z) - r3 / 4 * (c - e))
zero("height of Y above the line ZR = (sqrt3/2)c", sp.im(Y - Z) - r3 / 2 * c)
zero("|RQ|^2 = e^2 + ef + f^2", n2(Q - R) - (e ** 2 + e * f + f ** 2))
zero("(e+f)^2 - |RQ|^2 = ef", (e + f) ** 2 - n2(Q - R) - e * f)
zero("|RQ|^2 - (e/2 + f)^2 = (3/4) e^2 (dPhi/df >= 0)", n2(Q - R) - (e / 2 + f) ** 2 - sp.Rational(3, 4) * e ** 2)

# Lemma 3.8 (L8): l6 through A5 = R + a5 w^2 with direction w
A5 = R + a5 * d5
M = 1 + s - e - a5
zero("M = 1+s-e-a5 lies on l6", lam(M, A5, w))
zero("|A5 M| = s + c - a5 (M - A5 = (s+c-a5) w)", sp.expand(M - A5 - (s + c - a5) * w))
zero("lambda6(A4) = -(sqrt3/2) a5", lam(R, A5, w) + r3 / 2 * a5)
zero("lambda6(A3) = -(sqrt3/2)(a5+e)", lam(Z, A5, w) + r3 / 2 * (a5 + e))
zero("lambda6(A2) = -(sqrt3/2)(a5+e)", lam(Y, A5, w) + r3 / 2 * (a5 + e))
zero("lambda6(A1) = (sqrt3/2)(M-1)", lam(X, A5, w) - r3 / 2 * (M - 1))
zero("lambda6(A) = (sqrt3/2) M", lam(A, A5, w) - r3 / 2 * M)
zero("sigma_3 is parallel to l6 (direction -w)", sp.im(sp.expand((Z - Y) * sp.conjugate(w))))
zero("|AM| = a5 - (s+1-e) when M < 0", (-M) - (a5 - (s + 1 - e)))
zero("|AA4|^2 - (c+e-1)^2 = (s+c)(s+1-e)", n2(R) - (c + e - 1) ** 2 - (s + c) * (s + 1 - e))

# Mirror maps (Section 3.4 and Lemma 3.13)
mD = lambda z: sp.conjugate(D - z) / d
zero("mirror D -> 0", mD(D))
zero("mirror Y -> 1", mD(Y) - 1)
zero("mirror Z -> 1 + (c/d) wb", sp.expand(mD(Z) - (1 + c / d * wb)))
zero("mirror Q -> 1 + (c/d) wb - (f/d) w", sp.expand(mD(Q) - (1 + c / d * wb - f / d * w)))
Q2 = Q + g
zero("mirror Q2 -> mirror(Q) - g/d", sp.expand(mD(Q2) - (mD(Q) - g / d)))
mV = lambda z: wb * sp.conjugate(V - z) / v
zero("mirror_V V -> 0", mV(V))
zero("mirror_V D -> 1", sp.expand(mV(D) - 1))
zero("mirror_V Y -> 1 + (d/v) wb", sp.expand(mV(Y) - (1 + d / v * wb)))
zero("mirror_V Z -> 1 + (d/v) wb - (c/v) w", sp.expand(mV(Z) - (1 + d / v * wb - c / v * w)))
zero("mirror_V Q -> mirror_V(Z) - f/v", sp.expand(mV(Q) - (mV(Z) - f / v)))
zero("|VQ|^2 - (c+f-v)^2 = (d+c)(d+v-f)", n2(Q - V) - (c + f - v) ** 2 - (d + c) * (d + v - f))
zero("|VY|^2 = d^2 + dv + v^2 (> v^2)", n2(Y - V) - (d ** 2 + d * v + v ** 2))

# Lemma 3.13 (Y2)
xQ = d + (c - f) / 2
zero("x_Q = Re(D - Q) = d + (c-f)/2", sp.re(D - Q) - xQ)
zero("|DQ2|^2 = |DQ|^2 - g(2 x_Q - g)", n2(D - Q2) - (n2(D - Q) - g * (2 * xQ - g)))
zero("|DQ*| = |DQ| for Q* = Q + 2 x_Q", n2(D - (Q + 2 * xQ)) - n2(D - Q))
zero("L(S') - (g - 2 x_Q) = 1 + b + s + 3d + 2c + e", (1 + b + s + d + c + e + f + g) - (g - 2 * xQ) - (1 + b + s + 3 * d + 2 * c + e))
zero("|DQ2|^2 - (f+g-d)^2 = (c+f)(c+d-g)", n2(D - Q2) - (f + g - d) ** 2 - (c + f) * (c + d - g))
zero("2 x_Q <= c + d when f >= d: c + d - 2 x_Q = f - d", (c + d) - 2 * xQ - (f - d))

# Section 2.6: three points, c'^2 = a^2 + b'^2 - 2ab' cos(gamma), area = ab' sin(gamma)/2
aa, bb, gam = sp.symbols("aa bb gam", positive=True)
cc2 = aa ** 2 + bb ** 2 - 2 * aa * bb * sp.cos(gam)
lhs = (aa ** 2 + bb ** 2 + cc2) / 2 + 2 * r3 * (aa * bb * sp.sin(gam) / 2)
zero("L_S^2 = a^2 + b^2 + 2ab sin(gamma - 30deg)", sp.expand(sp.expand_trig(lhs - (aa ** 2 + bb ** 2 + 2 * aa * bb * sp.sin(gam - sp.pi / 6)))))
zero("a^2 + ab + b^2 - (3/4)(a+b)^2 = (a-b)^2/4", aa ** 2 + aa * bb + bb ** 2 - sp.Rational(3, 4) * (aa + bb) ** 2 - (aa - bb) ** 2 / 4)

print(f"SUMMARY: {sum(res)} OK, {len(res) - sum(res)} FAIL")
