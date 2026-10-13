"""Exact checks for milestone D1 (simplicity and primitivity of the CCR algebra).

Run from any directory; it reads and writes no files. Exact arithmetic with sympy: every
assert is an equality or a proved inequality, never a tolerance.

Model: V = Q^2 with sigma((a, b), (c, d)) = a d - b c. Operators act on finitely supported
functions V -> C, stored as dicts. Conventions as in BosonicLean/Weyl/Basic.lean and Right.lean
(in the dependency BosonicLean since 29 Sep 2026):
  (W(u) f)(v) = e^{i sigma(u, v)/2} f(v + u),   (R(w) f)(v) = e^{-i sigma(w, v)/2} f(v + w),
  W(u) W(w) = e^{-i sigma(u, w)/2} W(u + w),     tau(a) = <delta_0, a delta_0>.
"""
import random
from fractions import Fraction as Fr

import sympy as sp

rng = random.Random(20260927)
checks = []


def check(name, ok):
    checks.append((name, bool(ok)))
    print(('PASS ' if ok else 'FAIL ') + name)


def sigma(u, w):
    return u[0] * w[1] - u[1] * w[0]


def add(u, w):
    return (u[0] + w[0], u[1] + w[1])


def neg(u):
    return (-u[0], -u[1])


def smul(t, u):
    return (t * u[0], t * u[1])


def ph(x):
    return sp.exp(sp.I * sp.Rational(x.numerator, x.denominator))


def W(u, f, s=1):
    """W(u) for the form s*sigma; s = -1 gives the right Weyl operator R(u)."""
    return {add(v, neg(u)): sp.simplify(ph(Fr(s) * sigma(u, add(v, neg(u))) / 2) * c)
            for v, c in f.items()}


def R(w, f):
    return W(w, f, s=-1)


def eq(f, g):
    keys = set(f) | set(g)
    return all(sp.simplify(f.get(k, 0) - g.get(k, 0)) == 0 for k in keys)


def scale(c, f):
    return {k: c * v for k, v in f.items()}


def delta(v):
    return {v: sp.Integer(1)}


def rvec():
    return (Fr(rng.randint(-6, 6), rng.randint(1, 4)), Fr(rng.randint(-6, 6), rng.randint(1, 4)))


def rfun():
    return {rvec(): sp.Integer(rng.randint(-3, 3)) + sp.I * rng.randint(-3, 3) for _ in range(3)}


# 1. Weyl relation and the right Weyl operators (milestone B facts, re-checked in this model).
ok_rel = ok_comm = ok_rdelta = True
for _ in range(6):
    u, w, f = rvec(), rvec(), rfun()
    ok_rel &= eq(W(u, W(w, f)), scale(ph(-sigma(u, w) / 2), W(add(u, w), f)))
    ok_comm &= eq(W(u, R(w, f)), R(w, W(u, f)))
    ok_rdelta &= eq(R(w, delta((0, 0))), delta(neg(w)))
check("Weyl relation W(u)W(w) = e^{-i sigma(u,w)/2} W(u+w)", ok_rel)
check("R(w) commutes with W(u)", ok_comm)
check("R(w) delta_0 = delta_{-w} (step 1: faithfulness)", ok_rdelta)

# 2. Conjugation phase: W(x) W(v) W(x)* = e^{-i sigma(x,v)} W(v), with W(x)* = W(-x).
ok_conj = True
for _ in range(6):
    x, v, f = rvec(), rvec(), rfun()
    ok_conj &= eq(W(x, W(v, W(neg(x), f))), scale(ph(-sigma(x, v)), W(v, f)))
check("W(x) W(v) W(x)* = e^{-i sigma(x,v)} W(v)", ok_conj)

# tau(W(v)) = [v = 0]
check("tau(W(v)) = [v = 0]",
      all(W(v, delta((0, 0))).get((0, 0), 0) == (1 if v == (0, 0) else 0)
          for v in [(Fr(0), Fr(0)), (Fr(1), Fr(0)), (Fr(1, 2), Fr(-3))]))

# 3. Averaging: M_n^u(W(v)) = c_n W(v), c_n = (1/n) sum_{k<n} e^{-ik theta}, theta = sigma(u, v).
th, n = sp.symbols('theta n', real=True)
ok_avg = True
for _ in range(3):
    u, v, f = rvec(), rvec(), rfun()
    N = 3
    lhs = {}
    for k in range(N):
        term = W(smul(k, u), W(v, W(neg(smul(k, u)), f)))
        for key, c in term.items():
            lhs[key] = lhs.get(key, 0) + c / N
    cN = sum(ph(-k * sigma(u, v)) for k in range(N)) / N
    ok_avg &= eq(lhs, scale(cN, W(v, f)))
check("M_3^u(W(v)) = ((1/3) sum_k e^{-ik sigma(u,v)}) W(v)", ok_avg)

# Closed form of the geometric mean, and the bound |c_n| <= 2 / (n |1 - e^{-i theta}|).
k = sp.symbols('k', integer=True)
z = sp.exp(-sp.I * th)
geo = sp.summation(z**k, (k, 0, 4))
check("sum_{k<5} z^k = (1 - z^5)/(1 - z)", sp.simplify(geo * (1 - z) - (1 - z**5)) == 0)

# A rational nonzero theta is never in 2 pi Z (pi is irrational), so for rational data any
# u with sigma(u, v) != 0 already works; the rescaling t is needed only for general V.
check("theta/(2 pi) is irrational for theta = 3/7",
      (sp.Rational(3, 7) / (2 * sp.pi)).is_rational is False)

# Step 3, choice of u0: for v_1..v_N nonzero, some u0 in {e2, e1 + j e2 : 0 <= j <= N}
# has sigma(u0, v_j) != 0 for all j (each v_j kills at most one member of this family).
ok_choice = True
for _ in range(20):
    vs = [v for v in (rvec() for _ in range(5)) if v != (0, 0)]
    fam = [(Fr(0), Fr(1))] + [(Fr(1), Fr(j)) for j in range(len(vs) + 1)]
    ok_choice &= any(all(sigma(u0, v) != 0 for v in vs) for u0 in fam)
    ok_choice &= all(sum(sigma(u0, v) == 0 for u0 in fam) <= 1 for v in vs)
check("generic u0 exists; each v != 0 is sigma-orthogonal to at most one member", ok_choice)

failed = [name for name, ok in checks if not ok]
print(f"\n{len(checks) - len(failed)}/{len(checks)} checks passed")
raise SystemExit(1 if failed else 0)
