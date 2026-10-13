"""Milestone B check script: Weyl operators on l2(V), exact on finitely supported vectors.

V = R^2 with the standard symplectic form sigma(u, v) = u1 v2 - u2 v1 (and a degenerate
form for contrast). Vectors of l2(V) with finite support are dicts {point: coefficient};
Weyl operators map them to finitely supported vectors, so every identity below is checked
exactly up to floating-point rounding, on random rational points.

Checked:
  1. W(u) preserves the l2 norm; W(0) = 1.
  2. Weyl relation W(u) W(w) = exp(-i sigma(u,w)/2) W(u+w).
  3. <W(u) f, g> = <f, W(-u) g>, i.e. W(u)* = W(-u); W(u) W(-u) = 1.
  4. Relabelling: U_T f = f o T^{-1} for symplectic T; U_T W(u) U_T^{-1} = W(T u);
     U_{T1 T2} = U_{T1} U_{T2}. For an anti-symplectic T the identity fails.
  5. Right Weyl operators R(w) f (v) = exp(-i sigma(w,v)/2) f(v+w) commute with every W(u);
     R(w) delta_0 = delta_{-w}; W(u) delta_0 = delta_{-u}.
  6. tau(a) = <delta_0, a delta_0>: tau(W(v)) = [v = 0]; tau(W(u) W(w)) = 0 unless u+w = 0.
"""
import cmath
import random
from fractions import Fraction as Q

random.seed(20260925)
checks = []


def check(name, ok):
    checks.append((name, ok))
    print(('PASS ' if ok else 'FAIL ') + name)


def sig(u, v):
    return float(u[0] * v[1] - u[1] * v[0])


def add(u, v):
    return (u[0] + v[0], u[1] + v[1])


def neg(u):
    return (-u[0], -u[1])


def rpt():
    return (Q(random.randint(-6, 6), random.randint(1, 3)), Q(random.randint(-6, 6), random.randint(1, 3)))


def rvec(n=4):
    return {rpt(): complex(random.gauss(0, 1), random.gauss(0, 1)) for _ in range(n)}


def W(u, f, s=sig):
    # (W(u) f)(v) = e^{i s(u,v)/2} f(v+u); the support moves from p to p - u.
    return {add(p, neg(u)): cmath.exp(1j * s(u, add(p, neg(u))) / 2) * c for p, c in f.items()}


def R(w, f, s=sig):
    return {add(p, neg(w)): cmath.exp(-1j * s(w, add(p, neg(w))) / 2) * c for p, c in f.items()}


def smul(z, f):
    return {p: z * c for p, c in f.items()}


def inner(f, g):
    return sum(f[p].conjugate() * g[p] for p in f if p in g)


def close(f, g, tol=1e-12):
    keys = set(f) | set(g)
    return all(abs(f.get(k, 0) - g.get(k, 0)) < tol for k in keys)


def norm2(f):
    return sum(abs(c) ** 2 for c in f.values())


N = 60
# 1. isometry and W(0) = 1
check('W(u) preserves the l2 norm',
      all(abs(norm2(W(rpt(), f)) - norm2(f)) < 1e-12 for f in [rvec() for _ in range(N)]))
check('W(0) = 1', all(close(W((Q(0), Q(0)), f), f) for f in [rvec() for _ in range(N)]))

# 2. Weyl relation
ok = True
for _ in range(N):
    u, w, f = rpt(), rpt(), rvec()
    ok &= close(W(u, W(w, f)), smul(cmath.exp(-1j * sig(u, w) / 2), W(add(u, w), f)))
check('W(u)W(w) = exp(-i sigma(u,w)/2) W(u+w)', ok)

# 3. adjoint
ok = True
for _ in range(N):
    u, f, g = rpt(), rvec(), rvec()
    g = {**g, **{add(p, neg(u)): complex(1, 2) for p in f}}  # force overlap
    ok &= abs(inner(W(u, f), g) - inner(f, W(neg(u), g))) < 1e-12
check('<W(u) f, g> = <f, W(-u) g>', ok)
check('W(u)W(-u) = 1', all(close(W(u, W(neg(u), f)), f) for u, f in [(rpt(), rvec()) for _ in range(N)]))


# 4. relabelling by symplectic T (det T = 1) and anti-symplectic S (det S = -1)
def mat_apply(M, v):
    return (M[0][0] * v[0] + M[0][1] * v[1], M[1][0] * v[0] + M[1][1] * v[1])


def mat_inv(M):
    d = M[0][0] * M[1][1] - M[0][1] * M[1][0]
    return ((M[1][1] / d, -M[0][1] / d), (-M[1][0] / d, M[0][0] / d))


def mat_mul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)) for i in range(2))


def U(M, f):
    # (U_T f)(v) = f(T^{-1} v): the support moves from p to T p.
    return {mat_apply(M, p): c for p, c in f.items()}


def rsympl():
    a, b, c = (Q(random.randint(-3, 3)) for _ in range(3))
    a = a if a != 0 else Q(1)
    # det = 1: ((a, b), (c, (1 + b c)/a))
    return ((a, b), (c, (1 + b * c) / a))


ok = True
for _ in range(N):
    T, u, f = rsympl(), rpt(), rvec()
    lhs = U(T, W(u, U(mat_inv(T), f)))
    ok &= close(lhs, W(mat_apply(T, u), f))
check('U_T W(u) U_T^{-1} = W(T u) for symplectic T', ok)
ok = True
for _ in range(N):
    T1, T2, f = rsympl(), rsympl(), rvec()
    ok &= close(U(mat_mul(T1, T2), f), U(T1, U(T2, f)))
check('U_{T1 T2} = U_{T1} U_{T2}', ok)
S = ((Q(1), Q(0)), (Q(0), Q(-1)))  # time-reversal-like reflection, det -1
u, f = (Q(1), Q(1)), {(Q(0), Q(1)): 1 + 0j}
check('anti-symplectic S: U_S W(u) U_S^{-1} != W(S u)',
      not close(U(S, W(u, U(mat_inv(S), f))), W(mat_apply(S, u), f)))

# 5. right Weyl operators
ok = True
for _ in range(N):
    u, w, f = rpt(), rpt(), rvec()
    ok &= close(W(u, R(w, f)), R(w, W(u, f)))
check('R(w) W(u) = W(u) R(w)', ok)
d0 = {(Q(0), Q(0)): 1 + 0j}
check('R(w) delta_0 = delta_{-w}', all(close(R(w, d0), {neg(w): 1 + 0j}) for w in [rpt() for _ in range(N)]))
check('W(u) delta_0 = delta_{-u}', all(close(W(u, d0), {neg(u): 1 + 0j}) for u in [rpt() for _ in range(N)]))


# 6. the vector state tau
def tau_W(u):
    return inner(d0, W(u, d0))


check('tau(W(v)) = [v = 0]',
      abs(tau_W((Q(0), Q(0))) - 1) < 1e-12 and all(abs(tau_W(v)) < 1e-12 for v in [rpt() for _ in range(N)] if v != (0, 0)))
ok = True
for _ in range(N):
    u, w = rpt(), rpt()
    val = inner(d0, W(u, W(w, d0)))
    ok &= (abs(val) < 1e-12) if add(u, w) != (0, 0) else abs(abs(val) - 1) < 1e-12
check('tau(W(u)W(w)) = 0 unless u + w = 0', ok)

# degenerate form: the relation still holds (only alternation is used)
ok = True
zero = lambda u, v: 0.0
for _ in range(20):
    u, w, f = rpt(), rpt(), rvec()
    ok &= close(W(u, W(w, f, zero), zero), W(add(u, w), f, zero))
check('sigma = 0: W(u)W(w) = W(u+w)', ok)

print(f'{sum(ok for _, ok in checks)} of {len(checks)} checks pass')
