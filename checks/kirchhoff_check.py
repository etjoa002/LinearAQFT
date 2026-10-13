"""Stage G0 checks: the Kirchhoff Green operators of the wave operator on R^4 (massless, 3+1).

Conventions: points (t, x) in R x R^3, P = d_t^2 - Laplacian, and
  (G+ f)(t,x) = (1/4pi) int_{R^3} f(t - |y|, x - y) / |y| dy,
  (G- f)(t,x) = (1/4pi) int_{R^3} f(t + |y|, x - y) / |y| dy.
Test functions are Gaussians, whose derivatives are exact in closed form; integrals over R^3 use
polar coordinates y = r*w with Gauss-Legendre in r, in cos(theta) and in the azimuth.

Checks:
 1. core identity  int (P phi)(|y|, y)/|y| dy = 4 pi phi(0,0), i.e. G+ P phi = phi at (0,0),
    for an off-centre anisotropic Gaussian; also G+ P phi = phi and G- P phi = phi at other points;
 2. the one-dimensional reduction  int_0^oo rho (a_ss - a_rr - (2/rho) a_r)(rho, rho) drho = a(0,0);
 3. formal adjointness <f, G+ g> = <g, G- f> (Gaussian cross-correlations in closed form);
 4. the commutator  P(chi u) - chi P u = chi'' u + 2 chi' u_t  for a time cutoff chi(t);
 5. support: for f supported in a ball B, the integrand of (G+ f)(t,x) vanishes identically when
    (t,x) is outside J+(B) (sampled).
Added at later milestones (G1, G3, G4):
 6. (G1) formal symmetry int (box u) v = int u (box v) for Gaussians;
 7. (G3) the radial Laplacian f_rr + (2/r) f_r of a radial function;
 8. (G3) box commutes with the time and space reflections and translations;
 9. (G4) box(psi o g) = (box psi) o g for random orthochronous Poincare maps g;
10. (G4) the slab compactness bound tau_n(v) >= (n0 - |n|) v0 for future causal v.
"""
import math
import numpy as np

rng = np.random.default_rng(20260928)
leg = np.polynomial.legendre.leggauss


def sphere_rule(nth=48, nph=96):
    u, wu = leg(nth)                       # u = cos(theta) in [-1, 1]
    ph = (np.arange(nph) + 0.5) * 2 * math.pi / nph
    U, PH = np.meshgrid(u, ph, indexing="ij")
    W = np.outer(wu, np.full(nph, 2 * math.pi / nph))
    s = np.sqrt(1 - U**2)
    dirs = np.stack([s * np.cos(PH), s * np.sin(PH), U], axis=-1)
    return dirs.reshape(-1, 3), W.reshape(-1)  # sum of weights = 4 pi


def radial_rule(R=14.0, n=400):
    x, w = leg(n)
    return 0.5 * R * (x + 1), 0.5 * R * w


DIRS, WS = sphere_rule()
RS, WR = radial_rule()
assert abs(WS.sum() - 4 * math.pi) < 1e-12


def integrate_R3_over_r(F):
    """int_{R^3} F(y)/|y| dy = int_0^oo r dr int_{S^2} F(r w) dsigma."""
    tot = 0.0
    for r, wr in zip(RS, WR):
        tot += wr * r * np.dot(WS, F(r * DIRS))
    return tot


class Gauss:
    """phi(s, y) = exp(-alpha (s - s0)^2 - (y - c)^T B (y - c)), B symmetric positive."""
    def __init__(self, alpha, s0, B, c):
        self.a, self.s0, self.B, self.c = alpha, s0, np.asarray(B, float), np.asarray(c, float)

    def val(self, s, y):
        d = y - self.c
        return np.exp(-self.a * (s - self.s0) ** 2 - np.einsum("...i,ij,...j->...", d, self.B, d))

    def box(self, s, y):
        # d_s^2 phi = (4 a^2 (s-s0)^2 - 2a) phi;  Lap phi = (4 |B d|^2 - 2 tr B) phi
        d = y - self.c
        Bd = d @ self.B
        lap = 4 * np.einsum("...i,...i->...", Bd, Bd) - 2 * np.trace(self.B)
        dss = 4 * self.a**2 * (s - self.s0) ** 2 - 2 * self.a
        return (dss - lap) * self.val(s, y)


def check_core():
    B = np.array([[1.3, 0.2, 0.0], [0.2, 0.8, -0.1], [0.0, -0.1, 1.1]])
    phi = Gauss(0.9, 0.4, B, [0.3, -0.5, 0.2])
    worst = 0.0
    for (t, x, sign) in [(0.0, np.zeros(3), +1), (0.7, np.array([0.1, 0.4, -0.3]), +1),
                         (-0.5, np.array([-0.6, 0.0, 0.5]), -1), (1.1, np.array([0.2, -0.2, 0.9]), -1)]:
        # (G^sign P phi)(t,x) = (1/4pi) int (P phi)(t - sign|y|, x - y)/|y| dy
        F = lambda Y: phi.box(t - sign * np.linalg.norm(Y, axis=-1), x - Y)
        lhs = integrate_R3_over_r(F) / (4 * math.pi)
        rhs = float(phi.val(t, x))
        worst = max(worst, abs(lhs - rhs))
        print(f"  core identity G{'+' if sign > 0 else '-'} P phi = phi at t={t:+.2f}: "
              f"{lhs:.12f} vs {rhs:.12f}")
    assert worst < 1e-8, worst
    return worst


def check_reduction():
    worst = 0.0
    for alpha, s0, beta in [(0.9, 0.4, 1.2), (1.5, -0.3, 0.7), (0.6, 1.0, 2.0)]:
        a = lambda s, r: math.exp(-alpha * (s - s0) ** 2 - beta * r * r)
        def boxa(s, r):
            ass = 4 * alpha**2 * (s - s0) ** 2 - 2 * alpha
            arr = 4 * beta**2 * r * r - 2 * beta
            ar_over_r = -2 * beta           # a_r / r
            return (ass - arr - 2 * ar_over_r) * a(s, r)
        lhs = sum(w * r * boxa(r, r) for r, w in zip(RS, WR))
        worst = max(worst, abs(lhs - a(0.0, 0.0)))
        print(f"  1D reduction: {lhs:.12f} vs a(0,0) = {a(0.0, 0.0):.12f}")
    assert worst < 1e-9, worst
    return worst


def gauss4_correlation(A, a, Bm, b, c):
    """int_{R^4} exp(-(p-a)^T A (p-a)) exp(-(p-c-b)^T Bm (p-c-b)) dp, closed form."""
    S = A + Bm
    d = a - b - c
    M = A @ np.linalg.solve(S, Bm)
    return math.pi**2 / math.sqrt(np.linalg.det(S)) * math.exp(-d @ M @ d)


def check_adjoint():
    A = np.diag([1.0, 0.9, 1.1, 1.2]); a = np.array([0.5, 0.1, -0.2, 0.3])
    Bm = np.array([[1.4, 0.1, 0, 0], [0.1, 0.8, 0, 0.05], [0, 0, 1.0, 0], [0, 0.05, 0, 1.3]])
    b = np.array([-0.4, 0.2, 0.3, -0.1])
    # <f, G+ g> = (1/4pi) int dy/|y| C((|y|, y)),  C(c) = int f(p) g(p - c) dp
    lhs = integrate_R3_over_r(lambda Y: np.array([
        gauss4_correlation(A, a, Bm, b, np.concatenate([[np.linalg.norm(y)], y])) for y in Y])) / (4 * math.pi)
    # <g, G- f> = (1/4pi) int dy/|y| int g(q) f(q + (|y|, -y)) dq
    rhs = integrate_R3_over_r(lambda Y: np.array([
        gauss4_correlation(Bm, b, A, a, -np.concatenate([[np.linalg.norm(y)], -y])) for y in Y])) / (4 * math.pi)
    print(f"  adjointness: <f,G+g> = {lhs:.12f}, <g,G-f> = {rhs:.12f}")
    assert abs(lhs - rhs) < 1e-10 * max(1, abs(lhs))
    return abs(lhs - rhs)


def check_commutator():
    # u(t,x) = sin(t) g(x) + t^2 h(x) with polynomial-exponential g, h; chi(t) = t^3 (any smooth chi)
    # P(chi u) - chi P u should equal chi'' u + 2 chi' u_t; checked by finite differences.
    def u(t, x): return math.sin(1.3 * t) * math.exp(-x @ x) + t * t * (1 + x[0] * x[1])
    def chi(t): return t**3 - 0.5 * t
    def box(F, t, x, h=1e-3):
        dtt = (F(t + h, x) - 2 * F(t, x) + F(t - h, x)) / h**2
        lap = sum((F(t, x + h * e) - 2 * F(t, x) + F(t, x - h * e)) / h**2 for e in np.eye(3))
        return dtt - lap
    worst = 0.0
    for _ in range(5):
        t = rng.uniform(-1, 1); x = rng.uniform(-1, 1, 3)
        lhs = box(lambda s, y: chi(s) * u(s, y), t, x) - chi(t) * box(u, t, x)
        ut = (u(t + 1e-4, x) - u(t - 1e-4, x)) / 2e-4
        rhs = (6 * t) * u(t, x) + 2 * (3 * t * t - 0.5) * ut
        worst = max(worst, abs(lhs - rhs))
    print(f"  commutator [P, chi] u = chi'' u + 2 chi' u_t: max error {worst:.2e}")
    assert worst < 1e-4
    return worst


def check_support():
    # f supported in the closed ball B of radius 1 about (0,0) in R^4. If (t,x) is not in J+(B),
    # then (t - |y|, x - y) is not in B for every y (else (t,x) = q + (|y|, y) with q in B).
    def in_B(t, x): return t * t + x @ x <= 1.0
    def in_Jplus_B(t, x, n=4000):
        # (t,x) in J+(B) iff some q in B has t - q0 >= |x - q|; B convex compact: sample q
        q = rng.normal(size=(n, 4)); q /= np.linalg.norm(q, axis=1, keepdims=True)
        q *= rng.uniform(0, 1, (n, 1)) ** 0.25
        return np.any(t - q[:, 0] >= np.linalg.norm(x - q[:, 1:], axis=1) - 1e-12)
    bad = 0; tested = 0
    for _ in range(300):
        t = rng.uniform(-4, 4); x = rng.uniform(-4, 4, 3)
        # exact test of J+(B) for the ball: dist to the backward cone condition
        exact_in_J = (t >= -1) and (np.linalg.norm(x) - t <= math.sqrt(2)) and \
            (t + 1 >= 0) and _in_Jplus_ball(t, x)
        if exact_in_J:
            continue
        tested += 1
        for y in rng.uniform(-6, 6, (400, 3)):
            if in_B(t - np.linalg.norm(y), x - y):
                bad += 1
    print(f"  support: {tested} points outside J+(B), integrand nonzero at {bad} sampled y")
    assert bad == 0 and tested > 50
    return bad


def check_box_symmetric():
    """G1: int (box u) v = int u (box v) on R^4, for u, v products of 1D Gaussians (separable, so
    each int d_i^2 u . v factorises into 1D integrals; Gauss-Hermite-free: dense Legendre on [-L,L])."""
    x, w = leg(600); L = 12.0; x = L * x; w = L * w
    def g(a, m, s): return np.exp(-a * (s - m) ** 2)
    def g2(a, m, s): return (4 * a * a * (s - m) ** 2 - 2 * a) * g(a, m, s)   # second derivative
    ua = [(0.8, 0.3), (1.2, -0.4), (0.7, 0.1), (1.5, 0.2)]
    va = [(1.1, -0.2), (0.6, 0.5), (1.3, 0.0), (0.9, -0.3)]
    I = lambda f1, f2: float(np.dot(w, f1 * f2))
    base = [I(g(*ua[k], x), g(*va[k], x)) for k in range(4)]
    def box_pair(first_on_u):
        tot = 0.0
        for k in range(4):
            sign = 1.0 if k == 0 else -1.0
            if first_on_u:
                term = I(g2(*ua[k], x), g(*va[k], x))
            else:
                term = I(g(*ua[k], x), g2(*va[k], x))
            prod_others = np.prod([base[j] for j in range(4) if j != k])
            tot += sign * term * prod_others
        return tot
    lhs, rhs = box_pair(True), box_pair(False)
    print(f"  box symmetric: int (box u) v = {lhs:.14f}, int u (box v) = {rhs:.14f}")
    assert abs(lhs - rhs) < 1e-12
    return abs(lhs - rhs)


def check_radial_laplacian():
    """G3: for y != 0, sum_i d_i^2 [a(|y|)] = a''(|y|) + (2/|y|) a'(|y|) (finite differences)."""
    a = lambda r: math.exp(-0.7 * r * r) * (1 + 0.3 * r ** 4)
    da = lambda r, h=1e-4: (a(r + h) - a(r - h)) / (2 * h)
    dda = lambda r, h=1e-4: (a(r + h) - 2 * a(r) + a(r - h)) / h ** 2
    worst = 0.0
    for _ in range(8):
        y = rng.uniform(-1.5, 1.5, 3)
        F = lambda z: a(np.linalg.norm(z))
        h = 1e-4
        lap = sum((F(y + h * e) - 2 * F(y) + F(y - h * e)) / h ** 2 for e in np.eye(3))
        r = np.linalg.norm(y)
        worst = max(worst, abs(lap - (dda(r) + 2 / r * da(r))))
    print(f"  radial Laplacian: max error {worst:.2e}")
    assert worst < 1e-4
    return worst


def check_box_reflection():
    """G3: box(psi o A) = (box psi) o A for A(p) = a + (sigma p0, tau p_vec), sigma, tau = +-1."""
    B = np.array([[1.3, 0.2, 0.0], [0.2, 0.8, -0.1], [0.0, -0.1, 1.1]])
    psi = Gauss(0.9, 0.4, B, [0.3, -0.5, 0.2])
    worst = 0.0
    for sig in (1, -1):
        for tau in (1, -1):
            a0, av = 0.37, np.array([0.2, -0.1, 0.4])
            A = lambda s, y: (a0 + sig * s, av + tau * y)
            comp = lambda s, y: psi.val(*A(s, y))
            h = 1e-3
            for _ in range(4):
                s = rng.uniform(-1, 1); y = rng.uniform(-1, 1, 3)
                dss = (comp(s + h, y) - 2 * comp(s, y) + comp(s - h, y)) / h ** 2
                lap = sum((comp(s, y + h * e) - 2 * comp(s, y) + comp(s, y - h * e)) / h ** 2
                          for e in np.eye(3))
                worst = max(worst, abs((dss - lap) - psi.box(*A(s, y))))
    print(f"  box commutes with reflections/translations: max error {worst:.2e}")
    assert worst < 1e-4
    return worst


def _lorentz(rng):
    """A random orthochronous Lorentz matrix: rotation * boost * rotation, times a parity."""
    def rot():
        q, _ = np.linalg.qr(rng.normal(size=(3, 3)))
        return q
    def embed(R):
        M = np.eye(4); M[1:, 1:] = R; return M
    phi = rng.uniform(-1.5, 1.5)
    B = np.eye(4)
    B[0, 0] = B[1, 1] = math.cosh(phi); B[0, 1] = B[1, 0] = math.sinh(phi)
    P = np.diag([1.0, -1.0, 1.0, 1.0]) if rng.uniform() < 0.5 else np.eye(4)
    return embed(rot()) @ B @ embed(rot()) @ P


def check_box_lorentz():
    """G4: for orthochronous Lorentz L (L^T eta L = eta, (L e0)^0 > 0): |det L| = 1,
    L eta^{-1} L^T = eta^{-1}, and box(psi o g) = (box psi) o g for g(p) = L p + a."""
    eta = np.diag([-1.0, 1.0, 1.0, 1.0])
    B = np.array([[1.3, 0.2, 0.0], [0.2, 0.8, -0.1], [0.0, -0.1, 1.1]])
    psi = Gauss(0.9, 0.4, B, [0.3, -0.5, 0.2])
    worst = 0.0
    for _ in range(6):
        L = _lorentz(rng)
        assert np.allclose(L.T @ eta @ L, eta) and L[0, 0] > 0
        assert abs(abs(np.linalg.det(L)) - 1) < 1e-10
        assert np.allclose(L @ np.linalg.inv(eta) @ L.T, np.linalg.inv(eta))
        a = rng.uniform(-0.3, 0.3, 4)
        g = lambda p: L @ p + a
        comp = lambda p: psi.val(g(p)[0], g(p)[1:])
        h = 1e-3
        for _ in range(3):
            p = rng.uniform(-0.6, 0.6, 4)
            d2 = [(comp(p + h * e) - 2 * comp(p) + comp(p - h * e)) / h ** 2 for e in np.eye(4)]
            box_comp = d2[0] - d2[1] - d2[2] - d2[3]
            q = g(p)
            worst = max(worst, abs(box_comp - psi.box(q[0], q[1:])))
    print(f"  box(psi o g) = (box psi) o g for orthochronous Poincare g: max error {worst:.2e}")
    assert worst < 1e-3
    return worst


def check_slab_compact():
    """G4, Lemmas 2-3: for n future unit and v future causal, tau_n(v) >= (n0 - |n|) v0; hence
    J+(K) cut by {tau_n <= T} is bounded by the explicit bound of the proposal (sampled)."""
    worst = math.inf
    for _ in range(200):
        w = rng.normal(size=3); w *= rng.uniform(0, 3) / np.linalg.norm(w)
        n = np.concatenate([[math.sqrt(1 + w @ w)], w])
        v3 = rng.normal(size=3); v3 *= rng.uniform(0, 2) / max(np.linalg.norm(v3), 1e-12)
        v = np.concatenate([[np.linalg.norm(v3) + rng.uniform(0, 2)], v3])
        tau = n[0] * v[0] - n[1:] @ v[1:]
        margin = tau - (n[0] - np.linalg.norm(n[1:])) * v[0]
        worst = min(worst, margin)
    print(f"  tau_n(v) - (n0 - |n|) v0 >= {worst:.2e} over 200 samples")
    assert worst >= -1e-12
    return worst


def _in_Jplus_ball(t, x):
    # (t,x) in J+(unit ball in R^4): exists q with |q| <= 1, t - q0 >= |x - q_vec|.
    # Minimise |x - q_vec| - (t - q0) over the ball: by symmetry take q = (-cos a, sin a * x/|x|).
    r = np.linalg.norm(x)
    a = np.linspace(0, math.pi, 2001)
    val = np.abs(r - np.sin(a)) - (t + np.cos(a))
    return val.min() <= 1e-12


if __name__ == "__main__":
    print("Stage G0 checks (massless wave operator on R^4, Kirchhoff Green operators)")
    results = [("core identity", check_core), ("1D reduction", check_reduction),
               ("adjointness", check_adjoint), ("commutator", check_commutator),
               ("support", check_support), ("box symmetric (G1)", check_box_symmetric),
               ("radial Laplacian (G3)", check_radial_laplacian),
               ("box and reflections (G3)", check_box_reflection),
               ("box and Lorentz maps (G4)", check_box_lorentz),
               ("slab compactness bound (G4)", check_slab_compact)]
    passed = 0
    for name, fn in results:
        fn(); passed += 1; print(f"PASS {name}")
    print(f"\n{passed}/{len(results)} checks passed")
