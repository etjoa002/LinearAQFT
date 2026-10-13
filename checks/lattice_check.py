"""Numerical checks for milestone E1 (lattice propagators), run before any statement.

Lattice Z^2, points (t, x). Leapfrog operator
    (P u)(t, x) = u(t+1, x) + u(t-1, x) - u(t, x+1) - u(t, x-1) + m2 * u(t, x).
Retarded kernel K on (s, y): K(s, y) = 0 for s <= 0, K(1, y) = [y = 0],
    K(s+1, y) = -K(s-1, y) + K(s, y+1) + K(s, y-1) - m2 * K(s, y)   (s >= 1),
so that P K = delta at the origin. G+ f = sum_q f(q) K(. - q), G- f(t, x) = G+ (f o R)(-t, x)
with R(t, x) = (-t, x), E = G- - G+ (advanced minus retarded, programme Conventions of
26 Sep 2026), pairing <f, u> = sum_p f(p) u(p), and sigma([f], [g]) = <f, E g>, so that
[phi(f), phi(g)] = i sigma([f], [g]).
"""
import itertools
import numpy as np

rng = np.random.default_rng(20260925)
T = 14          # kernel computed for 0 <= s <= T
X = 20          # |y| <= X
MASSES = [0.0, 0.3, 1.7]
checks = []


def check(name, ok):
    checks.append((name, bool(ok)))
    print(('PASS ' if ok else 'FAIL ') + name)


def kernel(m2):
    K = np.zeros((T + 1, 2 * X + 1))       # index [s, y + X]
    K[1, X] = 1.0
    for s in range(1, T):
        for y in range(-X + 1, X):
            K[s + 1, y + X] = (-K[s - 1, y + X] + K[s, y + 1 + X] + K[s, y - 1 + X]
                               - m2 * K[s, y + X])
    return K


def Kval(K, s, y):
    if s <= 0 or s > T or abs(y) >= X:
        return 0.0
    return K[s, y + X]


def E(K, s, y):
    # advanced minus retarded (programme conventions, 26 Sep 2026)
    return Kval(K, -s, y) - Kval(K, s, y)


def Gplus(K, f, t, x):
    return sum(v * Kval(K, t - q[0], x - q[1]) for q, v in f.items())


def Gminus(K, f, t, x):
    return sum(v * Kval(K, q[0] - t, x - q[1]) for q, v in f.items())


def Efun(K, f, t, x):
    return Gminus(K, f, t, x) - Gplus(K, f, t, x)


def P(u, t, x, m2):
    return u(t + 1, x) + u(t - 1, x) - u(t, x + 1) - u(t, x - 1) + m2 * u(t, x)


def pair(f, u):
    return sum(v * u(*q) for q, v in f.items())


def rand_f(n=4, box=2):
    pts = {(int(rng.integers(-box, box + 1)), int(rng.integers(-box, box + 1))) for _ in range(n)}
    return {p: float(rng.normal()) for p in pts}


for m2 in MASSES:
    K = kernel(m2)
    tag = f'[m2={m2}]'
    # 1. cone support: K(s, y) != 0 only if |y| <= s - 1
    check(f'{tag} kernel supported in |y| <= s-1',
          all(abs(K[s, y + X]) < 1e-12 for s in range(T + 1) for y in range(-X, X + 1)
              if not abs(y) <= s - 1))
    # 2. P K = delta (interior of the window)
    ok = True
    for s in range(-3, T - 1):
        for y in range(-X + 2, X - 1):
            val = P(lambda a, b: Kval(K, a, b), s, y, m2)
            ok &= abs(val - (1.0 if (s, y) == (0, 0) else 0.0)) < 1e-9
    check(f'{tag} P K = delta', ok)
    # 3. evenness in y
    check(f'{tag} K(s, y) = K(s, -y)',
          np.allclose(K, K[:, ::-1]))
    # 4. G+ P f = f and G- P f = f for finitely supported f (evaluated near supp f)
    ok = True
    for _ in range(5):
        f = rand_f()
        Pf = {}
        for (t, x), v in f.items():
            for (dt, dx), c in [((1, 0), 1), ((-1, 0), 1), ((0, 1), -1), ((0, -1), -1), ((0, 0), m2)]:
                # (P f)(p) = sum_q f(q) P-stencil; P is symmetric, so Pf(p) collects f(p +- e)
                q = (t - dt, x - dx)
                Pf[q] = Pf.get(q, 0.0) + c * v
        for t, x in itertools.product(range(-4, 5), range(-4, 5)):
            ok &= abs(Gplus(K, Pf, t, x) - f.get((t, x), 0.0)) < 1e-9
            ok &= abs(Gminus(K, Pf, t, x) - f.get((t, x), 0.0)) < 1e-9
    check(f'{tag} G+ P f = f and G- P f = f', ok)
    # 5. antisymmetry <f, E g> = -<g, E f>
    ok = True
    for _ in range(10):
        f, g = rand_f(), rand_f()
        a = pair(f, lambda t, x: Efun(K, g, t, x))
        b = pair(g, lambda t, x: Efun(K, f, t, x))
        ok &= abs(a + b) < 1e-9
    check(f'{tag} <f, E g> = -<g, E f>', ok)
    # 6. causality: supports with no comparable pair give <f, E g> = 0
    ok = True
    for _ in range(20):
        f = {(0, int(x)): float(rng.normal()) for x in rng.integers(-3, 0, size=2)}
        g = {(0, int(x)): float(rng.normal()) for x in rng.integers(1, 4, size=2)}
        ok &= abs(pair(f, lambda t, x: Efun(K, g, t, x))) < 1e-12
    check(f'{tag} spacelike supports give <f, E g> = 0', ok)
    # 7. two-slice cutoff: f' = P((1 - chi) E f), chi = [t >= t1 + 1], supported on the slices
    #    t1, t1+1 inside J(supp f), and E f' = E f.
    ok = True
    for t1 in (-3, 0, 2):
        f = rand_f(n=3, box=1)
        u = lambda t, x, f=f: Efun(K, f, t, x)
        chiu = lambda t, x, u=u, t1=t1: u(t, x) if t <= t1 else 0.0
        fp = {}
        for t, x in itertools.product(range(t1 - 3, t1 + 5), range(-8, 9)):
            v = P(chiu, t, x, m2)
            if abs(v) > 1e-12:
                fp[(t, x)] = v
        supp_ok = all(t in (t1, t1 + 1) for (t, x) in fp)
        cone_ok = all(any(abs(x - q[1]) <= abs(t - q[0]) for q in f) for (t, x) in fp)
        same = all(abs(Efun(K, fp, t, x) - u(t, x)) < 1e-8
                   for t, x in itertools.product(range(-4, 5), range(-4, 5)))
        ok &= supp_ok and cone_ok and same
    check(f'{tag} cutoff f\' on S_t1 within J(supp f) with E f\' = E f', ok)

# 8. parity: at m2 = 0 the kernel lives on s + y odd, so sigma vanishes on equal parity
K0 = kernel(0.0)
check('[m2=0] kernel supported on s + y odd',
      all(abs(K0[s, y + X]) < 1e-12 for s in range(T + 1) for y in range(-X, X + 1)
          if (s + y) % 2 == 0))
f0 = {(0, 0): 1.0}
same_par = {(2, 0): 1.0}      # timelike, t + x even like (0, 0)
opp_par = {(3, 0): 1.0}       # timelike, opposite parity
sig = lambda K, f, g: pair(f, lambda t, x: Efun(K, g, t, x))  # sigma([f],[g]) = <f, E g>
check('[m2=0] timelike same-parity pair has sigma = 0', abs(sig(K0, f0, same_par)) < 1e-12)
check('[m2=0] timelike opposite-parity pair has sigma != 0', abs(sig(K0, f0, opp_par)) > 0.5)
check('[m2=0] exact witness: K(3,0) = 1, E(3,0) = -1, sigma(delta_(0,0), delta_(3,0)) = 1',
      Kval(K0, 3, 0) == 1.0 and E(K0, 3, 0) == -1.0 and sig(K0, f0, opp_par) == 1.0)
# 9. canonical sign: <delta_(0,x), E delta_(1,y)> = [x = y] and <delta_(0,x), E delta_(0,y)> = 0,
#    the lattice form of [phi(t,x), phi(t+1,y) - phi(t,y)] = i delta_xy.
for m2c in (0.0, 0.3, 1.7):
    Kc = kernel(m2c)
    ok = all(abs(sig(Kc, {(0, x): 1.0}, {(1, y): 1.0}) - (1.0 if x == y else 0.0)) < 1e-12
             and abs(sig(Kc, {(0, x): 1.0}, {(0, y): 1.0})) < 1e-12
             for x in range(-3, 4) for y in range(-3, 4))
    check(f'[m2={m2c}] canonical sign: [phi(0,x), pi(0,y)] = i delta_xy', ok)
K1 = kernel(0.3)
check('[m2=0.3] timelike same-parity pair has sigma != 0', abs(sig(K1, f0, same_par)) > 1e-3)
# 10. numbers quoted in the lecture notes (chapter 1 bullets, chapter 3 example), exactly
def J_point_slice(t1, p=(0, 0), X=50):
    # points of S_t1 comparable with p
    return [(t, x) for t in (t1, t1 + 1) for x in range(-X, X + 1)
            if abs(x - p[1]) <= abs(t - p[0])]
check('notes ch.1: J({p}) cap S_2 has twelve points', len(J_point_slice(2)) == 12)
check('notes ch.1: J({p}) cap S_t1 has at least four points for every t1 in [-20, 20]',
      min(len(J_point_slice(t1)) for t1 in range(-20, 21)) == 4)
check('notes ch.3: at m^2 = 0, K(2, +-1) = 1 and K(2, 0) = 0',
      Kval(K0, 2, 1) == 1.0 and Kval(K0, 2, -1) == 1.0 and Kval(K0, 2, 0) == 0.0)
print(f'{sum(ok for _, ok in checks)} of {len(checks)} checks pass')
