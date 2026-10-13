"""Exact checks for stage F (Green-hyperbolic data give phase-space data), on the lattice.

Run from any directory; it reads and writes no files. Integer arithmetic throughout (m^2 an
integer), so every assert is an equality.

Conventions as in checks/lattice_check.py and the lattice-net check of E2: points p = (t, x);
retarded kernel K(s, y) = 0 for s <= 0, K(1, y) = [y = 0],
K(s+1, y) = -K(s-1, y) + K(s, y+1) + K(s, y-1) - m2 K(s, y);
(G+ f)(p) = sum_q f(q) K(p - q) (retarded), (G- f)(p) = sum_q f(q) K(reflect(p - q)) with
reflect(t, x) = (-t, x) (advanced); E = G- - G+ (advanced minus retarded);
(P u)(t, x) = u(t+1, x) + u(t-1, x) - u(t, x+1) - u(t, x-1) + m2 u(t, x);
<f, h> = sum_p f(p) h(p); p <= q iff |q_x - p_x| <= q_t - p_t (causalLE).
Cutoff at t1: chi(h)(p) = h(p) if p_t >= t1 + 1 else 0; slab S = {t1, t1 + 1} x Z.
"""
import random
from functools import lru_cache

rng = random.Random(20260927)
MASSES = [0, 1, 2, -1]
checks = []


def check(name, ok):
    checks.append((name, bool(ok)))
    print(('PASS ' if ok else 'FAIL ') + name)


def make_kernel(m2):
    @lru_cache(maxsize=None)
    def K(s, y):
        if s <= 0:
            return 0
        if s == 1:
            return 1 if y == 0 else 0
        return -K(s - 2, y) + K(s - 1, y + 1) + K(s - 1, y - 1) - m2 * K(s - 1, y)
    return K


def causal_le(p, q):
    return abs(q[1] - p[1]) <= q[0] - p[0]


def comparable(p, q):
    return causal_le(p, q) or causal_le(q, p)


def rand_f(n=3, span=3):
    f = {}
    for _ in range(n):
        f[(rng.randint(-span, span), rng.randint(-span, span))] = rng.randint(-4, 4)
    return {p: c for p, c in f.items() if c != 0} or {(0, 0): 1}


def G_plus(K, f):
    return lambda p: sum(c * K(p[0] - q[0], p[1] - q[1]) for q, c in f.items())


def G_minus(K, f):
    return lambda p: sum(c * K(q[0] - p[0], p[1] - q[1]) for q, c in f.items())


def P(m2, u):
    return lambda p: (u((p[0] + 1, p[1])) + u((p[0] - 1, p[1])) - u((p[0], p[1] + 1))
                      - u((p[0], p[1] - 1)) + m2 * u(p))


def chi(t1, u):
    return lambda p: u(p) if p[0] >= t1 + 1 else 0


def window(R):
    return [(t, x) for t in range(-R, R + 1) for x in range(-R, R + 1)]


def pair(f, u):
    return sum(c * u(q) for q, c in f.items())


W = window(9)
ok_PG = ok_GP = ok_supp = ok_adj = ok_c1 = ok_c2 = ok_ts = ok_nondeg = True
for m2 in MASSES:
    K = make_kernel(m2)
    for _ in range(6):
        f, g = rand_f(), rand_f()
        Gp, Gm = G_plus(K, f), G_minus(K, f)
        # P G+- f = f on the window (interior, so P needs neighbours only)
        for p in window(6):
            ok_PG &= P(m2, Gp)(p) == f.get(p, 0) and P(m2, Gm)(p) == f.get(p, 0)
        # G+- P f = f: P f is finitely supported
        Pf = {p: P(m2, lambda q: f.get(q, 0))(p) for p in window(6)}
        Pf = {p: c for p, c in Pf.items() if c != 0}
        for p in window(5):
            ok_GP &= G_plus(K, Pf)(p) == f.get(p, 0) and G_minus(K, Pf)(p) == f.get(p, 0)
        # supports: supp G+ f in J+(supp f), supp G- f in J-(supp f)
        for p in W:
            if Gp(p) != 0:
                ok_supp &= any(causal_le(q, p) for q in f)
            if Gm(p) != 0:
                ok_supp &= any(causal_le(p, q) for q in f)
        # formal adjointness <f, G+ g> = <g, G- f>
        ok_adj &= pair(f, G_plus(K, g)) == pair(g, G_minus(K, f))
        # nondegeneracy: <delta_p, E f> = (E f)(p)
        E = lambda p, Gp=Gp, Gm=Gm: Gm(p) - Gp(p)
        for p in window(4):
            ok_nondeg &= pair({p: 1}, E) == E(p)
        # cutoff conditions at several t1
        for t1 in [-2, 0, 1, 3]:
            # (c1) supp P(chi E f) in S_{t1} cap J(supp f)
            PchiE = P(m2, chi(t1, E))
            for p in window(7):
                if PchiE(p) != 0:
                    ok_c1 &= p[0] in (t1, t1 + 1) and any(comparable(p, q) for q in f)
            # (c2) k = (1-chi) G+ f + chi G- f is finitely supported: zero outside a box
            k = lambda p, t1=t1: (Gp(p) if p[0] < t1 + 1 else 0) + (Gm(p) if p[0] >= t1 + 1 else 0)
            tmin = min(q[0] for q in f); tmax = max(q[0] for q in f)
            xmin = min(q[1] for q in f); xmax = max(q[1] for q in f)
            lo_t, hi_t = min(tmin, t1) - 1, max(tmax, t1 + 1) + 1
            span = (hi_t - lo_t) + 1
            for p in window(14):
                inside = lo_t <= p[0] <= hi_t and xmin - span <= p[1] <= xmax + span
                if not inside:
                    ok_c2 &= k(p) == 0
            # time slice: f' = f - P k equals -P(chi E f), E f' = E f, supp f' in S cap J(supp f)
            Pk = P(m2, k)
            # supp f' reaches |x| <= 3 + 7 = 10 (supp f in [-3,3]^2, t1 up to 3): window 13 covers it
            fprime = {p: f.get(p, 0) - Pk(p) for p in window(13)}
            fprime = {p: c for p, c in fprime.items() if c != 0}
            for p in window(8):
                ok_ts &= f.get(p, 0) - Pk(p) == -PchiE(p)
            Efp = lambda p: G_minus(K, fprime)(p) - G_plus(K, fprime)(p)
            for p in window(4):
                ok_ts &= Efp(p) == E(p)
            for p in fprime:
                ok_ts &= p[0] in (t1, t1 + 1) and any(comparable(p, q) for q in f)

check("P G+- f = f (m2 in {0,1,2,-1})", ok_PG)
check("G+- P f = f", ok_GP)
check("supp G+ f in J+(supp f), supp G- f in J-(supp f)", ok_supp)
check("formal adjointness <f, G+ g> = <g, G- f>", ok_adj)
check("<delta_p, E f> = (E f)(p) (nondegeneracy)", ok_nondeg)
check("(c1) supp P(chi E f) in S_t1 cap J(supp f)", ok_c1)
check("(c2) (1-chi) G+ f + chi G- f finitely supported", ok_c2)
check("time slice: f - P k = -P(chi E f), E f' = E f, supp f' in S cap J(supp f)", ok_ts)

# The draft (c1) of the plan is false: P(chi h) for P h = 0 leaves supp h.
K = make_kernel(0)
f = {(0, 0): 1}
Gm, Gp = G_minus(K, f), G_plus(K, f)
E = lambda p: Gm(p) - Gp(p)
PchiE = P(0, chi(0, E))
bad = [p for p in window(4) if PchiE(p) != 0 and E(p) == 0]
check("draft (c1) 'supp P(chi h) in supp h' fails on the lattice (counterexample found)",
      len(bad) > 0)

failed = [n for n, ok in checks if not ok]
print(f"\n{len(checks) - len(failed)}/{len(checks)} checks passed")
raise SystemExit(1 if failed else 0)
