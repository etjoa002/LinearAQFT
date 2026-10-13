"""Exact checks for milestone E2 (the lattice net and the Cauchy-data bridge).

Run from any directory; it reads and writes no files. Integer arithmetic throughout
(m^2 is an integer here), so every assert is an equality.

Conventions as in checks/lattice_check.py and the programme (26 Sep 2026): points (t, x),
retarded kernel K with K(s, y) = 0 for s <= 0, K(1, y) = [y = 0],
K(s+1, y) = -K(s-1, y) + K(s, y+1) + K(s, y-1) - m2 K(s, y); the commutator function
Delta(s, y) = K(-s, y) - K(s, y) (advanced minus retarded); (E f)(p) = sum_q f(q) Delta(p - q);
<f, u> = sum_p f(p) u(p); sigma([f], [g]) = <f, E g>.

Cauchy data on the slice pair (t1, t1 + 1): T[f] = ((E f)(t1, .), (E f)(t1 + 1, .)), with the
Wronskian omega((a, b), (a', b')) = sum_x (a(x) b'(x) - b(x) a'(x)).
"""
import random
from functools import lru_cache

rng = random.Random(20260927)
MASSES = [0, 1, 2]
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


def make_delta(K):
    return lambda s, y: K(-s, y) - K(s, y)


def Efun(D, f):
    return lambda t, x: sum(v * D(t - q[0], x - q[1]) for q, v in f.items())


def pair(f, u):
    return sum(v * u(*q) for q, v in f.items())


def sigma(D, f, g):
    return pair(f, Efun(D, g))


def rand_f(n=4, box=2):
    f = {}
    for _ in range(n):
        f[(rng.randint(-box, box), rng.randint(-box, box))] = rng.randint(-5, 5)
    return {p: v for p, v in f.items() if v != 0}


def rand_data(box=3):
    a = {x: rng.randint(-5, 5) for x in range(-box, box + 1)}
    b = {x: rng.randint(-5, 5) for x in range(-box, box + 1)}
    return a, b


XS = range(-30, 31)


def cauchy(D, f, t1):
    u = Efun(D, f)
    a = {x: u(t1, x) for x in XS}
    b = {x: u(t1 + 1, x) for x in XS}
    return a, b


def omega(ab, ab2):
    (a, b), (a2, b2) = ab, ab2
    return sum(a.get(x, 0) * b2.get(x, 0) - b.get(x, 0) * a2.get(x, 0) for x in XS)


def leapfrog(m2, ab):
    a, b = ab
    return (dict(b), {x: -a.get(x, 0) + b.get(x + 1, 0) + b.get(x - 1, 0) - m2 * b.get(x, 0)
                      for x in XS})


def inverse(ab, t1):
    """The two-slice test function f' with f'(t1, .) = -b and f'(t1 + 1, .) = a."""
    a, b = ab
    fp = {}
    for x, v in b.items():
        if v:
            fp[(t1, x)] = -v
    for x, v in a.items():
        if v:
            fp[(t1 + 1, x)] = v
    return fp


def same(ab, ab2):
    return all(ab[0].get(x, 0) == ab2[0].get(x, 0) and ab[1].get(x, 0) == ab2[1].get(x, 0)
               for x in XS)


# 1. The witness (plan item 2): Delta(3, 0) = -1 and sigma([delta_(0,0)], [delta_(3,0)]) = 1
#    at m^2 = 0.
D0 = make_delta(make_kernel(0))
check('[m2=0] Delta(3, 0) = -1', D0(3, 0) == -1)
check('[m2=0] witness sigma([delta_(0,0)], [delta_(3,0)]) = 1',
      sigma(D0, {(0, 0): 1}, {(3, 0): 1}) == 1)

check('general m2: sigma([delta_(0,0)], [delta_(3,0)]) = 1 + m2^2',
      all(sigma(make_delta(make_kernel(m2)), {(0, 0): 1}, {(3, 0): 1}) == 1 + m2 ** 2
          for m2 in range(-3, 4)))

# 2. An orthogonal pair of regions, each carrying a nonzero test function: {(0,0)} and {(0,1)}.
def comparable(p, q):
    return abs(q[1] - p[1]) <= abs(q[0] - p[0])


check('orthogonal pair: (0,0) and (0,1) are not comparable',
      not comparable((0, 0), (0, 1)))
check('orthogonal pair: sigma([delta_(0,0)], [delta_(1,0)]) = sigma([delta_(0,1)], '
      '[delta_(1,1)]) = 1 for every m2, so both classes are nonzero',
      all(sigma(make_delta(make_kernel(m2)), {(0, 0): 1}, {(1, 0): 1}) == 1
          and sigma(make_delta(make_kernel(m2)), {(0, 1): 1}, {(1, 1): 1}) == 1 for m2 in MASSES))
check('orthogonal pair: sigma([delta_(0,0)], [delta_(0,1)]) = 0 for every m2',
      all(sigma(make_delta(make_kernel(m2)), {(0, 0): 1}, {(0, 1): 1}) == 0 for m2 in MASSES))

# 3. A dependent pair O < O' with O not inside O': O = {(5,0)}, O' = J(O) cap S_0.
O = {(5, 0)}
Oprime = {(t, x) for t in (0, 1) for x in range(-10, 11) if comparable((t, x), (5, 0))}
check('dependent pair: J(O) cap S_0 has 11 + 9 = 20 points and does not contain (5,0)',
      len(Oprime) == 20 and not O <= Oprime)

for m2 in MASSES:
    tag = f'[m2={m2}]'
    D = make_delta(make_kernel(m2))
    # 4. Values of Delta on the slices t = -1, 0, 1 (notes Prop. 3.7(e)).
    check(f'{tag} Delta(-1, x) = [x=0], Delta(0, x) = 0, Delta(1, x) = -[x=0]',
          all(D(-1, x) == (1 if x == 0 else 0) and D(0, x) == 0
              and D(1, x) == -(1 if x == 0 else 0) for x in range(-6, 7)))
    # 5. Nondegeneracy formula: sigma([f], [delta_p]) = -(E f)(p).
    ok = True
    for _ in range(10):
        f = rand_f()
        p = (rng.randint(-4, 4), rng.randint(-4, 4))
        ok &= sigma(D, f, {p: 1}) == -Efun(D, f)(*p)
    check(f'{tag} sigma([f], [delta_p]) = -(E f)(p)', ok)
    # 6. Translations and the spatial reflection commute with E.
    ok = True
    for _ in range(10):
        f = rand_f()
        a = (rng.randint(-3, 3), rng.randint(-3, 3))
        fa = {(q[0] + a[0], q[1] + a[1]): v for q, v in f.items()}
        fr = {(q[0], -q[1]): v for q, v in f.items()}
        Ef, Efa, Efr = Efun(D, f), Efun(D, fa), Efun(D, fr)
        for t in range(-4, 5):
            for x in range(-4, 5):
                ok &= Efa(t, x) == Ef(t - a[0], x - a[1])
                ok &= Efr(t, x) == Ef(t, -x)
    check(f'{tag} E commutes with translations and with x -> -x', ok)
    for t1 in (-3, 0, 2):
        # 7. Cauchy-data inversion: E f' has data (a, b).
        ok = True
        for _ in range(5):
            ab = rand_data()
            ok &= same(cauchy(D, inverse(ab, t1), t1), ab)
        check(f'{tag} t1={t1}: E f\' has Cauchy data (a, b) for f\' = (-b, a) on S_t1', ok)
        # 8. Symplectic: omega(T[f], T[g]) = <f, E g>.
        ok = True
        for _ in range(6):
            f, g = rand_f(), rand_f()
            ok &= omega(cauchy(D, f, t1), cauchy(D, g, t1)) == sigma(D, f, g)
        check(f'{tag} t1={t1}: omega(T[f], T[g]) = <f, E g>', ok)
        # 9. Two consecutive slices determine E f (the recursion both ways).
        ok = True
        for _ in range(3):
            f = rand_f()
            u = Efun(D, f)
            vals = {(t1, x): u(t1, x) for x in range(-20, 21)}
            vals.update({(t1 + 1, x): u(t1 + 1, x) for x in range(-20, 21)})
            for t in range(t1 + 1, t1 + 5):
                for x in range(-20 + (t - t1), 21 - (t - t1)):
                    vals[(t + 1, x)] = (-vals[(t - 1, x)] + vals[(t, x + 1)] + vals[(t, x - 1)]
                                        - m2 * vals[(t, x)])
            for t in range(t1, t1 - 4, -1):
                w = t1 + 1 - t
                for x in range(-20 + w, 21 - w):
                    vals[(t - 1, x)] = (-vals[(t + 1, x)] + vals[(t, x + 1)] + vals[(t, x - 1)]
                                        - m2 * vals[(t, x)])
            ok &= all(v == u(*p) for p, v in vals.items())
        check(f'{tag} t1={t1}: E f is determined by its data on S_t1', ok)
        # 10. Change of slice: T_{t1+1}[f] = Gamma(T_{t1}[f]).
        ok = True
        for _ in range(5):
            f = rand_f()
            ok &= same(cauchy(D, f, t1 + 1), leapfrog(m2, cauchy(D, f, t1)))
        check(f'{tag} t1={t1}: T_(t1+1)[f] = Gamma(T_t1[f])', ok)
    # 11. Gamma preserves omega.
    ok = True
    for _ in range(10):
        u, w = rand_data(), rand_data()
        ok &= omega(leapfrog(m2, u), leapfrog(m2, w)) == omega(u, w)
    check(f'{tag} omega(Gamma u, Gamma w) = omega(u, w)', ok)

npass = sum(ok for _, ok in checks)
print(f'{npass} of {len(checks)} checks pass')
assert npass == len(checks)
