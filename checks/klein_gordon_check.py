"""Stage H, step H0: numerical checks for the massive Green operators (light; run inline).

G^+ is the Kirchhoff operator of chapter 8: (G^+ f)(t,x) = int_{R^3} f(t-|y|, x-y) / (4 pi |y|) dy.
The massive retarded operator is G_m^+ = sum_k (-m^2)^k (G^+)^{k+1}.

Checks
 1. Power bound: G^+ applied to (t-t0)_+^n / n! (a function of time only) is (t-t0)_+^{n+2}/(n+2)!,
    via int_0^T rho (T-rho)^n / n! d rho = T^{n+2}/(n+2)!.
 2. Kernel of (G^+)^2 is (1/8 pi) times the indicator of the solid future cone (plane-wave test:
    both sides give (sin ks - ks cos ks)/(2k^3) as the time kernel for exp(i k.x)).
 3. The cone-power series sums to the Bessel tail: sum_{k>=1} (-m^2)^k s^{k-1}/(2 pi 4^k k!(k-1)!)
    = -(m/4 pi) J_1(m sqrt s)/sqrt s for s = t^2 - |x|^2 > 0.
 4. Telescoping on plane waves: for f = g(t) exp(i k.x), G^+ is the Volterra operator with kernel
    sin(k s)/k; the series with m gives the kernel sin(w s)/w, w = sqrt(k^2 + m^2), i.e. the
    retarded Green function of d_t^2 + k^2 + m^2.
 5. Huygens: for a bump f near the origin and p = (T, 0) timelike to supp f, the massless value
    G^+ f(p) is 0 and the massive value is nonzero; small-m asymptotics G_m f(p) ~ -m^2 (G^+)^2 f(p).
 6. Dilation: G_m^+ f_lambda(lambda p) = lambda^2 G_{lambda m}^+ f(p) with f_lambda = f(./lambda).
 7. (H2) The iterated power bound for k <= 6.
 8. (H4) Positivity: (G^+)^2 f(p) > 0, and G_mu f(p) has the sign of -mu, for either sign of mu.
 9. (H4) The tail bound |G_mu f(p) - G^+ f(p) + mu (G^+)^2 f(p)| <= C mu^2 tau^6 cosh(sqrt|mu| tau),
    and G_mu f(p) != 0 below the threshold mu0 = A / (C tau^6 cosh tau).
10. (H4) Dilation of the full operator: G_mu^+ f_l(l p) = l^2 G_{l^2 mu}^+ f(p), for either sign of mu.
"""
import math
import numpy as np
from scipy import integrate, special

ok_all = True
def report(name, ok, detail):
    global ok_all
    ok_all &= ok
    print(("PASS " if ok else "FAIL ") + name + ": " + detail)

# 1. power bound
worst = 0.0
for n in range(0, 9):
    for T in (0.3, 1.0, 2.7):
        lhs = integrate.quad(lambda r: r * (T - r) ** n / math.factorial(n), 0, T)[0]
        rhs = T ** (n + 2) / math.factorial(n + 2)
        worst = max(worst, abs(lhs - rhs) / rhs)
report("1 power bound", worst < 1e-12, "max rel. error %.1e over n<=8" % worst)

# 2. (G^+)^2 kernel = (1/8pi) solid cone, plane-wave time kernels
worst = 0.0
for k in (0.5, 1.3, 3.0):
    for s in (0.2, 1.0, 2.5):
        # (G^+)^2: convolution of two time kernels rho sin(k rho)/(k rho) = sin(k rho)/k
        conv = integrate.quad(lambda r: math.sin(k * r) / k * math.sin(k * (s - r)) / k, 0, s)[0]
        cone = (math.sin(k * s) - k * s * math.cos(k * s)) / (2 * k ** 3)
        worst = max(worst, abs(conv - cone))
report("2 (G+)^2 = solid cone / 8pi", worst < 1e-12, "max abs. error %.1e" % worst)

# 3. cone-power series = Bessel tail
def series(m, s, K=60):
    return sum((-m * m) ** k * s ** (k - 1) / (2 * math.pi * 4 ** k * math.factorial(k) * math.factorial(k - 1))
               for k in range(1, K))
worst = 0.0
for m in (0.3, 1.0, 2.0):
    for s in (0.05, 0.7, 3.0, 9.0):
        b = -(m / (4 * math.pi)) * special.j1(m * math.sqrt(s)) / math.sqrt(s)
        worst = max(worst, abs(series(m, s) - b))
report("3 series = -(m/4pi) J1(m sqrt s)/sqrt s", worst < 1e-12, "max abs. error %.1e" % worst)

# 4. telescoping on plane waves (Volterra kernels on a grid)
def volterra_series(k, m, s_max=4.0, N=801, K=40):
    s = np.linspace(0, s_max, N); ds = s[1] - s[0]
    base = np.sin(k * s) / k
    term = base.copy(); total = base.copy()
    for j in range(1, K):
        # term <- base * term (Volterra convolution), trapezoid rule
        new = np.array([np.trapezoid(base[:i + 1][::-1] * term[:i + 1], dx=ds) if i else 0.0 for i in range(N)])
        term = new
        total += (-m * m) ** j * term
        if np.max(np.abs(term)) * (m * m) ** j < 1e-14:
            break
    return s, total
worst = 0.0
for k, m in ((1.0, 0.7), (2.0, 1.5)):
    s, tot = volterra_series(k, m)
    w = math.sqrt(k * k + m * m)
    worst = max(worst, np.max(np.abs(tot - np.sin(w * s) / w)))
report("4 telescoping: series kernel = sin(ws)/w", worst < 1e-5, "max abs. error %.1e (grid)" % worst)

# 5. Huygens: bump f(t,x) = b(t) c(|x|) near the origin, p = (T, 0)
eps = 0.1
def bump(u):
    return np.where(np.abs(u) < 1, np.exp(-1 / np.maximum(1 - u * u, 1e-300)), 0.0)
def G0f(T):  # massless: int f(T-|y|, -y)/(4pi|y|) dy = int_0^inf rho f(T-rho, rho) d rho
    return integrate.quad(lambda r: r * bump((T - r) / eps) * bump(r / eps), 0, 2 * eps, points=[eps])[0]
def Gmf(T, m):  # massive: light-cone term + tail -(m/4pi) int_{solid cone} J1(m sqrt s)/sqrt s f(p-w) dw
    light = G0f(T)
    def inner(r):  # w = (tau, y), |y| = r <= tau, p - w = (T - tau, -y)
        def g(tau):
            s = tau * tau - r * r
            ker = (m / 2) if s <= 0 else special.j1(m * math.sqrt(s)) / math.sqrt(s)
            return ker * bump((T - tau) / eps)
        return 4 * math.pi * r * r * bump(r / eps) * integrate.quad(g, max(r, T - eps), T + eps)[0]
    tail = -(m / (4 * math.pi)) * integrate.quad(inner, 0, eps)[0]
    return light + tail
def G2f(T):  # (1/8pi) int_{J^-(p)} f
    return (1 / (8 * math.pi)) * integrate.dblquad(
        lambda r, t: 4 * math.pi * r * r * bump(t / eps) * bump(r / eps) * (T - t >= r),
        -eps, eps, 0, eps)[0]
T = 1.0
g0 = G0f(T)
report("5a massless Huygens: G+ f(p) = 0 inside the cone", abs(g0) < 1e-15, "G+f(1,0) = %.1e" % g0)
vals = []
for m in (0.05, 0.1, 0.2):
    gm = Gmf(T, m); vals.append((m, gm, -m * m * G2f(T)))
rel = max(abs(a - b) / abs(b) for _, a, b in vals)
report("5b massive: G_m f(p) != 0 and ~ -m^2 (G+)^2 f(p)", all(abs(a) > 0 for _, a, _ in vals) and rel < 0.05,
       "; ".join("m=%.2f: %.3e vs %.3e" % v for v in vals))

# 6. dilation (on the plane-wave kernels: G_m kernel sin(w s)/w; G^+ scales by lambda^2)
lam, m, k = 0.5, 1.2, 0.8
# G_m^+ applied to f_lambda at lambda p equals lambda^2 G_{lambda m}^+ f(p): check the Bessel kernel form
s0 = 2.0
lhs = -(m / (4 * math.pi)) * special.j1(m * math.sqrt(lam * lam * s0)) / math.sqrt(lam * lam * s0) * lam ** 4
rhs = lam ** 2 * (-(lam * m / (4 * math.pi)) * special.j1(lam * m * math.sqrt(s0)) / math.sqrt(s0))
report("6 dilation of the tail kernel (lambda^4 dw with lambda^2 prefactor)", abs(lhs - rhs) < 1e-14,
       "difference %.1e" % abs(lhs - rhs))

# 7. (H2, Corollary 6) iterated power bound: for h depending on time only, vanishing before t0,
#    G^+ h(t) = int_0^{t - t0} rho h(t - rho) d rho; check |(G^+)^k h| <= sup|h| (t - t0)^{2k}/(2k)!
t0, T, N = 0.0, 3.0, 3001
ts = np.linspace(t0, T, N); dt = ts[1] - ts[0]
h = np.sin(3 * ts) * np.exp(-ts) + 0.5 * np.cos(7 * ts)      # bounded, arbitrary sign
sup_h = np.max(np.abs(h))
cur = h.copy(); worst = -np.inf
for k in range(1, 7):
    new = np.zeros(N)
    for i in range(1, N):
        rho = ts[:i + 1] - t0                                      # rho from 0 to t_i - t0
        new[i] = np.trapezoid(rho * cur[i::-1], dx=dt)
    cur = new
    bound = sup_h * (ts - t0) ** (2 * k) / math.factorial(2 * k)
    worst = max(worst, np.max(np.abs(cur) - bound - 1e-9))
report("7 iterated bound |(G+)^k h| <= sup|h| (t-t0)^{2k}/(2k)!, k <= 6", worst <= 0,
       "max excess %.1e (negative: bound holds)" % worst)

# 8-10 (H4): the route for the failure of Huygens' principle, for either sign of mu.
#    f = bump of width e at the origin (f >= 0, sup f = C), p = (T, 0), t0 = -e, tau = T + e.
def tail_kernel(mu, s):  # kernel of G_mu^+ - G^+ inside the cone; m^2 = mu, analytic in mu
    if mu == 0:
        return 0.0
    k = math.sqrt(abs(mu))
    if s <= 0:
        return -mu / (8 * math.pi)
    x = k * math.sqrt(s)
    return (-(k / (4 * math.pi)) * special.j1(x) if mu > 0 else (k / (4 * math.pi)) * special.i1(x)) / math.sqrt(s)
def Gmu_f(T, mu, e):  # G_mu^+ f(p), p = (T, 0), f = bump(t/e) bump(|x|/e)
    light = integrate.quad(lambda r: r * bump((T - r) / e) * bump(r / e), 0, 2 * e, points=[e])[0]
    def inner(r):
        g = lambda tau: tail_kernel(mu, tau * tau - r * r) * bump((T - tau) / e)
        return 4 * math.pi * r * r * bump(r / e) * integrate.quad(g, max(r, T - e), T + e)[0]
    return light + integrate.quad(inner, 0, e)[0]
def G2_f(T, e):  # (G^+)^2 f(p) = (1/8pi) int_{J^-(p)} f
    return (1 / (8 * math.pi)) * integrate.dblquad(
        lambda r, t: 4 * math.pi * r * r * bump(t / e) * bump(r / e) * (T - t >= r), -e, e, 0, e)[0]
e, T = 0.1, 1.0
C, tau = math.exp(-2.0), T + e
A = G2_f(T, e)
report("8 positivity (G+)^2 f(p) > 0 and sign of G_mu f(p) = sign of -mu A",
       A > 0 and all(np.sign(Gmu_f(T, mu, e)) == -np.sign(mu) for mu in (0.02, -0.02, 0.2, -0.2)),
       "A = %.3e" % A)
# 9. tail bound |G_mu f + mu A| <= C mu^2 tau^6 cosh(sqrt|mu| tau), and the threshold mu0
ser_ok = all(sum(x ** (2 * k) / math.factorial(2 * k) for k in range(2, 60)) <= x ** 4 * math.cosh(x) + 1e-15
             for x in (0.0, 0.3, 1.0, 3.0, 7.0))
worst = -np.inf
for mu in (0.01, -0.01, 0.1, -0.1, 1.0, -1.0):
    lhs = abs(Gmu_f(T, mu, e) + mu * A)
    worst = max(worst, lhs - C * mu * mu * tau ** 6 * math.cosh(math.sqrt(abs(mu)) * tau))
mu0 = min(1.0, A / (C * tau ** 6 * math.cosh(tau)))
nz = all(Gmu_f(T, mu, e) != 0 for mu in (0.9 * mu0, -0.9 * mu0, 0.1 * mu0))
report("9 tail bound, sum_{k>=2} x^2k/(2k)! <= x^4 cosh x, nonzero below mu0",
       ser_ok and worst <= 0 and nz, "max excess %.1e; mu0 = %.2e" % (worst, mu0))
# 10. dilation: G_mu^+ f_l(l p) = l^2 G_{l^2 mu}^+ f(p), f_l = f(./l) (bump of width l e)
worst = 0.0
for l, mu in ((0.5, 3.0), (0.25, -2.0), (2.0, 0.05)):
    lhs = Gmu_f(l * T, mu, l * e)
    rhs = l ** 2 * Gmu_f(T, l * l * mu, e)
    worst = max(worst, abs(lhs - rhs) / abs(rhs))
report("10 dilation G_mu f_l(l p) = l^2 G_{l^2 mu} f(p)", worst < 1e-6, "max rel. error %.1e" % worst)

print("ALL PASS" if ok_all else "SOME FAILED")
