"""Numerical check of Theorem B: if 1/(N+1) < x < 1/N with x irrational and
N >= 8, then B = max(beta(x), beta(-x)) = N - 1 and the first tail degree of
G(x) is exactly N - 1."""
from fractions import Fraction as F
from math import isqrt
from gtools import beta, first_tail, g_series, hj, predicted, qi

def pick_x(N, D):
    """An irrational a + b*sqrt(D) strictly inside (1/(N+1), 1/N)."""
    # use x = (p + sqrt(D))/s with s chosen so the value lands in the window
    lo, hi = F(1, N + 1), F(1, N)
    for s in range(1, 400):
        # x = (k + sqrt(D)) / s ; sqrt(D) ~ isqrt(D*10**20)/10**10
        rt = F(isqrt(D * 10 ** 40), 10 ** 20)
        for k in range(-4 * s, 4 * s + 1):
            v = (k + rt) / s
            if lo < v < hi:
                x = qi(F(k, s), F(1, s), D)
                return x
    return None

print(f"{'N':>5}{'D':>3}{'B':>6}{'N-1':>6}{'d':>6}  hj(x)[:4]           hj(-x)[:3]")
bad = 0
for N in [8, 9, 10, 12, 15, 20, 25, 31, 40, 55, 70]:
    for D in (2, 3, 5):
        x = pick_x(N, D)
        if x is None:
            continue
        B = predicted(x)
        g, lo, ld = g_series(x, N + 20)
        d, top = first_tail(g, lo, ld)
        ok = (B == N - 1 and d == N - 1)
        if not ok:
            bad += 1
        print(f"{N:>5}{D:>3}{B:>6}{N-1:>6}{str(d):>6}  {str(hj(x,4)):<20}{str(hj(-x,3)):<14}"
              f"{'' if ok else '   <-- MISMATCH'}")
print("mismatches:", bad)
