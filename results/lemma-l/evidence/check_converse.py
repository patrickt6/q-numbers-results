"""
Agent A, T2. Witnesses that the converse of the valuation corollary fails:
v_p(s) >= a does NOT imply Phi_{p^a} | C. Scans d <= 400 for
(p, a) in {(2,3), (3,2), (5,2)} looking for d with v_p(s) >= a and
Phi_{p^a} not dividing C, and prints the first few witnesses of each.
"""
import sys, math

sys.path.insert(0, "<path>")
import fastlam  # noqa: E402
import sympy as sp

Q = sp.Symbol('q')
CASES = [(2, 3), (3, 2), (5, 2)]
PHI = {}
for p, a in CASES:
    n = p ** a
    PHI[n] = [int(x) for x in sp.Poly(sp.cyclotomic_poly(n, Q), Q).all_coeffs()[::-1]]


def shift(poly):
    mn = min(poly)
    out = [0] * (max(poly) - mn + 1)
    for e, c in poly.items():
        out[e - mn] = c
    return out


def rem_monic(dividend, divisor):
    rem = list(dividend)
    dd = len(divisor) - 1
    deg = len(rem) - 1
    while deg >= dd:
        while deg >= 0 and rem[deg] == 0:
            deg -= 1
        if deg < dd:
            break
        lead = rem[deg]
        if lead:
            sh = deg - dd
            for i, dc in enumerate(divisor):
                rem[sh + i] -= lead * dc
        deg -= 1
    return all(c == 0 for c in rem)


def v_p(x, p):
    v = 0
    x = abs(x)
    while x and x % p == 0:
        x //= p
        v += 1
    return v


found = {c: [] for c in CASES}
for d in range(2, 401):
    r0 = math.isqrt(d)
    if r0 * r0 == d:
        continue
    (r, s), (A, B, C, D) = fastlam.lam_q_fast(d)
    for p, a in CASES:
        if v_p(s, p) >= a and len(found[(p, a)]) < 5:
            div = rem_monic(shift(C), PHI[p ** a])
            if not div:
                found[(p, a)].append((d, s, v_p(s, p)))

for (p, a), lst in found.items():
    print(f"p={p} a={a}: witnesses (d, s, v_p(s)) with p^a | s but Phi_(p^a) does not divide C:")
    print("  ", lst if lst else "none found to d=400")
