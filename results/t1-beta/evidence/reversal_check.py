"""Check the reversal decomposition of G.

Claim R1.  With A_n = R_n/S_n the n-th HJ convergent of x and
Atil_n(q) := -q^{-1} A_n(1/q), one has
    Atil_n - Atil_{n-1} = + q^{C_n - 2 c_1 + 1} / (S_n^* S_{n-1}^*),
where S^*(q) = q^{deg S} S(1/q), and S_n, S_n^* are monic with constant term 1.
Hence val(Atil_n - Atil_{n-1}) = C_n - 2 c_1 + 1 exactly.

Claim R2.  [-x]_q = lim_n Atil_n, so val([-x]_q - Atil_n) = C_{n+1} - 2 c_1 + 1.

Claim R3.  Consequently
    G = W + sum_{k>=1} (-q^{gamma_k} u_k) + sum_{k>=2} (q^{delta_k} w_k),
    W = [c_1]_q - q^{-1}[c_1]_{1/q} = sum_{i=0}^{N-1} q^i - sum_{i=1}^{N} q^{-i},
    N = |c_1|,  gamma_k = C_k,  delta_k = C_k - 2 c_1 + 1,
with u_k = 1/(S_{k+1} S_k) and w_k = 1/(S_k^* S_{k-1}^*) unit series (value 1 at q=0).
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import product

from exact import (
    C_partial,
    G_exact,
    QuadraticIrrational,
    convergent_ratfun,
    divide,
    hj,
    ladd,
    lsub,
    lmul,
    q_bracket,
    q_series,
)


def reverse_poly(p):
    """q^{deg p} p(1/q) for a Laurent polynomial dict."""
    d = max(p)
    return {d - k: v for k, v in p.items()}


def W_series(c1):
    N = abs(c1)
    out = {}
    for i in range(0, N):
        out[i] = F(1)
    for i in range(1, N + 1):
        out[-i] = F(-1)
    return out


def check_R1_R2(x, target=60, nmax=8):
    terms = hj(x, nmax + 2)
    c1 = terms[0]
    Cs = C_partial(terms)
    out = []
    B, _, _ = q_series(-x, target)
    for n in range(1, nmax + 1):
        R, S = convergent_ratfun(x, n)
        if not R:
            continue
        # Atil_n = -q^{-1} A_n(1/q) = -q^{-1} (q^{-dR} R*) / (q^{-dS} S*)
        Rs, Ss = reverse_poly(R), reverse_poly(S)
        dR, dS = max(R), max(S)
        shift = dS - dR - 1  # equals -c1
        num = {k + shift: -v for k, v in Rs.items()}
        At = divide(num, Ss, target)
        diff = {k: v for k, v in lsub(B, At).items() if v}
        val = min(diff) if diff else None
        pred = Cs[n + 1] - 2 * c1 + 1
        ok = (val == pred) or (val is None and pred > target)
        out.append((n, shift == -c1, val, pred, ok,
                    S.get(0) == 1, Ss.get(0) == 1))
    return out


def convergent_list(x, n):
    """[(R_k, S_k) for k = 1..n], built incrementally."""
    terms = hj(x, n)
    P = ({0: F(1)}, {}, {}, {0: F(1)})
    out = []
    for c in terms[:n]:
        P = mat_mul_local(P, M_local(c))
        out.append((P[0], P[2]))
    return out


def M_local(c):
    return (q_bracket(c), {c - 1: F(-1)}, {0: F(1)}, {})


def mat_mul_local(A, B):
    a00, a01, a10, a11 = A
    b00, b01, b10, b11 = B
    return (ladd(lmul(a00, b00), lmul(a01, b10)),
            ladd(lmul(a00, b01), lmul(a01, b11)),
            ladd(lmul(a10, b00), lmul(a11, b10)),
            ladd(lmul(a10, b01), lmul(a11, b11)))


def check_R3(x, target=60):
    """Rebuild G from W plus the two event families and compare with G_exact."""
    terms = hj(x, 4000)
    Cs = C_partial(terms)
    kg = next(k for k in range(1, len(Cs)) if Cs[k] > target)
    kd = next(k for k in range(2, len(Cs)) if Cs[k] - 2 * terms[0] + 1 > target)
    nmax = max(kg, kd) + 3
    conv = convergent_list(x, nmax + 1)
    Ss = {k + 1: conv[k][1] for k in range(len(conv))}
    c1 = terms[0]
    g = G_exact(x, target)
    acc = W_series(c1)
    for k in range(1, nmax):
        if Cs[k] > target:
            break
        acc = ladd(acc, divide({Cs[k]: F(-1)}, lmul(Ss[k + 1], Ss[k]), target))
    for k in range(2, nmax):
        d = Cs[k] - 2 * c1 + 1
        if d > target:
            break
        acc = ladd(acc, divide({d: F(1)},
                               lmul(reverse_poly(Ss[k]), reverse_poly(Ss[k - 1])),
                               target))
    acc = {kk: v for kk, v in acc.items() if v and kk <= target}
    gg = {kk: v for kk, v in g.items() if kk <= target}
    return {kk: v for kk, v in lsub(gg, acc).items() if v}


def main():
    bad1 = bad3 = n = 0
    for D in (2, 3, 5, 7):
        for qa, qb in product(range(1, 3), repeat=2):
            for pa in range(-4 * qa, 4 * qa + 1):
                for pb in range(1, 3 * qb + 1):
                    x = QuadraticIrrational.from_ab(F(pa, qa), F(pb, qb), D)
                    n += 1
                    for rec in check_R1_R2(x, 45, 5):
                        if not (rec[4] and rec[5] and rec[6]):
                            bad1 += 1
                            if bad1 < 10:
                                print("R1/R2 FAIL", pa, qa, pb, qb, D, rec)
                    d = check_R3(x, 45)
                    if d:
                        bad3 += 1
                        if bad3 < 10:
                            print("R3 FAIL", pa, qa, pb, qb, D, sorted(d.items())[:5])
    print(f"checked {n} numbers; R1/R2 failures {bad1}; R3 failures {bad3}")


if __name__ == "__main__":
    main()
