"""Test the proposed reduction lemma for T1.

Claim under test (core lemma):
    Let x be a quadratic irrational with HJ expansion [[c_1, c_2, c_3, ...]],
    let r = [[c_1, c_2]] be its second HJ convergent (a rational), and let
    beta = (c_1 - 1) + (c_2 - 1). Then

        [x]_q - [r]_q = -q^beta + (terms of degree > beta),

    the leading coefficient being exactly -1, not merely nonzero.

Consequence to test:
    coeff of G(x) at degree beta  ==  coeff of G(r) at degree beta  -  1.

Exact arithmetic throughout: integer polynomial coefficients in dicts.
"""
from fractions import Fraction

from qreals.quadratic import QuadraticIrrational, hj_terms

# ---------------------------------------------------------------- polynomials


def pmul(a, b, cap):
    out = {}
    for i, ai in a.items():
        if ai == 0:
            continue
        for j, bj in b.items():
            k = i + j
            if k > cap:
                continue
            out[k] = out.get(k, 0) + ai * bj
    return {k: v for k, v in out.items() if v != 0}


def padd(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v != 0}


def pneg(a):
    return {k: -v for k, v in a.items()}


def q_bracket(c):
    """[c]_q as a Laurent dict; handles c <= 0 via [c]_q = -q^c [-c]_q."""
    if c > 0:
        return {i: 1 for i in range(c)}
    if c == 0:
        return {}
    return {c + i: -1 for i in range(-c)}


def mat_mul(A, B, cap):
    return [
        padd(pmul(A[0], B[0], cap), pmul(A[1], B[2], cap)),
        padd(pmul(A[0], B[1], cap), pmul(A[1], B[3], cap)),
        padd(pmul(A[2], B[0], cap), pmul(A[3], B[2], cap)),
        padd(pmul(A[2], B[1], cap), pmul(A[3], B[3], cap)),
    ]


def step(c):
    return [q_bracket(c), {c - 1: -1}, {0: 1}, {}]


def divide(num, den, lo, hi):
    """Laurent division num/den. den must have a lowest term; returns dict."""
    vn = min(num) if num else 0
    vd = min(den) if den else 0
    if not num:
        return {}
    d0 = den[vd]
    n = {k - vn: Fraction(v) for k, v in num.items()}
    d = {k - vd: Fraction(v) for k, v in den.items()}
    order = hi - (vn - vd) + 1
    c = {}
    for m in range(order + 1):
        s = n.get(m, Fraction(0))
        for i in range(1, m + 1):
            di = d.get(i)
            if di:
                s -= di * c[m - i]
        c[m] = s / d0
    return {(vn - vd + m): v for m, v in c.items() if v != 0 and lo <= (vn - vd + m) <= hi}


def convergent(terms, cap):
    """R_n/S_n as a Laurent series for the HJ word `terms`."""
    M = [{0: 1}, {}, {}, {0: 1}]
    for c in terms:
        M = mat_mul(M, step(c), cap + 40)
    lo = min(0, terms[0] - 1) - 4
    return divide(M[0], M[2], lo, cap)


# ---------------------------------------------------------------- the test


def check(a, b, D, nterms=14):
    x = QuadraticIrrational.from_ab(Fraction(a), Fraction(b), D)
    terms, _, _ = hj_terms(x, nterms)
    if len(terms) < 4:
        return None
    beta = (terms[0] - 1) + (terms[1] - 1)
    cap = beta + 6
    limit = convergent(terms, cap)          # deep convergent stands in for [x]_q
    r2 = convergent(terms[:2], cap)          # [r]_q, r = second convergent
    diff = padd(limit, pneg(r2))
    diff = {k: v for k, v in diff.items() if v != 0}
    if not diff:
        return ("EMPTY", beta, None, None)
    v = min(diff)
    return ("OK", beta, v, diff[v])


def main():
    bad = []
    n = 0
    for D in (2, 3, 5):
        for an in range(-20, 21):
            for bn in range(-12, 13):
                if bn == 0:
                    continue
                res = check(Fraction(an, 4), Fraction(bn, 4), D)
                if res is None:
                    continue
                status, beta, v, lead = res
                n += 1
                if status != "OK" or v != beta or lead != -1:
                    bad.append((D, an, bn, beta, v, lead))
    print(f"checked {n} quadratic irrationals over D in 2,3,5")
    print(f"violations of ([x]_q - [r]_q = -q^beta + h.o.t.): {len(bad)}")
    for row in bad[:20]:
        print("  ", row)


if __name__ == "__main__":
    main()
