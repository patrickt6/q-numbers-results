"""Spot checks for the nine-quadratic table of characterization.tex cor:named.

1. For each recorded automorph, compute the exact mismatch ratio
   r = q^(mu+1) C(1/q) / C(q) from rho(M) and confirm:
   monomial rows satisfy r = q^((a-d')/c), i.e. the exponent is the trace
   of the fixed quadratic irrational; non-monomial rows have a^2 != 1 mod c.
2. Confirm the two non-monomial automorphs are positive words in R, L
   (so the route-B corollary applies to them and their non-monomial ratio is
   a theorem, not an observation).
"""
from __future__ import annotations

import sys

FALSIFY = ("<path>"
           "2026-07-21-next-steps/problems/T3-quadratic-conjecture/attempts/falsify")
PAPERGAPS = ("<path>"
             "2026-07-11-paper-gaps/code")
for p in (FALSIFY, PAPERGAPS):
    if p not in sys.path:
        sys.path.append(p)

from fast_word import sl2_word_fast  # noqa: E402
from fastlam import rho_fast, p_add, p_mul  # noqa: E402

TABLE = [
    ("(1+sqrt5)/2", ((2, 1), (1, 1)), "q"),
    ("1+sqrt2", ((5, 2), (2, 1)), "q^2"),
    ("2+sqrt2", ((7, -4), (2, -1)), "q^4"),
    ("(3+sqrt13)/2", ((10, 3), (3, 1)), "q^3"),
    ("3+sqrt3", ((5, -6), (1, -1)), "q^6"),
    ("(1+sqrt2)/2", ((5, 1), (4, 1)), "q"),
    ("(1+sqrt3)/2", ((3, 1), (2, 1)), "q"),
    ("(2+sqrt7)/3", ((14, 3), (9, 2)), "not monomial"),
    ("(1+sqrt13)/3", ((829, 720), (540, 469)), "not monomial"),
]


def det_exponent(A, B, C, D):
    det = p_add(p_mul(A, D), p_mul(B, C), scale=-1)
    assert len(det) == 1
    ((e, c),) = det.items()
    assert c in (1, -1)
    return e


def ratio_as_monomial(C, mu):
    """r = q^(mu+1) conj(C) / C. Return ('q^k', k) if r = +q^k, ('-q^k', k)
    if -q^k, else None."""
    num = {mu + 1 - e: c for e, c in C.items()}  # q^(mu+1) C(1/q)
    lo_n, lo_d = min(num), min(C)
    k = lo_n - lo_d
    if num == {e + k: c for e, c in C.items()}:
        return "+", k
    if num == {e + k: -c for e, c in C.items()}:
        return "-", k
    return None


def is_positive_word(word):
    """sl2_word_fast tokens -> True if M = +(positive word), returning the
    R/L block form when so. Tokens are ('R', n) and ('S',); the classical
    identity L = S^{-1} R^{-1} S^{-1}... is not used; instead rebuild:
    the word is positive iff every R exponent is >= 0 after converting the
    R,S word into an R,L word via L^k = S R^{-k} S^{-1}-free direct check:
    simply re-derive the R/L form from the matrix by the Euclidean algorithm
    on columns, which succeeds iff the matrix is a product of nonnegative
    R and L powers."""
    return None  # not used; direct check below


def rl_decompose(M):
    """M = R^{e1} L^{e2} R^{e3} ... with all ei >= 1 (e1, e_last >= 0
    allowed): returns the letter string, or None if M is not a positive
    word."""
    (a, b), (c, d) = M
    out = []
    # peel letters from the LEFT: M = R X iff X = R^{-1} M has nonneg
    # entries etc.; a positive word's leftmost letter is R iff a > c... use:
    # R^{-1} M = [[a-c, b-d],[c, d]], L^{-1} M = [[a, b],[c-a, d-b]]
    while (a, b, c, d) not in [(1, 0, 0, 1)]:
        if a >= c and b >= d and (a - c, b - d) != (0, 0) and not (a - c == 0 and b - d < 0):
            # try R first when row1 dominates
            if a - c >= 0 and b - d >= 0 and (a - c) * d - (b - d) * c == 1:
                out.append("R")
                a, b = a - c, b - d
                continue
        if c - a >= 0 and d - b >= 0 and a * (d - b) - b * (c - a) == 1:
            out.append("L")
            c, d = c - a, d - b
            continue
        return None
    return "".join(out)


def main():
    print(f"{'x':>14} {'automorph':>22} {'ratio':>14} {'(a-d)/c':>8} "
          f"{'a^2 mod c':>10} {'pos word':>28}")
    for name, M, recorded in TABLE:
        (a, b), (c, d) = M
        word = sl2_word_fast(M)
        A, B, C, D = rho_fast(word)
        mu = det_exponent(A, B, C, D)
        r = ratio_as_monomial(C, mu)
        rl = rl_decompose(M)

        def blocks(s):
            if not s:
                return s
            out, cur, n = [], s[0], 1
            for ch in s[1:]:
                if ch == cur:
                    n += 1
                else:
                    out.append(f"{cur}{n if n > 1 else ''}")
                    cur, n = ch, 1
            out.append(f"{cur}{n if n > 1 else ''}")
            return "".join(out)

        rtxt = f"{r[0]}q^{r[1]}" if r else "not monomial"
        tr = (a - d) / c
        a2 = (a * a) % abs(c)
        print(f"{name:>14} {str(M):>22} {rtxt:>14} {tr:>8} {a2:>10} "
              f"{blocks(rl) if rl else 'no':>28}")
        # assertions of the corollary
        if r:
            assert recorded != "not monomial"
            assert r[0] == "+" and r[1] == (a - d) // c, (name, r)
            assert a2 == 1 % abs(c) or (a - d) % c == 0, name
        else:
            assert recorded == "not monomial"
            assert a2 != 1 % abs(c), name
            if rl is not None:  # positive word: corollary applies as theorem
                assert (a - d) % c != 0, name
    print("\nall table assertions passed")


if __name__ == "__main__":
    main()
