"""Pure-integer SL(2,Z) word decomposition, dropping sympy from the hot path.

`proof_verification.sl2_word` (READ-ONLY, imported and reused elsewhere in
this folder) implements the same Euclidean-algorithm decomposition, but does
every step as an `sp.Matrix` multiplication. That is pure integer arithmetic
wrapped in sympy's general symbolic machinery, and the attempt-1/README.md notes
it as the throughput bottleneck for widening the trace-zero scan.

`sl2_word_fast` below is the identical algorithm (same recursion, same
generator convention R = [[1,1],[0,1]], S = [[0,-1],[1,0]]) over plain Python
ints and 2x2 nested tuples, verified against `proof_verification.sl2_word`
below (`self_check`), which this module runs on import in debug mode only.
"""
from __future__ import annotations

Mat = tuple[tuple[int, int], tuple[int, int]]


def mat_mul(A: Mat, B: Mat) -> Mat:
    (a, b), (c, d) = A
    (e, f), (g, h) = B
    return ((a * e + b * g, a * f + b * h), (c * e + d * g, c * f + d * h))


def sl2_word_fast(M: Mat) -> list[tuple]:
    """M in SL(2,Z) -> list of ('R', n) / ('S',), M = product, up to sign.

    Identical algorithm to proof_verification.sl2_word, over plain ints.
    """
    a, b = M[0]
    c, d = M[1]
    w: list[tuple] = []
    while c != 0:
        n = a // c
        w.append(("R", n))
        # M <- [[1,-n],[0,1]] @ M
        a, b = a - n * c, b - n * d
        w.append(("S",))
        # M <- [[0,1],[-1,0]] @ M
        a, b, c, d = c, d, -a, -b
    w.append(("R", b // a))
    return w


def self_check() -> None:
    import random
    import sys

    sys.path.insert(
        0, "<path>"
    )
    import sympy as sp
    from proof_verification import sl2_word

    rng = random.Random(0)
    for _ in range(200):
        # random SL(2,Z) matrix as a product of small R^k, S generators
        M = ((1, 0), (0, 1))
        for _ in range(rng.randint(1, 12)):
            if rng.random() < 0.5:
                k = rng.randint(-5, 5)
                M = mat_mul(M, ((1, k), (0, 1)))
            else:
                M = mat_mul(M, ((0, -1), (1, 0)))
        a, b = M[0]
        c, d = M[1]
        assert a * d - b * c == 1, M
        w_fast = sl2_word_fast(M)
        w_slow = sl2_word(sp.Matrix([[a, b], [c, d]]))
        w_slow = [(t[0], int(t[1])) if t[0] == "R" else (t[0],) for t in w_slow]
        assert w_fast == w_slow, (M, w_fast, w_slow)
    print("self_check: 200/200 random SL(2,Z) words agree with proof_verification.sl2_word")


if __name__ == "__main__":
    self_check()
