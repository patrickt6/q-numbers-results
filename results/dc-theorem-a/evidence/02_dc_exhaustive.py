"""Exhaustive downward-closure test on residue slices.

Because S_n(w) at a primitive k-th root depends only on the residues of
(c_2, ..., c_n) mod k (anchored in 01_anchor.py), (DC) restricted to
continued-fraction length n and index k is a FINITE statement: check all
k^{n-1} residue tuples. A violation here is a genuine counterexample to
(DC); absence here is an exhaustive proof of the (n, k) slice.

Slices covered (chosen to include the frontier pairs with l >= 6):
  n = 5: all composite k <= 30
  n = 6: all composite k <= 16
  n = 7: k in {8, 9, 12, 14, 16}
  n = 8: k in {8, 9}
Exact arithmetic only.
"""
import sys
import time

sys.path.insert(0, "<path>"
                    "<path>")
from ring import CycRing  # noqa: E402


def divisors_gt1(k):
    return [l for l in range(2, k) if k % l == 0]


def sweep(k, n):
    R = CycRing(k)
    divs = divisors_gt1(k)
    if not divs:
        return 0, 0
    subrings = {l: CycRing(l) for l in divs}
    hits = 0
    violations = 0
    zero = R.zero
    qint, qpow, mul, sub = R.qint, R.qpow, R.mul, R.sub
    one = R.one

    tuple_buf = [0] * (n - 1)

    def rec(depth, prev, cur):
        nonlocal hits, violations
        if depth == n - 1:
            if cur == zero:
                hits += 1
                rs = tuple(tuple_buf)
                for l, Rl in subrings.items():
                    if Rl.S_of_residues([r % l for r in rs]) != Rl.zero:
                        violations += 1
                        print(f"  *** VIOLATION k={k} l={l} n={n} residues={rs}")
            return
        for r in range(k):
            tuple_buf[depth] = r
            if depth == 0:
                rec(1, one, qint[r])
            else:
                r_old = tuple_buf[depth - 1]
                nxt = sub(mul(qint[r], cur), mul(qpow[(r_old - 1) % k], prev))
                rec(depth + 1, cur, nxt)

    # depth 0 seeds S_2; note rec(0, ...) placeholder args unused at depth 0
    rec(0, None, None)
    return hits, violations


def main():
    jobs = []
    for k in range(4, 31):
        if any(k % l == 0 for l in range(2, k)):
            jobs.append((k, 5))
    for k in range(4, 17):
        if any(k % l == 0 for l in range(2, k)):
            jobs.append((k, 6))
    for k in (8, 9, 12, 14, 16):
        jobs.append((k, 7))
    for k in (8, 9):
        jobs.append((k, 8))

    total_hits = total_viol = 0
    for k, n in jobs:
        t0 = time.time()
        h, v = sweep(k, n)
        total_hits += h
        total_viol += v
        print(f"k={k:3d} n={n}  tuples={k**(n-1):>9d}  hits={h:>7d}  "
              f"violations={v}  [{time.time()-t0:.1f}s]", flush=True)
    print(f"TOTAL hits={total_hits} violations={total_viol}")


if __name__ == "__main__":
    main()
