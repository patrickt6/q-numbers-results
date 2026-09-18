"""Classify the falsify form box by the split-class theorem, with no (P) scan.

The falsify Gap A form scan ran over the nominal box A0 in 1..60, B0 in
-60..60 with B0 != 0, C0 in -60..60, positive nonsquare discriminant. It
tested 115,232 forms, abstained on 226,180 (no fundamental Pell solution
within u <= 20000), and never reached the rest of the box.

The split-class theorem proved in WRITEUP.tex covers a form exactly when some
integer n lies strictly between the two roots of A0 X^2 + B0 X + C0, that is,
when A0 n^2 + B0 n + C0 < 0 for some integer n. Since the parabola is convex
with A0 > 0, it suffices to test the two integers nearest the vertex
-B0/(2 A0). This script counts, over the whole nominal box:

  total     forms with positive nonsquare discriminant and B0 != 0
  covered   forms proved by the split-class theorem (Gap A is a theorem there,
            no Pell solution and no scan needed)
  residual  forms with both roots in one open unit interval (Gap A still
            conjectural)
  oppsign   the subset of covered with C0 < 0 (opposite-sign roots, the
            positive-word class)

No (P) computation and no Pell search is performed; this is bookkeeping only.
"""
import math


def is_square(n: int) -> bool:
    if n < 0:
        return False
    r = math.isqrt(n)
    return r * r == n


def main():
    total = covered = oppsign = 0
    for a0 in range(1, 61):
        for b0 in range(-60, 61):
            if b0 == 0:
                continue
            for c0 in range(-60, 61):
                disc = b0 * b0 - 4 * a0 * c0
                if disc <= 0 or is_square(disc):
                    continue
                total += 1
                # nearest integers to the vertex -b0 / (2 a0)
                v = -b0 / (2 * a0)
                cov = any(
                    a0 * n * n + b0 * n + c0 < 0
                    for n in (math.floor(v), math.ceil(v))
                )
                if cov:
                    covered += 1
                    if c0 < 0:
                        oppsign += 1
    residual = total - covered
    print(f"nominal box, B0 != 0, positive nonsquare discriminant: {total}")
    print(f"covered by the split-class theorem: {covered} "
          f"({100 * covered / total:.2f} percent)")
    print(f"  of which opposite-sign roots (C0 < 0): {oppsign}")
    print(f"residual (both roots in one unit interval): {residual} "
          f"({100 * residual / total:.2f} percent)")


if __name__ == "__main__":
    main()
