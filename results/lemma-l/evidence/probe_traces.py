"""
T2 (route B). Floating-point sanity probe (NOT part of the proof; the proof
uses only exact classical facts) of the trace bookkeeping in PROOF.md:

  - SL2 lifts of the specialized generators at q = zeta_n have the trace
    triple (0, 1, 2cos(pi/n)) on the generating pair of PSL(2,Z), matching
    the Fuchsian (2,3,n) triangle group triple.
  - The commutator [S, R] specializes to a hyperbolic element for n = 9
    (tr^2/det = 6.41 > 4), and to the parabolic boundary tr^2/det = 4
    exactly at n = 6, confirming that n = 6 is the degenerate index.
"""
import cmath
import math


def probe(n, k=1):
    z = cmath.exp(2j * cmath.pi * k / n)
    hz = cmath.exp(1j * cmath.pi * k / n)  # z^{1/2}
    S = [[0, -1 / z * hz], [hz, 0]]        # zeta^{1/2} S_zeta, det 1
    R = [[z / hz, 1 / hz], [0, 1 / hz]]    # zeta^{-1/2} R_zeta, det 1

    def mul(X, Y):
        return [[X[0][0] * Y[0][0] + X[0][1] * Y[1][0], X[0][0] * Y[0][1] + X[0][1] * Y[1][1]],
                [X[1][0] * Y[0][0] + X[1][1] * Y[1][0], X[1][0] * Y[0][1] + X[1][1] * Y[1][1]]]

    def tr(X):
        return X[0][0] + X[1][1]

    def det(X):
        return X[0][0] * X[1][1] - X[0][1] * X[1][0]

    def inv(X):
        dd = det(X)
        return [[X[1][1] / dd, -X[0][1] / dd], [-X[1][0] / dd, X[0][0] / dd]]

    RS = mul(R, S)
    print(f"n={n} k={k}: det S~={det(S):.4f} det R~={det(R):.4f}")
    print(f"  tr S~  = {tr(S):.6f} (expect 0)")
    print(f"  tr R~S~ = {tr(RS):.6f} (expect +-1)")
    print(f"  tr R~  = {tr(R):.6f} vs 2cos(pi k/n) = {2 * math.cos(math.pi * k / n):.6f}")
    C = mul(mul(S, R), mul(inv(S), inv(R)))
    print(f"  tr^2/det of [S~,R~] = {tr(C) ** 2 / det(C):.6f} "
          f"(real and > 4 means hyperbolic, hence infinite order)")


if __name__ == "__main__":
    probe(9)
    probe(9, 2)
    probe(6)
