"""Exact arithmetic in Z[q]/Phi_k(q). No floating point anywhere.

Elements are tuples of ints of length deg Phi_k, coefficients of
1, q, ..., q^{d-1}. Zero element is the all-zero tuple.
"""
import sympy as sp
from sympy import symbols, cyclotomic_poly

_q = symbols('q')


def phi_coeffs(k):
    p = sp.Poly(cyclotomic_poly(k, _q), _q)
    return [int(c) for c in reversed(p.all_coeffs())]


class CycRing:
    def __init__(self, k):
        self.k = k
        phi = phi_coeffs(k)
        self.d = len(phi) - 1
        d = self.d
        # reduction table: x^j mod Phi_k for j = 0 .. 2d-2, as lists
        red = []
        for j in range(d):
            v = [0] * d
            v[j] = 1
            red.append(v)
        for j in range(d, 2 * d - 1):
            # x^j = x * x^{j-1}, then reduce leading term
            prev = red[j - 1]
            v = [0] + prev[:]           # multiply by x, length d+1
            lead = v[d]
            if lead:
                # x^d = -(phi[0] + ... + phi[d-1] x^{d-1})  (Phi monic)
                for i in range(d):
                    v[i] -= lead * phi[i]
            red.append(v[:d])
        self.red = red
        self.zero = tuple([0] * d)
        self.one = tuple([1] + [0] * (d - 1))
        # powers of q mod Phi_k, exponents 0..k-1
        self.qpow = []
        cur = list(self.one)
        for _ in range(k):
            self.qpow.append(tuple(cur))
            cur = self._mul_by_x(cur)
        # q-integers [r]_w for lifts r = 0..k-1
        self.qint = []
        acc = [0] * d
        for r in range(k):
            self.qint.append(tuple(acc))
            p = self.qpow[r]
            acc = [a + b for a, b in zip(acc, p)]
        # note: qint[r] = 1 + q + ... + q^{r-1}; qint[0] = 0

    def _mul_by_x(self, v):
        d = self.d
        out = [0] + list(v)
        lead = out[d]
        if lead:
            phi = phi_coeffs(self.k)
            for i in range(d):
                out[i] -= lead * phi[i]
        return out[:d]

    def mul(self, a, b):
        d = self.d
        conv = [0] * (2 * d - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    if bj:
                        conv[i + j] += ai * bj
        out = [0] * d
        red = self.red
        for j, cj in enumerate(conv):
            if cj:
                rj = red[j]
                for i in range(d):
                    out[i] += cj * rj[i]
        return tuple(out)

    def sub(self, a, b):
        return tuple(x - y for x, y in zip(a, b))

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def S_of_residues(self, rs):
        """S_n(w) for residue tuple rs = (r_2, ..., r_n), each in 0..k-1.

        Recurrence: S_1 = 1, S_2 = [r_2], S_{i+1} = [r_{i+1}] S_i - q^{r_i - 1} S_{i-1},
        exponent from the PREVIOUS quotient. Residues taken mod k throughout.
        """
        k = self.k
        prev = self.one           # S_1
        cur = self.qint[rs[0] % k]  # S_2
        for i in range(1, len(rs)):
            r_new = rs[i] % k
            r_old = rs[i - 1] % k
            t1 = self.mul(self.qint[r_new], cur)
            t2 = self.mul(self.qpow[(r_old - 1) % k], prev)
            prev, cur = cur, self.sub(t1, t2)
        return cur
