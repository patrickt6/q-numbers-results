#!/usr/bin/env python3
r"""N2. Independent test of the a collaborator-a collaborator downward-closure route.

Self contained. No sympy, no external cyclotomic table, no floating point. Cyclotomic
polynomials are built inside this file by exact integer division of x^k - 1 by the lower
Phi_d. Nothing here imports vanishing_locus.py or closure_check.py.

Conventions.

    S_0 = 0,  S_1 = 1,  S_{i+1} = [c_{i+1}]_q S_i - q^{c_i - 1} S_{i-1},
    [a]_q = (1 - q^a) / (1 - q),  so [0]_q = 0 and [-a]_q = -q^{-a} [a]_q.

S_i depends on (c_2, ..., c_i) only.

Four experiments.

  A. Residue loci V_i(k) and the downward closure test: for every k, every l > 1 dividing
     k, every w in V_i(k), is (w mod l) in V_i(l)?

  B. Universality census. For each solution word, take the centered integer representative
     and ask whether S_i is identically zero as a Laurent polynomial. A word that is
     identically zero vanishes at every root of unity, so downward closure is trivial for
     it. The words that are not identically zero are the genuinely k-dependent ones and
     are the whole content of the problem.

  C. Integer-word test. For integer words in a centered box, compute the exact set
     K(w) = {k > 1 : Phi_k divides S_i(w)} and test whether it is closed under divisors.
     This tests downward closure directly on integers rather than on residues.

  D. Soundness of the length-5 family list at every modulus, by exhibiting a Laurent
     identity at the canonical integer representatives, with the free parameter ranging
     over an interval of integers.
"""

from __future__ import annotations

import sys
from itertools import product

# ---------------------------------------------------------------------------
# dense integer polynomials, coefficient lists low degree first
# ---------------------------------------------------------------------------


def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(n)])


def psub(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)
                 for i in range(n)])


def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        if u:
            for j, v in enumerate(b):
                if v:
                    out[i + j] += u * v
    return trim(out)


def pdivmod_monic(a, m):
    """Exact division with remainder by a monic integer polynomial m."""
    a = a[:]
    q = [0] * max(0, len(a) - len(m) + 1)
    for i in range(len(a) - len(m), -1, -1):
        c = a[i + len(m) - 1]
        if c:
            q[i] = c
            for j, v in enumerate(m):
                a[i + j] -= c * v
    return trim(q), trim(a)


_PHI = {}


def phi(k):
    """Phi_k built by exact division of x^k - 1 by the product of the lower Phi_d."""
    if k in _PHI:
        return _PHI[k]
    num = [-1] + [0] * (k - 1) + [1]
    den = [1]
    for d in range(1, k):
        if k % d == 0:
            den = pmul(den, phi(d))
    q, r = pdivmod_monic(num, den)
    assert r == [], f"Phi_{k} did not divide exactly"
    _PHI[k] = q
    return q


# ---------------------------------------------------------------------------
# the ring Z[x]/Phi_k, used for the residue sweeps
# ---------------------------------------------------------------------------


class Ring:
    def __init__(self, k):
        self.k = k
        self.m = phi(k)
        self.d = len(self.m) - 1
        # x^e reduced, for e = 0 .. 2d
        tab, cur = [], [1]
        for _ in range(2 * self.d + 1):
            tab.append(cur[:] + [0] * (self.d - len(cur)))
            cur = pdivmod_monic([0] + cur, self.m)[1]
        self.tab = tab
        # x^a and [a]_q for a = 0 .. k-1
        self.mono, cur = [], [1]
        for _ in range(k):
            self.mono.append(self.fit(cur))
            cur = pdivmod_monic([0] + cur, self.m)[1]
        self.brk, acc = [], self.zero()
        for a in range(k):
            self.brk.append(acc[:])
            acc = [u + v for u, v in zip(acc, self.mono[a])]

    def fit(self, v):
        return list(v) + [0] * (self.d - len(v))

    def zero(self):
        return [0] * self.d

    def one(self):
        v = self.zero()
        v[0] = 1
        return v

    def mul(self, a, b):
        d = self.d
        conv = [0] * (2 * d - 1)
        for i, u in enumerate(a):
            if u:
                for j, v in enumerate(b):
                    if v:
                        conv[i + j] += u * v
        out = conv[:d] + [0] * max(0, d - len(conv))
        for e in range(d, 2 * d - 1):
            c = conv[e]
            if c:
                t = self.tab[e]
                for i in range(d):
                    out[i] += c * t[i]
        return out


def locus(k, length):
    """V_length(k), by depth first search sharing prefixes of the recurrence."""
    R = Ring(k)
    out = []
    n = length - 1                       # number of letters c_2 .. c_length

    def go(depth, prev, cur, cprev, word):
        if depth == n:
            if not any(cur):
                out.append(tuple(word))
            return
        for c in range(k):
            sub = R.zero() if cprev is None else R.mul(R.mono[(cprev - 1) % k], prev)
            nxt = [u - v for u, v in zip(R.mul(R.brk[c], cur), sub)]
            word.append(c)
            go(depth + 1, cur, nxt, c, word)
            word.pop()

    go(0, R.zero(), R.one(), None, [])
    return out


# ---------------------------------------------------------------------------
# Laurent polynomials over Z, stored as (offset, coefficient list)
# ---------------------------------------------------------------------------


class Lau:
    __slots__ = ("o", "c")

    def __init__(self, o, c):
        c = trim(list(c))
        if not c:
            o = 0
        else:
            z = 0
            while c[z] == 0:
                z += 1
            o, c = o + z, c[z:]
        self.o, self.c = o, c

    @staticmethod
    def zero():
        return Lau(0, [])

    @staticmethod
    def one():
        return Lau(0, [1])

    @staticmethod
    def mono(e):
        return Lau(e, [1])

    @staticmethod
    def bracket(a):
        """[a]_q, exactly, for any integer a."""
        if a == 0:
            return Lau.zero()
        if a > 0:
            return Lau(0, [1] * a)
        return Lau(a, [-1] * (-a))       # -q^a (1 + ... + q^{-a-1})

    def is_zero(self):
        return not self.c

    def __add__(self, other):
        o = min(self.o, other.o)
        n = max(self.o + len(self.c), other.o + len(other.c)) - o
        c = [0] * n
        for i, v in enumerate(self.c):
            c[self.o - o + i] += v
        for i, v in enumerate(other.c):
            c[other.o - o + i] += v
        return Lau(o, c)

    def __sub__(self, other):
        return self + Lau(other.o, [-v for v in other.c])

    def __mul__(self, other):
        return Lau(self.o + other.o, pmul(self.c, other.c))

    def divisible_by_phi(self, k):
        return pdivmod_monic(self.c, phi(k))[1] == []

    def degree(self):
        return len(self.c) - 1


def S(word):
    """S_i on the integer word (c_2, ..., c_i), exactly, as a Laurent polynomial."""
    prev, cur, cprev = Lau.zero(), Lau.one(), None
    for c in word:
        sub = Lau.zero() if cprev is None else Lau.mono(cprev - 1) * prev
        prev, cur, cprev = cur, Lau.bracket(c) * cur - sub, c
    return cur


def centered(r, k):
    return r - k if r > k // 2 else r


def divisors_above_one(k):
    return [l for l in range(2, k) if k % l == 0]


# ---------------------------------------------------------------------------
# A and B
# ---------------------------------------------------------------------------


def experiment_A_B(plan):
    print("=" * 74)
    print("A. downward closure on residue loci, and B. universality census")
    print("=" * 74)
    ok = True
    for length, kmax in plan:
        loci = {k: set(map(tuple, locus(k, length))) for k in range(2, kmax + 1)}
        inst = viol = 0
        fails = []
        for k in range(2, kmax + 1):
            for l in divisors_above_one(k):
                for w in loci[k]:
                    inst += 1
                    if tuple(c % l for c in w) not in loci[l]:
                        viol += 1
                        if len(fails) < 5:
                            fails.append((k, l, w))
        # B: universality. A residue word is universal if SOME integer representative
        # makes S identically zero as a Laurent polynomial, since then the word lies in
        # V_length(l) for every l at once and closure is trivial for it. Representatives
        # are searched one period either side of the centered one.
        kdep = {}
        for k in range(2, kmax + 1):
            bad = []
            for w in loci[k]:
                base = [centered(c, k) for c in w]
                if not any(S(list(rep)).is_zero()
                           for rep in product(*[(b - k, b, b + k) for b in base])):
                    bad.append(tuple(base))
            if bad:
                kdep[k] = sorted(bad)
        tot = sum(len(v) for v in loci.values())
        print(f"length {length}, k = 2..{kmax}: |V| total {tot}, "
              f"{inst} closure instances, {viol} violations")
        if fails:
            ok = False
            print("   FAILURES:", fails)
        if kdep:
            print(f"   k-dependent words (centered rep not identically zero):")
            for k, v in sorted(kdep.items()):
                print(f"     k={k}: {len(v)} -> {v[:8]}{' ...' if len(v) > 8 else ''}")
        else:
            print("   every solution word is identically zero at its centered "
                  "representative")
    return ok


# ---------------------------------------------------------------------------
# C
# ---------------------------------------------------------------------------


def experiment_C(plan):
    print()
    print("=" * 74)
    print("C. downward closure on integer words in a centered box")
    print("=" * 74)
    ok = True
    for length, W in plan:
        words = nonzero = viol = inst = 0
        universal = 0
        kmax_seen = 0
        fails = []
        for w in product(range(-W, W + 1), repeat=length - 1):
            words += 1
            s = S(list(w))
            if s.is_zero():
                universal += 1
                continue
            nonzero += 1
            # Phi_k can divide s only if deg Phi_k <= deg s; deg Phi_k >= sqrt(k/2)
            bound = max(2, (s.degree() + 1) ** 2 * 2 + 2)
            K = {k for k in range(2, bound + 1)
                 if len(phi(k)) - 1 <= s.degree() and s.divisible_by_phi(k)}
            if K:
                kmax_seen = max(kmax_seen, max(K))
            for k in K:
                for l in divisors_above_one(k):
                    inst += 1
                    if l not in K:
                        viol += 1
                        if len(fails) < 5:
                            fails.append((w, k, l, sorted(K)))
        print(f"length {length}, box [-{W},{W}]: {words} words, "
              f"{universal} identically zero, {nonzero} with a genuine K(w), "
              f"largest k seen {kmax_seen}, {inst} (w,k,l) closure instances, "
              f"{viol} violations")
        if fails:
            ok = False
            print("   FAILURES:", fails)
    return ok


# ---------------------------------------------------------------------------
# D
# ---------------------------------------------------------------------------


def experiment_D(trange=range(-12, 13)):
    print()
    print("=" * 74)
    print("D. soundness of the family shapes as Laurent identities")
    print("=" * 74)
    shapes = []
    for e in (1, -1):
        shapes.append((f"L3 (e,e), e={e}", [lambda t, e=e: (e, e)], False))
    for e in (1, -1):
        shapes.append((f"L4 Z1 (0,t,0), e={e}", [lambda t: (0, t, 0)], True))
        shapes.append((f"L4 Z2 (t,0,-t)", [lambda t: (t, 0, -t)], True))
        shapes.append((f"L4 C (e,2e,e), e={e}", [lambda t, e=e: (e, 2 * e, e)], False))
        shapes.append((f"L4 C (2e,e,2e), e={e}", [lambda t, e=e: (2 * e, e, 2 * e)], False))
    for e in (1, -1):
        shapes += [
            (f"L5 F1 (0,t,e,e), e={e}", [lambda t, e=e: (0, t, e, e)], True),
            (f"L5 F2 (e,e,t,0), e={e}", [lambda t, e=e: (e, e, t, 0)], True),
            (f"L5 F3 (t,0,e-t,e), e={e}", [lambda t, e=e: (t, 0, e - t, e)], True),
            (f"L5 F4 (e,t,0,e-t), e={e}", [lambda t, e=e: (e, t, 0, e - t)], True),
            (f"L5 F5 (t,e,e,e-t), e={e}", [lambda t, e=e: (t, e, e, e - t)], True),
            (f"L5 F6 (2e,e,3e,e), e={e}", [lambda t, e=e: (2 * e, e, 3 * e, e)], False),
            (f"L5 F7 (e,3e,e,2e), e={e}", [lambda t, e=e: (e, 3 * e, e, 2 * e)], False),
            (f"L5 F8 (2e,2e,e,3e), e={e}", [lambda t, e=e: (2 * e, 2 * e, e, 3 * e)], False),
            (f"L5 F9 (3e,e,2e,2e), e={e}", [lambda t, e=e: (3 * e, e, 2 * e, 2 * e)], False),
            (f"L5 F10 (e,2e,2e,e), e={e}", [lambda t, e=e: (e, 2 * e, 2 * e, e)], False),
        ]
    ok = True
    for name, (f,), has_t in shapes:
        ts = trange if has_t else [0]
        bad = [t for t in ts if not S(list(f(t))).is_zero()]
        status = "identically zero" if not bad else f"NOT ZERO at t in {bad[:6]}"
        if bad:
            ok = False
        print(f"  {name:34s} {status}")
    return ok


def main():
    a = experiment_A_B([(3, 30), (4, 24), (5, 16), (6, 12)])
    c = experiment_C([(3, 6), (4, 5), (5, 4), (6, 3)])
    d = experiment_D()
    print()
    print("OVERALL:", "all tests pass" if (a and c and d) else "FAILURE")
    return 0 if (a and c and d) else 1


if __name__ == "__main__":
    sys.exit(main())
