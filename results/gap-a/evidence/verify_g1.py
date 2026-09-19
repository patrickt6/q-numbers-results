"""Exact verification of every lemma in the route-B Gap A proof for positive words.

Everything is pure integer Laurent-dict arithmetic ({exponent: coeff}); no
window, no series, no floating point. The script is self-contained except for
one OPTIONAL independent oracle (qreals.rational.q_rational_pair, used on
short words only) that cross-checks the identification C = q^(1+trail) S_{a/c}
against an implementation that shares no code with this file.

Checks, for every word in {R, L}^n with both letters present, 2 <= n <= NMAX:

  C1  coefficients of C are all positive, C != 0
  C2  val C = 1 + trail_R, deg C = mu - lead_R          (degree lemma)
  C3  (P) holds  <=>  C palindromic AND lead_R = trail_R (exact-center split)
  C4  C palindromic  <=>  a = d' (mod c)                 (KMRWY Thm 3.6 shadow)
  C5  (P) holds  <=>  a = d'  <=>  word is a palindrome  (Gap A, word form)
  C6  V-decomposition W = R^p V R^t: V's diagonal (p1, p2) has
      1 <= p1 <= c, 1 <= p2 <= c, and a - d' = (p1 - p2) + c (p - t);
      C palindromic <=> p1 = p2                          (corner bound lemma)
  C7  if C palindromic: a - d' = c (lead_R - trail_R), so the mismatch ratio
      r = q^(mu+1) C(1/q)/C(q) = q^{lead-trail} = q^{(a-d')/c} = q^{x+sigma(x)}
  C8  reversal identity: q^mu conj(W_q) = [[D*, q B*],[q^{-1} C*, A*]] where
      starred entries belong to the reversed word
  C9  translation law: for X' = R_q^n W_q R_q^{-n}, C' = q^{-n} C exactly and
      det X' = q^mu, so r(x + n) = q^{2n} r(x)           (sampled words, n = 1..3)
  C10 oracle: C * q^{-(1+trail)} equals the reduced MGO denominator S_{a/c}
      computed by qreals.rational.q_rational_pair          (n <= ORACLE_NMAX)
"""
from __future__ import annotations

import itertools
import sys
import time

NMAX = 16
ORACLE_NMAX = 10
REVERSAL_NMAX = 12

# ---------------------------------------------------------------------- dicts
def p_add(a, b, scale=1):
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, 0) + scale * c
        if out[e] == 0:
            del out[e]
    return out


def p_mul(a, b):
    out = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = e1 + e2
            out[e] = out.get(e, 0) + c1 * c2
    return {e: c for e, c in out.items() if c != 0}


def m_mul(X, Y):
    (A1, B1), (C1, D1) = X
    (A2, B2), (C2, D2) = Y
    return (
        (p_add(p_mul(A1, A2), p_mul(B1, C2)), p_add(p_mul(A1, B2), p_mul(B1, D2))),
        (p_add(p_mul(C1, A2), p_mul(D1, C2)), p_add(p_mul(C1, B2), p_mul(D1, D2))),
    )


RQ = (({1: 1}, {0: 1}), ({}, {0: 1}))          # [[q, 1], [0, 1]]
LQ = (({1: 1}, {}), ({1: 1}, {0: 1}))          # [[q, 0], [q, 1]]
IDQ = (({0: 1}, {}), ({}, {0: 1}))
RQ_INV = (({-1: 1}, {-1: -1}), ({}, {0: 1}))   # [[1/q, -1/q], [0, 1]]

R1 = ((1, 1), (0, 1))
L1 = ((1, 0), (1, 1))


def mat1_mul(X, Y):
    (a, b), (c, d) = X
    (e, f), (g, h) = Y
    return ((a * e + b * g, a * f + b * h), (c * e + d * g, c * f + d * h))


def word_q(word):
    X = IDQ
    for ch in word:
        X = m_mul(X, RQ if ch == "R" else LQ)
    return X


def word_1(word):
    X = ((1, 0), (0, 1))
    for ch in word:
        X = mat1_mul(X, R1 if ch == "R" else L1)
    return X


def det_exp(X):
    (A, B), (C, D) = X
    det = p_add(p_mul(A, D), p_mul(B, C), scale=-1)
    assert len(det) == 1, det
    ((e, c),) = det.items()
    assert c == 1, det
    return e


def is_palindromic(p):
    """Coefficient sequence of the Laurent dict p reads the same reversed."""
    if not p:
        return False
    lo, hi = min(p), max(p)
    return all(p.get(lo + i, 0) == p.get(hi - i, 0) for i in range(hi - lo + 1))


def crit_P(C, mu):
    """(P): q^(mu+1) C(1/q) = +- C(q)."""
    if not C:
        return False
    shifted = {mu + 1 - e: c for e, c in C.items()}
    if shifted == C:
        return True
    if shifted == {e: -c for e, c in C.items()}:
        return True
    return False


def conj(p):
    return {-e: c for e, c in p.items()}


def shift(p, k):
    return {e + k: c for e, c in p.items()}


# ---------------------------------------------------------------------- oracle
sys.path.insert(0, "<path>")
try:
    from qreals.rational import q_rational_pair

    HAVE_ORACLE = True
except Exception as exc:  # pragma: no cover
    print(f"oracle unavailable: {exc}")
    HAVE_ORACLE = False


def oracle_S(a, c):
    """Reduced MGO denominator of [a/c]_q as a plain dict, S(0) = 1."""
    _num, den = q_rational_pair(a, c)
    d = {int(e[0]) if isinstance(e, tuple) else int(e): int(v)
         for e, v in den.as_dict().items()}
    # normalise constant term to +1 (q_rational_pair normalises monic; the MGO
    # denominator has S(0) = 1 and positive coefficients so both agree; assert)
    assert d.get(0, 0) == 1, (a, c, d)
    return d


# ---------------------------------------------------------------------- main
def run():
    t0 = time.time()
    words = 0
    oracle_checked = 0
    reversal_checked = 0
    for n in range(2, NMAX + 1):
        for bits in itertools.product("RL", repeat=n):
            if "R" not in bits or "L" not in bits:
                continue
            w = "".join(bits)
            words += 1
            X = word_q(w)
            (A, B), (C, D) = X
            mu = det_exp(X)
            assert mu == n, (w, mu)
            M = word_1(w)
            (a, b), (c, d) = M
            assert a * d - b * c == 1

            lead = len(w) - len(w.lstrip("R"))
            trail = len(w) - len(w.rstrip("R"))

            # C1
            assert C and all(v > 0 for v in C.values()), (w, C)
            # C2
            assert min(C) == 1 + trail, (w, min(C), trail)
            assert max(C) == mu - lead, (w, max(C), lead)
            # C3
            P = crit_P(C, mu)
            palC = is_palindromic(C)
            assert P == (palC and lead == trail), (w, P, palC, lead, trail)
            # C4  (empirical shadow of KMRWY Theorem 3.6 on this family)
            cong = (a - d) % c == 0
            assert palC == cong, (w, palC, a, d, c)
            # C5
            is_pal_word = w == w[::-1]
            assert P == (a == d) == is_pal_word, (w, P, a, d)
            # C6
            v = w[lead: n - trail] if trail else w[lead:]
            assert v.startswith("L") and v.endswith("L"), (w, v)
            Vm = word_1(v)
            (p1, r_), (s_, p2) = Vm
            assert s_ == c, (w, s_, c)
            assert 1 <= p1 <= c and 1 <= p2 <= c, (w, p1, p2, c)
            assert a - d == (p1 - p2) + c * (lead - trail), (w, a, d, p1, p2)
            assert palC == (p1 == p2), (w, palC, p1, p2)
            # C7
            if palC:
                assert a - d == c * (lead - trail), (w, a, d, c, lead, trail)
                # r(x) = q^(mu+1) conj(C)/C = q^{lead-trail} exactly:
                assert shift(conj(C), mu + 1) == shift(C, lead - trail), w
            # C8
            if n <= REVERSAL_NMAX:
                Xr = word_q(w[::-1])
                (Ar, Br), (Cr, Dr) = Xr
                lhs = tuple(tuple(shift(conj(E), mu) for E in row) for row in X)
                rhs = ((Dr, shift(Br, 1)), (shift(Cr, -1), Ar))
                assert lhs == rhs, (w, "reversal identity")
                reversal_checked += 1
            # C10
            if HAVE_ORACLE and n <= ORACLE_NMAX:
                S = oracle_S(a, c)
                assert C == shift(S, 1 + trail), (w, C, S, trail)
                oracle_checked += 1
        print(f"  length {n}: cumulative words {words}, "
              f"elapsed {time.time() - t0:.1f}s", flush=True)

    # C9: translation law on a sample of words, n = 1..3
    import random

    rng = random.Random(7)
    sampled = 0
    for _ in range(300):
        ln = rng.randint(2, 12)
        w = "".join(rng.choice("RL") for _ in range(ln))
        if "R" not in w or "L" not in w:
            continue
        X = word_q(w)
        mu = det_exp(X)
        C = X[1][0]
        for k in range(1, 4):
            Rk = IDQ
            Rki = IDQ
            for _ in range(k):
                Rk = m_mul(Rk, RQ)
                Rki = m_mul(Rki, RQ_INV)
            Xp = m_mul(m_mul(Rk, X), Rki)
            assert det_exp(Xp) == mu, (w, k)
            assert Xp[1][0] == shift(C, -k), (w, k, "translation law")
        sampled += 1

    print(f"\nALL CHECKS PASSED")
    print(f"  words tested (C1-C7): {words}  (lengths 2..{NMAX}, exhaustive, "
          f"both letters present)")
    print(f"  reversal identity C8: {reversal_checked} words (lengths 2..{REVERSAL_NMAX})")
    print(f"  oracle identity C10:  {oracle_checked} words (lengths 2..{ORACLE_NMAX})"
          f"{'' if HAVE_ORACLE else '  [ORACLE UNAVAILABLE]'}")
    print(f"  translation law C9:   {sampled} sampled words x n in 1..3")
    print(f"  total elapsed {time.time() - t0:.1f}s")


if __name__ == "__main__":
    run()
