"""Exact verification of every step in the route-A proof of Gap A for positive
words (reformulation G1), plus the purely-periodic corollary machinery.

All polynomial arithmetic is integer Laurent-dict arithmetic written from
scratch in this file; the single external oracle is
qreals.rational.q_rational_pair (shares no code with this file), used to
identify C with the reduced MGO denominator S_{a/c} and to test the KMRWY
congruence independently over fractions.

Run with:
    export PYTHONPATH=<path>
    python3 check_chain.py

Checks (word checks run over every word in {R,L}^n with both letters,
2 <= n <= NMAX):

  K1  reversal identity, full matrix form:
      M(W^rev) = q^mu [[conj D, conj B / q], [q conj C, conj A]];
      in particular C(W^rev) = q^(mu+1) conj C(W).
  K2  C(W) has strictly positive coefficients (so the sign in (P) is +),
      val C = 1 + t (t = trailing R-run), deg C = mu - h (h = leading R-run),
      and both extreme coefficients equal 1.
  K3  q = 1 degeneracy: C(W)(1) = C(W^rev)(1) for every word (the classical
      statement carries no information; the obstruction is q-level only).
  K4  stripping: for W = R^t U R^t (equal runs), C(W) = q^t C(U), and
      (P for W) <=> (P for U).
  K5  wedge bound: for U starting and ending with L, |U| >= 2:
      1 <= a <= c - 1 and 1 <= d' <= c - 1 at q = 1.
  K6  identification: for U starting and ending with L,
      C(U) = q * S_{a/c}(q) with S from the qreals oracle (n <= ORACLE_NMAX),
      and deg S = mu - 1, S(0) = 1.
  K7  the chain itself: C(W) = C(W^rev)  <=>  a = d'  <=>  W palindrome;
      and the minus sign C(W) = -C(W^rev) never occurs.
  K8  KMRWY Theorem 3.6, independent test over fractions r/s (not words):
      S_{r/s} self-reciprocal  <=>  r^2 = 1 (mod s), for all coprime pairs
      1 <= r < s <= SMAX, plus translates r + s, r + 2s.
  K9  a = d' => palindrome, tested directly (subsumed by K7, kept separate
      because the induction proof is a standalone lemma).
  K10 purely periodic corollary: for each quadratic irrational x > 0 with
      Galois conjugate sigma < 0 in the sample list, the Farey letter
      expansion is purely periodic; the period word P satisfies
      M(P) . x = x exactly; P is a palindrome iff x + sigma = 0; and for the
      nonzero-trace ones, C(P_q) != +- C(P^rev_q), so (P) fails and
      [x]_q + [-x]_q is not in Q(q) by thm:crit.
"""
from __future__ import annotations

import itertools
import sys
from fractions import Fraction

import sympy as sp

NMAX = 15
ORACLE_NMAX = 12
SMAX = 120

FAIL = 0


def report(name: str, ok: bool, detail: str = "") -> None:
    global FAIL
    if not ok:
        FAIL += 1
        print(f"  FAIL {name}: {detail}")


# ---------------------------------------------------------------- Laurent dicts
def padd(a, b, s=1):
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, 0) + s * c
        if out[e] == 0:
            del out[e]
    return out


def pmul(a, b):
    out = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            out[e1 + e2] = out.get(e1 + e2, 0) + c1 * c2
    return {e: c for e, c in out.items() if c != 0}


def pconj(a):  # q -> 1/q
    return {-e: c for e, c in a.items()}


def pshift(a, k):  # multiply by q^k
    return {e + k: c for e, c in a.items()}


def pat1(a):
    return sum(a.values())


def mmul(X, Y):
    (A1, B1), (C1, D1) = X
    (A2, B2), (C2, D2) = Y
    return (
        (padd(pmul(A1, A2), pmul(B1, C2)), padd(pmul(A1, B2), pmul(B1, D2))),
        (padd(pmul(C1, A2), pmul(D1, C2)), padd(pmul(C1, B2), pmul(D1, D2))),
    )


ONE = {0: 1}
Q = {1: 1}
RQ = ((Q, ONE), ({}, ONE))          # [[q, 1], [0, 1]]
LQ = ((Q, {}), (Q, ONE))            # [[q, 0], [q, 1]]
LETTER = {"R": RQ, "L": LQ}


def word_matrix(w: str):
    M = ((ONE, {}), ({}, ONE))
    for ch in w:
        M = mmul(M, LETTER[ch])
    return M


def runs(w: str):
    """leading R-run, trailing R-run."""
    h = len(w) - len(w.lstrip("R"))
    t = len(w) - len(w.rstrip("R"))
    return h, t


# ------------------------------------------------------------------ the oracle
sys.path.insert(0, "<path>")
from qreals.rational import q_rational_pair  # noqa: E402


def s_poly_dict(p: int, s: int):
    _, S = q_rational_pair(p, s)
    return {e[0]: int(c) for e, c in S.terms()}


def selfreciprocal(d):
    if not d:
        return True
    lo, hi = min(d), max(d)
    return all(d.get(lo + i, 0) == d.get(hi - i, 0) for i in range(hi - lo + 1))


# ------------------------------------------------------------------ word scans
def word_scan():
    counts = {"words": 0, "pal": 0}
    for n in range(2, NMAX + 1):
        for bits in itertools.product("RL", repeat=n):
            w = "".join(bits)
            if "R" not in w or "L" not in w:
                continue
            counts["words"] += 1
            mu = n
            M = word_matrix(w)
            (A, B), (C, D) = M
            wrev = w[::-1]
            Mrev = word_matrix(wrev)
            (Ar, Br), (Cr, Dr) = Mrev

            # K1 full reversal identity
            ok = (
                Ar == pshift(pconj(D), mu)
                and Br == pshift(pconj(B), mu - 1)
                and Cr == pshift(pconj(C), mu + 1)
                and Dr == pshift(pconj(A), mu)
            )
            report("K1", ok, w)

            # K2 positivity, val, deg, extreme coefficients
            h, t = runs(w)
            ok = all(c > 0 for c in C.values())
            report("K2.pos", ok, w)
            ok = min(C) == t + 1 and max(C) == mu - h
            report("K2.valdeg", ok, w)
            ok = C[t + 1] == 1 and C[mu - h] == 1
            report("K2.extreme", ok, w)

            # K3 q = 1 degeneracy
            report("K3", pat1(C) == pat1(Cr), w)

            # K4 stripping when h == t and an L exists
            if h == t and h > 0:
                u = w[h: n - t]
                Cu = word_matrix(u)[1][0]
                report("K4", C == pshift(Cu, t), w)

            a, dp = pat1(A), pat1(D)
            c = pat1(C)
            pal = w == wrev

            # K5, K6 for words starting and ending with L
            if w[0] == "L" and w[-1] == "L":
                report("K5", 1 <= a <= c - 1 and 1 <= dp <= c - 1, w)
                if n <= ORACLE_NMAX:
                    S = s_poly_dict(a, c)
                    report(
                        "K6",
                        C == pshift(S, 1)
                        and max(S) == mu - 1
                        and S.get(0, 0) == 1,
                        w,
                    )

            # K7 the chain
            eq = C == Cr
            neg = C == {e: -cc for e, cc in Cr.items()}
            report("K7.sign", not neg, w)
            report("K7.eq_iff_ad", eq == (a == dp), w)
            report("K7.eq_iff_pal", eq == pal, w)

            # K9 a = d' => palindrome
            if a == dp:
                report("K9", pal, w)
            if pal:
                counts["pal"] += 1
    return counts


# ------------------------------------------------------- KMRWY fraction check
def kmrwy_scan():
    n_checked = 0
    for s in range(2, SMAX + 1):
        for r in range(1, s):
            if sp.gcd(r, s) != 1:
                continue
            base = selfreciprocal(s_poly_dict(r, s))
            cong = (r * r) % s == 1
            report("K8", base == cong, f"{r}/{s}")
            n_checked += 1
            # translates share S and the congruence class
            for k in (1, 2):
                report(
                    "K8.translate",
                    selfreciprocal(s_poly_dict(r + k * s, s)) == cong,
                    f"{r + k * s}/{s}",
                )
    return n_checked


# --------------------------------------------- purely periodic corollary (K10)
def farey_period(x_expr, cap=400):
    """Return the letter word of one full period of the Farey expansion of
    x_expr (exact sympy quadratic irrational with x > 0 > conjugate), by
    iterating until the exact value returns to the start."""
    x0 = sp.radsimp(sp.nsimplify(x_expr))
    x = x0
    word = ""
    for _ in range(cap):
        if float(x) > 1:
            word += "R"
            x = sp.radsimp(x - 1)
        else:
            word += "L"
            x = sp.radsimp(x / (1 - x))
        x = sp.simplify(x)
        if word and sp.simplify(x - x0) == 0:
            return word
    raise RuntimeError("no period found within cap")


def mobius_fixes(w: str, x) -> bool:
    M = sp.eye(2)
    R1 = sp.Matrix([[1, 1], [0, 1]])
    L1 = sp.Matrix([[1, 0], [1, 1]])
    for ch in w:
        M = M * (R1 if ch == "R" else L1)
    a, b, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    return sp.simplify((a * x + b) / (c * x + d) - x) == 0


def periodic_corollary():
    samples = [
        # (label, x, trace zero?)
        ("(1+sqrt5)/2", (1 + sp.sqrt(5)) / 2, False),
        ("1+sqrt2", 1 + sp.sqrt(2), False),
        ("(3+sqrt13)/2", (3 + sp.sqrt(13)) / 2, False),
        ("(1+sqrt2)/2", (1 + sp.sqrt(2)) / 2, False),
        ("(1+sqrt3)/2", (1 + sp.sqrt(3)) / 2, False),
        ("(2+sqrt7)/3", (2 + sp.sqrt(7)) / 3, False),
        ("(1+sqrt13)/3", (1 + sp.sqrt(13)) / 3, False),
        ("sqrt2", sp.sqrt(2), True),
        ("sqrt3", sp.sqrt(3), True),
        ("sqrt(3)/2", sp.sqrt(3) / 2, True),
        ("sqrt(2)/2", sp.sqrt(2) / 2, True),
    ]
    rows = []
    for label, x, tz in samples:
        # Galois conjugate via the minimal polynomial.
        poly = sp.minimal_polynomial(x, sp.Symbol("X"))
        roots = sp.solve(poly, sp.Symbol("X"))
        conj = [r for r in roots if sp.simplify(r - x) != 0][0]
        assert float(x) > 0 and float(conj) < 0, label
        P = farey_period(x)
        fixes = mobius_fixes(P, x)
        pal = P == P[::-1]
        trace_zero = sp.simplify(x + conj) == 0
        Cw = word_matrix(P)[1][0]
        Cr = word_matrix(P[::-1])[1][0]
        p_holds = Cw == Cr or Cw == {e: -c for e, c in Cr.items()}
        ok = fixes and (pal == trace_zero) and (p_holds == trace_zero) and (tz == trace_zero)
        report("K10", ok, f"{label} word={P}")
        rows.append((label, P, pal, p_holds))
    return rows


def main():
    print(f"word scan, lengths 2..{NMAX} (oracle to {ORACLE_NMAX}) ...")
    counts = word_scan()
    print(f"  {counts['words']} words with both letters, "
          f"{counts['pal']} palindromes among them")
    print(f"KMRWY fraction scan, s <= {SMAX} ...")
    n = kmrwy_scan()
    print(f"  {n} reduced fractions checked (plus 2 translates each)")
    print("purely periodic corollary samples ...")
    rows = periodic_corollary()
    for label, P, pal, ph in rows:
        print(f"  {label:>14}  period={P}  palindrome={pal}  (P)holds={ph}")
    print(f"TOTAL FAILURES: {FAIL}")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
