"""Convert abstentions of the falsify form scan into data, time-boxed.

The falsify run (gap_a_search.py --mode form --amax 60 --bmax 60 --cmax 60)
skipped 226,180 primitive forms because no fundamental solution (t, u) of
t^2 - Delta u^2 = 4 was found with u < 20000 by brute force. Those forms were
never tested against criterion (P).

This script removes the u cap exactly instead of raising it. Two facts make
that possible:

  1. The fundamental solution of the +-1 Pell equation x^2 - Delta y^2 = +-1
     is computable exactly from the continued fraction of sqrt(Delta), with
     no search cap. Doubling (and squaring first when the norm is -1) gives a
     solution (t, u) = (2x, 2y) of t^2 - Delta u^2 = 4.
  2. Criterion (P) is an invariant of the fixed quadratic irrational: it is
     unchanged when the automorph M is replaced by M^k (characterization.tex
     rem:invariance, proved). So testing the automorph built from ANY
     solution (t, u) decides (P) for the form; fundamentality is not needed
     for the (P) verdict, only for classifying which forms the original scan
     abstained on. Minimal u is computed exactly here for that
     classification.

The only remaining reason to skip a form is genuine cost: the automorph
entries grow like the Pell unit, and the R/L word length (= the determinant
exponent mu) grows with them. A word-length guard and a global time budget
bound the run; skipped-for-cost forms are counted and reported as still
untested. This converts abstentions into data exactly as far as the budget
allows and misstates nothing.

Box: A0 in 1..60, B0 in -60..60 with B0 != 0, C0 in -60..60, primitive,
positive nonsquare discriminant (the falsify box). Note the falsify run only
reached 341,412 of these forms before its 500 s budget expired; this script
classifies the WHOLE box, so its abstention count is >= 226,180.
"""
from __future__ import annotations

import sys
import time
from math import gcd, isqrt

FALSIFY = ("<path>"
           "2026-07-21-next-steps/problems/T3-quadratic-conjecture/attempts/falsify")
PAPERGAPS = ("<path>"
             "2026-07-11-paper-gaps/code")
for p in (FALSIFY, PAPERGAPS):
    if p not in sys.path:
        sys.path.append(p)

from fast_word import sl2_word_fast  # noqa: E402
from fastlam import rho_fast, p_add, p_mul  # noqa: E402

AMAX = BMAX = CMAX = 60
OLD_UCAP = 20000          # the original scan tested u in range(1, 20000)
WORD_LEN_GUARD = 4000     # same guard as the falsify run
TIME_BUDGET_S = 420.0


# ------------------------------------------------------------------ exact Pell
def sqrt_cf_convergents(D, periods=3):
    """Yield convergents (p, q) of sqrt(D) for `periods` full periods."""
    a0 = isqrt(D)
    m, d, a = 0, 1, a0
    p_prev, q_prev = 1, 0
    p_cur, q_cur = a0, 1
    yield p_cur, q_cur
    count = 0
    while count < periods:
        m = d * a - m
        d = (D - m * m) // d
        a = (a0 + m) // d
        p_cur, p_prev = a * p_cur + p_prev, p_cur
        q_cur, q_prev = a * q_cur + q_prev, q_cur
        yield p_cur, q_cur
        if d == 1:
            count += 1


def min_u4(D):
    """Exact minimal u > 0 with t^2 - D u^2 = 4 solvable, via convergents.

    Every solution of t^2 - D u^2 = 4 has t/u equal, after reduction, to a
    convergent of sqrt(D) of norm 4 (t, u odd) or norm 1 (t, u even), for
    D > 16; three periods of convergents contain the fundamental one. For
    D <= 16 the direct brute force below is used instead.
    """
    if D <= 16:
        for u in range(1, 2000):
            t2 = 4 + D * u * u
            t = isqrt(t2)
            if t * t == t2:
                return t, u
        raise RuntimeError(D)
    best = None
    for p, q in sqrt_cf_convergents(D, periods=3):
        n = p * p - D * q * q
        cand = None
        if n == 4:
            cand = (p, q)
        elif n == 1:
            cand = (2 * p, 2 * q)
        if cand and (best is None or cand[1] < best[1]):
            best = cand
    if best is None:
        # norm -1 or -4 only within the scanned range: square the fundamental
        # +-1/-4 element to reach norm +1/+16
        for p, q in sqrt_cf_convergents(D, periods=3):
            n = p * p - D * q * q
            if n == -1:
                x, y = p * p + D * q * q, 2 * p * q
                cand = (2 * x, 2 * y)
            elif n == -4:
                cand = ((p * p + D * q * q) // 2, p * q)
            else:
                continue
            if best is None or cand[1] < best[1]:
                best = cand
    return best


def det_exponent(A, B, C, D):
    det = p_add(p_mul(A, D), p_mul(B, C), scale=-1)
    if len(det) != 1:
        return None
    ((e, c),) = det.items()
    return e if c in (1, -1) else None


def crit_P(C, m):
    if not C:
        return False
    shifted = {m + 1 - e: c for e, c in C.items()}
    return shifted == C or shifted == {e: -c for e, c in C.items()}


def test_form(A0, B0, C0, t, u):
    """(P) verdict for the automorph of the form built from solution (t, u).

    Returns (holds, mu, wordlen) or ('skip', wordlen, None) when the word
    exceeds the guard.
    """
    a = (t - B0 * u) // 2
    b = -C0 * u
    c = A0 * u
    d = (t + B0 * u) // 2
    assert a * d - b * c == 1, (A0, B0, C0, t, u)
    word = sl2_word_fast(((a, b), (c, d)))
    wlen = sum(abs(tk[1]) if tk[0] == "R" else 1 for tk in word)
    if wlen > WORD_LEN_GUARD:
        return "skip", wlen, None
    Aq, Bq, Cq, Dq = rho_fast(word)
    m = det_exponent(Aq, Bq, Cq, Dq)
    assert m is not None
    return crit_P(Cq, m), m, wlen


def run():
    t0 = time.time()
    # 1. classify the whole box by discriminant
    deltas = {}
    for A0 in range(1, AMAX + 1):
        for B0 in range(-BMAX, BMAX + 1):
            if B0 == 0:
                continue
            for C0 in range(-CMAX, CMAX + 1):
                Delta = B0 * B0 - 4 * A0 * C0
                if Delta <= 0:
                    continue
                r = isqrt(Delta)
                if r * r == Delta:
                    continue
                if gcd(gcd(A0, abs(B0)), abs(C0)) != 1:
                    continue
                deltas.setdefault(Delta, []).append((A0, B0, C0))
    n_forms = sum(len(v) for v in deltas.values())
    print(f"box: {n_forms} primitive nonsquare-positive-discriminant forms, "
          f"{len(deltas)} distinct discriminants, {time.time()-t0:.1f}s", flush=True)

    # 2. exact minimal u for every discriminant
    fund = {}
    for D in deltas:
        fund[D] = min_u4(D)
    # sanity: agree with the old brute force on a sample below the cap
    import random
    rng = random.Random(1)
    small = [D for D in deltas if fund[D][1] < 1000]
    for D in rng.sample(small, min(200, len(small))):
        t_, u_ = fund[D]
        assert t_ * t_ - D * u_ * u_ == 4
        found = None
        for u in range(1, u_ + 1):
            t2 = 4 + D * u * u
            tt = isqrt(t2)
            if tt * tt == t2:
                found = (tt, u)
                break
        assert found == (t_, u_), (D, found, (t_, u_))
    abstained = {D: v for D, v in deltas.items() if fund[D][1] >= OLD_UCAP}
    n_abst = sum(len(v) for v in abstained.values())
    print(f"abstained under the old cap u < {OLD_UCAP}: {n_abst} forms over "
          f"{len(abstained)} discriminants "
          f"(original partial-coverage count was 226,180), "
          f"{time.time()-t0:.1f}s", flush=True)

    # 3. test abstained forms, cheapest discriminants first, inside the budget
    order = sorted(abstained, key=lambda D: fund[D][1])
    tested = skipped_cost = 0
    violations = []
    out_of_time = 0
    for D in order:
        t_, u_ = fund[D]
        for (A0, B0, C0) in abstained[D]:
            if time.time() - t0 > TIME_BUDGET_S:
                out_of_time += 1
                continue
            res, x, _ = test_form(A0, B0, C0, t_, u_)
            if res == "skip":
                skipped_cost += 1
                continue
            tested += 1
            if res:
                violations.append((A0, B0, C0, D))
                print(f"  GAP A VIOLATION: form ({A0},{B0},{C0}) Delta={D}",
                      flush=True)
            if tested % 200 == 0:
                print(f"  ... tested {tested}, skipped(word>{WORD_LEN_GUARD})"
                      f"={skipped_cost}, elapsed {time.time()-t0:.1f}s",
                      flush=True)
    print(f"\nRESULT: abstained forms in full box: {n_abst}")
    print(f"  tested now:            {tested}")
    print(f"  violations of Gap A:   {len(violations)}")
    print(f"  skipped (word length): {skipped_cost}")
    print(f"  not reached (budget):  {out_of_time}")
    print(f"  elapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    run()
