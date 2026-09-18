"""Numerical confirmation of the transported (split-class) theorem.

For each sample quadratic irrational x, this script computes the fundamental
automorph via the read-only T3 asset qperiod.py (period_data), its exact
q-deformation rho(M) (rho_fast word decomposition), and the mismatch ratio

    r(x) = q^(mu+1) C(1/q) / C(q),

then tests the two predictions of the split-class theorem
(floor(x) != floor(sigma), sigma the Galois conjugate):

  P1  if a^2 = 1 (mod c)  (corner congruence):  r(x) = q^(x + sigma) exactly,
      and x + sigma is an integer;
  P2  otherwise: r(x) is not plus or minus a monomial.

Trace-zero members of the split class must return r = 1 (prop:tzP control).
Non-split samples (both conjugates in one unit interval) carry no theorem;
their r is printed as data.

Run with:
    export PYTHONPATH=<path>
    python3 extended_checks.py
"""
from __future__ import annotations

import math
import sys
from fractions import Fraction

sys.path.insert(
    0,
    "<path>"
    "2026-07-21-next-steps/problems/T3-quadratic-conjecture/attempts/opus",
)
from qperiod import period_data, rho_q, _parse_quadratic_or_rational  # noqa: E402

FAIL = 0


def conj_dict(p):
    return {-e: c for e, c in p.items()}


def shift(p, k):
    return {e + k: c for e, c in p.items()}


def det_exponent(Mq):
    A, B, C, D = Mq
    det = {}
    for e1, c1 in A.items():
        for e2, c2 in D.items():
            det[e1 + e2] = det.get(e1 + e2, 0) + c1 * c2
    for e1, c1 in B.items():
        for e2, c2 in C.items():
            det[e1 + e2] = det.get(e1 + e2, 0) - c1 * c2
    det = {e: c for e, c in det.items() if c != 0}
    assert len(det) == 1 and list(det.values())[0] == 1, det
    return list(det)[0]


def ratio_as_monomial(C, mu):
    """Return ('mono', k) if q^(mu+1) conj C = + q^k C, ('negmono', k) for the
    minus sign, else ('nonmono', None)."""
    lhs = shift(conj_dict(C), mu + 1)
    k = min(lhs) - min(C)
    if max(lhs) - max(C) == k:
        if lhs == shift(C, k):
            return "mono", k
        if lhs == {e: -c for e, c in shift(C, k).items()}:
            return "negmono", k
    return "nonmono", None


SPLIT_SAMPLES = [
    # same-sign conjugates, integer between them
    "2+sqrt(2)", "3+sqrt(3)", "2+sqrt(3)", "3+sqrt(2)", "5+sqrt(7)",
    "(7+sqrt(5))/2", "(9+sqrt(21))/2", "4+sqrt(5)", "(11+sqrt(13))/3",
    # opposite-sign conjugates (positive-word class), controls
    "(1+sqrt(5))/2", "1+sqrt(2)", "(3+sqrt(13))/2", "(2+sqrt(7))/3",
    "(1+sqrt(13))/3",
    # trace-zero controls inside the split class
    "sqrt(2)", "sqrt(3)", "sqrt(2)/2",
]

NONSPLIT_SAMPLES = [
    "(5+sqrt(5))/10",      # roots of 5X^2 - 5X + 1, both in (0, 1)
    "(7+sqrt(21))/14",     # roots of 7X^2 - 7X + 1, both in (0, 1)
    "(9+sqrt(17))/16",     # roots of 8X^2 - 9X + 2, both in (0, 1)
    "(15+sqrt(29))/14",    # roots of 7X^2 - 15X + 7, both in (0, 3)? check
]


def analyse_one(label):
    global FAIL
    kind, x = _parse_quadratic_or_rational(label)
    assert kind == "quadratic", label
    pd = period_data(x)
    (a, b), (c, dpr) = pd.automorph
    Mq = rho_q(pd.automorph)
    A, B, C, D = Mq
    mu = det_exponent(Mq)
    kind, k = ratio_as_monomial(C, mu)
    # exact trace and conjugate
    trace = Fraction(a - dpr, c)
    xf = float(x.p + x.r * math.sqrt(x.D)) / x.s
    sf = float(x.p - x.r * math.sqrt(x.D)) / x.s
    split = math.floor(xf) != math.floor(sf)
    cong = (a * a - 1) % abs(c) == 0
    verdict = "?"
    if split:
        if cong:
            ok = kind == "mono" and trace.denominator == 1 and k == trace
            verdict = f"P1 {'ok' if ok else 'FAIL'}"
            if not ok:
                FAIL += 1
        else:
            ok = kind == "nonmono"
            verdict = f"P2 {'ok' if ok else 'FAIL'}"
            if not ok:
                FAIL += 1
    else:
        verdict = "no theorem (non-split), data only"
    rtxt = {"mono": f"q^{k}", "negmono": f"-q^{k}", "nonmono": "not +-monomial"}[kind]
    print(f"  {label:>16}  M={pd.automorph}  trace={trace}  split={split} "
          f"cong={cong}  r={rtxt}  {verdict}")


def main():
    print("split-class samples (theorem applies):")
    for s in SPLIT_SAMPLES:
        analyse_one(s)
    print("non-split samples (residual Gap A domain, data only):")
    for s in NONSPLIT_SAMPLES:
        analyse_one(s)
    print(f"TOTAL FAILURES: {FAIL}")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
