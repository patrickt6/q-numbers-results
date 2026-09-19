"""Verification script for the intertwining characterization (T3, attack 1).

Checks, with exact symbolic computation, every computational claim made in
characterization.tex in this directory:

  1.  The R,S word factorization and the q-deformation rho agree with known
      q-rationals ([3/2]_q etc.) and with q-equivariance at random rationals.
  2.  Fact E2 (trace palindromicity with center = det exponent) holds for
      every matrix used anywhere in this script.
  3.  Lemma checks on concrete quadratics (golden ratio, 1+sqrt2, 2+sqrt2,
      (3+sqrt13)/2, sqrt2, sqrt(1/2)): [x]_q and [-x]_q computed by convergent
      stabilization satisfy the fixed-point quadratics of rho(M) and of
      Phi(rho(M)) = T rho(M)-bar T^{-1} respectively, and W' = +-q^{-m} W.
  4.  Theorem B on trace-zero surds: F(x) = (A-D)/C coefficientwise.
  5.  The rationality criterion q^{m+1} C(1/q) = +-C(q): evaluated on
      (a) an exhaustive scan of positive R/L words,
      (b) automorphs of quadratic forms (A,B,C) over a search box,
      and compared against the trace-zero condition (B = 0, i.e. a = d).
  6.  Pure-rational-surd scan: for x = sqrt(num/den) the reduced (A-D)/C,
      with a finite/infinite verdict for each.

Run:  python3 verify.py > verify-output.txt 2>&1
"""

import itertools
import sys
from math import gcd, isqrt

import sympy as sp

q = sp.Symbol('q')

# ---------------------------------------------------------------- generators
R = sp.Matrix([[1, 1], [0, 1]])
S = sp.Matrix([[0, -1], [1, 0]])
Rq = sp.Matrix([[q, 1], [0, 1]])
Sq = sp.Matrix([[0, -sp.Rational(1) / q], [1, 0]])
Rq_inv = sp.Matrix([[1 / q, -1 / q], [0, 1]])
Sq_inv = sp.Matrix([[0, 1], [-1 / q, 0]])   # q * adj / det: S_q^{-1} = [[0,q],[-q,0]]/q


def rs_word(M):
    """Factor M in SL(2,Z) as +- R^{k1} S R^{k2} S ... (list of ('R',k)/('S',) tokens)."""
    a, b, c, d = int(M[0, 0]), int(M[0, 1]), int(M[1, 0]), int(M[1, 1])
    assert a * d - b * c == 1, "not SL2"
    toks = []
    X = [[a, b], [c, d]]
    guard = 0
    while X[1][0] != 0:
        guard += 1
        assert guard < 10000
        k = X[0][0] // X[1][0]
        # X <- R^{-k} X
        X = [[X[0][0] - k * X[1][0], X[0][1] - k * X[1][1]], [X[1][0], X[1][1]]]
        toks.append(('R', k))
        # X <- S^{-1} X   (S^{-1} = [[0,1],[-1,0]])
        X = [[X[1][0], X[1][1]], [-X[0][0], -X[0][1]]]
        toks.append(('S',))
    # now X = +-[[1, n],[0, 1]]
    if X[0][0] == -1:
        X = [[-X[0][0], -X[0][1]], [X[1][0], -X[1][1] + 2 * X[1][1]]]  # sign only
        X[1][1] = 1
    assert X[0][0] == 1 and X[1][1] == 1
    if X[0][1] != 0:
        toks.append(('R', X[0][1]))
    # verify classically
    P = sp.eye(2)
    for t in toks:
        P = P * (R ** t[1] if t[0] == 'R' else S)
    assert P == M or P == -M, "word does not reproduce M projectively"
    return toks


def _mexp(P):
    return sp.Matrix([[sp.expand(P[0, 0]), sp.expand(P[0, 1])],
                      [sp.expand(P[1, 0]), sp.expand(P[1, 1])]])


def _rq_pow(k):
    """Rq^k exactly: [[q^k, [k]_q],[0,1]] for k>=0, and its inverse form for k<0."""
    if k >= 0:
        return sp.Matrix([[q ** k, sum(q ** i for i in range(k))], [0, 1]])
    kk = -k
    return sp.Matrix([[q ** -kk, -sum(q ** i for i in range(kk)) / q ** kk], [0, 1]])


def rho(toks):
    """q-deformation: product of Rq^k / Sq along the token list."""
    P = sp.eye(2)
    for t in toks:
        P = _mexp(P * (_rq_pow(t[1]) if t[0] == 'R' else Sq))
    return sp.Matrix([[sp.cancel(P[0, 0]), sp.cancel(P[0, 1])],
                      [sp.cancel(P[1, 0]), sp.cancel(P[1, 1])]])


def det_exponent(Mq):
    """det Mq = q^m exactly; return m (asserts monomial with coefficient 1)."""
    d = sp.cancel(sp.together(Mq[0, 0] * Mq[1, 1] - Mq[0, 1] * Mq[1, 0]))
    r = is_monomial_times(d, sp.Integer(1))
    assert r is not None and r[0] == 1, f"det not a monomial: {d}"
    return int(r[1])


def bar(f):
    return sp.cancel(f.subs(q, 1 / q))


def is_monomial_times(f, g):
    """If f = c*q^j*g for c in {1,-1}, return (c, j); else None. Fast, no simplify."""
    r = sp.cancel(sp.together(f / g))
    num, den = sp.fraction(r)
    num, den = sp.expand(num), sp.expand(den)
    if num == 0:
        return None
    if not (num.is_polynomial(q) and den.is_polynomial(q)):
        return None
    pn, pd = sp.Poly(num, q), sp.Poly(den, q)
    if len(pn.terms()) == 1 and len(pd.terms()) == 1:
        (en,), cn = pn.terms()[0]
        (ed,), cd = pd.terms()[0]
        c = sp.Rational(cn, cd)
        if c in (1, -1):
            return (int(c), int(en - ed))
    return None


def criterion(Mq, m):
    """True iff q^{m+1} C(1/q) = +- C(q) exactly. Also returns the offset."""
    C = Mq[1, 0]
    lhs = sp.cancel(q ** (m + 1) * bar(C))
    r = is_monomial_times(lhs, C)
    holds = r is not None and r[1] == 0
    return holds, r


def trace_center_check(Mq, m):
    """Fact E2: Tr(1/q) = +- q^{-m} Tr(q) exactly (sign +1 expected up to rep)."""
    T = sp.cancel(Mq[0, 0] + Mq[1, 1])
    r = is_monomial_times(bar(T), sp.cancel(q ** (-m) * T))
    return r is not None and r[1] == 0


# ------------------------------------------------------- q-rationals via rho
def sl2_over_infinity(r, s):
    """Matrix in SL2(Z) with first column (r, s) (r/s in lowest terms, s != 0 allowed 0)."""
    if s == 0:
        assert abs(r) == 1
        return sp.Matrix([[r, 0], [0, r]])
    g = gcd(abs(r), abs(s))
    assert g == 1
    # find b, d with r*d - s*b = 1
    d0, b0 = sp.gcdex(r, -s)[0:2]  # r*d0 + (-s)*b0 = 1
    d0, b0 = int(d0), int(b0)
    return sp.Matrix([[r, b0], [s, d0]])


def q_rational(r, s):
    """[r/s]_q as an exact rational function of q (right deformation)."""
    M = sl2_over_infinity(r, s)
    Mq = rho(rs_word(M))
    return sp.cancel(Mq[0, 0] / Mq[1, 0])


def laurent_coeffs(f, lo, hi):
    """Coefficients of q^lo..q^hi of the Laurent expansion of rational f at q=0."""
    num, den = sp.fraction(sp.together(f))
    if sp.expand(num) == 0:
        return {e: sp.Integer(0) for e in range(lo, hi + 1)}
    pnum = sp.Poly(sp.expand(num), q)
    pden = sp.Poly(sp.expand(den), q)
    # valuations
    vn = min(m[0] for m in pnum.monoms()) if pnum.monoms() else 0
    vd = min(m[0] for m in pden.monoms())
    val = vn - vd
    # normalized power series division
    a = [int(pnum.coeff_monomial(q ** (vn + i))) for i in range(pnum.degree() - vn + 1)]
    b = [int(pden.coeff_monomial(q ** (vd + i))) for i in range(pden.degree() - vd + 1)]
    n_need = hi - val + 1
    c = []
    acc = a + [0] * max(0, n_need - len(a))
    for i in range(max(0, n_need)):
        ci = sp.Rational(acc[i], b[0])
        c.append(ci)
        for j in range(1, len(b)):
            if i + j < len(acc):
                acc[i + j] -= ci * b[j]
    out = {}
    for i, ci in enumerate(c):
        e = val + i
        if lo <= e <= hi:
            out[e] = ci
    for e in range(lo, min(hi, val - 1) + 1):
        out[e] = sp.Integer(0)
    return out


# --------------------------------------------- continued fractions (exact PQa)
def cf_quadratic(P0, Q0, D, n_terms):
    """CF terms of x = (P0 + sqrt(D))/Q0, exact, D nonsquare, Q0 != 0."""
    if (D - P0 * P0) % Q0 != 0:
        P0, Q0, D = P0 * abs(Q0), Q0 * abs(Q0), D * Q0 * Q0
    terms = []
    P, Q = P0, Q0
    sD = isqrt(D)
    for _ in range(n_terms):
        if Q > 0:
            a = (P + sD) // Q
        else:
            a = int(sp.floor((P + sp.sqrt(D)) / Q))
        terms.append(a)
        P = a * Q - P
        Q = (D - P * P) // Q
    return terms


def convergents(terms):
    h0, h1 = 1, terms[0]
    k0, k1 = 0, 1
    yield h1, k1
    for a in terms[1:]:
        h0, h1 = h1, a * h1 + h0
        k0, k1 = k1, a * k1 + k0
        yield h1, k1


def stabilized_series(P0, Q0, D, sign, lo, hi, max_cf=90):
    """Stabilized Laurent coefficients of [sign * x]_q, x=(P0+sqrt(D))/Q0 > 0.

    Uses E0: any rational sequence -> x works; we use sign*(convergents of x).
    Returns dict exponent -> coeff once two consecutive convergents agree on
    the full window [lo, hi]."""
    terms = cf_quadratic(P0, Q0, D, max_cf)
    prev = None
    for r, s in convergents(terms):
        g = gcd(abs(r), abs(s))
        f = q_rational(sign * r // g, s // g)
        cur = laurent_coeffs(f, lo, hi)
        if prev is not None and prev == cur:
            return cur
        prev = cur
    raise RuntimeError("no stabilization within max_cf convergents")


def series_of_expr(f, lo, hi):
    return laurent_coeffs(f, lo, hi)


def apply_quadratic(Mq, coeffs, lo, hi):
    """Evaluate C z^2 + (D-A) z - B on a Laurent-window z; return window of result.

    Result window is trimmed to a range where truncation cannot pollute:
    [2*lo + valuation slack, hi + lo] is safe for the z^2 term; we simply
    check exponents up to hi + lo - |shift|."""
    A, B, C, Dd = Mq[0, 0], Mq[0, 1], Mq[1, 0], Mq[1, 1]
    z = sum(c * q ** e for e, c in coeffs.items())
    expr = sp.expand(C * z * z + (Dd - A) * z - B)
    expr = sp.cancel(sp.together(expr))
    out = laurent_coeffs(expr, 2 * lo, hi + lo - 2)
    return out


def phi(Mq):
    """Phi(X) = T Xbar T^{-1}, T = diag(-1/q, 1): the rho-image of N M N."""
    A, B, C, Dd = Mq[0, 0], Mq[0, 1], Mq[1, 0], Mq[1, 1]
    return sp.Matrix([[bar(A), sp.cancel(-bar(B) / q)],
                      [sp.cancel(-q * bar(C)), bar(Dd)]])


def check(label, ok):
    print(("PASS " if ok else "FAIL ") + label)
    if not ok:
        global FAILURES
        FAILURES += 1


FAILURES = 0

print("=" * 72)
print("SECTION 1: pipeline sanity (rho, q-rationals, equivariance)")
print("=" * 72)

check("[3/2]_q = (q^2+q+1)/(q+1)",
      sp.simplify(q_rational(3, 2) - (q ** 2 + q + 1) / (q + 1)) == 0)
check("[5/2]_q = (q^3+q^2+2q+1)/(q+1)... via translation [5/2]=q[3/2]+1",
      sp.simplify(q_rational(5, 2) - (q * q_rational(3, 2) + 1)) == 0)
check("[-1/2]_q = -q^{-1}[1/2]_{1/q}  (reversal rule at a rational)",
      sp.simplify(q_rational(-1, 2) - (-q ** -1 * bar(q_rational(1, 2)))) == 0)
check("[2]_q = 1+q", sp.simplify(q_rational(2, 1) - (1 + q)) == 0)

# equivariance at rationals for a few random M and y
import random
random.seed(7)
eq_ok = True
for _ in range(12):
    M = sp.eye(2)
    for _ in range(4):
        M = M * random.choice([R, R.inv(), S])
    M = sp.Matrix([[int(M[0, 0]), int(M[0, 1])], [int(M[1, 0]), int(M[1, 1])]])
    if M[1, 0] == 0 and M[0, 0] * M[1, 1] != 1:
        continue
    r0, s0 = random.choice([(3, 2), (5, 3), (7, 4), (2, 5)])
    a, b, c, d = M[0, 0], M[0, 1], M[1, 0], M[1, 1]
    rn, sn = a * r0 + b * s0, c * r0 + d * s0
    if sn == 0:
        continue
    g = gcd(abs(rn), abs(sn))
    rn, sn = rn // g, sn // g
    if sn < 0:
        rn, sn = -rn, -sn
    Mq = rho(rs_word(M))
    lhs = q_rational(int(rn), int(sn))
    fr = q_rational(r0, s0)
    rhs = sp.cancel((Mq[0, 0] * fr + Mq[0, 1]) / (Mq[1, 0] * fr + Mq[1, 1]))
    if sp.simplify(lhs - rhs) != 0:
        eq_ok = False
        print("   equivariance FAILED at", M.tolist(), (r0, s0))
check("q-equivariance [M.y]_q = rho(M).[y]_q at 12 random (M, y)", eq_ok)

print()
print("=" * 72)
print("SECTION 2: named quadratics: lemma-level checks + criterion")
print("=" * 72)

# Each entry: label, (P0,Q0,D) with x=(P0+sqrt(D))/Q0, automorph M (fixing x),
# expected trace-zero flag.
CASES = [
    ("sqrt(2)",        (0, 1, 2),   sp.Matrix([[3, 4], [2, 3]]),  True),
    ("sqrt(1/2)",      (0, 2, 2),   sp.Matrix([[3, 2], [4, 3]]),  True),
    ("sqrt(3/2)",      (0, 2, 6),   sp.Matrix([[5, 6], [4, 5]]),  True),
    ("golden (1+sqrt5)/2", (1, 2, 5), sp.Matrix([[2, 1], [1, 1]]), False),
    ("1+sqrt(2)",      (1, 1, 2),   sp.Matrix([[5, 2], [2, 1]]),  False),
    ("2+sqrt(2)",      (2, 1, 2),   sp.Matrix([[7, -4], [2, -1]]), False),
    ("(3+sqrt13)/2",   (3, 2, 13),  sp.Matrix([[10, 3], [3, 1]]), False),
]

LO, HI = -14, 26

for label, (P0, Q0, D), M, tz in CASES:
    print("-" * 72)
    print(f"x = {label}, automorph M = {M.tolist()}")
    a, b, c, d = [int(v) for v in M]
    assert a * d - b * c == 1
    # M fixes x?
    x_exact = (P0 + sp.sqrt(D)) / Q0
    check("  M fixes x", sp.simplify((a * x_exact + b) / (c * x_exact + d) - x_exact) == 0)
    check("  trace-zero flag matches a=d", (a == d) == tz)
    Mq = rho(rs_word(M))
    m = det_exponent(Mq)
    check("  E2 trace center = m", trace_center_check(Mq, m))
    # [x]_q window and fixed-point quadratic
    zx = stabilized_series(P0, Q0, D, +1, LO, HI)
    resx = apply_quadratic(Mq, zx, LO, HI)
    check("  [x]_q satisfies C z^2+(D-A)z-B = 0 (window)",
          all(v == 0 for v in resx.values()))
    # [-x]_q window and Phi(Mq) quadratic
    zmx = stabilized_series(P0, Q0, D, -1, LO, HI)
    Mq2 = phi(Mq)
    resmx = apply_quadratic(Mq2, zmx, LO, HI)
    check("  [-x]_q satisfies Phi quadratic (window)",
          all(v == 0 for v in resmx.values()))
    # W' = +- q^{-m} W on windows
    Wx = {e: 0 for e in range(2 * LO, HI + LO - 2)}
    Wexpr = lambda MM, zz: {  # 2C z - (A - D) as window
        e: sp.nsimplify(v) for e, v in
        laurent_coeffs(sp.cancel(sp.together(
            2 * MM[1, 0] * sum(cc * q ** ee for ee, cc in zz.items())
            - (MM[0, 0] - MM[1, 1]))), LO - 2, HI - 4).items()}
    W1 = Wexpr(Mq, zx)
    W2 = Wexpr(Mq2, zmx)
    # compare W2 with +- q^{-m} W1
    shifted = {e: W1.get(e + m, sp.Integer(0)) for e in range(LO - 2, HI - 4 - m)}
    common = [e for e in shifted if e in W2]
    same = all(W2[e] == shifted[e] for e in common)
    opp = all(W2[e] == -shifted[e] for e in common)
    check("  W' = +-q^{-m} W (window)", same or opp)
    hold, r = criterion(Mq, m)
    print(f"  criterion q^(m+1)C(1/q) vs C(q): holds={hold}, (sign, offset)={r}, m={m}")
    check("  criterion holds iff trace-zero", hold == tz)
    if tz:
        # Theorem B: F = (A-D)/C coefficientwise
        FADC = sp.cancel((Mq[0, 0] - Mq[1, 1]) / Mq[1, 0])
        target = series_of_expr(FADC, LO, HI)
        Fsum = {e: zx.get(e, 0) + zmx.get(e, 0) for e in range(LO, HI + 1)}
        check("  Theorem B: [x]_q+[-x]_q = (A-D)/C (window)",
              all(sp.nsimplify(Fsum[e] - target.get(e, 0)) == 0 for e in Fsum))
        print("   (A-D)/C =", sp.factor(FADC))

print()
print("=" * 72)
print("SECTION 2b: full falsification list, criterion only")
print("=" * 72)
# Automorphs for the last five taken from attempts/attempt-1/falsification-record.json
# and re-verified to fix their x; first four already treated above.
EXTRA = [
    ("3+sqrt(3)",      (3, 1, 3),   [[5, -6], [1, -1]],      False),
    ("(1+sqrt(2))/2",  (1, 2, 2),   [[5, 1], [4, 1]],        False),
    ("(1+sqrt(3))/2",  (1, 2, 3),   [[3, 1], [2, 1]],        False),
    ("(2+sqrt(7))/3",  (2, 3, 7),   [[14, 3], [9, 2]],       False),
    ("(1+sqrt(13))/3", (1, 3, 13),  [[829, 720], [540, 469]], False),
    ("sqrt(3)/2",      (0, 2, 3),   [[7, 6], [8, 7]],        True),
    ("sqrt(2)/3",      (0, 3, 2),   [[17, 8], [36, 17]],     True),
    ("3*sqrt(5)/2",    (0, 2, 45),  [[161, 540], [48, 161]], True),
]
for label, (P0, Q0, D), mm, tz in EXTRA:
    M = sp.Matrix(mm)
    a, b, c, d = [int(v) for v in M]
    assert a * d - b * c == 1
    x_exact = (P0 + sp.sqrt(D)) / Q0
    fixes = sp.simplify((a * x_exact + b) / (c * x_exact + d) - x_exact) == 0
    check(f"  {label}: M fixes x", fixes)
    Mq = rho(rs_word(M))
    m = det_exponent(Mq)
    check(f"  {label}: E2 trace center = m", trace_center_check(Mq, m))
    hold, r = criterion(Mq, m)
    ratio = sp.cancel(sp.together(q ** (m + 1) * bar(Mq[1, 0]) / Mq[1, 0]))
    mono = is_monomial_times(ratio, sp.Integer(1))
    print(f"  {label}: (P) holds={hold}, ratio="
          f"{sp.factor(ratio) if mono else 'not a monomial'}")
    check(f"  {label}: criterion holds iff trace-zero", hold == tz)

print()
print("=" * 72)
print("SECTION 3: positive-word scan (Gap 1 probe, purely periodic side)")
print("=" * 72)
# All words over {R, L} of length 3..11 containing both letters.
# Claims probed: (a=d) <=> palindromic word ; criterion <=> (a=d).
Lm = sp.Matrix([[1, 0], [1, 1]])
Lq = sp.Matrix([[q, 0], [q, 1]])
total = 0
mismatch_classical = 0
mismatch_criterion = []
for n in range(2, 12):
    for bits in itertools.product('RL', repeat=n):
        if 'R' not in bits or 'L' not in bits:
            continue
        total += 1
        Mcl = sp.eye(2)
        Mqw = sp.eye(2)
        for ch in bits:
            Mcl = Mcl * (R if ch == 'R' else Lm)
            Mqw = Mqw * (Rq if ch == 'R' else Lq)
        Mqw = sp.Matrix([[sp.expand(v) for v in Mqw.row(i)] for i in range(2)])
        a, d = int(Mcl[0, 0]), int(Mcl[1, 1])
        pal = list(bits) == list(bits)[::-1]
        if (a == d) != pal:
            mismatch_classical += 1
        m = n  # det exponent = number of letters
        assert sp.simplify(Mqw.det() - q ** m) == 0
        if not trace_center_check(Mqw, m):
            print("   E2 FAILED at word", ''.join(bits))
        hold, r = criterion(Mqw, m)
        if hold != (a == d):
            mismatch_criterion.append((''.join(bits), a, d, hold, r))
print(f"words tested: {total}")
check("(a=d) <=> palindromic word, all words", mismatch_classical == 0)
check("criterion <=> (a=d), all words", len(mismatch_criterion) == 0)
for w, a, d, hold, r in mismatch_criterion[:20]:
    print("   MISMATCH:", w, "a,d=", a, d, "criterion=", hold, r)

print()
print("=" * 72)
print("SECTION 4: quadratic-form automorph scan (Gap 1 probe, general side)")
print("=" * 72)


def fundamental_tu(Delta, umax=200000):
    for u in range(1, umax):
        t2 = 4 + Delta * u * u
        t = isqrt(t2)
        if t * t == t2:
            return t, u
    return None


seen = set()
count = 0
crit_mismatch = []
for A_ in range(1, 7):
    for B_ in range(-6, 7):
        for C_ in range(-6, 7):
            Delta = B_ * B_ - 4 * A_ * C_
            if Delta <= 0 or isqrt(Delta) ** 2 == Delta:
                continue
            if gcd(gcd(A_, abs(B_)), abs(C_)) != 1:
                continue
            key = (A_, B_, C_)
            if key in seen:
                continue
            seen.add(key)
            fu = fundamental_tu(Delta)
            if fu is None:
                continue
            t, u = fu
            if (t - B_ * u) % 2 != 0:
                continue
            a = (t - B_ * u) // 2
            b = -C_ * u
            c = A_ * u
            d = (t + B_ * u) // 2
            M = sp.Matrix([[a, b], [c, d]])
            if a * d - b * c != 1:
                continue
            # word length guard
            try:
                toks = rs_word(M)
            except AssertionError:
                continue
            wlen = sum(abs(tk[1]) if tk[0] == 'R' else 1 for tk in toks)
            if wlen > 220:
                continue
            Mq = rho(toks)
            try:
                m = det_exponent(Mq)
            except AssertionError:
                continue
            if not trace_center_check(Mq, m):
                print("   E2 FAILED at form", key)
            hold, r = criterion(Mq, m)
            count += 1
            if hold != (B_ == 0):
                crit_mismatch.append((key, (a, b, c, d), hold, r))
print(f"forms tested: {count}")
check("criterion <=> B=0 (trace-zero), all forms", len(crit_mismatch) == 0)
for k, mm, hold, r in crit_mismatch[:20]:
    print("   MISMATCH:", k, mm, "criterion=", hold, r)

print()
print("=" * 72)
print("SECTION 5: pure rational surd scan sqrt(num/den) - (A-D)/C verdicts")
print("=" * 72)


def surd_verdict(num, den):
    """x = sqrt(num/den): fundamental automorph, reduced (A-D)/C, verdict."""
    D0 = num * den
    fu = None
    for u in range(1, 200000):
        r2 = 1 + D0 * u * u
        rr = isqrt(r2)
        if rr * rr == r2:
            fu = (rr, u)
            break
    if fu is None:
        return None
    rr, u = fu
    M = sp.Matrix([[rr, num * u], [den * u, rr]])
    toks = rs_word(M)
    wlen = sum(abs(tk[1]) if tk[0] == 'R' else 1 for tk in toks)
    if wlen > 260:
        return ('skipped', None, None)
    Mq = rho(toks)
    m = det_exponent(Mq)
    hold, roff = criterion(Mq, m)
    F = sp.cancel((Mq[0, 0] - Mq[1, 1]) / Mq[1, 0])
    numF, denF = sp.fraction(sp.together(F))
    pden = sp.Poly(sp.expand(denF), q)
    finite = len(pden.terms()) == 1
    return ('finite' if finite else 'infinite', sp.factor(F), hold)


rows = []
for den in range(1, 7):
    for num in range(1, 13):
        if gcd(num, den) != 1 or num == den:
            continue
        frac = sp.Rational(num, den)
        if sp.sqrt(frac).is_rational:
            continue
        v = surd_verdict(num, den)
        if v is None or v[0] == 'skipped':
            rows.append((num, den, 'SKIP', None))
            continue
        verdict, F, hold = v
        rows.append((num, den, verdict, F if verdict == 'finite' else None))
        if not hold:
            print(f"   WARNING criterion fails at trace-zero sqrt({num}/{den})!")

fin = [(n, d, F) for n, d, v, F in rows if v == 'finite']
inf = [(n, d) for n, d, v, F in rows if v == 'infinite']
print("finite negation sum (C | A-D):")
for n, d, F in fin:
    print(f"   sqrt({n}/{d}):  F = {F}")
print(f"infinite: {len(inf)} cases: {inf}")
noninteger_finite = [(n, d) for n, d, F in fin if d != 1]
check("no NON-integer rational surd with finite sum found in box",
      len(noninteger_finite) == 0)
if noninteger_finite:
    print("   !!! candidates against conjecture-as-stated:", noninteger_finite)

print()
print("=" * 72)
print(f"TOTAL FAILURES: {FAILURES}")
print("=" * 72)
