#!/usr/bin/env python3
r"""
T13 Lemma N structural probe (route B).

Reconstructs the q-automorph entries A, C, D (up to a global monomial unit,
which is irrelevant to divisibility and factorization) from the VALIDATED
primitives qval (gives [r/s]_q = A/C) and G_of_rs (gives F(d) = (A-D)/C),
then studies the negative-Pell squaring decomposition Lambda = Lambda_-^2 and
the surviving non-cyclotomic factor.

Exact arithmetic only (sympy over ZZ / Laurent dicts). No brute-force scan.
"""
import sys
sys.path.insert(0, "<path>")

import sympy as sp
from math import isqrt, gcd

from qpoly import qval, G_of_rs, pell_fundamental, poly_trim, poly_deg

q = sp.Symbol('q')


# ---------- Laurent / poly helpers as sympy expressions ----------
def shifted_to_expr(shift, coeffs):
    """q^shift * sum coeffs[i] q^i  as a sympy expr."""
    coeffs = list(coeffs)
    e = sp.Integer(0)
    for i, c in enumerate(coeffs):
        if c:
            e += int(c) * q**(shift + i)
    return e


def as_ratfun(shift, num, den):
    return shifted_to_expr(shift, num) / shifted_to_expr(0, den)


def poly_list_to_expr(coeffs):
    return shifted_to_expr(0, coeffs)


def reverse_poly(expr):
    """q^deg * expr(1/q) restricted to make an honest polynomial: returns the
    reciprocal polynomial (as expr) for a Laurent expr, normalized to start at q^0."""
    P = sp.Poly(sp.together(expr).as_numer_denom()[0], q)  # numerator poly
    return P


def is_monomial_times(expr):
    """Return True if expr is a Laurent monomial (single term)."""
    e = sp.cancel(sp.together(expr))
    n, d = sp.fraction(e)
    pn = sp.Poly(sp.expand(n), q)
    pd = sp.Poly(sp.expand(d), q)
    return len(pn.terms()) <= 1 and len(pd.terms()) <= 1


def strip_monomial(expr):
    """Divide out the lowest power of q so result is an ordinary polynomial with
    nonzero constant term; return (poly_expr, valuation)."""
    e = sp.cancel(sp.together(expr))
    n, d = sp.fraction(e)
    pn = sp.Poly(sp.expand(n), q)
    pd = sp.Poly(sp.expand(d), q)
    # only handle case d is a monomial (true for A,C,D,A-D which are Laurent polys)
    assert len(pd.terms()) == 1, f"denominator not monomial: {pd}"
    dval = pd.monoms()[0][0]
    dc = pd.coeffs()[0]
    monoms = [m[0] for m in pn.monoms()]
    v = min(monoms) - dval
    num = sp.expand((n / d) / q**v)
    return sp.Poly(num, q), v


def palindromic_upto_monomial(expr):
    """Check f(q) = +- q^e f(1/q) i.e. coeff list is a palindrome (or anti)."""
    P, v = strip_monomial(expr)
    c = P.all_coeffs()  # descending
    c = c[::-1]  # ascending
    pal = (c == c[::-1])
    anti = (c == [-x for x in c[::-1]])
    return pal, anti, c


def reversal_upto_monomial(exprA, exprD):
    """Check D = q^m * A(1/q) up to monomial, i.e. coeff list of D equals reverse
    of coeff list of A (up to sign/shift)."""
    PA, _ = strip_monomial(exprA)
    PD, _ = strip_monomial(exprD)
    ca = PA.all_coeffs()[::-1]
    cd = PD.all_coeffs()[::-1]
    return (cd == ca[::-1]), (cd == [-x for x in ca[::-1]]), ca, cd


# ---------- automorph entry reconstruction ----------
def automorph_entries(r, s):
    """Return sympy exprs A, C, AminusD, D for the +1 automorph of the fraction r/s.
    Gauge: A/C = [r/s]_q reduced (A,C coprime primitive with the qval shift on A).
    A - D = F * C where F = G_of_rs(r,s)."""
    shiftA, Anum, Cden = qval(r, s)
    A = shifted_to_expr(shiftA, Anum)
    C = shifted_to_expr(0, Cden)
    shiftF, Fnum, Fden = G_of_rs(r, s)
    F = as_ratfun(shiftF, Fnum, Fden)
    AminusD = sp.cancel(sp.together(F * C))
    # AminusD must be a Laurent polynomial (C is a multiple of Fden)
    D = sp.cancel(sp.expand(A - AminusD))
    return A, C, AminusD, D, F


def factor_report(expr, label):
    P, v = strip_monomial(expr)
    fac = sp.factor_list(P.as_expr())
    return f"{label}: val={v} factors={fac}"


def neg_pell_fundamental(d):
    """Fundamental negative-Pell solution (x0,y0): x0^2 - d y0^2 = -1, smallest,
    or None if unsolvable. Uses CF convergents."""
    a0 = isqrt(d)
    if a0 * a0 == d:
        return None
    # generate convergents, test -1
    m_, den_, a_ = 0, 1, a0
    p_m1, p_m2 = 1, 0
    q_m1, q_m2 = 0, 1
    # a0 convergent
    convs = []
    ai = a0
    for _ in range(400):
        p = ai * p_m1 + p_m2
        qq = ai * q_m1 + q_m2
        convs.append((p, qq))
        if p*p - d*qq*qq == -1:
            return p, qq
        p_m2, p_m1 = p_m1, p
        q_m2, q_m1 = q_m1, qq
        # next CF term
        m_ = den_ * ai - m_
        den_ = (d - m_*m_) // den_
        ai = (a0 + m_) // den_
    return None


def cyclotomic_part(P):
    """Given sympy Poly P (integer, primitive), strip all cyclotomic factors,
    return (list_of_(n,mult), noncyclotomic_poly_expr)."""
    from sympy import cyclotomic_poly
    expr = P.as_expr()
    deg = P.degree()
    cyclos = []
    remaining = P
    # try indices up to some bound
    for n in range(1, 3*deg + 6):
        phi = sp.Poly(cyclotomic_poly(n, q), q)
        mult = 0
        while remaining.degree() >= phi.degree():
            quo, rem = sp.div(remaining, phi, domain='QQ')
            if rem.is_zero:
                remaining = quo
                mult += 1
            else:
                break
        if mult:
            cyclos.append((n, mult))
        if remaining.degree() == 0:
            break
    return cyclos, remaining.as_expr()


def report_d(d, verbose=True):
    out = []
    pf = pell_fundamental(d)
    if pf is None:
        return f"d={d}: square"
    r, s, plen, parity = pf
    A, C, AmD, D, F = automorph_entries(r, s)
    # finiteness
    Pc, vc = strip_monomial(C)
    Pf_num, _ = strip_monomial(sp.together(F).as_numer_denom()[0]) if not is_monomial_times(F) else (None,0)
    finite = is_monomial_times(F)
    out.append(f"d={d} (r,s)=({r},{s}) period={plen}{parity} finite={finite}")
    # duality validation
    pal_C, anti_C, cC = palindromic_upto_monomial(C)
    rev_ok, rev_anti, cA, cD = reversal_upto_monomial(A, D)
    out.append(f"  C palindromic_up_to_monomial={pal_C}  D=rev(A)? {rev_ok} (anti {rev_anti})")
    # factor C and A-D
    cyc_C, ncc_C = cyclotomic_part(Pc)
    out.append(f"  C: cyclo={cyc_C}  noncyc={sp.factor(ncc_C)}")
    if not finite:
        # reduced denominator = denominator of F
        Fden = sp.together(F).as_numer_denom()[1]
        PFden, _ = strip_monomial(Fden)
        cyc_R, ncc_R = cyclotomic_part(PFden)
        out.append(f"  S_red: cyclo={cyc_R}  noncyc={sp.factor(ncc_R)}")
    # A - D factor (which factors of C divide it)
    PamD, vAmD = strip_monomial(AmD)
    g = sp.gcd(Pc.as_expr(), PamD.as_expr())
    out.append(f"  gcd(C, A-D) = {sp.factor(g)}")
    return "\n".join(out)


def neg_pell_report(d):
    """Study Lambda = Lambda_-^2 decomposition."""
    out = []
    np = neg_pell_fundamental(d)
    if np is None:
        return f"d={d}: no negative-Pell solution"
    x0, y0 = np
    pf = pell_fundamental(d)
    r, s, plen, parity = pf
    out.append(f"d={d}: neg-Pell (x0,y0)=({x0},{y0}) y0={y0}; +Pell (r,s)=({r},{s})")
    # sanity: r = 2 x0^2 +1, s = 2 x0 y0
    out.append(f"   check r=2x0^2+1? {r == 2*x0*x0+1}  s=2 x0 y0? {s == 2*x0*y0}")
    # automorph entries for + side and - side
    A, C, AmD, D, F = automorph_entries(r, s)
    Am, Cm, AmDm, Dm, Fm = automorph_entries(x0, y0)   # negative side via qval(x0,y0)+G
    tminus = sp.expand(Am + Dm)  # trace of Lambda_-
    # check F(d) equals F computed on both
    same_F = sp.simplify(F - Fm) == 0
    out.append(f"   F(d) from (r,s) == F from (x0,y0)? {same_F}")
    # check C = C_- * t_-  up to monomial
    ratio_C = sp.cancel(C / (Cm * tminus))
    out.append(f"   C / (C_- * t_-) monomial? {is_monomial_times(ratio_C)}  = {sp.simplify(ratio_C)}")
    ratio_AmD = sp.cancel(AmD / (AmDm * tminus))
    out.append(f"   (A-D)/((A_- - D_-) t_-) monomial? {is_monomial_times(ratio_AmD)} = {sp.simplify(ratio_AmD)}")
    # palindromy of C_- and t_-
    pal_Cm, anti_Cm, _ = palindromic_upto_monomial(Cm)
    pal_t, anti_t, _ = palindromic_upto_monomial(tminus)
    out.append(f"   C_- palindromic={pal_Cm} (anti {anti_Cm});  t_- palindromic={pal_t} (anti {anti_t})")
    out.append(f"   C_-(1)={sp.together(Cm).subs(q,1)}  (should be y0={y0})")
    # factor C_-
    PCm, _ = strip_monomial(Cm)
    cyc, ncc = cyclotomic_part(PCm)
    out.append(f"   C_-: cyclo={cyc} noncyc={sp.factor(ncc)}")
    # does C_- divide A_- - D_- ? (finiteness on neg side)
    PamDm, _ = strip_monomial(AmDm)
    g = sp.gcd(PCm.as_expr(), PamDm.as_expr())
    out.append(f"   gcd(C_-, A_- - D_-) = {sp.factor(g)}  (finite iff == C_- up to monomial)")
    return "\n".join(out)


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["basic", "neg"], default="basic", nargs="?")
    ap.add_argument("--ds", type=str, default="2,7,19,53")
    args = ap.parse_args()
    ds = [int(x) for x in args.ds.split(",")]
    for d in ds:
        if args.mode == "basic":
            print(report_d(d))
        else:
            print(neg_pell_report(d))
        print("-"*70)
