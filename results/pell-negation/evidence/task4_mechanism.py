#!/usr/bin/env python3
"""Task 4: mechanism spot check for the first four family members
d = 13, 41, 74, 130 (fundamental Pell +1 solution from census).
For each: S(q) = reduced denominator of [r/s]_q (qpoly.qval), factor it
(cyclo.factor_str / cyclotomic_analysis), identify the Phi_5 factor and the
non-cyclotomic palindromic cofactor, then confirm G_of_rs(r,s) has constant
denominator (F(d) finite) i.e. the cofactor cancels in (A-D)/C.
"""
import sys
sys.path.insert(0, "<path>")

import sympy as sp
from qpoly import qval, G_of_rs, is_finite_GDen, poly_deg, laurent_str
from cyclo import cyclotomic_analysis, factor_str, is_palindromic

_q = sp.Symbol("q")

# (d, r, s) fundamental Pell+1 solutions, from census_d2_6000_slim.csv
members = [
    (13, 649, 180),
    (41, 2049, 320),
    (74, 3699, 430),
    (130, 6499, 570),
]

cofactors = []
for d, r, s in members:
    print(f"\n{'='*70}\nd={d}  (r,s)=({r},{s})")
    shiftR, Rnum, Rden = qval(r, s)
    # S(q) is Rden (the reduced denominator of [r/s]_q)
    S = Rden
    print(f"  deg S = {poly_deg(S)}")
    analysis = cyclotomic_analysis(S)
    print(f"  is_cyc_squarefree_product = {analysis['is_cyc_squarefree_product']}")
    print(f"  factor_ks (cyclotomic factors, if all cyclotomic) = {analysis['factor_ks']}")
    print(f"  noncyclotomic_factor_degrees = {analysis['noncyclotomic_factor_degrees']}")
    print(f"  S factored: {factor_str(S)}")

    # explicit factor list via sympy to split out Phi_5 vs cofactor
    poly = sp.Poly(list(reversed(S)), _q, domain="QQ")
    const, factors = sp.factor_list(poly)
    phi5 = sp.Poly(sp.cyclotomic_poly(5, _q), _q, domain="QQ")
    phi5_mult = 0
    cofactor_parts = []
    for f, mult in factors:
        if f == phi5:
            phi5_mult = mult
        else:
            cofactor_parts.append((f, mult))
    print(f"  Phi_5 multiplicity: {phi5_mult}")
    cof_expr = sp.Integer(1)
    for f, mult in cofactor_parts:
        cof_expr *= f.as_expr() ** mult
    cof_expr = sp.expand(cof_expr)
    cof_poly = sp.Poly(cof_expr, _q)
    cof_coeffs_asc = cof_poly.all_coeffs()[::-1]
    print(f"  non-Phi5 cofactor (deg {cof_poly.degree()}): {sp.factor(cof_expr)}")
    print(f"  cofactor coeffs (ascending): {cof_coeffs_asc}")
    print(f"  cofactor palindromic: {is_palindromic(list(cof_coeffs_asc))}")
    cofactors.append((d, cof_poly.degree(), cof_coeffs_asc, cof_expr))

    # confirm finiteness via G_of_rs
    shift, Num, Den = G_of_rs(r, s)
    finite = is_finite_GDen(Den)
    print(f"  G_of_rs Den degree = {poly_deg(Den)}  -> is_finite = {finite}")
    if finite:
        print(f"  F(d) = {laurent_str(shift, Num)}")

print(f"\n{'='*70}\nCofactor comparison across members:")
for d, deg, coeffs, expr in cofactors:
    print(f"  d={d:4d}  deg={deg:3d}  coeffs={coeffs}")

print("\nRatio / pattern check (cofactor(d_{k+1}) vs cofactor(d_k), same degree growth?):")
degs = [deg for _, deg, _, _ in cofactors]
print("degrees:", degs)
diffs = [degs[i+1]-degs[i] for i in range(len(degs)-1)]
print("degree diffs:", diffs)
