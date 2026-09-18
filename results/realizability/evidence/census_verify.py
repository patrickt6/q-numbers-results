#!/usr/bin/env python3
"""Verify on ALL 166 census proper collapses (and the wider a^2=1 scan):

  V1 (unit law / GAP 2 detector): N(S'(i)) = 4 * 2 * 4^{max(0, v2(s)-2)} exactly
      when v2(s) >= 2, i.e. S'(i) = 2i * Phi_2(i) * (units and Phi_{2^k}(i) factors),
      equivalently no odd prime divides S'(i). [On full rows the norm picks up m0^2.]
  V2 (q = -1 edge detector): |S'(-1)| = prod_{2p^j in T} p * 2^{#{2^k in T, k>=2}},
      recomputed independently, plus collect S'(-1) values for closed-form hunt.

Census source: census_d2_6000_slim.csv, rows with S_is_cyc_squarefree_product True
and proper collapse status determined by recomputing T via cyclotomic division.
"""
import csv
import sys
from math import gcd

sys.path.insert(0, '<path>')
from qpoly import qval, poly_trim

import sympy as sp
_q = sp.Symbol('q')

_cyc = {}
def cyclo(m):
    if m not in _cyc:
        _cyc[m] = sp.Poly(sp.cyclotomic_poly(m, _q), _q, domain='ZZ')
    return _cyc[m]

def poly_from_list(coeffs):
    return sp.Poly(list(reversed(poly_trim(list(coeffs)))), _q, domain='ZZ')

def divisors(n):
    out = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            out.append(i)
            if i != n // i:
                out.append(n // i)
        i += 1
    return sorted(out)

def eval_gauss(coeffs, re0, im0):
    re, im = 0, 0
    for c in reversed(poly_trim(list(coeffs))):
        re, im = re * re0 - im * im0 + c, re * im0 + im * re0
    return re, im

def deriv(coeffs):
    return [k * c for k, c in enumerate(coeffs)][1:]

def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k

def odd_part(n):
    n = abs(n)
    while n % 2 == 0:
        n //= 2
    return n

def check_row(a, s):
    _, _, S = qval(a, s)
    S = poly_trim(S)
    Spoly = poly_from_list(S)
    T = []
    prod = sp.Poly(1, _q, domain='ZZ')
    for n in divisors(s):
        if n < 2:
            continue
        _, rr = sp.div(Spoly, cyclo(n), domain='ZZ')
        if rr == 0:
            T.append(n)
            prod = prod * cyclo(n)
    pure = (prod == Spoly)
    dS = deriv(S)
    dSi = eval_gauss(dS, 0, 1)
    dSm1 = eval_gauss(dS, -1, 0)[0]
    return T, pure, dSi, dSm1

def main():
    path = '<path>'
    rows = []
    with open(path) as f:
        for row in csv.DictReader(f):
            if row['S_is_cyc_squarefree_product'] == 'True':
                rows.append((int(row['d']), int(row['r_d']), int(row['s_d'])))
    print(f'{len(rows)} cyc-squarefree census rows')

    n_proper = 0
    v1_viol = []
    v2_viol = []
    edge_data = []
    for (d, r, s) in rows:
        if s == 1:
            continue
        a = r % s
        if a in (1, s - 1):
            continue  # full rows
        T, pure, dSi, dSm1 = check_row(a, s)
        if not pure:
            print('IMPURE census row?!', d, a, s)
            continue
        n_proper += 1
        # V1
        if s % 4 == 0:
            norm = dSi[0] ** 2 + dSi[1] ** 2
            expected = 8 * 4 ** max(0, v2(s) - 2)
            if norm != expected:
                v1_viol.append((d, a, s, norm, expected, sorted(T)))
        # V2
        pred = 1
        for t in T:
            m = t
            k = v2(t)
            if k == 1 and len(sp.factorint(t // 2)) == 1 and t > 2:
                pred *= list(sp.factorint(t // 2))[0] ** 0 + 0 or 1
        # recompute pred properly: |S'(-1)| = prod over t in T, t != 2 of |Phi_t(-1)|
        pred = 1
        for t in T:
            if t == 2:
                continue
            pred *= abs(int(sp.cyclotomic_poly(t, -1)))
        ok = (s % 2 == 1) or (abs(dSm1) == pred)
        if s % 2 == 1:
            ok = True  # S(-1) != 0 case, skip
        if not ok:
            v2_viol.append((d, a, s, dSm1, pred))
        edge_data.append(dict(d=d, a=a, s=s, T=sorted(T), dSm1=dSm1, dSi=list(dSi)))
        if n_proper % 20 == 0:
            print(f'{n_proper} proper rows done', flush=True)

    print(f'proper collapses processed: {n_proper}')
    print(f'V1 violations (odd prime divides S\'(i), 4|s): {len(v1_viol)}')
    for v in v1_viol[:10]:
        print('  ', v)
    print(f'V2 violations: {len(v2_viol)}')
    for v in v2_viol[:10]:
        print('  ', v)
    import json
    json.dump(edge_data, open('<path>', 'w'))
    print('saved census_jets.json')

if __name__ == '__main__':
    main()
