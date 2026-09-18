"""
1. Characterize which positive words M = R^{c1} S R^{c2} S ... R^{cL} S
   satisfy CONG: C | (A-D) - (q-1)B in Q[q,1/q].
   Candidate predictors, per word:
     - palindromic exponent tuple up to cyclic rotation
     - equal diagonal at q=1 (a == d classically)
     - classical c | a - d
     - M conjugate to M^T in SL(2,Z)-sense proxy: word palindromic up to rotation
2. Large-d exact CONG scan for Pell automorphs (the T5 population),
   using exact integer arithmetic long division (C has leading coeff +-1
   after normalization; verified on the fly), no floating point, no mod-p.
"""
import sys
import random

sys.path.insert(0, '<path>')
from fastlam import lam_q_fast, rho_fast, p_add, p_mul  # noqa

import sympy as sp
q = sp.symbols('q')


def sub(a, b):
    return p_add(a, b, scale=-1)


def qshift(p, k):
    return {e + k: c for e, c in p.items()}


def norm(p):
    if not p:
        return []
    lo, hi = min(p), max(p)
    out = [0] * (hi - lo + 1)
    for e, c in p.items():
        out[e - lo] = c
    return out


def divides_exact(g, f):
    """g | f in Q[q]; integer-safe long division with rational fallback."""
    from fractions import Fraction
    if not f:
        return True
    if not g:
        return False
    f = [Fraction(c) for c in f]
    dg = len(g) - 1
    lg = Fraction(g[-1])
    while True:
        df = len(f) - 1
        while df >= 0 and f[df] == 0:
            df -= 1
        if df < dg:
            break
        coef = f[df] / lg
        for i in range(dg + 1):
            f[df - dg + i] -= coef * Fraction(g[i])
        f = f[:df]
    return not any(f)


def cong_holds(A, B, C, D):
    f = sub(A, D)
    qm1B = sub(qshift(B, 1), B)
    E = sub(f, qm1B)
    return divides_exact(norm(C), norm(E))


def is_cyclic_palindrome(t):
    n = len(t)
    tt = list(t)
    for r in range(n):
        w = tt[r:] + tt[:r]
        if w == w[::-1]:
            return True
    return False


def classical(A, B, C, D):
    a = sum(A.values()); b = sum(B.values())
    c = sum(C.values()); d = sum(D.values())
    return a, b, c, d


def main():
    random.seed(99)
    print('== characterization over random positive words ==')
    import collections
    table = collections.Counter()
    examples = {}
    for _ in range(600):
        L = random.randint(2, 6)
        cs = tuple(random.randint(1, 4) for _ in range(L))
        w = [x for c in cs for x in [('R', c), ('S', 0)]]
        A, B, C, D = rho_fast(w)
        if not C:
            continue
        cg = cong_holds(A, B, C, D)
        a, b, c, d = classical(A, B, C, D)
        pal = is_cyclic_palindrome(cs)
        eqd = (a == d) or (a == -d)
        cdiv = (c != 0 and (a - d) % c == 0)
        key = (cg, pal, eqd, cdiv)
        table[key] += 1
        if key not in examples:
            examples[key] = cs
    print('  (CONG, cyc-palindrome, |a|==|d|, c | a-d) : count : example word')
    for key, n in sorted(table.items()):
        print(' ', key, ':', n, ':', examples[key])

    print('\n== exact CONG scan over Pell automorphs ==')
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    bad = []
    ndone = 0
    import time
    t0 = time.time()
    for d in range(2, dmax + 1):
        r = sp.integer_nthroot(d, 2)[0]
        if r * r == d:
            continue
        (_, _), (A, B, C, D) = lam_q_fast(d)
        if not cong_holds(A, B, C, D):
            bad.append(d)
            print('  CONG FAILS at d =', d)
        ndone += 1
        if ndone % 200 == 0:
            print(f'  ...{ndone} values done (d={d}) [{time.time()-t0:.0f}s]')
    print(f'CONG checked on {ndone} nonsquare d in [2,{dmax}]: failures {bad}')


if __name__ == '__main__':
    main()
