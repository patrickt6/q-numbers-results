"""
Verification suite for the exact identity behind T5.

  IDENTITY (t = 0):   q (A - D) = (q - 1)(q B + C)      [equal-diagonal M]
  IDENTITY (general): (A - D) - (q-1) B = H_t C,  H_t = [t]_q + (q-1) q^{t-1},
                      for M in SL(2,Z) with c | a - d, t = (a-d)/c.
  Both statements are linear and homogeneous in the entries, hence independent
  of the projective representative of rho(M).

  (v1) exact t=0 identity on every Pell automorph, nonsquare d in [2, 6000],
       allowing the representative's global sign: q E = +- (q-1) C exactly.
  (v2) symbolic closure re-check: P(M) => P(R^k M R^k), P(L^k M L^k) with
       A, B, C, D symbolic and C eliminated by the constraint, k = 1..4.
  (v3) general-t identity on positive words with c | a - d.
  (v4) the norm corollary is equivalent to (v1); spot-check the rational
       function (A-D)/C + (q-1) B/C ... skipped, implied.
"""
import sys
import time
import random

sys.path.insert(0, '<path>')
from fastlam import lam_q_fast, rho_fast, p_add, p_mul  # noqa

import sympy as sp
q = sp.symbols('q')


def sub(a, b):
    return p_add(a, b, scale=-1)


def qshift(p, k):
    return {e + k: c for e, c in p.items()}


def neg(p):
    return {e: -c for e, c in p.items()}


def qint(t):
    """[t]_q as a dict, any integer t."""
    if t > 0:
        return {i: 1 for i in range(t)}
    if t == 0:
        return {}
    return {i: -1 for i in range(t, 0)}


def H(t):
    """H_t = [t]_q + (q-1) q^{t-1}."""
    return p_add(qint(t), sub({t: 1}, {t - 1: 1}))


def main():
    # ---- v1: Pell automorphs, exact, d <= 6000 ----
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
    t0 = time.time()
    bad = []
    n = 0
    for d in range(2, dmax + 1):
        r = sp.integer_nthroot(d, 2)[0]
        if r * r == d:
            continue
        (_, _), (A, B, C, D) = lam_q_fast(d)
        f = sub(A, D)
        lhs = qshift(f, 1)                                   # q (A - D)
        rhs = sub(p_add(qshift(B, 2), qshift(C, 1)),
                  p_add(qshift(B, 1), C))                    # (q-1)(qB + C)
        ok = (sub(lhs, rhs) == {}) or (p_add(lhs, rhs) == {})
        if not ok:
            bad.append(d)
            if len(bad) < 5:
                print('  v1 FAIL at d =', d)
        n += 1
        if n % 1000 == 0:
            print(f'  v1 ...{n} d done (d={d}) [{time.time()-t0:.0f}s]')
    print(f'v1: exact identity q(A-D) = +-(q-1)(qB+C) on {n} nonsquare d '
          f'in [2,{dmax}]: failures {bad}')

    # ---- v2: symbolic closure ----
    A_, B_, C_, D_ = sp.symbols('A B C D')
    okall = True
    for k in range(1, 5):
        qk = q**k
        br = sp.together((q * A_ - q * D_) / (q - 1) - q * B_)  # C from P(M)
        # R^k M R^k
        A2 = q**(2 * k) * A_ + qk * sp.together((qk - 1) / (q - 1)) * C_
        B2 = qk * sp.together((qk - 1) / (q - 1)) * A_ + qk * B_ \
            + sp.together(((qk - 1) / (q - 1))**2) * C_ \
            + sp.together((qk - 1) / (q - 1)) * D_
        C2 = qk * C_
        D2 = sp.together((qk - 1) / (q - 1)) * C_ + D_
        P2 = sp.simplify((q * (A2 - D2) - (q - 1) * (q * B2 + C2))
                         .subs(C_, br))
        okR = (sp.simplify(P2) == 0)
        # L^k M L^k
        A3 = q**(2 * k) * A_ + q**(k + 1) * sp.together((qk - 1) / (q - 1)) * B_
        B3 = qk * B_
        C3 = q**(k + 1) * sp.together((qk - 1) / (q - 1)) * A_ \
            + q**2 * sp.together(((qk - 1) / (q - 1))**2) * B_ \
            + qk * C_ + q * sp.together((qk - 1) / (q - 1)) * D_
        D3 = q * sp.together((qk - 1) / (q - 1)) * B_ + D_
        P3 = sp.simplify((q * (A3 - D3) - (q - 1) * (q * B3 + C3))
                         .subs(C_, br))
        okL = (sp.simplify(P3) == 0)
        print(f'v2: closure k={k}: R-ends {okR}  L-ends {okL}')
        okall = okall and okR and okL
    print('v2 overall:', okall)

    # ---- v3: general-t identity on positive words with c | a-d ----
    random.seed(7)
    nok = nbad = 0
    for _ in range(2000):
        L = random.randint(1, 6)
        cs = [random.randint(1, 5) for _ in range(L)]
        w = [x for c in cs for x in [('R', c), ('S', 0)]]
        A, B, C, D = rho_fast(w)
        if not C:
            continue
        a = sum(A.values()); dd = sum(D.values()); c = sum(C.values())
        if c == 0 or (a - dd) % c != 0:
            continue
        t = (a - dd) // c
        E = sub(sub(A, D), sub(qshift(B, 1), B))
        HtC = p_mul(H(t), C)
        ok = (sub(E, HtC) == {}) or (p_add(E, HtC) == {})
        if ok:
            nok += 1
        else:
            nbad += 1
            if nbad <= 3:
                print('  v3 FAIL word', cs, 't =', t)
    print(f'v3: general-t identity on positive words: {nok} ok, {nbad} fail')


if __name__ == '__main__':
    main()
