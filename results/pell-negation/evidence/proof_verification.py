"""Verify the PROOF of Claim 1.

Lambda = [[r, d*s],[s, r]]  (fundamental automorph of x^2-d y^2=1; fixes sqrt d, sends oo -> r/s)
N = diag(-1,1).  Then N Lambda N = Lambda^{-1}.
rho: PSL2(Z) -> PGL2(Z[q,q^-1]),  R=[[1,1],[0,1]] |-> Rq=[[q,1],[0,1]],  S=[[0,-1],[1,0]] |-> Sq=[[0,-q^-1],[1,0]].
Claim:  G(Lambda^k . oo) = (A - D)/C  for every k>=1,  where Lambda_q = [[A,B],[C,D]].
"""
import sympy as sp
from fractions import Fraction as F
from qcore import q, qrat_B, G, pell_plus1, is_laurent_poly

Rq = sp.Matrix([[q, 1], [0, 1]])
Sq = sp.Matrix([[0, -1 / q], [1, 0]])
R = sp.Matrix([[1, 1], [0, 1]])
S = sp.Matrix([[0, -1], [1, 0]])


def sl2_word(M):
    """M in SL2(Z) -> list of ('R',n) / ('S',) with M = prod, up to sign."""
    M = sp.Matrix(M)
    w = []
    while M[1, 0] != 0:
        a, c = int(M[0, 0]), int(M[1, 0])
        n = a // c
        w.append(('R', n))
        M = sp.Matrix([[1, -n], [0, 1]]) * M          # R^{-n} M
        w.append(('S',))
        M = sp.Matrix([[0, 1], [-1, 0]]) * M          # S^{-1} M
    # now M = +- [[1,b],[0,1]]
    a, b = int(M[0, 0]), int(M[0, 1])
    w.append(('R', b // a))
    return w


def rho(w):
    M = sp.eye(2)
    for t in w:
        M = M * (Rq**t[1] if t[0] == 'R' else Sq)
    return sp.simplify(M)


def lam_q(d):
    r, s = pell_plus1(d)
    L = sp.Matrix([[r, d * s], [s, r]])
    w = sl2_word(L)
    Lq = rho(w)
    # sanity: rho is a homomorphism -> setting q=1 recovers +-L
    chk = sp.simplify(Lq.subs(q, 1))
    assert chk == L or chk == -L, (d, chk, L)
    return (r, s), Lq


if __name__ == '__main__':
    for d in [2, 3, 5, 6, 7, 8, 11, 12, 13, 15, 18, 19, 27, 43, 45, 50, 53, 75]:
        (r, s), Lq = lam_q(d)
        A, B, C, D = Lq[0, 0], Lq[0, 1], Lq[1, 0], Lq[1, 1]
        pred = sp.cancel((A - D) / C)
        # k = 1, 2, 3 : G at the k-th Pell convergent, computed independently
        ok = []
        Lk = sp.eye(2)
        for k in (1, 2, 3):
            Lk = sp.simplify(Lk * Lq)
            Ak, Ck, Dk = Lk[0, 0], Lk[1, 0], Lk[1, 1]
            gk = sp.cancel((Ak - Dk) / Ck)
            ok.append(sp.cancel(gk - pred) == 0)
        # independent: G(r/s) from the T/S q-real implementation
        gind = G(F(r, s))
        match = sp.cancel(gind - pred) == 0
        print(f"d={d:3d} pell=({r},{s})  (A-D)/C == G(r/s): {match}   "
              f"const in k=1,2,3: {ok}   Laurent: {is_laurent_poly(pred)}   G = {sp.factor(pred)}")
