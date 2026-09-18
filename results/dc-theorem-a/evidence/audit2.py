import sys
sys.path.insert(0, '<path>')
import sympy as sp
from proof_verification import lam_q
from qcore import q

t = sp.symbols('t')

def get_f(d):
    (r,s), Lq = lam_q(d)
    A,B,C,D = Lq[0,0],Lq[0,1],Lq[1,0],Lq[1,1]
    det = sp.simplify(A*D-B*C)
    m = sp.simplify(q*sp.diff(det,q)/det)
    f = sp.cancel(A-D)
    # clear denominator (Laurent): multiply by q^N to make polynomial, doesn't change (q-1)-adic val of the poly part
    num, den = sp.fraction(sp.together(f))
    # den is a power of q, a unit at q=1, so v_{q-1}(f)=v_{q-1}(num)
    return r,s,m,sp.expand(num),sp.expand(den),f

def vqm1_over_Z(poly):
    # (q-1)-adic valuation over Z (rational): largest k with (q-1)^k | poly in Q[q]
    P = sp.Poly(poly, q)
    if P.is_zero: return None
    k=0
    while True:
        Pq,Pr = sp.div(P, sp.Poly((q-1)**(k+1), q))
        if Pr.is_zero:
            k+=1
        else:
            break
    return k

def vqm1_mod_p(poly, p):
    P = sp.Poly(poly, q, modulus=p)
    if P.is_zero: return None
    # factor out (q-1)
    k=0
    base = sp.Poly(q-1, q, modulus=p)
    while True:
        Pq, Pr = sp.div(P, base)
        if Pr.is_zero:
            P=Pq; k+=1
        else:
            break
    return k

print("=== Item (2): parity of (q-1)-adic valuation over Z ===")
for d in [2,3,5,6,7,11,13,15,19,21]:
    r,s,m,num,den,f = get_f(d)
    v = vqm1_over_Z(num)
    print(f"d={d:3d} m={m} v_(q-1)(f)={v} odd={v%2==1}")

print("\n=== Item (2b): over F_2 does parity fail? (theorem excludes p=2) ===")
for d in [2,3,5,6,7,11,13]:
    r,s,m,num,den,f = get_f(d)
    v2 = vqm1_mod_p(num, 2)
    vZ = vqm1_over_Z(num)
    print(f"d={d:3d} v_Z={vZ}(odd={vZ%2==1})  v_F2={v2}(odd={v2%2==1 if v2 is not None else None})")
