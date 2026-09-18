import sys
sys.path.insert(0, '<path>')
import sympy as sp
from proof_verification import lam_q
from qcore import q

def get_fm(d):
    (r,s), Lq = lam_q(d)
    A,B,C,D = Lq[0,0],Lq[0,1],Lq[1,0],Lq[1,1]
    det = sp.simplify(A*D-B*C)
    # det = q^m (monomial); recover m = q * det'/det
    m = sp.simplify(q*sp.diff(det,q)/det)
    f = sp.expand(sp.cancel(A-D))
    return r,s,m,f,A,B,C,D

def jets_at1(f, order):
    # plain derivatives g_k = f^{(k)}(1)
    g=[]
    fk=f
    for k in range(order+1):
        g.append(sp.simplify(fk.subs(q,1)))
        fk=sp.diff(fk,q)
    return g  # g[0]=f(1), g[1]=f'(1),...

print("=== Item (1): odd-jet reduction, g2=(m-1)g1 ===")
for d in [7,13,19]:
    r,s,m,f,A,B,C,D = get_fm(d)
    det = sp.expand(sp.cancel(A*D-B*C))
    g = jets_at1(f,4)
    g1p = (d+1)*s
    print(f"d={d} pell=({r},{s}) m={m} det={det}")
    print(f"   f(1)={g[0]}  g1={g[1]}  (d+1)s={g1p}  match={g[1]==g1p}")
    print(f"   g2={g[2]}  (m-1)g1={(m-1)*g[1]}  match={g[2]==(m-1)*g[1]}")
    # Taylor coeff gamma_k=g_k/k!
    gam1=sp.Rational(g[1],1); gam2=sp.Rational(g[2],2)
    print(f"   gamma1={gam1} gamma2={gam2}  (m-1)gamma1/2={sp.Rational((m-1)*g[1],2)}  match={gam2==sp.Rational((m-1)*g[1],2)}")
    # check functional equation f(1/q) = -q^{-m} f(q)
    lhs = sp.expand(sp.cancel(f.subs(q,1/q)))
    rhs = sp.expand(sp.cancel(-q**(-m)*f))
    print(f"   func eq f(1/q)=-q^-m f: {sp.simplify(lhs-rhs)==0}")
