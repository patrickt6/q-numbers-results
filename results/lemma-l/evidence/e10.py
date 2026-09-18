import sympy as sp, math
from proof_verification import lam_q, q
def detexp(Lq):
    v=complex(Lq.det().subs(q,1.3)); return round(math.log(abs(v))/math.log(1.3))

print("VERIFY g1*s = r^2+s^2-1 = (d+1)s^2, and A/C=[r/s]_q exactly:")
from qcore import qrat_B
from fractions import Fraction as Fr
for d in [2,5,6,7,11,13,19,53]:
    (r,s),Lq=lam_q(d); A,D,C=Lq[0,0],Lq[1,1],Lq[1,0]; m=detexp(Lq)
    g1=sp.diff(sp.expand(A-D),q).subs(q,1)
    # check A/C == [r/s]_q  and -D/C==[-r/s]_q
    AC=sp.cancel(A/C); rs=sp.cancel(qrat_B(Fr(r,s)))
    DC=sp.cancel(-D/C); mrs=sp.cancel(qrat_B(Fr(-r,s)))
    print(f"d={d}: g1={g1}, (d+1)s={ (d+1)*s}, g1*s={g1*s}, r^2+s^2-1={r*r+s*s-1}, s|g1={int(g1)%s==0}, A/C=[r/s]?{sp.simplify(AC-rs)==0}, -D/C=[-r/s]?{sp.simplify(DC-mrs)==0}")

print("\nVERIFY n=2: is m even exactly when Phi_2 | C (i.e. C(-1)=0)?  and 2|s link")
for d in range(2,60):
    if int(math.isqrt(d))**2==d: continue
    (r,s),Lq=lam_q(d); C=Lq[1,0]; m=detexp(Lq)
    phi2 = sp.simplify(C.subs(q,-1))==0
    print(f"d={d} s={s} m={m} m_even={m%2==0} Phi2|C={phi2} 2|s={s%2==0}", end="   ")
    if (m%2==0)!=phi2 or phi2!=(s%2==0): print("  <-- MISMATCH")
    else: print()
