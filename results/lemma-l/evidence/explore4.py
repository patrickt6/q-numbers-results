import sympy as sp, cmath, math
from proof_verification import lam_q, q
from qcore import pell_plus1

def detexp(Lq):
    dd = sp.simplify(Lq.det())
    p = sp.Poly(sp.together(dd).as_numer_denom()[0],q)
    # dd is q^m; get m from a nonzero sample
    val = complex(dd.subs(q, 1.3))
    m = round(math.log(abs(val))/math.log(1.3))
    return m

def cyclo_factors_of_C(C):
    Cn = sp.expand(sp.numer(sp.cancel(C)))
    facs = sp.factor_list(Cn)[1]
    out=[]
    for (f,mult) in facs:
        for n in range(1, 80):
            if sp.expand(f-sp.cyclotomic_poly(n,q))==0:
                out.append((n,mult)); break
    return out

for d in [2,3,5,6,7,13,19,43,53]:
    (r,s),Lq = lam_q(d)
    A,B,C,D = Lq[0,0],Lq[0,1],Lq[1,0],Lq[1,1]
    m = detexp(Lq)
    facs = cyclo_factors_of_C(C)
    print(f"\n=== d={d} m={m} r,s={r},{s}  cyclo(n,mult): {facs}")
    for (n,mult) in facs:
        zeta = cmath.exp(2j*math.pi/n)
        Av=complex(A.subs(q,zeta)); Dv=complex(D.subs(q,zeta)); Cv=complex(C.subs(q,zeta))
        zm=zeta**m; u=Av/Dv; A2=Av**2/zm
        # find j: A(zeta) = eps * zeta^j  -> arg
        print(f"  n={n} m{mult}: |C|={abs(Cv):.1e} |A|={abs(Av):.4f} A/D={u.real:+.4f}{u.imag:+.4f}i A^2/z^m={A2.real:+.4f}{A2.imag:+.4f}i  A==D?{abs(Av-Dv)<1e-8}")
