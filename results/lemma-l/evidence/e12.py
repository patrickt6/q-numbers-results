import sympy as sp, math
from proof_verification import lam_q, q
def cyc(P):
    Pn=sp.expand(sp.numer(sp.cancel(P))); out=[]
    for (f,mm) in sp.factor_list(Pn)[1]:
        for n in range(1,60):
            if sp.expand(f-sp.cyclotomic_poly(n,q))==0: out.append((n,mm));break
    return out
# g_k = k-th Taylor coeff of (A-D) at q=1 = (A-D)^(k)(1)/k!
print("Prime-power cyclotomic factors: check criterion p|g_k for k=1..p^{a-1}")
for d in range(2,60):
    if int(math.isqrt(d))**2==d: continue
    (r,s),Lq=lam_q(d); A,D,C=Lq[0,0],Lq[1,1],Lq[1,0]
    AD=sp.expand(A-D)
    for (n,mm) in cyc(C):
        fac=sp.factorint(n)
        if len(fac)!=1: continue   # prime power only
        p=list(fac)[0]; a=fac[p]
        if a<2: continue           # a>=2 (n=4,8,9,25,27,...)
        thr=p**(a-1)
        gk=[]
        f=AD
        for k in range(1,thr+1):
            f=sp.diff(f,q)
            val=sp.diff(AD,q,k).subs(q,1)/math.factorial(k)
            gk.append(int(val))
        ok=all(g%p==0 for g in gk)
        print(f"d={d} n={n}=({p}^{a}) need p|g_k k=1..{thr}: g={gk} all div by {p}? {ok}")
