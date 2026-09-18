import sympy as sp, cmath, math
from proof_verification import lam_q, q
def detexp(Lq):
    v=complex(Lq.det().subs(q,1.3)); return round(math.log(abs(v))/math.log(1.3))
def cyc(P):
    Pn=sp.expand(sp.numer(sp.cancel(P))); out=[]
    for (f,mm) in sp.factor_list(Pn)[1]:
        for n in range(1,60):
            if sp.expand(f-sp.cyclotomic_poly(n,q))==0: out.append((n,mm));break
    return out
res=[]
for d in range(2,60):
    if int(math.isqrt(d))**2==d: continue
    (r,s),Lq=lam_q(d); A,D,C=Lq[0,0],Lq[1,1],Lq[1,0]; m=detexp(Lq)
    g=sp.expand(sp.cancel(A-D))
    g1=sp.diff(g,q).subs(q,1)   # (A-D)'(1)
    Ap1=sp.diff(A,q).subs(q,1)
    for (n,mm) in cyc(C):
        res.append((d,n,mm,r,s,m,int(g1),int(Ap1)))
print("d  n mult  r    s   m    g1=(A-D)'(1)   Ap1=A'(1)   n prime? p|g1?")
for (d,n,mm,r,s,m,g1,Ap1) in res:
    isp = sp.isprime(n)
    pdiv = (g1 % n ==0)
    print(f"{d:3d} {n:2d} {mm}   {r:5d} {s:4d} {m:4d}  {g1:8d}     {Ap1:6d}   prime={isp} p|g1={pdiv if isp else '-'}  g1/n={g1/n:.2f}")
# check hypothesis: for n prime, n | g1 always?
primes=[x for x in res if sp.isprime(x[1])]
print("\nn prime cases:",len(primes),"  all n|g1?", all((x[6]%x[1]==0) for x in primes))
comps=[x for x in res if not sp.isprime(x[1])]
print("composite/prime-power n present:", sorted(set(x[1] for x in comps)))
