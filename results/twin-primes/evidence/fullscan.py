import sympy as sp
from sympy import primerange, cyclotomic_poly, Poly, gcd
from engine import mgo_S, q
primes=list(primerange(3,60))
pairs=[(p,pp) for i,p in enumerate(primes) for pp in primes[i+1:] if p*pp<=210]
viol=[]
for (p,pp) in pairs:
    d=p*pp
    target=Poly(sp.expand(cyclotomic_poly(p,q)*cyclotomic_poly(pp,q)),q).primitive()[1]
    hits=[]
    for a in range(1,d):
        if gcd(a,d)!=1: continue
        S=mgo_S(a,d)
        if S==target:
            hits.append((a, a*a%d))
    twin=(pp==p+2)
    # expected hits: twin -> a=p+1 and d-(p+1), both square roots of 1; nontwin -> none
    exp = sorted([p+1, d-(p+1)]) if twin else []
    got = sorted(a for a,_ in hits)
    ok = (got==exp)
    # also confirm every hit has a^2=1
    allsr = all(sq==1 for _,sq in hits)
    if not ok or not allsr:
        viol.append((p,pp,got,exp,allsr))
    print(f"({p},{pp}) d={d} twin={twin} hits={hits} expected_a={exp} OK={ok} all_sqrt1={allsr}")
print("\nVIOLATIONS:", viol if viol else "NONE")
