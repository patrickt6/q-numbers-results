import sys, math
sys.path.insert(0,"<path>")
from downward_closure import phi_divides
import fastlam
# Route B theorem: n>=7, n!=6, Phi_n | C  =>  (1) Phi_n|(A-D)  (2) Phi_n|B  (3) n|s
# B never tested n=8,16,32.  These are >=7 and !=6, so fully in scope.
def sub(P,Q):
    ks=set(P)|set(Q); return {k:P.get(k,0)-Q.get(k,0) for k in ks if P.get(k,0)-Q.get(k,0)!=0}
targets=[8,16,32,4]
viol=[]; counts={n:0 for n in targets}
for d in range(2,3001):
    a0=math.isqrt(d)
    if a0*a0==d: continue
    (r,s),(A,B,C,D)=fastlam.lam_q_fast(d)
    for n in targets:
        if not phi_divides(C,n): continue
        counts[n]+=1
        c1=phi_divides(sub(A,D),n); c2=phi_divides(B,n); c3=(s%n==0)
        if not(c1 and c2 and c3):
            viol.append((d,n,c1,c2,c3,s))
print("hits per n:",counts)
print("in-scope (n=8,16,32) hits:",sum(counts[n] for n in (8,16,32)))
print("VIOLATIONS:",len(viol))
for v in viol[:20]: print("   d=%d n=%d  Phi|A-D=%s Phi|B=%s n|s=%s  s=%d"%v)
