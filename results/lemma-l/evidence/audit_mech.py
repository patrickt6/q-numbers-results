import sys, math
sys.path.insert(0,"<path>")
from downward_closure import phi_divides, v_p, PHI_COEFFS, TEST_SET
import fastlam

# hypothesis H: Phi_{p^a} | C  <=>  v_p(s) >= a
pairs=[(2,1),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3),(3,4),(5,1),(5,2),(5,3),(7,1),(7,2),(11,1),(11,2),(13,1)]
fwd_fail=[]; bwd_fail=[]; ntest=0
for d in range(2,501):
    a0=math.isqrt(d)
    if a0*a0==d: continue
    ntest+=1
    (r,s),(A,B,C,D)=fastlam.lam_q_fast(d)
    for (p,a) in pairs:
        n=p**a
        if n not in PHI_COEFFS: continue
        div=phi_divides(C,n); vp=v_p(s,p)
        if div and not (vp>=a): fwd_fail.append((d,p,a,vp))
        if (vp>=a) and not div: bwd_fail.append((d,p,a,vp))
print("d tested:",ntest)
print("Phi_{p^a}|C but v_p(s)<a :",len(fwd_fail), fwd_fail[:10])
print("v_p(s)>=a but Phi_{p^a} does NOT divide C :",len(bwd_fail), bwd_fail[:15])
