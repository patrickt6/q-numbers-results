import sys, math
sys.path.insert(0,"<path>")
from downward_closure import phi_divides, v_p
import fastlam
# KMRWY Cor 7.2 direction:  3 | s  =>  Phi_3 | S    (S = C up to monomial)
# and the elementary step:  Phi_{3^a} | C  =>  Phi_{3^a}(1)=3 divides C(1)=+-s  =>  3 | s
bad_kmrwy=[]; bad_step=[]; n3=0; n9=0
for d in range(2,1201):
    a0=math.isqrt(d)
    if a0*a0==d: continue
    (r,s),(A,B,C,D)=fastlam.lam_q_fast(d)
    p3=phi_divides(C,3); p9=phi_divides(C,9); p27=phi_divides(C,27)
    if s%3==0:
        n3+=1
        if not p3: bad_kmrwy.append((d,s))          # would refute KMRWY direction
    if p9 or p27:
        n9+=1
        if s%3!=0: bad_step.append((d,s,'3|s fails'))
        if not p3: bad_step.append((d,s,'Phi_3 missing'))
print("d<=1200 nonsquare")
print("  cases with 3|s :",n3," KMRWY (3|s => Phi_3|C) failures:",len(bad_kmrwy),bad_kmrwy[:5])
print("  cases Phi_9 or Phi_27 | C :",n9," chain-to-Phi_3 failures:",len(bad_step),bad_step[:5])
