import sys
sys.path.insert(0, '<path>')
import sympy as sp
from proof_verification import lam_q
from qcore import q, pell_plus1

def get(d):
    (r,s), Lq = lam_q(d)
    A,B,C,D = Lq[0,0],Lq[0,1],Lq[1,0],Lq[1,1]
    f = sp.cancel(A-D)
    num,den = sp.fraction(sp.together(f))
    fpoly = sp.Poly(sp.expand(num), q)
    Cnum,_ = sp.fraction(sp.together(sp.cancel(C)))
    Cpoly = sp.Poly(sp.expand(Cnum), q)
    return r,s,fpoly,Cpoly

def gamma(fpoly, k):
    # gamma_k = f^{(k)}(1)/k!  via k-fold derivative (k small)
    e = fpoly.as_expr()
    for _ in range(k):
        e = sp.diff(e, q)
    val = e.subs(q,1)
    return sp.Rational(val, sp.factorial(k))

def phi_div(Cpoly, n):
    Phi = sp.Poly(sp.cyclotomic_poly(n, q), q)
    _,R = sp.div(Cpoly, Phi)
    return R.is_zero

print("=== Item (5): d=79, Phi_9|C, J(3,2): 3|gamma_k k=1,2,3 ===", flush=True)
r,s,fpoly,Cpoly = get(79)
print(f"d=79 pell r={r} s={s}  3|s?{s%3==0} 9|s?{s%9==0}  Phi_9|C?{phi_div(Cpoly,9)}  deg f={fpoly.degree()}", flush=True)
for k in [1,2,3,4]:
    gk = gamma(fpoly,k)
    v3 = sp.factorint(abs(gk)).get(3,0) if gk!=0 else 'inf'
    print(f"  gamma_{k}={gk}  v_3={v3}  3|gamma_{k}:{gk%3==0}", flush=True)

print("\n=== Item (5b): Phi_8|C case, small-Pell only, J(2,3): 2|gamma_k k<=4 ===", flush=True)
found=0
for d in range(2,150):
    ds=int(d**0.5)
    if ds*ds==d: continue
    try:
        r,s = pell_plus1(d)
    except Exception:
        continue
    if s>500 or r>5000:   # skip huge-Pell d that blow up rho
        continue
    try:
        r,s,fpoly,Cpoly = get(d)
    except Exception:
        continue
    if phi_div(Cpoly,8):
        gs=[gamma(fpoly,k) for k in range(1,6)]
        ok=all(g%2==0 for g in gs[:4])
        print(f"d={d} Phi_8|C 8|s?{s%8==0} gammas1..5={gs} 2|gamma_k k<=4:{ok} gamma5%2={gs[4]%2}", flush=True)
        found+=1
        if found>=3: break
if not found:
    print("no small-Pell Phi_8 case under 150", flush=True)
print("ALLDONE", flush=True)
