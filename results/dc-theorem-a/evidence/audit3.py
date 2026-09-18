import sys
sys.path.insert(0, '<path>')
import sympy as sp
from proof_verification import lam_q
from qcore import q

def get(d):
    (r,s), Lq = lam_q(d)
    A,B,C,D = Lq[0,0],Lq[0,1],Lq[1,0],Lq[1,1]
    f = sp.cancel(A-D)
    num,den = sp.fraction(sp.together(f))
    # den is q-power (unit at q=1)
    fpoly = sp.Poly(sp.expand(num), q)
    Cnum,Cden = sp.fraction(sp.together(sp.cancel(C)))
    Cpoly = sp.Poly(sp.expand(Cnum), q)
    return r,s,fpoly,Cpoly,f,C

def gamma(fpoly, k):
    # Taylor coeff of f at q=1 : gamma_k = coeff of (q-1)^k = f^{(k)}(1)/k!
    # shift q->q+1, then coefficient of q^k
    P = fpoly.as_expr()
    Psh = sp.expand(P.subs(q, q+1))
    return sp.Poly(Psh, q).coeff_monomial(q**k)

def phi_divides_C(Cpoly, n):
    Phi = sp.Poly(sp.cyclotomic_poly(n, q), q)
    Q,R = sp.div(Cpoly, Phi)
    return R.is_zero

print("=== Item (5): d=79, Phi_9 | C, check 3 | gamma_1,gamma_2,gamma_3 ===")
r,s,fpoly,Cpoly,f,C = get(79)
print(f"d=79 pell r={r} s={s}  3|s? {s%3==0}  9|s? {s%9==0}")
print(f"Phi_9 | C ? {phi_divides_C(Cpoly,9)}")
for k in [1,2,3,4]:
    gk = gamma(fpoly,k)
    print(f"  gamma_{k} = {gk}   v_3 = {sp.Integer(gk).as_content_primitive()[0] if gk!=0 else 'inf'}  3|gamma_{k}: {gk%3==0}")

print("\n=== check boundary: J(3,2) claims only need k<=3=p^(a-1); confirm gamma_1,2 free via tower ===")
# also confirm the cautionary negative: d=79 vs d=85 gamma_5 not div by extra
print("\n=== Item (5b): find a Phi_8 | C case and check 2|gamma_k, k<=4 (p=2,a=3) ===")
found=0
for d in range(2,200):
    ds = sp.sqrt(d)
    if ds==int(ds): continue
    try:
        r,s,fpoly,Cpoly,f,C = get(d)
    except Exception as e:
        continue
    if phi_divides_C(Cpoly,8):
        gs=[gamma(fpoly,k) for k in range(1,6)]
        ok=all(g%2==0 for g in gs[:4])
        print(f"d={d} Phi_8|C  8|s?{s%8==0}  gammas1..5={gs}  2|gamma_k k<=4: {ok}  gamma_5%2={gs[4]%2}")
        found+=1
        if found>=3: break
if not found:
    print("no Phi_8 case under 200")
