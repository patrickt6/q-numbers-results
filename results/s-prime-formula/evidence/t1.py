import sys, sympy as sp, random
sys.path.insert(0, "<path>")
from harness import NS, q

def ainv_of(a, d):
    return int(sp.mod_inverse(a, d)) % d  # in (0,d)

print("=== TARGET 1: 2 S'(1) = d*degS + (ainv - a) ===")
Sp = S = None
bad = 0; tested = 0
random.seed(1)
pairs = set()
while len(pairs) < 20:
    d = random.randint(3, 100); a = random.randint(1, d-1)
    if sp.gcd(a, d) == 1:
        pairs.add((a, d))
for (a, d) in sorted(pairs):
    N, S = NS(a, d)
    Sder = S.diff(q)
    Sp1 = Sder.eval(1)
    degS = S.degree()
    ainv = ainv_of(a, d)
    lhs = 2*Sp1
    rhs = d*degS + (ainv - a)
    ok = (lhs == rhs)
    tested += 1
    if not ok:
        bad += 1
        print(f"  FAIL a/d={a}/{d}: 2S'={lhs} d*degS+ainv-a={rhs} (ainv={ainv})")
print(f"  tested={tested} bad={bad}")

# also verify the intermediate det-identity claim: s_{k-1} = d - ainv, in (0,d)
# s_{k-1} = S_{k-1}(1) where S_{k-1} is second-to-last convergent denom.
# We can't easily get that from value alone; skip (structural). Check C1/C2/C3.

print("\n=== C1: S'(1) = d*degS/2  iff  a^2 = 1 mod d ===")
bad = 0
for (a, d) in sorted(pairs):
    N, S = NS(a, d)
    Sp1 = S.diff(q).eval(1); degS = S.degree()
    lhs = sp.Rational(2*Sp1, 1) == sp.Rational(d*degS, 1)  # S'(1)=d degS/2  <=> 2S'(1)=d degS
    cond = (pow(a, 2, d) == 1 % d)
    if bool(lhs) != bool(cond):
        bad += 1; print(f"  FAIL a/d={a}/{d}: 2S'={2*Sp1} ddegS={d*degS} a^2mod d={pow(a,2,d)}")
print(f"  bad={bad}")

print("\n=== C1 palindrome: palindromic S => S'(1)/S(1)=degS/2 ===")
# find cases where S is palindromic and check
bad=0; found=0
for d in range(3, 60):
    for a in range(1, d):
        if sp.gcd(a,d)!=1: continue
        N,S = NS(a,d)
        coeffs = S.all_coeffs()
        if coeffs == coeffs[::-1]:
            found+=1
            Sp1=S.diff(q).eval(1); S1=S.eval(1); degS=S.degree()
            if sp.Rational(Sp1,S1) != sp.Rational(degS,2):
                bad+=1; print(f"  FAIL palindrome a/d={a}/{d}")
print(f"  palindromic cases found={found} bad={bad}")

print("\n=== C2: Phi_p | S (p odd prime) => a = +-1 mod p ===")
bad=0; found=0
for d in range(3, 80):
    for a in range(1, d):
        if sp.gcd(a,d)!=1: continue
        N,S = NS(a,d)
        for p in [3,5,7,11,13]:
            Phi = sp.Poly(sp.cyclotomic_poly(p, q), q)
            r = S.rem(Phi)
            if r.is_zero:
                found+=1
                if not (a % p == 1 or a % p == p-1):
                    bad+=1; print(f"  FAIL C2 a/d={a}/{d} p={p}: a mod p={a%p}")
print(f"  C2 Phi_p|S cases found={found} bad={bad}")

print("\n=== C3: Phi_{p^j}|S => a^2 = 1 mod p ===")
bad=0; found=0
for d in range(3, 120):
    for a in range(1, d):
        if sp.gcd(a,d)!=1: continue
        N,S = NS(a,d)
        for (p,j,pj) in [(3,2,9),(2,2,4),(2,3,8),(3,1,3),(5,1,5),(5,2,25)]:
            Phi = sp.Poly(sp.cyclotomic_poly(pj, q), q)
            if S.degree() < Phi.degree(): continue
            r = S.rem(Phi)
            if r.is_zero:
                found+=1
                if pow(a,2,p)!=1%p:
                    bad+=1; print(f"  FAIL C3 a/d={a}/{d} p^j={pj}: a^2 mod p={pow(a,2,p)}")
print(f"  C3 cases found={found} bad={bad}")
