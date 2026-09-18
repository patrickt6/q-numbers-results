import sympy as sp
from sympy import cyclotomic_poly, Poly
from engine import mgo_S, hj_tail, continuant, q
from sweep import mixed_root

def inv_mod(a, d):
    return pow(a, -1, d)

def deg_from_tail(w):
    return sum(c - 1 for c in w)

def is_palindrome(w):
    return w == w[::-1]

def split_check(w):
    """Return dict of splitting-identity data. w is the tail (palindrome expected)."""
    d = continuant(w)
    L = len(w)
    info = {'w': w, 'len': L, 'd': d, 'palindrome': is_palindrome(w)}
    if L % 2 == 1:
        # (u, c, ubar), u = first (L-1)/2
        h = (L - 1) // 2
        u = w[:h]
        c = w[h]
        ubar = w[h+1:]
        P = continuant(u)
        Qp = continuant(u[:-1]) if u else 1   # K(u minus last); empty->1
        info.update(parity='odd', u=u, c=c, P=P, Qp=Qp,
                    identity=P*(c*P - 2*Qp), id_ok=(P*(c*P-2*Qp)==d),
                    ubar_ok=(ubar==u[::-1]))
    else:
        h = L // 2
        u = w[:h]
        ubar = w[h:]
        P = continuant(u)
        Qp = continuant(u[:-1]) if u else 1
        info.update(parity='even', u=u, P=P, Qp=Qp,
                    identity=(P-Qp)*(P+Qp), id_ok=((P-Qp)*(P+Qp)==d),
                    ubar_ok=(ubar==u[::-1]))
    return info

print("="*70)
print("PROBE A: reversal law  (tail of a/d palindrome  <=>  a^2 = 1 mod d)")
print("="*70)
import random
random.seed(1)
bad = 0
for trial in range(300):
    d = random.randint(5, 500)
    a = random.randint(1, d-1)
    if sp.gcd(a, d) != 1:
        continue
    w = hj_tail(a, d)
    assert continuant(w) == d, (a, d, w, continuant(w))
    pal = is_palindrome(w)
    sq1 = (a*a % d == 1)
    # reversal -> ainv
    wbar = w[::-1]
    # numerator of fraction with tail wbar = d - K(wbar minus first)
    num_rev = d - continuant(wbar[1:]) if wbar else None
    ainv = inv_mod(a, d)
    if pal != sq1:
        bad += 1
        print("  MISMATCH pal vs a^2=1:", a, d, w)
    if num_rev is not None and num_rev != ainv:
        bad += 1
        print("  MISMATCH reversal numerator:", a, d, "got", num_rev, "want ainv", ainv)
print(f"reversal law: {bad} mismatches over trials")

print()
print("="*70)
print("PROBE B: 5 concrete pairs (1 twin, 4 non-twin) - mixed root a0")
print("="*70)
probe_pairs = [(5,7,'TWIN'), (3,7,'nontwin'), (3,11,'nontwin'), (5,11,'nontwin'), (7,11,'nontwin')]
for (p, pp, tag) in probe_pairs:
    d = p*pp
    a0 = mixed_root(p, pp)
    w = hj_tail(a0, d)
    S = mgo_S(a0, d)
    degS = S.degree()
    target = Poly(sp.expand(cyclotomic_poly(p,q)*cyclotomic_poly(pp,q)), q).primitive()[1]
    info = split_check(w)
    print(f"\n({p},{pp}) {tag}  d={d}  a0={a0}  (p+1={p+1})")
    print(f"  tail w = {w}   palindrome={info['palindrome']}  a0^2%d={a0*a0%d}")
    print(f"  deg S = {degS};  sum(c_i-1) = {deg_from_tail(w)};  p+p'-2 = {p+pp-2}")
    print(f"  S == Phi_p*Phi_p' : {S==target}")
    print(f"  parity={info['parity']} u={info['u']} P=K(u)={info['P']} Q'=K(u-last)={info['Qp']}")
    if info['parity']=='odd':
        print(f"    c={info['c']}  P(cP-2Q')={info['identity']}  == d ? {info['id_ok']}   ubar_ok={info['ubar_ok']}")
        print(f"    P==p ? {info['P']==p}   (factor-matching claim)")
    else:
        print(f"    (P-Q')(P+Q')={info['identity']}  == d ? {info['id_ok']}   ubar_ok={info['ubar_ok']}")
        print(f"    P==(p+p')/2 ? {info['P']==(p+pp)//2}  Q'==(p'-p)/2 ? {info['Qp']==(pp-p)//2}")

print()
print("="*70)
print("PROBE C: p=3 consistency with independently-proved HJ expansions")
print("  p'=6j-1 -> [[1,2,2,2j+1,2,2]] ; p'=6j+1 -> [[1,3,2j+1,3]] ; deg S = 2j+4")
print("="*70)
for pp in [5,7,11,13,17,19,23,29,31]:
    if pp % 6 == 5:  # 6j-1
        j = (pp+1)//6
        pred = [2,2,2*j+1,2,2]
    else:            # 6j+1
        j = (pp-1)//6
        pred = [3,2*j+1,3]
    d = 3*pp
    a0 = mixed_root(3, pp)
    w = hj_tail(a0, d)
    S = mgo_S(a0, d)
    print(f"p'={pp:3d} (6j{'+1' if pp%6==1 else '-1'}, j={j}) a0={a0}: tail={w}")
    print(f"      predicted tail={pred}  match={w==pred}  degS={S.degree()} pred 2j+4={2*j+4} match={S.degree()==2*j+4}"
          f"  twin={'YES' if pp==5 else 'no'}")
