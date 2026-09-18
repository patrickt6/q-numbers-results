import sympy as sp
from sympy import primerange, isprime
from engine import mgo_S, phi, factor_cyclo, hj_tail, continuant, q, Poly, cyclotomic_poly

def mixed_root(p, pp):
    # a0 = 1 mod p, -1 mod p'
    d = p * pp
    for a in range(1, d):
        if a % p == 1 and a % pp == pp - 1:
            return a
    return None

primes = list(primerange(3, 1000))
pairs = []
LIMIT = 1000
for i, p in enumerate(primes):
    for pp in primes[i+1:]:
        if p * pp <= LIMIT:
            pairs.append((p, pp))

print(f"# semiprime pairs d<= {LIMIT}: {len(pairs)}")
target_hits = []   # (p,pp,a,tag) where S == Phi_p Phi_pp
anomalies = []
for (p, pp) in pairs:
    d = p * pp
    a0 = mixed_root(p, pp)
    cands = {'a=1': 1, 'a=d-1': d-1, 'a0': a0, 'd-a0': d - a0}
    target = Poly(sp.expand(cyclotomic_poly(p, q) * cyclotomic_poly(pp, q)), q).primitive()[1]
    Svals = {}
    for tag, a in cands.items():
        S = mgo_S(a, d)
        Svals[tag] = S
        if S == target:
            target_hits.append((p, pp, tag, a))
    # S identical at both mixed roots?
    if Svals['a0'] != Svals['d-a0']:
        anomalies.append(('mixed-mismatch', p, pp))
    twin = (pp == p + 2)
    hit_mixed = (Svals['a0'] == target)
    if twin and not hit_mixed:
        anomalies.append(('twin-no-hit', p, pp))
    if (not twin) and hit_mixed:
        anomalies.append(('nontwin-hit', p, pp))
    # witness check: for twin, hit should be exactly at a0 = p+1 and d-a0
    if twin:
        if a0 != p + 1:
            anomalies.append(('a0-not-p+1', p, pp, a0))

print("\n# target hits (S == Phi_p Phi_p'):")
for h in target_hits:
    print("  ", h, " twin" if h[1]==h[0]+2 else " NONTWIN")
print("\n# anomalies:", anomalies if anomalies else "NONE")

# summarize: every twin pair hits at a0 and d-a0 only
twins = [(p,pp) for (p,pp) in pairs if pp==p+2]
print(f"\n# twin pairs in range: {len(twins)} -> {twins}")
hit_pairs = set((h[0],h[1]) for h in target_hits)
print("# distinct pairs with a two-cyclotomic Phi_pPhi_p' denom:", sorted(hit_pairs))
print("# all hit pairs are twin:", all(pp==p+2 for (p,pp) in hit_pairs))
print("# all twin pairs are hit:", all((p,pp) in hit_pairs for (p,pp) in twins))
# tags of hits
from collections import defaultdict
tagmap = defaultdict(list)
for (p,pp,tag,a) in target_hits:
    tagmap[(p,pp)].append(tag)
print("# hit tags per pair (expect a0,d-a0 only):")
for k in sorted(tagmap):
    print("   ", k, tagmap[k])
