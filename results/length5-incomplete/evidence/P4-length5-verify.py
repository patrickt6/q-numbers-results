#!/usr/bin/env python3
"""Independent exact verification of the length-5 Phi_k | S_5 classification."""
from itertools import product

def ptrim(a):
    while a and a[-1] == 0:
        a.pop()
    return a

def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        if u:
            for j, v in enumerate(b):
                if v:
                    out[i + j] += u * v
    return ptrim(out)

def pdivmod(a, b):
    a = a[:]
    lb = b[-1]
    q = [0] * max(0, len(a) - len(b) + 1)
    while len(a) >= len(b) and a:
        d = len(a) - len(b)
        c = a[-1] // lb
        assert c * lb == a[-1], "non-exact leading division"
        q[d] = c
        for i, v in enumerate(b):
            a[i + d] -= c * v
        ptrim(a)
    return ptrim(q), a

_PHI = {}
def phi(k):
    if k in _PHI:
        return _PHI[k]
    num = [-1] + [0] * (k - 1) + [1]
    for d in range(1, k):
        if k % d == 0:
            q, r = pdivmod(num, phi(d))
            assert r == [], "cyclotomic division must be exact"
            num = q
    _PHI[k] = num
    return num

class Ring:
    def __init__(self, k):
        self.k = k
        self.f = phi(k)
        self.d = len(self.f) - 1
    def red(self, a):
        _, r = pdivmod(a[:], self.f)
        return tuple(r + [0] * (self.d - len(r)))
    def mul(self, a, b):
        return self.red(list(pmul(list(a), list(b))))
    def sub(self, a, b):
        return tuple(u - v for u, v in zip(a, b))
    def bracket(self, c):
        return self.red([1] * (c % self.k))
    def qpow(self, e):
        return self.red([0] * (e % self.k) + [1])
    def one(self):
        return self.red([1])
    def zero(self):
        return tuple([0] * self.d)

def S_last(R, cs, variant=False):
    Sprev = R.zero(); S = R.one(); prev_c = None
    for c in cs:
        if prev_c is None:
            Snew = R.bracket(c)
        else:
            e = c if variant else prev_c
            Snew = R.sub(R.mul(R.bracket(c), S), R.mul(R.qpow(e - 1), Sprev))
        Sprev, S, prev_c = S, Snew, c
    return S

def solutions(k, n, variant=False):
    R = Ring(k)
    return set(cs for cs in product(range(k), repeat=n - 1)
               if all(v == 0 for v in S_last(R, cs, variant)))

def fam_defs():
    F = {}
    F['1'] = lambda c2,c3,c4,c5,k,e: c2%k==0 and c4%k==e%k and c5%k==e%k
    F['2'] = lambda c2,c3,c4,c5,k,e: c3%k==0 and c4%k==0 and c2%k==e%k and c5%k==e%k
    F['3'] = lambda c2,c3,c4,c5,k,e: c5%k==0 and c2%k==e%k and c3%k==e%k
    F['4'] = lambda c2,c3,c4,c5,k,e: c3%k==0 and c5%k==e%k and (c2+c4)%k==e%k
    F['5'] = lambda c2,c3,c4,c5,k,e: c2%k==e%k and (c3+c5)%k==e%k and c4%k==0
    F['6'] = lambda c2,c3,c4,c5,k,e: c3%k==e%k and c5%k==e%k and c2%k==(2*e)%k and c4%k==(3*e)%k
    F['7'] = lambda c2,c3,c4,c5,k,e: c4%k==e%k and c3%k==(2*e)%k and c2%k==(2*e)%k and c5%k==(3*e)%k
    F['8'] = lambda c2,c3,c4,c5,k,e: c4%k==(2*e)%k and c5%k==(2*e)%k and c3%k==e%k and c2%k==(3*e)%k
    F['9'] = lambda c2,c3,c4,c5,k,e: c3%k==e%k and c4%k==e%k and (c2+c5)%k==e%k
    F['C5'] = lambda c2,c3,c4,c5,k,e: c2%k==e%k and c3%k==(2*e)%k and c4%k==(2*e)%k and c5%k==e%k
    F['D5'] = lambda c2,c3,c4,c5,k,e: c2%k==e%k and c3%k==(3*e)%k and c4%k==e%k and c5%k==(2*e)%k
    return F

def cover_set(k, names, signs):
    F = fam_defs(); out = set()
    for w in product(range(k), repeat=4):
        for nm in names:
            if any(F[nm](*w, k, e) for e in signs[nm]):
                out.add(w); break
    return out
