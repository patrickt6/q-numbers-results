"""
Tests of the candidate GENERAL law behind T5, for arbitrary elements of
PSL_q(2,Z), not only Pell automorphs:

  LAW-G   gcd(C, A-D) = gcd(C, B) up to units of Q[q,1/q]
  CONG    C | (A - D) - (q-1) B   in Q[q, 1/q]        (exact congruence)
  CONG2   the S-companion: C | q(A - D) + (q-1) B     (alternative sign)
  TRIPLE  gcd(A-D, B) = gcd(A-D, C) = gcd(B, C)       (stronger speculation)

Populations:
  1. random positive words  M = prod_i R^{c_i} S, c_i in [1, cmax]
  2. random signed words    c_i in [-cmax, cmax] \ {0}
  3. Pell automorphs (the T5 case)
  4. automorphs of a + sqrt d

Also verifies the column interpretation: M_q . 0 = B/D is the q-deformation
of the rational M.0 (up to monomial), by cross-multiplying against an
independently generated matrix with the same value of M.0 at q=1.
"""
import sys
import random

sys.path.insert(0, '<path>')
from fastlam import lam_q_fast, rho_fast, p_add, p_mul  # noqa
sys.path.insert(0, '<path>')
from proof_verification import sl2_word  # noqa
from qcore import pell_plus1  # noqa

import sympy as sp
q = sp.symbols('q')


def sub(p1, p2):
    return p_add(p1, p2, scale=-1)


def to_poly(pdict):
    """dict -> sympy Poly in q, normalized so min exponent is 0."""
    if not pdict:
        return sp.Poly(0, q)
    lo = min(pdict)
    return sp.Poly({e - lo: c for e, c in pdict.items()}, q)


def monic_gcd(p1, p2):
    """gcd of two dict-polys over Q[q], monic, with q-powers stripped."""
    P1, P2 = to_poly(p1), to_poly(p2)
    g = sp.gcd(P1, P2)
    g = sp.Poly(g, q)
    # strip q factors
    while g.eval(0) == 0 and g.degree() > 0:
        g = sp.Poly(sp.div(g.as_expr(), q, q)[0], q)
    return g.monic()

def divides_poly(g, f):
    """g | f in Q[q] after q-power stripping. f zero counts divisible."""
    F, G = to_poly(f), to_poly(g)
    if F.is_zero:
        return True
    if G.is_zero:
        return False
    return sp.rem(F, G, q).is_zero


def qshift(p, k):
    return {e + k: c for e, c in p.items()}


def tests_for(A, B, C, D, tag, stats):
    if not C:
        return
    f = sub(A, D)
    g1 = monic_gcd(C, f)
    g2 = monic_gcd(C, B)
    lawg = (g1 == g2)
    # CONG: C | (A-D) - (q-1) B, computed in Laurent dicts: (q-1)B = qshift(B,1) - B
    qm1B = sub(qshift(B, 1), B)
    cong = divides_poly(C, sub(f, qm1B))
    cong2 = divides_poly(C, p_add(qshift(f, 1), qm1B))
    g3 = monic_gcd(f, B)
    triple = (g1 == g2 == g3)
    stats.setdefault(tag, {'n': 0, 'lawg': 0, 'cong': 0, 'cong2': 0,
                           'triple': 0, 'lawg_fail': [], 'cong_fail': []})
    st = stats[tag]
    st['n'] += 1
    st['lawg'] += lawg
    st['cong'] += cong
    st['cong2'] += cong2
    st['triple'] += triple
    if not lawg and len(st['lawg_fail']) < 5:
        st['lawg_fail'].append((g1.as_expr(), g2.as_expr()))
    if not cong and len(st['cong_fail']) < 3:
        st['cong_fail'].append(True)


def main():
    random.seed(20260723)
    stats = {}

    # population 1 and 2: random words
    for trial in range(400):
        L = random.randint(1, 7)
        wpos = [x for c in [random.randint(1, 6) for _ in range(L)]
                for x in [('R', c), ('S', 0)]]
        A, B, C, D = rho_fast(wpos)
        tests_for(A, B, C, D, 'random positive word', stats)

    for trial in range(400):
        L = random.randint(1, 7)
        cs = []
        for _ in range(L):
            c = 0
            while c == 0:
                c = random.randint(-5, 5)
            cs.append(c)
        wsig = [x for c in cs for x in [('R', c), ('S', 0)]]
        A, B, C, D = rho_fast(wsig)
        tests_for(A, B, C, D, 'random signed word', stats)

    # population 3: Pell automorphs
    for d in range(2, 200):
        r = sp.integer_nthroot(d, 2)[0]
        if r * r == d:
            continue
        (_, _), (A, B, C, D) = lam_q_fast(d)
        tests_for(A, B, C, D, 'Pell automorph', stats)

    # population 4: automorphs of a + sqrt d
    for d in range(2, 40):
        rr = sp.integer_nthroot(d, 2)[0]
        if rr * rr == d:
            continue
        r, s = pell_plus1(d)
        for a in range(1, 4):
            M = [[r + a * s, (d - a * a) * s], [s, r - a * s]]
            if M[0][1] <= 0:
                continue
            try:
                w = sl2_word(sp.Matrix(M))
            except Exception:
                continue
            A, B, C, D = rho_fast(w)
            tests_for(A, B, C, D, 'a+sqrt(d) automorph', stats)

    for tag, st in stats.items():
        print(f"{tag}: n={st['n']}  LAW-G {st['lawg']}  CONG {st['cong']}  "
              f"CONG2 {st['cong2']}  TRIPLE {st['triple']}")
        for gg in st['lawg_fail']:
            print('   LAW-G fail:', gg)

    # column check: B/D is the q-deformation of M.0 (up to monomial)
    print('\ncolumn check: B/D ~ q^j * [M.0]_q')
    okc = 0
    tot = 0
    for d in [2, 3, 5, 6, 7, 10, 13, 19]:
        (r, s), (A, B, C, D) = lam_q_fast(d)
        p, u = d * s, r          # Lambda.0 = ds/r
        g, x, y = sp.gcdex(p, u)
        # find p'' , u'' with p*u'' - p''*u = 1: from x*p + y*u = 1
        # take V = [[p, -y],[u, x]] : det = p x + y u = 1
        V = sp.Matrix([[p, -y], [u, x]])
        assert V.det() == 1
        wv = sl2_word(V)
        Av, Bv, Cv, Dv = rho_fast(wv)
        # compare B/D with Av/Cv up to monomial: B*Cv - eps*q^j*D*Av = 0
        lhs = p_mul(B, Cv)
        rhs = p_mul(D, Av)
        # test proportionality by monomial: lhs = eps * q^j * rhs
        if lhs and rhs:
            j = min(lhs) - min(rhs)
            e0 = min(lhs)
            c_l = lhs[e0]
            c_r = rhs[e0 - j]
            eps = sp.Rational(c_l, c_r)
            ok = (sub(lhs, {e + j: eps * c for e, c in rhs.items()}) == {})
        else:
            ok = False
        okc += bool(ok)
        tot += 1
        print(f'  d={d}: B/D matches q^{{{j}}}*{eps}*[ds/r]_q : {ok}')
    print(f'column check: {okc}/{tot}')


if __name__ == '__main__':
    main()
