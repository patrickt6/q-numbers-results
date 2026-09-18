"""Independent MGO q-rational engine + HJ continuant machinery for auditing P4."""
import sympy as sp
from sympy import Poly, cyclotomic_poly, factorint, gcd, symbols, simplify, cancel, fraction, Rational

q = symbols('q')


def qint(c):
    # [c]_q = 1+q+...+q^{c-1}, works for c>=0; c can be with 1/q via subs
    if c == 0:
        return sp.Integer(0)
    return sum(q**i for i in range(c))


def reg_cf(a, d):
    """Regular continued fraction of a/d in (0,1): returns word [c0=0, c1, c2, ...]."""
    # a/d in (0,1)
    assert 0 < a < d
    x = Rational(a, d)
    w = []
    # produce [c0; c1, c2, ...]; c0 = 0
    while True:
        fl = int(sp.floor(x))
        w.append(fl)
        frac = x - fl
        if frac == 0:
            break
        x = 1 / frac
    return w


def mgo_S(a, d):
    """MGO q-rational [a/d]_q via block matrix product; return reduced denominator polynomial S (primitive, S(0)!=0, positive lead) and S(1)."""
    word = reg_cf(a, d)
    # ensure even length word (leading 0 included). Use identity [.., c_n] -> [.., c_n-1, 1] if odd length.
    if len(word) % 2 == 1:
        # split last term
        last = word[-1]
        if last >= 2:
            word = word[:-1] + [last - 1, 1]
        else:  # last == 1
            # [..,c,1] -> [..,c+1]
            word = word[:-2] + [word[-2] + 1]
            if len(word) % 2 == 1:
                # fallback: append trick differently
                word = word[:-1] + [word[-1] - 1, 1]
    assert len(word) % 2 == 0, (a, d, word)
    M = sp.eye(2)
    for i, c in enumerate(word):
        if i % 2 == 0:
            B = sp.Matrix([[qint(c), q**c], [1, 0]])
        else:
            # [c]_{1/q} = (1 + 1/q + ... + 1/q^{c-1}); q^{-c}
            cq = sum(q**(-j) for j in range(c)) if c > 0 else sp.Integer(0)
            B = sp.Matrix([[cq, q**(-c)], [1, 0]])
        M = M * B
    R = M[0, 0]
    S = M[1, 0]
    val = cancel(R / S)
    num, den = fraction(val)
    denp = Poly(sp.expand(den), q)
    # strip q factors, make primitive, positive leading, positive constant
    # remove q^k
    coeffs = denp.all_coeffs()
    # trailing zeros -> factor q
    p = denp
    while p.eval(0) == 0:
        p = Poly(sp.cancel(p.as_expr() / q), q)
    # primitive part
    p = p.primitive()[1]
    if p.LC() < 0:
        p = Poly(-p.as_expr(), q)
    return p


def phi(m):
    return Poly(cyclotomic_poly(m, q), q)


def factor_cyclo(Spoly):
    """Return dict {m: mult} if Spoly is a product of cyclotomics, else None."""
    remaining = Spoly
    result = {}
    if remaining.degree() == 0:
        return result
    # try dividing by cyclotomic factors up to some bound
    bound = remaining.degree() + 2
    changed = True
    # We factor over rationals via sympy then map to cyclotomic indices.
    fac = sp.factor_list(remaining.as_expr(), q)
    const, factors = fac
    out = {}
    for f, mult in factors:
        fp = Poly(f, q)
        # identify cyclotomic index
        found = None
        for m in range(1, 400):
            if Poly(cyclotomic_poly(m, q), q) == fp:
                found = m
                break
        if found is None:
            return None
        out[found] = out.get(found, 0) + mult
    return out


def neg_cf_gt1(y):
    """Negative (HJ) continued fraction of rational y>1: [[b1,b2,...]], all b_i>=2, y=b1-1/(b2-1/...)."""
    b = []
    while True:
        c = int(sp.ceiling(y))
        b.append(c)
        rem = c - y  # = 1/(next)
        if rem == 0:
            break
        y = 1 / rem
    return b


def hj_tail(a, d):
    """Tail w=(c2,...,ck) of HJ expansion of a/d in (0,1) with c1=1.
    x = 1 - 1/(rest), rest = 1/(1-x) = d/(d-a); w = neg_cf of d/(d-a)."""
    y = Rational(d, d - a)
    return neg_cf_gt1(y)


def continuant(word):
    """Classical HJ continuant K with recursion K_j = c_j K_{j-1} - K_{j-2}; K(empty)=1, K_{-1}=0."""
    Km1 = 0  # K_{-1}
    K0 = 1   # K_0 (empty)
    if not word:
        return 1
    prev, cur = K0, None
    Kprev2, Kprev1 = 0, 1
    for c in word:
        Kcur = c * Kprev1 - Kprev2
        Kprev2, Kprev1 = Kprev1, Kcur
    return Kprev1


if __name__ == '__main__':
    # sanity: [2/3]_q denom = 1+q+q^2
    print('S(2/3) =', mgo_S(2, 3).as_expr(), 'expect 1+q+q^2')
    # difference of squares anchor: x=m/(m^2-1), reduced denom = [m-1]_q[m+1]_q
    print('--- difference-of-squares anchor ---')
    for m in range(2, 25):
        d = m * m - 1
        a = m
        S = mgo_S(a, d)
        expect = Poly(sp.expand(qint(m - 1) * qint(m + 1)), q)
        expect = expect.primitive()[1]
        ok = (S == expect)
        assert S.eval(1) == d, (m, S.eval(1), d)
        print(f'm={m:3d} d={d:5d} S(1)={S.eval(1)} match_expect={ok}')
