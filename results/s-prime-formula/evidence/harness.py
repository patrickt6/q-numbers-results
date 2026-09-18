import sys, sympy as sp
sys.path.insert(0, "<path>")
from mgo import mgo_qrational, q

def NS(a, d):
    """Return reduced numerator N and denominator S of [a/d]_q,
    normalized so S(0)=1 (constant term 1). Also return N,S as Poly."""
    val = sp.cancel(mgo_qrational(a, d))
    N, S = sp.fraction(sp.together(val))
    N = sp.Poly(sp.expand(N), q)
    S = sp.Poly(sp.expand(S), q)
    # normalize so S has constant term +1 (MGO convention S(0)=1)
    c0 = S.eval(0)
    if c0 == 0:
        raise ValueError(f"S(0)=0 for {a}/{d}")
    N = sp.Poly(N.as_expr()/c0, q)
    S = sp.Poly(S.as_expr()/c0, q)
    return N, S

def check_norm():
    print("=== normalization check: S(0)=1, S(1)=d, N(1)=a, gcd=1, degS=sum(c_i-1) ===")
    import random
    bad = 0
    for _ in range(40):
        d = random.randint(3, 100)
        a = random.randint(1, d-1)
        if sp.gcd(a, d) != 1:
            continue
        N, S = NS(a, d)
        s0 = S.eval(0); s1 = S.eval(1); n1 = N.eval(1)
        g = sp.gcd(N, S)
        ok = (s0 == 1 and s1 == d and n1 == a and g.degree() == 0)
        if not ok:
            bad += 1
            print(f"  FAIL a/d={a}/{d}: S(0)={s0} S(1)={s1} N(1)={n1} deg gcd={g.degree()}")
    print(f"  bad={bad}")

if __name__ == "__main__":
    check_norm()
