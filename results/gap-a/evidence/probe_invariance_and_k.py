"""Attack 3, follow-ups.

(1) Invariance of r under automorph power: recompute r(x) from M and from M^2,
    M^3 for the golden ratio and for 1+sqrt(2). r(x) must not change, while the
    per-automorph corner a/c and (gamma, D) do change.
(2) Trace-zero controls: r must be exactly 1 (k = 0 and palindromic).
(3) Residual exponent k on nonzero-trace cases: tabulate mu, gamma, D, k and the
    corner data, to see whether k has a visible closed form and whether k = 0 can
    coincide with nonzero trace among palindromic corners (it must not, if Gap A
    holds).
"""
import sys
import sympy as sp

T3_OPUS = (
    "<path>"
    "2026-07-21-next-steps/problems/T3-quadratic-conjecture/attempts/opus"
)
sys.path.insert(0, T3_OPUS)
import qperiod as qp  # noqa: E402

q = sp.symbols("q")


def data(M):
    a, c = M[0][0], M[1][0]
    d = M[1][1]
    Mq = qp.rho_q(M)
    A, B, C, D_ = Mq
    detX = qp.p_add(qp.p_mul(A, D_), qp.p_mul(B, C), scale=-1)
    mu = next(iter(detX))
    gamma = min(C)
    D = max(C) - gamma
    coeffs = [C.get(gamma + i, 0) for i in range(D + 1)]
    palin = coeffs == coeffs[::-1]
    C_expr = qp.ldict_to_expr(C)
    r = sp.cancel(sp.simplify(q**(mu + 1) * C_expr.subs(q, 1 / q) / C_expr))
    k = mu + 1 - 2 * gamma - D
    return dict(a=a, c=c, d=d, trace=a + d, mu=mu, gamma=gamma, D=D, k=k,
               palin=palin, r=r, cong=pow(a, 2, c) if c else 0)


def matpow(M, n):
    R = [[1, 0], [0, 1]]
    for _ in range(n):
        R = qp.mat_mul(R, M)
    return R


print("=== (1) invariance of r under M -> M^n ===")
for name, M in [("phi", [[2, 1], [1, 1]]), ("1+sqrt2", [[5, 2], [2, 1]])]:
    print(f"  {name}:")
    for n in (1, 2, 3):
        Mn = matpow(M, n)
        di = data(Mn)
        print(f"    M^{n} = {Mn}  a/c={di['a']}/{di['c']} "
              f"trace={di['trace']} mu={di['mu']} gamma={di['gamma']} "
              f"D={di['D']} k={di['k']} palin={di['palin']} "
              f"cong={di['cong']} r={di['r']}")

print("=== (2) trace-zero controls (must give r=1, k=0, palin) ===")
# automorphs of pure/scaled surds with a = d' (trace-zero family)
tz = [
    ("sqrt2", [[3, 4], [2, 3]]),    # t^2-2u^2=1, (t,u)=(3,2), a=d'=3
    ("sqrt3", [[2, 3], [1, 2]]),    # (t,u)=(2,1), a=d'=2
    ("sqrt5", [[9, 20], [4, 9]]),   # (t,u)=(9,4), a=d'=9
]
for name, M in tz:
    di = data(M)
    print(f"  {name}: M={M} a=d'? {M[0][0]==M[1][1]} trace={di['trace']} "
          f"mu={di['mu']} k={di['k']} palin={di['palin']} r={di['r']}")

print("=== (3) residual k on the nonzero-trace named cases ===")
named = [
    ("(1+sqrt5)/2", [[2, 1], [1, 1]]),
    ("1+sqrt2", [[5, 2], [2, 1]]),
    ("2+sqrt2", [[7, -4], [2, -1]]),
    ("(3+sqrt13)/2", [[10, 3], [3, 1]]),
    ("3+sqrt3", [[5, -6], [1, -1]]),
    ("(1+sqrt2)/2", [[5, 1], [4, 1]]),
    ("(1+sqrt3)/2", [[3, 1], [2, 1]]),
    ("(2+sqrt7)/3", [[14, 3], [9, 2]]),
    ("(1+sqrt13)/3", [[829, 720], [540, 469]]),
]
print(f"  {'x':16}{'a/c':10}{'trace':7}{'mu':5}{'gamma':7}{'D':5}"
      f"{'k':5}{'palin':7}{'cong':6}")
for name, M in named:
    di = data(M)
    print(f"  {name:16}{str(di['a'])+'/'+str(di['c']):10}{di['trace']:<7}"
          f"{di['mu']:<5}{di['gamma']:<7}{di['D']:<5}{di['k']:<5}"
          f"{str(di['palin']):7}{di['cong']:<6}")
