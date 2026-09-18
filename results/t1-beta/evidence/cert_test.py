"""Apply the exact algebraic certificate to the nine known finite values and
to a set of near-rational impostors."""
import sympy as sp
from fractions import Fraction as F
from algebraic import certify_finite, laurent_expr, minimal_quadratic, q
from gtools import first_tail, g_series, qi

print("--- the nine on-axis finite values ---")
for D, ks in ((2, (1, 2, 3, 4)), (3, (1, 2, 3)), (5, (1, 2))):
    for k in ks:
        x = qi(0, k, D)
        g, lo, ld = g_series(x, 40)
        d, top = first_tail(g, lo, ld)
        h = laurent_expr({a: b for a, b in g.items() if b != 0})
        v, why = certify_finite(x, h)
        print(f"  x={k}sqrt({D}):  h = {h}   tail_in_window={d}  CERTIFIED={v}  ({why})")

print("--- controls: perturbed h must be rejected ---")
x = qi(0, 1, 3)
g, lo, ld = g_series(x, 40)
h = laurent_expr({a: b for a, b in g.items() if b != 0})
for pert in (q**7, q**3, -q**1):
    print(f"  h+({pert}):", certify_finite(x, h + pert))

print("--- impostors: points the sweep flagged finite_looking, escalation killed ---")
# rows taken from escalation-official.csv (read-only), verdict infinite
for (D, pa, qa, pb, qb) in [(2, -10, 3, 26, 11), (2, 1, 4, 7, 8), (3, 1, 2, 1, 3)]:
    x = qi(F(pa, qa), F(pb, qb), D)
    g, lo, ld = g_series(x, 40)
    d, top = first_tail(g, lo, ld)
    h = laurent_expr({a: b for a, b in g.items() if b != 0 and a < 6})
    v, why = certify_finite(x, h)
    print(f"  x={F(pa,qa)}+{F(pb,qb)}sqrt({D}): tail={d}  certify(head)={v} ({why})")
