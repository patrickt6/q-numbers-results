"""Exact check of every step in the multiplicative proof of Phi_8 | S => 8 | s.

For each recorded hit (r, s) with Phi_8 | S from evidence/phi8_search_result.json
(the hits_by_s_sample field), verify with exact integer arithmetic in sympy:

  (a) Phi_8 | S            (re-confirms the hit)
  (b) Phi_4 | S            (the input supplied by Corollary A2)
  (c) Phi_2 | S            (the step via s even, MO20 Prop 1.8)
  (d) [8]_q = Phi_2*Phi_4*Phi_8 divides S   (the multiplicative step)
  (e) 8 | s, and s == S(1)                  (the conclusion)

Also checks the identity [8]_q == Phi_2*Phi_4*Phi_8 once, symbolically.
No floating point anywhere.
"""
import json, sys
sys.path.insert(0, "<path>")
import sympy as sp
from qreals.rational import q_rational_pair

q = sp.symbols("q")
Phi2, Phi4, Phi8 = q + 1, q**2 + 1, q**4 + 1
q8 = sp.expand(sum(q**i for i in range(8)))
assert sp.expand(Phi2 * Phi4 * Phi8 - q8) == 0, "identity [8]_q = Phi2*Phi4*Phi8"

def divides(d, f):
    return sp.rem(sp.Poly(f, q), sp.Poly(d, q)).is_zero

data = json.load(open("<path>"
    "<path>"
    "phi8_search_result.json"))

checked = 0
for s_str, rs in data["hits_by_s_sample"].items():
    s = int(s_str)
    for r in rs:
        num, den = q_rational_pair(r, s)
        S = sp.Poly(sp.sympify(str(den)), q)
        assert divides(Phi8, S), (r, s, "Phi8")
        assert divides(Phi4, S), (r, s, "Phi4")
        assert divides(Phi2, S), (r, s, "Phi2")
        assert divides(sp.Poly(q8, q), S), (r, s, "[8]_q")
        assert S.eval(1) == s and s % 8 == 0, (r, s, "value at 1")
        checked += 1
print(f"all five checks passed on {checked} recorded hits")
