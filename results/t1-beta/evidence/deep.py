"""How large can (first tail degree d) - B get?  Construct x with a small
C_2 but a large C_3 or C_4, by prescribing the head of the HJ expansion."""
from fractions import Fraction as F
from qreals.quadratic import QuadraticIrrational
from gtools import beta, first_tail, g_series, hj, predicted

def from_hj_head(head, tail_x):
    """x = c_1 - 1/(c_2 - 1/(... - 1/tail_x)) for head = [c_1, c_2, ...]."""
    z = tail_x
    for c in reversed(head):
        z = QuadraticIrrational(c * z.s - z.p, -z.r, z.s, z.D).reciprocal()
        # z currently = 1/(c - prev); we want c - 1/prev, so redo properly
    return z

def build(head, tail):
    z = tail
    for c in reversed(head):
        inv = z.reciprocal()                     # 1/z
        z = QuadraticIrrational(c, 0, 1, z.D) - inv   # c - 1/z
    return z

D = 2
print(f"{'head':<22}{'hj(x)':<28}{'B':>5}{'d':>6}{'d-B':>6}")
for head, tailc in [([3,2],5),([3,2],10),([3,2],20),([3,2],50),
                    ([3,2,2],10),([3,2,2],30),([3,2,2,2],10),([3,2,2,2],30),
                    ([2,2],20),([4,2],20),([3,3],20),([2,2,2,2],20)]:
    t = QuadraticIrrational(tailc, 1, 1, D)   # tailc + sqrt(2)
    x = build(head, t)
    B = predicted(x)
    g, lo, ld = g_series(x, 90)
    d, top = first_tail(g, lo, ld)
    print(f"{str(head)+'+'+str(tailc):<22}{str(hj(x,5)):<28}{B:>5}{str(d):>6}{str(None if d is None else d-B):>6}")
