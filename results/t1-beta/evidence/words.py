"""Build a quadratic irrational from a prescribed Hirzebruch-Jung word.

This gives direct control over (c_1, c_2, ...), which the a + b sqrt(D) grid does
not, and is the right instrument for adversarial search in the residual regime
where the main theorem is silent.

All arithmetic is exact: integer matrices, exact square-root extraction by
integer isqrt, and Q(sqrt D) arithmetic from qreals.quadratic.
"""

from __future__ import annotations

import random
from fractions import Fraction as F
from math import isqrt

from exact import G_exact, QuadraticIrrational, first_tail, hj


def mat_word(word):
    a, b, c, d = 1, 0, 0, 1
    for e in word:
        # multiply on the right by [[e,-1],[1,0]]
        a, b, c, d = a * e + b, -a, c * e + d, -c
    return a, b, c, d


def squarefree_part(n):
    """n = f^2 * D with D squarefree; return (f, D)."""
    f, D = 1, n
    i = 2
    while i * i <= D:
        while D % (i * i) == 0:
            D //= i * i
            f *= i
        i += 1
    return f, D


def qi_mul(u, v):
    p = u.p * v.p + u.D * u.r * v.r
    r = u.p * v.r + u.r * v.p
    s = u.s * v.s
    return QuadraticIrrational(p, r, s, u.D)


def mobius(mat, t):
    a, b, c, d = mat
    num = t.scalar_mul(a) + F(b)
    den = t.scalar_mul(c) + F(d)
    if den.is_zero():
        raise ZeroDivisionError
    return qi_mul(num, den.reciprocal())


def from_word(pre, per):
    """x with HJ expansion pre + per^infinity, or None if the word is not realized."""
    if not per:
        raise ValueError("need a periodic part")
    a, b, c, d = mat_word(per)
    tr = a + d
    disc = tr * tr - 4
    if disc <= 0:
        return None
    root = isqrt(disc)
    if root * root == disc:
        return None  # rational fixed point
    f, D = squarefree_part(disc)
    if D <= 1:
        return None
    # c t^2 + (d - a) t - b = 0  ->  t = ((a-d) +- f sqrt(D)) / (2c)
    if c == 0:
        return None
    for sgn in (1, -1):
        t = QuadraticIrrational(a - d, sgn * f, 2 * c, D)
        try:
            x = mobius(mat_word(pre), t) if pre else t
        except ZeroDivisionError:
            continue
        want = list(pre) + list(per) * 4
        got = hj(x, len(want))
        if got == want:
            return x
    return None


def scan(rows, target=200, tail_start=6):
    out = []
    for pre, per in rows:
        x = from_word(pre, per)
        if x is None:
            continue
        tx = hj(x, 2)
        tn = hj(-x, 2)
        bx = tx[0] + tx[1] - 2
        bn = tn[0] + tn[1] - 2
        g = G_exact(x, target)
        ft = first_tail(g, target, tail_start)
        out.append(dict(pre=tuple(pre), per=tuple(per), c1=tx[0], c2=tx[1],
                        d1=tn[0], d2=tn[1], bx=bx, bn=bn,
                        bmax=max(bx, bn), ft=-1 if ft is None else ft))
    return out


def random_residual_words(n, seed, c1lo=-9, c1hi=9, small=6, plen=6, prelen=4):
    """Random words biased toward the residual regime (small second terms)."""
    rng = random.Random(seed)
    rows = []
    for _ in range(n):
        c1 = rng.randint(c1lo, c1hi)
        m = rng.randint(0, prelen)
        k = rng.randint(1, plen)
        pre = [c1] + [rng.randint(2, small) for _ in range(m)]
        per = [rng.randint(2, small) for _ in range(k)]
        rows.append((pre, per))
    return rows
