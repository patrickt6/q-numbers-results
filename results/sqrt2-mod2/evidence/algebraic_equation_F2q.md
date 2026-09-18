# The algebraic equation for `[sqrt(2)]_q` over `F_2(q)`

This is the input that licenses the Christol-Furstenberg automaton in
`proof_sqrt2_mod2.md`.

## Over `Q(q)`

Let `[sqrt(2)]_q = sum_{n >= 0} c_n q^n` be the Morier-Genoud-Ovsienko
q-deformation of `sqrt(2)`. By MGO Proposition 4.5 (arXiv:1908.04365,
"reals.pdf"),

    q^2 y^2 - (q^3 - 1) y - (q^2 + 1) = 0,                          (1)

equivalently `P(q) y^2 + Q(q) y + R(q) = 0` with

    P(q) = q^2,   Q(q) = 1 - q^3,   R(q) = -(1 + q^2).

The discriminant is `Q^2 - 4 P R = (1 - q^3)^2 + 4 q^2 (1 + q^2)`.

This is the same equation used in `<path>`
and `<path>`; only the
prime of reduction changes here (2 instead of 7).

## Reduction mod 2

Reducing the integer coefficients of (1) modulo 2 (so `-1 = 1`) gives the
degree-2 polynomial `f_bar in F_2(q)[Y]`:

    f_bar(Y, q) = q^2 Y^2 + (1 + q^3) Y + (1 + q^2) = 0   over F_2(q).  (*)

Notes on the reduction:

- `f_bar` is **not** the zero polynomial and does not degenerate: the
  leading coefficient `q^2` is nonzero in `F_2(q)`, so the series root
  remains algebraic of degree 2. (This was the pre-construction sanity
  gate in the buildout PRD risk register.)
- The discriminant mod 2 collapses to a square: `4 q^2 (1 + q^2) = 0`
  mod 2, so `disc(f_bar) = (1 + q^3)^2 = (1 + q)^2 (1 + q + q^2)^2`, a
  perfect square in `F_2[q]`. (Compare the MGO `sqrt(2)` discriminant
  `q^2 + 1 -> (q + 1)^2` noted in the PRD risk register.) The equation is
  still irreducible as the minimal equation of the power-series root with
  `c_0 = 1`; the square discriminant only means the two formal roots are
  not separated by a square-root extension of `F_2(q)`, which is expected
  in characteristic 2.

## Why this gives an automaton

`[sqrt(2)]_q in F_2[[q]]` is algebraic over `F_2(q)` by (*). By
**Christol's theorem** (Christol 1979; Christol-Kamae-Mendes France-Rauzy
1980): the reduction of an algebraic power series over `F_p(q)` is
`p`-automatic. Hence `(c_n mod 2)_{n>=0}` is computed by a finite
deterministic automaton with output reading the base-2 digits of `n`.

## The coefficient-extraction recurrence mod 2

Extracting the coefficient of `q^k` from (*) and using the
characteristic-2 Frobenius identity `y(q)^2 = y(q^2)` (so that the
`q^2 y^2` term contributes `c_{(k-2)/2}` when `k` is even and `k >= 2`)
gives the closed recurrence in `F_2`:

    c_k = [k=0] + [k=2] + c_{k-3} (for k >= 3) + c_{(k-2)/2} (for k even, k >= 2).   (R)

with `c_0 = 1`. Because `k - 3 < k` and `(k - 2)/2 < k`, (R) determines
the entire sequence, and it is well-defined as a recurrence. (R) is
verified against the canonical MGO coefficient file in
`verify_against_atlas.py` (byte-equal on all 20000 indices), which
confirms the symbolic reduction above is correct.

## Provenance

- MGO Proposition 4.5: arXiv:1908.04365.
- Source recurrence (over Q): `<path>`.
- Atlas anchor row (sqrt2, p=2, d=3): `<path>`,
  (store `<path>`).
