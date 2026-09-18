# q-mult-not-bihomographic

## Summary

An exact negative result: the q-deformed real product `[xy]_q`, the single
q-real of the ordinary product `x*y`, is **not** a bihomographic
(bilinear-fractional) function of the two separate q-reals `[x]_q` and `[y]_q`.
Equivalently, no Gosper-style bihomographic transducer of any bounded size
computes `[xy]_q` from the q-continued-fraction data of `x` and `y`. This is the
multiplication counterpart of the addition result in the `q-gosper-engine`
experiment; the two share the same exact-kernel machinery.


## What was computed

A bihomographic state carries a single `2x4` matrix
`S = [[a,b,c,d],[e,f,g,h]]` representing the bilinear-fractional function

    z(X,Y) = (a XY + b X + c Y + d) / (e XY + f X + g Y + h)

in the monomial basis `(XY, X, Y, 1)`. After ingesting the q-continued-fraction
digits of `x` and `y`, the engine evaluates this `z` at `X = [x]_q`, `Y = [y]_q`,
so the set of values a bihomographic transducer can emit is exactly the
bilinear-fractional functions of `[x]_q, [y]_q`. The ordinary product
`[x]_q * [y]_q` is one such value; the question is whether `[xy]_q` is too.

Writing `X = [x]_q`, `Y = [y]_q`, `T = [xy]_q`, a bihomographic law is the
bilinear relation whose coefficient vector `(a,...,h)` must lie in the kernel of
an `8x8` relation matrix built from eight rational pairs. The search evaluates
this matrix exactly over `Q(q)` and finds it full rank (rank 8): the kernel is
trivial, so no bihomographic law exists, at any coefficient degree.

## Verdict

**NO.** There is no bilinear-fractional form with coefficients in `Q(q)`,
constant in `x` and `y`, such that `z([x]_q, [y]_q) = [xy]_q`.

A further finding distinguishes multiplication from addition. For addition the
sole obstruction is the reversal `[x]_{1/q}` (the map `q -> 1/q`). For the
square `[x^2]_q`, that reversal is **absent** as the obstruction: on a catalog
of 32 non-integer `x > 1`, the relation matrix in the pair
`([x]_q, [x]_{1/q})` has full rank 8, while a control target built from the
reversal itself has rank 6. Multiplication is therefore a strictly richer
obstruction than addition's single involution, not a variant of it.

## Scope

- Proved exactly over `Q(q)`, at any coefficient degree and magnitude.
- Regime `x, y > 1`, where each `[x]_q, [y]_q` has constant term 1.
- Not claimed: that `[xy]_q` or `[x^2]_q` has no closed form of any kind, only
  that neither is bihomographic in `[x]_q, [y]_q` (respectively
  `[x]_q, [x]_{1/q}`).

## Code

`code/mult_impossibility_search.py` runs the battery; it reuses helpers from
`code/impossibility_search.py` (the addition search). Both import the q-Gosper
engine module `q_gosper` (and `qreals`), which is a separate project module not
included in this dataset; make it available on the Python path to run the
scripts. The battery is deterministic (fixed pairs, q-values, and primes, no
I/O), so it re-runs bit-identically and any drift surfaces as a hash mismatch.
