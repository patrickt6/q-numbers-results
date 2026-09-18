# T1: the beta bound is false

Verdict: **disproved**, with explicit counterexamples at D = 2, D = 3 and D = 5,
confirmed by two independent computation routes. A partial positive result is
recovered below, together with an exact diagnosis of which step of the natural
proof fails and why.

## 1. Statement tested

For a quadratic irrational `x` with Hirzebruch-Jung expansion `[c_1, c_2, ...]`,
set `beta(x) = (c_1 - 1) + (c_2 - 1)` and `pred(x) = max(beta(x), beta(-x))`.
The claim under audit (F5) is that the first nonzero coefficient of
`G(x) = [x]_q + [-x]_q` at degree at least `TAIL_START = 6` occurs at degree at
most `pred(x)`.

The bound has content only when `pred(x) >= 6`. Below that it is vacuously
violated by the definition of the tail index, and no census verdict reads it in
that regime. All counts below are restricted to `pred(x) >= 6`.

## 2. Counterexamples

Smallest counterexample found, at D = 2:

    x = 1 + 3*sqrt(2)
    HJ(x)  gives beta(x)  =  6
    HJ(-x) gives beta(-x) = -2
    pred(x) = 6
    G(x) coefficients at degrees 6, 7, 8, 9 = 0, -1, 0, 2
    first nonzero tail degree = 7 > 6 = pred(x)

Further counterexamples, all with coefficient 0 at degree 6:

| D | x | beta(x) | beta(-x) | pred | true tail |
|---|---|---|---|---|---|
| 2 | `1 + 3 sqrt(2)` | 6 | -2 | 6 | 7 |
| 2 | `2 + (9/4) sqrt(2)` | 6 | -1 | 6 | 7 |
| 2 | `13/4 + sqrt(2)` | 6 | -4 | 6 | 7 |
| 3 | `3/2 + (3/4) sqrt(3)` | 6 | -2 | 6 | 7 |
| 3 | `5/2 + (5/4) sqrt(3)` | 6 | -4 | 6 | 7 |
| 5 | `(5/4) sqrt(5)` | 6 | -2 | 6 | 7 |

Each row was computed twice, once through the official engine
(`qreals.negation.locked_series` plus `classify`, windows derived from
`window_bounds`, depth 160) and once through a separate implementation that
builds `[x]_q` and `[-x]_q` from deep HJ convergents using exact integer
polynomial arithmetic and shares no code with `negation.py`. Both routes return
the same coefficients and the same tail degree.

## 3. Scale of the failure

Grid: `x = a + b sqrt(D)` with `a` in eighths over `[-5, 5]`, `b` in eighths
over `[-3, 3]`, `b` nonzero, `D` in {2, 3, 5}. Restricted to points where
`pred(x) >= 6` and where the convergent depth is certified past the read window
by the agreement bound `C_n`.

    certified points                    6464
    exceedances of pred(x)               146   (2.26 percent)
    by D                                 D=2: 42,  D=3: 60,  D=5: 44
    excess (tail - pred) distribution    1: 92,  2: 28,  3: 12,  4: 6,  6: 4,  8: 2,  9: 2
    pred value at every exceedance       6: 102,  7: 34,  8: 4,  9: 4,  12: 2

Two structural observations, both empirical:

1. Every exceedance in the scan has `pred(x) <= 12`. The failures sit near the
   tail start, not out at large `pred`.
2. Exceedances occur in `(x, -x)` pairs, as they must, since `G(x) = G(-x)` and
   `pred` is symmetric. This is a consistency check on the harness.

The largest excess observed is 9, at `x = (1/2) + (5/2) sqrt(5)`, where
`pred = 7` and the true tail degree is 16.

## 4. Why the natural proof fails

A sharpened form of the agreement bound is available and is proved below. It is
the strongest statement the determinant identity supports, and it is not enough.

**Lemma 1 (sharpened agreement bound).** Let `x` be a quadratic irrational with
HJ expansion `[c_1, c_2, ...]`, let `r_n = [[c_1, ..., c_n]]` be its n-th
convergent, and let `C_n = sum_{i<=n} (c_i - 1)`. Then

    [x]_q - [r_n]_q  =  -q^{C_n} + (terms of degree > C_n),

the leading coefficient being exactly `-1`.

*Proof.* By the verified identity `R_{n+1} S_n - S_{n+1} R_n = -q^{C_n}`, and
since `S_n` has constant term 1 for every n, the successive-convergent
difference is `R_{n+1}/S_{n+1} - R_n/S_n = -q^{C_n} u_n` with
`u_n = 1/(S_{n+1} S_n)` a unit power series, so `u_n(0) = 1`. Summing over the
q-adically convergent telescoping series gives
`[x]_q - [r_n]_q = -sum_{m >= n} q^{C_m} u_m`. Since `c_k >= 2` for `k >= 2`,
the exponents satisfy `C_n < C_{n+1} < ...`, so no term beyond the first can
contribute at degree `C_n`. The coefficient there is therefore `-u_n(0) = -1`.

Verified on 2952 quadratic irrationals over D in {2, 3, 5}: degree exactly
`C_2` and leading coefficient exactly `-1`, zero violations.

**The decomposition.** Applying Lemma 1 at `n = 2` to `x` and to `-x`
separately, with `r` the second convergent of `x` and `r'` the second convergent
of `-x`, and writing `H = [r]_q + [r']_q`,

    G(x) = H - q^{beta(x)} - q^{beta(-x)}
             + (terms of degree > beta(x))
             + (terms of degree > beta(-x)).

This is where the argument stops. The error term coming from the `-x` side is
controlled only above `beta(-x)`. When `beta(-x) < beta(x)` that side is
uncontrolled at degree `beta(x)`, so nothing can be concluded about the
coefficient of `G` at `pred(x) = beta(x)`. The decomposition supports a
statement at `min(beta(x), beta(-x))`, never at the max. **The census uses the
max where the mathematics only reaches the min**, and every counterexample in
section 2 has `beta(-x) < 0 < 6 <= beta(x)`, precisely the uncontrolled regime.

**The trap that closes the obvious repair.** The natural fix is to avoid the
second convergent of `-x` entirely by using the published reversal rule
`[-x]_q = -q^{-1} [x]_{1/q}` (LMGOV Remark 2.3), which would transfer the
expansion of `[x]_q` directly onto the `-x` side and produce the max form. This
does not work. For irrational `x` the series `[x]_q` is infinite, so `[x]_{1/q}`
is a series in descending powers of `q` and is not an element of the Laurent
ring in which `[-x]_q` lives. The reversal rule is an identity of analytic
functions on the common domain of convergence, not an identity of formal Laurent
series, and it cannot be applied termwise. Checked directly on
`x = -4 + 3 sqrt(2)`: the reversal route predicts
`[-x]_q - [-r]_q = q^{-beta-1} + (lower degrees)`, whereas the true difference is
`q - q^2 + ...`, supported in positive degrees. This route was pursued and
abandoned; it should not be retried.

**The min form is also false.** Restricting to `min(beta(x), beta(-x)) >= 6`
gives 280 certified points, of which 88 exceed the min bound. In most of those
the true tail degree lands exactly on `max(beta(x), beta(-x))`. So `pred` is
better read as the generic *exact value* of the tail degree than as an upper
bound on it, which is consistent with the 658 of 1093 exact-equality rate
already recorded in `escalate_official.py`. The residual cases are cancellations
at degree `pred`, where `H` contributes exactly `+1`.

## 5. Consequence for the census, and why the two records do not conflict

The counterexamples do not contradict the 1093-case clean record, because the
two populations are disjoint. Recount from `escalation-official.csv`, 3084 rows,
2896 of them `infinite` with a recorded tail index:

    predicted_tail range over the escalated population   70 to 2940
    rows with pred >= 6                                  2896 (all of them)
    exceedances of pred                                     0
    exact equalities tail == pred                        2350 (81.1 percent)

Every escalated point has `pred >= 70`. Every counterexample found here has
`pred <= 12`. The escalation flags points that sit very close to a rational,
and such points have large `beta`, so the census never evaluates the bound in
the regime where it fails. That is a property of the flagged population, not a
property of `beta`, and it is stated nowhere.

A plausible mechanism for the separation, heuristic and unproved: failure at
degree `pred` requires the auxiliary series `H` to contribute exactly `+1`
there, cancelling the `-1` from Lemma 1. Coefficients of `H` grow in magnitude
with degree, so an exact hit of `+1` becomes progressively less likely as `pred`
grows. This suggests the bound is asymptotically safe, and it is not a proof.

What is nevertheless wrong is the wording. The `escalate_official.py` docstring
calls `pred` "a strict upper bound on the first nonzero tail index" and argues
that "a zero run is only informative once it clears predicted(x)". As a general
statement about quadratic irrationals that is false. The defensible statement is
narrower:

> On the escalated population, every point of which has `pred >= 70`, the first
> nonzero tail index was at most `pred` in 2896 of 2896 cases and equal to
> `pred` in 2350. No proof of this is known, and the bound is known to fail for
> `pred` between 6 and 12.

Actual exposure to a wrong verdict appears to be nil, for two further reasons,
both of which should be confirmed rather than assumed:

1. `escalation-official.csv` currently contains zero `finite_looking` rows
   (GROUND-TRUTH section 5, F10). No committed verdict rests on the guard.
2. The operative test is `MIN_ZERO_RUN = 60` consecutive zeros, far stronger
   than clearing `pred`, and every observed excess is at most 9.

The recommended action is therefore not to strengthen `beta` but to stop
claiming it certifies anything. `pred(x)` should be described as a heuristic
depth target with a stated verified range, and finiteness should continue to
rest on the 60-zero run, which is itself heuristic. Every census claim currently
phrased as resting on `beta` should be rephrased accordingly.

## 6. What is proved, what is checked, what is open

Proved: Lemma 1, including the exact leading coefficient `-1`, from the verified
determinant identity and the constant-term-1 property of `S_n`.

Checked, not proved: the counterexamples (exact arithmetic, two independent
routes); the 2.26 percent exceedance rate on the stated grid; the observation
that every exceedance has `pred <= 12` and excess at most 9.

Open, and this is the question that actually matters: whether exceedances can
occur at large `pred`. The census operates entirely at `pred >= 70`, and the
bound is unbeaten there over 2896 cases, but no proof covers that regime and the
scan here cannot reach it. A targeted search enriched for large `pred`, and for
points where `H` has a coefficient of exactly `+1` at degree `pred`, is the
natural next step. It would settle whether a repaired bound of the form
`pred + K` is plausible. Nothing here proves such a `K` exists.


No record exists for beta. One should be filed containing: the statement of
Lemma 1 with its proof and the 2952-case verification; the counterexample list
of section 2 with the exact `G` coefficients at degrees 6 through 9 for each;
the section 3 scan parameters (grid, D values, certification rule, seedless and
exhaustive) with the 6464 and 146 counts; and the retraction of the F5 soundness
claim. The scripts `reduction_check.py`, `consequence_check.py` and
`exceedance_scan.py` in this directory reproduce every number.
