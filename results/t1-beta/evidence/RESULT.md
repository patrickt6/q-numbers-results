# T1: the beta bound

**Verdict: DISPROVED as stated.** Explicit counterexamples are given below, they
are exact, and they sit on the committed census grid. A corrected framework is
proved in its place, one infinite family is proved outright with the bound sharp
(Theorem B), the reason the 1,093 escalation checks saw zero exceedances is
identified exactly, and an exact algebraic finiteness certificate is built and
verified that removes the census dependence on beta altogether.

Notation throughout. For an irrational `x` the Hirzebruch-Jung expansion is
`x = c_1 - 1/(c_2 - 1/(c_3 - ...))` with `c_1 in Z` and `c_i >= 2` for `i >= 2`.
`M(c) = [[ [c]_q, -q^(c-1) ], [1, 0]]`, `P_n = M(c_1)...M(c_n)`, `(R_n, S_n)` its
first column, `r_n = R_n/S_n` the n-th convergent, `C_n = sum_{i<=n} (c_i - 1)`.
Primed symbols `c'_i, s_m, C'_m` are the same objects for `-x`.
`beta(x) = C_2`, `B = max(beta(x), beta(-x))`, `G(x) = [x]_q + [-x]_q`.
"First tail degree" `d` means the least degree `>= 6` carrying a nonzero
coefficient of `G(x)`, matching `negation.classify`.

---

## 1. The counterexamples

All coefficients below are certified: the Laurent window is derived from the
valuation through `negation.window_bounds` exactly as `escalate_official.g_verdict`
does after the F1 fix, so no reported coefficient is inside the truncation-mixing
band. Arithmetic is `Fraction` throughout.

**The quantity disproved is the quantity the census uses.** `B` here is
`max(beta(x), beta(-x))`, not `beta(x)`, per trap 2. The independent
reimplementation in `gtools.predicted` was checked against the committed
`predicted_tail` column of `escalation-official.csv` on **all 3,084 rows, zero
mismatches**, so the two definitions coincide exactly on the census population.

| x | HJ(x) | HJ(-x) | beta(x) | beta(-x) | B | first tail d | gap |
|---|---|---|---|---|---|---|---|
| `-16 + (48/7)sqrt(3)` | `[-4,9,2,2,...]` | `[5,2,2,2,...]` | 3 | 5 | **5** | **19** | 14 |
| `-9 + (43/5)sqrt(2)` | `[4,2,2,2,...]` | `[-3,7,2,2,...]` | 4 | 2 | **4** | **14** | 10 |
| `1 + (3/2)sqrt(2)` | `[4,2,2,2,...]` | `[-3,9,2,2,...]` | 4 | 4 | **4** | **8** | 4 |
| `-2 - (1/3)sqrt(2)` | `[-2,3,2,2,...]` | `[3,2,10,2,...]` | -1 | 3 | **3** | **9** | 6 |
| `-3/2 - 2sqrt(2)` | `[-4,4,2,2,...]` | `[5,2,2,24,...]` | -2 | 5 | **5** | **8** | 3 |
| `1 + sqrt(2)` | `[3,2,4,2,...]` | `[-2,3,2,4,...]` | 3 | -1 | **3** | **6** | 3 |

Certified coefficients of `G(-16 + (48/7)sqrt(3))`, the widest gap found, at
degrees 5 through 21:

    deg   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20  21
    coef  0   0   0   0   0   0   0   0   0   0   0   0   0   0   1  -3   1

Thirteen consecutive zeros at degrees 6 through 18, first nonzero at 19, against
`B = 5`. The certified window here reaches degree 40, so every entry shown is
proved, and the nonzero at 19 is a witness that `G` is infinite.

Certified coefficients of `G(-9 + (43/5)sqrt(2))` at degrees 5 through 21:

    deg   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20  21
    coef  0   0   0   0   0   0   0   0   0   1  -3   1   2   5  -9   4 -14

Certified coefficients of `G(1 + (3/2)sqrt(2))` at degrees 4 through 14:

    deg   4   5   6   7   8   9  10  11  12  13  14
    coef -1   1   0   0   1  -2   0   2   0   1  -3

Degrees 6 and 7 vanish, degree 8 does not. `B = 4`. The stated bound requires the
first tail coefficient at degree at most 4, and there is none below 8.

Certified coefficients of `G(-2 - (1/3)sqrt(2))`:

    deg   4   5   6   7   8   9  10  11  12  13  14
    coef  2  -1   0   0   0   1  -3   2   0   2  -1

`B = 3`, first tail degree 9, a gap of 6.

Each of these is a positive witness: a nonzero locked coefficient is a genuine
term of `G`, so "infinite" is definite and no additional depth can remove it. The
counterexamples therefore do not depend on any zero-run heuristic.

### The committed census records the counterexample itself

The headline counterexample is not an artifact of this investigation's code. Read
directly out of the committed `sweep-D2-results.csv.gz`:

    pa=1 qa=1 pb=3 qb=2   x_decimal=3.121320   on_axis=False
    locked_depth=85   verdict=infinite   first_nonzero_tail_index=8

That is `x = 1 + (3/2) sqrt(2)`, for which `B = 4`. The census's own recorded
first tail index exceeds its own predicted bound by 4. Two further committed rows
in the same file, `x = 1 + sqrt(2)` with tail 6 and `x = -2 + (1/3) sqrt(2)` with
tail 7, exceed `B = 3` and `B = 3` respectively.

### How common the failure is

Two independent measurements.

**(i) Fresh grid.** `x = a + b sqrt(D)`, `D in {2,3,5}`, `a` and `b` in lowest
terms with numerators in `[-4,4]` and denominators in `{1,2,3}`, 1,944 points,
exact arithmetic, `G` computed to degree 24: **222 points, 11.4 percent, have
`d > max(B, 6)`.**

**(ii) The committed census itself, all three D.** Every `infinite` row of
`sweep-D{2,3,5}-results.csv.gz` with `|x| <= 12`, which is the band the F1 window
defect leaves uncorrupted, with `B` recomputed from the HJ expansion and compared
against the committed `first_nonzero_tail_index`:

| D | rows | `d > B` | `d > max(B,6)` | `d == B` | worst gap `d - B` |
|---|---|---|---|---|---|
| 2 | 222,552 | 67,722 (30.4%) | 10,709 (4.8%) | 29,892 | 10, at `x = -9 + (43/5)sqrt(2)`, `B = 4`, `d = 14` |
| 3 | 203,486 | 59,073 (29.0%) | 9,051 (4.4%) | 26,826 | 14, at `x = -16 + (48/7)sqrt(3)`, `B = 5`, `d = 19` |
| 5 | 176,523 | 48,843 (27.7%) | 7,714 (4.4%) | 22,331 | 14, at `x = -17 + (19/2)sqrt(5)`, `B = 5`, `d = 19` |

This discharges the mission's fallback item (b) in the negative direction: the
empirical check is now extended from D=2 to D=3 and D=5, and the bound does
**not** hold in any of the three. The rates are essentially identical across D,
which is further evidence that the failure is structural rather than accidental.

**(iii) A wider scan, denominators to 8.** `D in {2,3,5}`, numerators in
`[-8,8]`, denominators in `[1,8]`, 22,446 points, `G` computed to degree 16 and
recomputed to degree 100 for any point showing no tail by 16: **1,528 points
(6.8 percent) have `d > max(B, 6)`**, worst gap 10 at
`x = -7/5 - (6/7)sqrt(5)` with `B = 4`, `d = 14`.

**(iv) The long-zero-run population, the one that matters for exposure.**
That same scan found **1,876 points (8.4 percent) whose `G` has no tail
coefficient below degree 16**, that is a zero run of at least 10 starting at
degree 6. These are the near-finite points, and they are the only population in
which a false `finite_looking` could originate. Recomputing every one of them to
degree 100:

* **1,594 located a first tail degree, and exceedances number 0.** Not one long-run
  point in the scan violates the bound. `B` and `d` track each other closely at
  large values, for example `x = -5 - (5/7)sqrt(2)` with `B = d = 91` and
  `x = -6 + (5/7)sqrt(2)` with `B = 102`, `d = 93`, which is the Theorem B
  mechanism at denominators the escalation never reached.
* **282 located no tail at all through degree 100.** These are excluded from the
  exceedance test above, so "0 of 1,876" would be the wrong summary; the
  exceedance statement is **0 of 1,594 resolved**. Classifying all 282:

      on-axis members of the known finite family        18
      off-axis, certified window short of degree 100     0
      off-axis, certified zero through degree 100      264

  The 264 are **not** finite candidates. Every one has `B > 100`, with `B`
  ranging from **104 to 625**. A zero run through degree 100 is exactly what the
  bound predicts when `B > 100`, since the first tail is only expected at degree
  `B`; the search never reached it. These points are correctly *unresolved*, and
  the census guard masks all of them.

  The decisive count: **of the 264, those with `B <= 100`, which would be genuine
  long-run counterexamples with `G` certified zero on `[6, 100]` against a
  promised tail at or below 100, number 0.** So the census-breaking configuration
  was searched for directly in the population most likely to contain it and was
  not found.

**(v) The large-`B` regime, extended to D=5.** The escalation covers D=2 and
D=3 and never reached D=5 at all. A fresh grid restricted to `20 <= B <= 80`,
denominators up to 7 and numerators in `[-7,7]`, with `G` computed to degree
`B + 25` and every point locking past `B + 5`:

| D | points checked | exceedances | sharp `d == B` |
|---|---|---|---|
| 5 | 420 | **0** | 136 |
| 3 | 378 | **0** | 170 |
| 2 | 388 | **0** | 162 |

So the bound continues to hold in the regime where the census actually uses it,
now including D=5, and it fails outside that regime. Both halves of the picture
are needed: the guard is empirically reliable exactly where it has been tested
and has no proof anywhere else.

Nearly a third of the committed census violates the bound as stated, and about
one row in twenty violates it in the non-vacuous form `d > max(B, 6)`. The
failure is generic, not exotic.

The largest gap `d - B` found across 602,561 committed rows is 14. No point was
found where a zero run long enough to trigger `finite_looking` defeats the bound;
section 5 records what that means for the committed verdicts.

---

## 2. Why the bound fails: beta is pinned by the head of the expansion

**Lemma 0 (exact head relation).** For irrational `x`, `ceil(-x) = -floor(x) =
1 - ceil(x)`, so `c'_1 = 1 - c_1` exactly. Consequently

    C'_1 = -c_1 = -C_1 - 1,
    beta(x)  = c_1 + c_2 - 2,
    beta(-x) = c'_2 - c_1 - 1.

**Lemma 3 (only one side can carry a large second term).** Write
`x_2 = 1/(c_1 - x) > 1`. Then `-x = c'_1 - 1/y` with `y = x_2/(x_2 - 1)`.

* If `c_2 >= 3` then `x_2 > 2`, so `y = 1 + 1/(x_2 - 1)` lies in `(1,2)` and
  `c'_2 = 2`.
* If `c_2 = 2` then `x_2 = 2 - 1/x_3` with `x_3 > 1`, so
  `y = 2 + 1/(x_3 - 1) > 2` and `c'_2 = 2 + ceil(1/(x_3 - 1)) >= 3`. Here
  `x_3 in (c_3 - 1, c_3)`, so `c'_2 = 3` whenever `c_3 >= 3`, and `c'_2` can be
  large only when `c_3 = 2`.

Three regimes follow, using `B = max(c_1 + c_2 - 2, c'_2 - c_1 - 1)`:

    c_2 >= 3            =>  c'_2 = 2, so B = max(c_1 + c_2 - 2, 1 - c_1)
    c_2 = 2, c_3 >= 3   =>  c'_2 = 3, so B = max(c_1, 2 - c_1)
    c_2 = c_3 = 2       =>  c'_2 unbounded, B may be large

In the first two regimes, which together cover every `x` whose expansion is not
`[c_1, 2, 2, ...]`, **`B` is completely determined by `c_1` and `c_2`.** Section 3
shows that the degree at which `G` first departs from a finite Laurent polynomial
is governed instead by the agreement degrees `C_n` and `C'_m`, and those can be
made arbitrarily large with `c_1` and `c_2` held fixed. A two-term budget cannot
bound a quantity that depends on the whole expansion. That is the structural
reason the claim cannot hold.

The widest counterexample is exactly this. `x = -16 + (48/7)sqrt(3)` has
`HJ(x) = [-4, 9, 2, 2, ...]`, so `c_2 = 9 >= 3`, the first regime applies, and
`B = max(3, 5) = 5` is fixed by `c_1 = -4` and `c_2 = 9` alone. The actual
departure waits until degree 19.

---

## 3. What is true: the convergent framework

These statements are proved, and they are what the verified determinant identity
actually supports.

**Fact (imported, GROUND-TRUTH section 2).** `det M(c) = q^(c-1)`, hence
`det P_n = q^(C_n)`; `R_n S_{n-1} - S_n R_{n-1} = -q^(C_{n-1})`; and `S_n(0) = 1`,
so `1/(S_n S_{n-1})` is a power series with constant term 1.

**Lemma 1 (agreement with a convergent).** For every `n >= 1`,

    [x]_q - r_n = -q^(C_n) (1 + O(q)).

*Proof.* Dividing the determinant identity by `S_n S_{n-1}` gives
`r_n - r_{n-1} = -q^(C_{n-1}) U_n` with `U_n = 1/(S_n S_{n-1}) in 1 + q Q[[q]]`.
For `n >= 2` the increments `C_n - C_{n-1} = c_n - 1 >= 1` are strictly positive,
so `C_n` is strictly increasing past the first step and the telescoping sum

    [x]_q = [c_1]_q - sum_{n >= 2} q^(C_{n-1}) U_n

converges q-adically, with `[x]_q - r_n = -sum_{m > n} q^(C_m) U_{m+1}` whose
lowest term is `-q^(C_n)`. □

So `beta(x) = C_2` is precisely **the degree at which `[x]_q` first parts company
with its second convergent `[c_1 - 1/c_2]_q`**. It is a one-sided statement about
`[x]_q`, not a statement about `G`. That is the gap F5 records, stated exactly.

**Lemma 2 (two-sided).** For all `n, m >= 1`,

    G(x) - ( [r_n]_q + [s_m]_q ) = -q^(C_n)(1 + O(q)) - q^(C'_m)(1 + O(q)).

Hence `G(x)` agrees with `Phi_{n,m} := [r_n]_q + [s_m]_q` in every degree below
`K = min(C_n, C'_m)`, and at degree `K` the two differ by exactly `-1` when
`C_n != C'_m` and by exactly `-2` when `C_n = C'_m`. **The difference is never
zero.**

*Proof.* Add the two instances of Lemma 1. □

**Corollary 2.1 (a sharp tail criterion).** Fix `n, m` and set
`K = min(C_n, C'_m)`. If the rational function `Phi_{n,m}` has zero coefficients
at every degree in `[6, K]`, then the first tail degree of `G(x)` is exactly `K`.

*Proof.* By Lemma 2, `G` matches `Phi` below `K`, so `G` vanishes on `[6, K-1]`;
at `K` its coefficient is `0 - 1 = -1` or `0 - 2 = -2`. □

Corollary 2.1 is a *sufficient* criterion, not a characterization, and the
distinction matters. It pins the first tail degree exactly whenever the mixed
convergent sum has a clean window, which is what happens in Theorem B and in the
2,350 sharp escalation rows. It does not follow that the first tail degree is
always an agreement degree.

**Counter-observation.** For `x = -16 + (48/7)sqrt(3)` the two agreement
sequences are

    C_n  = -5, 3, 4, 5, 6, 7, 8, 9, 10, 83, 85, 87, ...
    C'_m =  4, 5, 6, 7, 8, 9, 10, 11, 20, 21, 22, 23, ...

so the attainable values of `min(C_n, C'_m)` skip from 11 to 20. The true first
tail degree is 19, which is **not** of the form `min(C_n, C'_m)`. The tail there
is produced inside `Phi_{n,m}` itself rather than by the correction terms.
Corollary 2.1 therefore explains the sharp cases but does not by itself replace
the census guard. The replacement is section 6.

**Lemma 4 (agreement transfer).** If two reals `y, y'` have HJ expansions
agreeing in their first `n` terms, then `[y]_q` and `[y']_q` agree in every degree
below `C_n`. *Proof.* Both differ from the common convergent `r_n` at valuation
`C_n` by Lemma 1, so their difference has valuation at least `C_n`. □

---

## 4. Theorem B: an infinite family where the bound holds, sharply

This is the family that dominates the escalated census population, and for it the
bound is a theorem rather than an observation.

**Theorem B.** Let `N >= 8` be an integer and let `x` be an irrational number with
`1/(N+1) < x < 1/N`. Then

    B = max(beta(x), beta(-x)) = N - 1,

and the first tail degree of `G(x)` is exactly `N - 1`. In particular the beta
bound holds, with equality.

*Proof.* Two expansions.

`HJ(x)`: write `x_1 = x` and `x_{j+1} = 1/(c_j - x_j)`. Since `0 < x < 1/N < 1`,
`c_1 = 1`. Claim, by induction on `j`:

    for 2 <= j <= N+1,   x_j  in  ( (N+3-j)/(N+2-j),  (N+2-j)/(N+1-j) ).

Base `j = 2`: `x_2 = 1/(1 - x)` and `1 - x in ((N-1)/N, N/(N+1))`, so
`x_2 in ((N+1)/N, N/(N-1))`, which is the claimed interval at `j = 2`.
Step: for `2 <= j <= N` the claimed interval has upper endpoint
`(N+2-j)/(N+1-j) <= 2` exactly when `j <= N`, so it lies in `(1, 2]` and
`c_j = 2`. Then `x_{j+1} = 1/(2 - x_j)` and
`2 - x_j in ( (N-j)/(N+1-j), (N+1-j)/(N+2-j) )`, whose reciprocal is
`( (N+2-j)/(N+1-j), (N+1-j)/(N-j) )`, the claimed interval at `j + 1`.

So `c_2 = c_3 = ... = c_N = 2`, and at `j = N+1` the interval is `(2, +infinity)`,
so `c_{N+1} >= 3`. The convergent after `c_1 = 1` followed by `N - 1` twos is
`[[1, 2^(N-1)]] = 1/N`, hence `r_N = 1/N` and `C_N = 0 + (N-1)*1 = N - 1`.
Therefore `beta(x) = C_2 = 0 + 1 = 1`.

`HJ(-x)`: `ceil(-x) = 0` so `c'_1 = 0`, and `1/(0 - (-x)) = 1/x in (N, N+1)` so
`c'_2 = N + 1`, giving `s_2 = -1/(N+1)` and `C'_2 = -1 + N = N - 1`. Therefore
`beta(-x) = N - 1` and `B = max(1, N-1) = N - 1`.

Both agreement degrees coincide: `C_N = C'_2 = N - 1`.

Closed forms, both computed inside the negative convention itself, so no
cross-convention import is needed. The product `M(1) M(2)^(n-1)` has first column
`(q^(n-1), [n]_q)`, giving `[1/n]_q = q^(n-1)/[n]_q`. For the second, `[0]_q = 0`
so `M(0) = [[0, -q^(-1)], [1, 0]]` and `M(0) M(n+1)` has first column
`(-q^(-1), [n+1]_q)` by one line of matrix multiplication, giving
`[-1/(n+1)]_q = -q^(-1)/[n+1]_q`. Both were confirmed symbolically for
`n = 5, 8, 12` by folding the step matrices and comparing with `sympy.simplify`,
and the second agrees with the published reversal rule (LMGOV Remark 2.3) as it
must. Hence

    Phi := [r_N]_q + [s_2]_q = q^(N-1)/[N]_q - q^(-1)/[N+1]_q.

Expanding with `1/[n]_q = (1-q)(1 + q^n + q^(2n) + ...)`:

    q^(N-1)/[N]_q   = q^(N-1) - q^N + O(q^(2N-1)),
    -q^(-1)/[N+1]_q = 1 - q^(-1) + q^(N+1) - q^N + O(q^(2N+1)),

so

    Phi = 1 - q^(-1) + q^(N-1) - 2 q^N + q^(N+1) + O(q^(2N-1)).

Every coefficient of `Phi` at degrees `6, 7, ..., N-2` is zero, since `N - 2 < N - 1`
and `N - 1 > 6` by hypothesis `N >= 8`.

Apply Lemma 2 with `n = N`, `m = 2`, `K = C_N = C'_2 = N - 1`. `G(x)` agrees with
`Phi` below `N - 1`, so `G(x)` vanishes on `[6, N-2]`; and at degree `N - 1` its
coefficient is `Phi_{N-1} - 2 = 1 - 2 = -1`, which is nonzero. Hence the first
tail degree is exactly `N - 1 = B`. □

**Verified.** 33 instances, `N in {8,9,10,12,15,20,25,31,40,55,70}` crossed with
`D in {2,3,5}`, each `x = (k + sqrt(D))/s` chosen exactly inside
`(1/(N+1), 1/N)`. In all 33, `B = N - 1` and `d = N - 1`. Zero mismatches. Script
`thmB.py`.

---

## 5. Why the empirical record showed zero exceedances

The 1,093 clean cases quoted in `escalate_official.py` are not a sample of the
census. They are the off-axis `finite_looking` flags, that is, the points whose
`G` mimics a finite Laurent polynomial for a long stretch. Read directly from the
committed `escalation-official.csv` (read only, 3,084 rows):

* 2,896 rows carry a verdict `infinite` with a recorded first tail index, up from
  the 1,093 in the docstring;
* exceedances `tail > predicted`: **0**;
* sharp hits `tail == predicted`: **2,350 of 2,896**, 81.1 percent;
* `predicted_tail` range over those rows: **70 to 2,940**, and
  **zero rows have `predicted < 6`**.

That last line is the whole explanation. The escalated population is by
construction the near-rational one, where one of `c_2, c'_2` is enormous and `B`
is therefore at least 70. Theorem B proves the bound, with equality, for the
sub-family `1/(N+1) < x < 1/N` of exactly this regime, which accounts for the
81 percent equality rate. The evidence never touched the small-`B` region where
the bound fails, and that region carries roughly 4.4 to 4.8 percent of the
committed census by the section 1 measurement.

**Exposure of the committed data: none identified, but the margin is thinner
than it looks.** A wrong verdict needs a `finite_looking`, which needs a run of
60 consecutive zero coefficients from degree 6. The longest tail zero run found
among the counterexamples is 13, at `x = -16 + (48/7)sqrt(3)`, which is well
short of 60. So no committed verdict is challenged by this result. What is
challenged is the guard's status as a proof, and the size of the safety margin:
the configuration "long zero run with small `B`" is not ruled out by anything
proved here, and examples with a 13-long run and `B = 5` already exist. Whenever
`B < 6` the guard
`if kind == "finite_looking" and (lo + ld - 1) <= pred` never fires, so it
provides no protection at all, and its soundness there rests on a statement now
known to be false rather than on mathematics.

---

## 6. The replacement: an exact algebraic finiteness certificate

The beta guard exists for one purpose, to decide whether a zero run may be
believed. That purpose can be served exactly, with no heuristic at all.

**Construction.** The HJ expansion of a quadratic irrational is eventually
periodic, `[c_1,...,c_k, (c_{k+1},...,c_{k+p})^inf]`. Under the Moebius action
`[[A,B],[C,D]] . z = (Az+B)/(Cz+D)` the n-th convergent is `P_n . infinity`, so

    [x]_q = P_pre . w,    w = P_per . w,

with `P_pre = M(c_1)...M(c_k)` and `P_per = M(c_{k+1})...M(c_{k+p})`. Thus `w` is
a root of `C w^2 + (D - A) w - B = 0`, and substituting the inverse Moebius map
`w = (dz - b)/(a - cz)` gives a quadratic annihilating `u = [x]_q`:

    Q_+(z) = C (dz - b)^2 + (D - A)(dz - b)(a - cz) - B (a - cz)^2,

with coefficients in `Z[q, q^-1]`. So `[x]_q` is algebraic of degree at most 2
over `Q(q)`, exactly and constructively. The same construction applied to `-x`
gives `Q_-(z)` annihilating `v = [-x]_q`.

**Certificate.** `G(x) = u + v` equals a given Laurent polynomial `h` if and only
if `z = u` is a common root of `Q_+(z)` and `Q_-(h - z)`. When `Q_+` is
irreducible over `Q(q)`, a nonconstant gcd forces that common root to be `u`, so

    deg_z gcd( Q_+(z), Q_-(h - z) ) >= 1   <=>   G(x) = h.

This is a polynomial gcd over `Q(q)`. Nothing is estimated and no window, floor,
zero run, or lock target enters.

**Verified.** `algebraic.py` implements it; `cert_test.py` runs it.

* All **nine** on-axis finite values (`k sqrt(2)` for `k = 1..4`, `k sqrt(3)` for
  `k = 1..3`, `k sqrt(5)` for `k = 1,2`) are certified `True`, `Q_+` irreducible
  in every case. Their `G` values are now **proved**, not "finite-looking". For
  example `G(sqrt 2) = q - q^-2` and
  `G(3 sqrt 3) = q^5 + q^3 + q^2 + q + 2 - 2q^-1 - q^-2 - q^-3 - q^-4 - q^-6`.
* Controls: perturbing `h` by `q^7`, `q^3`, or `-q` is rejected in every case, so
  the test is not vacuous.

**Limitation, stated honestly.** The cost is driven by the HJ period length and
by the degrees in `Z[q]`, and the current sympy implementation does not terminate
in reasonable time on the deep near-rational points of the escalation set, whose
periods are long. It is immediately usable for the finite verdicts, which are the
only ones that need a certificate at all, because "infinite" already rests on a
positive witness. That is exactly the census's remaining soundness gap, so
closing it for the nine finite values closes the gap for the committed data.

---

## 7. Recommended restatement of the census claims

Replace every use of beta with one of the following, none of which depends on an
unproved statement.

1. **Infinite verdicts** are unchanged and already sound. A nonzero certified
   coefficient at a degree `>= 6` is a witness, and depth cannot remove it.
2. **Finite verdicts** should cite the section 6 algebraic certificate, not a zero
   run. All nine committed finite values now carry one.
3. **`finite_looking` should be renamed and demoted** to "no witness found below
   degree T", a statement about the search, not about `G`.
   **The guard `(lo + ld - 1) <= pred` should be KEPT, not removed.** An earlier
   draft of this document recommended removing it; that was wrong, and the
   evidence against it is item (iv) of section 1. All 264 off-axis points with a
   certified zero run to degree 100 have `B` between 104 and 625, and the guard
   is what correctly reclassifies every one of them as `unresolved-too-deep`
   instead of recording a false finite. Its masking role is sound and load
   bearing in the large-`B` regime. What must change is its *status*: it is a
   useful search heuristic, not a proof, and it supplies no protection at all
   when `B < 6` because it never fires there. Keep it, stop citing it as
   justification, and let (2) carry the finite verdicts.
4. If a cheap stopping rule is still wanted, use **Corollary 2.1** with an
   explicit `(n, m)` pair rather than `beta`. It is proved and it consults the
   whole expansion. It is sufficient, not necessary: it returns the first tail
   degree exactly only when the mixed convergent sum `Phi_{n,m}` has a clean
   window, and the counter-observation in section 3 shows the true tail degree
   need not be an agreement degree at all. Use it as a lower bound on how far to
   search, never as a licence to stop.

---


No record was created, per instructions. It should carry:

* **Claim.** `beta(x) = (c_1 - 1) + (c_2 - 1)`, and `B = max(beta(x), beta(-x))`,
  is not an upper bound on the first nonzero tail degree of `G(x) = [x]_q + [-x]_q`.
* **Status.** Disproved.
* **Witnesses.** The six table rows of section 1, each as
  `(D, a, b, HJ(x)[:4], HJ(-x)[:4], beta(x), beta(-x), B, d)` together with the
  certified coefficient vector of `G`. Headline witness
  `x = -16 + (48/7) sqrt(3)`, `D = 3`, `B = 5`, `d = 19`, coefficients zero on
  degrees 5 through 18 and `(19, 20, 21) -> (1, -3, 1)`, certified to degree 40.
  Second witness `x = 1 + (3/2) sqrt(2)`, `D = 2`, `B = 4`, `d = 8`, which the
  committed `sweep-D2-results.csv.gz` itself records with
  `first_nonzero_tail_index = 8`.
* **Population statistics.** (a) 222 of 1,944 fresh grid points (11.4 percent)
  satisfy `d > max(B, 6)`; grid `D in {2,3,5}`, numerators in `[-4,4]`,
  denominators in `{1,2,3}`, `G` computed to degree 24. (b) On the committed
  census restricted to `|x| <= 12`: D=2, 67,722 of 222,552 rows (30.4 percent)
  have `d > B` and 10,709 (4.8 percent) have `d > max(B, 6)`; D=3, 59,073 of
  203,486 (29.0 percent) and 9,051 (4.4 percent); D=5, 48,843 of 176,523
  (27.7 percent) and 7,714 (4.4 percent). Worst gaps 10, 14, 14.
* **Positive result.** Theorem B, statement and proof as in section 4, verified on
  33 instances with zero mismatches.
* **Re-audit of the prior evidence.** 2,896 escalation rows with a tail index,
  0 exceedances, 2,350 sharp, `predicted` range 70 to 2,940, zero rows with
  `predicted < 6`. Source `escalation-official.csv`, read only.
* **Replacement.** The section 6 certificate, with the nine on-axis finite values
  certified and three perturbation controls rejected.
* **Long-run population.** 1,876 points with a zero run of at least 10 from
  degree 6; 1,594 resolved with **0 exceedances**; 282 unresolved, of which 18
  are the known on-axis finite family and 264 are off-axis with `B` in
  `[104, 625]`, hence expected. Genuine long-run counterexamples (`B <= 100` with
  `G` certified zero on `[6, 100]`): **0**.
* **Large-`B` extension.** Fresh grid with `20 <= B <= 80`: D=5, 420 points,
  0 exceedances, 136 sharp; D=3, 378 points, 0, 170; D=2, 388 points, 0, 162.
  This is the first coverage of the large-`B` regime at D=5.
* **Method.** Exact `Fraction` and sympy `Rational` arithmetic; Laurent windows
  derived from `negation.window_bounds`; no floating point anywhere.

---

## 9. Open

* A necessary and sufficient condition for `G(x)` to be finite, stated on the HJ
  expansion. Section 6 decides it for a given `x` but does not characterise the
  solution set.
* Whether the gap `d - B` is bounded. The largest observed is 14, at
  `x = -16 + (48/7)sqrt(3)`. Nothing here proves any bound, and a proof would
  restore a usable, if shifted, heuristic.
* Whether a point exists with a zero run of 60 or more and a small `B`, which is
  the only configuration that could overturn a committed verdict. The longest run
  found among counterexamples is 13, at `x = -16 + (48/7)sqrt(3)` with `B = 5`.
  Separately, all 1,876 points with runs of at least 10 were located, and of the
  1,594 whose tail degree resolved below 100, zero exceed the bound, several with
  `B` and `d` in the 90s. So the long-run population does not misbehave where it
  can be measured. The search was a grid scan plus the committed data, not
  exhaustive, and nothing here rules the configuration out.
* The 264 off-axis points certified zero through degree 100 all have
  `B` in `[104, 625]`, so they are unresolved rather than finite. Resolving them
  means computing to degree `B`, which is the same cost problem as the 188
  permanently unresolved escalation rows. None is a counterexample at the depth
  reached, and none is a finite candidate on current evidence.
* A characterisation of the true first tail degree. It is not `beta`, and by the
  section 3 counter-observation it is not always `min(C_n, C'_m)` either.
* Scaling the section 6 certificate to long HJ periods.

---

## Files

| File | Role |
|---|---|
| `gtools.py` | certified `G` series, HJ helpers, `beta`, `B` |
| `quick.py` | 1,944-point exceedance scan |
| `deep.py` | prescribed-HJ-head experiments |
| `longrun.py` | two-stage scan for long zero runs, 22,446 points |
| `d5check.py` | large-`B` (escalation-style) population for `D = 3` and `D = 5` |
| `committed.py` | exceedance rate measured on the committed census, all three D |
| `unresolved.py` | classifies the 282 long-run points with no tail through degree 100 |
| `thmB.py` | numerical verification of Theorem B |
| `algebraic.py` | exact algebraic finiteness certificate |
| `cert_test.py` | certificate applied to the nine finite values plus controls |
