# q-numbers-results

Statements, evidence files and Lean sources for the results listed on the q-numbers results page.
Each result has its own folder under `results/`. `results.json` at the root is a copy of the site
data file that lists every result (generated_at 2026-09-18, 35 results).

**To browse the results, open [RESULTS.md](RESULTS.md).** Each result folder also has a README.md with its statement, Lean status and evidence files.

## Layout

```
results.json                  copy of the site results file
LICENSE                       MIT
lean/                         combined Lake project (Lean 4.29.1 + Mathlib): lakefile, manifest, top module, audit config
lean-status.json              output of tools/audit_lean.py, one Lean status per result
tools/audit_lean.py           Lean audit script (standard library only)
tools/make_pages.py           writes RESULTS.md and each results/<id>/README.md from results.json and status.json
RESULTS.md                    every result in one table, grouped by status
.github/workflows/lean.yml    CI: build and audit
results/<id>/
  statement.tex               the LaTeX statement as a minimal snippet, first line names the id and status
  status.json                 id, status, date, lean.flag, lean.files, lean.no_sorry_in_source; for Lean results also lean.coverage and lean.covers; for Lean results also lean.coverage and lean.covers
  evidence/                   scripts, output files and short reports that back the result
  lean/                       only for results with a Lean file: the exact modules plus lake files (all Mathlib-based modules are built by the root lean/ project, degreeeq builds on its own)
```

An `evidence/` folder that holds only `.gitkeep` means no shippable artifact was found for that
result. It does not mean that no evidence exists. Some scripts and reports were left out because
they carry internal context that cannot be published, and a few files had incidental path strings,
names and record identifiers redacted in place. Redacted scripts may therefore not run unchanged.
Evidence files are grouped by topic. They were not re-run for this repository.

## Status definitions

The definitions below are the legend of `results.json`.

| status | meaning |
|---|---|
| proved | Proved on paper, and in some cases machine-checked in Lean. |
| verified | Established by exact computation over a stated search range. Not a proof. |
| disproved | A claim that was believed, tested, and found false. Includes my own. |
| scooped | Correct, but already in the literature. Found during a novelty check. |
| open | Stated precisely, not settled. |

One row per result. Status is not editorial. A result that turned out false stays in the table with status 'disproved', because the record of what failed is the point.

## Lean

Results with a `results/<id>/lean/` folder carry Lean 4 sources (`lean.flag` true in `status.json`).
The modules of pell-negation, intertwining, jump-gap and degree-equality are copies of source
files in which only comments were edited (redactions), and the code text is identical. Their
folders also keep the small Lake package they came from (`lakefile.toml`, `lean-toolchain`,
`lake-manifest.json`); the GosperCF `lakefile.toml` files carry an added `roots` line so that
only the copied modules are listed as library roots. The other results hold one `.lean` file each.

### What `proved` means, and what coverage adds

`proved` is a statement about the Lean file only: it compiles under `lake build`, contains no
`sorry`, declares no axiom, and `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound` for every public theorem. It does not say how much of the claim in the ledger the
file covers. `coverage` (in `status.json` as `lean.coverage`, with a one-sentence `lean.covers`)
says that. Values: `full` (the Lean statement is the ledger claim or stronger), `narrower` (a
faithful statement of part of the claim), `partial` (a real theorem, but it leaves out the
central content of the claim), `conditional` (the claim is derived from hypotheses that Lean does
not prove), `statement_only` (the statement compiles and the proof is `sorry`), `unreviewed` (no
reviewer has compared the Lean statement with the ledger claim yet).

State is the audit result in `lean-status.json`. Coverage comes from a read-only comparison of
each Lean statement with the paper statement and the ledger row, made once and recorded here;
it is not recomputed by any script.

| id | state | coverage | what the Lean file covers |
|---|---|---|---|
| t5-scalar | proved | full | For every positive Pell automorph, the R,L-word q-deformation Λ_q satisfies q(A-D)=(q-1)(qB+C) and C\|B iff C\|A-D in ℤ[q,q⁻¹]. |
| lemma-n | proved | full | Negation symmetry of the cyclotomic vanishing locus V_j(k), every length, every k>1. |
| addition-nogo | proved | full | Lean 4 proves that no nonzero (a,...,h) in Q(q)^8 satisfies (aXY+bX+cY+d) - [x+y]_q (eXY+fX+gY+h) = 0 for all rational x,y > 1 (X=[x]_q, Y=[y]_q, MGO continued-fraction definition). The 8x8 relation matrix at eight explicit samples has rank 8. |
| mult-nogo | proved | narrower | Lean 4 proves [xy]_q is not bihomographic in [x]_q and [y]_q over Q(q), with the same relation and rank-8 certificate as for addition. That the q-reversal is not the obstruction here is a computation, not a Lean result. |
| twin-primes | proved | narrower | For every m >= 2, the q-rational of m/(m^2-1) is q^(m-1)[m]_q/([m-1]_q[m+1]_q) in lowest terms, and its reduced denominator equals Phi_{m-1} Phi_{m+1} exactly when m-1 and m+1 are both prime (Lean 4). The wider claim over all numerators of d = p p' is not formalised. |
| intertwining | proved | narrower | For det-1 real M fixing distinct x, x^σ (m3≠0), NMN=M⁻¹ iff x+x^σ=0; the equivalence with x=b0√D is not formalised. |
| gap-a | proved | conditional | Lean 4 checks the integer-matrix identity R^m N M N R^-m = M^-1 and, taking four published transformation laws of the mismatch ratio as hypotheses, derives r(M)^2 = q^{2m} and r(M) = +-1 iff x + x^sigma = 0. The q-deformation and the four laws themselves are not formalised. |
| dc-theorem-a | proved | full | Lean proves, with no hypothesis and no sorry, that for l in {2,3,4,5}, any prime p and any a, if Phi_{p^a l} divides the continuant S of an integer word c_2..c_i then Phi_l divides it, at every length; it does not cover l >= 6 or any statement about C-entries of Lambda_q. |
| length5 | proved | full | Proved in Lean: for every k > 1 and every integer word whose residues mod k lie in the five shapes or the ten words, Phi_k divides S_5 (the converse is not proved). |
| pell-negation | proved | partial | Lean verifies N·Λ·N=Λ⁻¹ (and k-th powers) for the integer Pell automorph; the q-deformed identity [√d]_q+[-√d]_q=(A-D)/C is not formalised. |
| jump-gap | proved | partial | Over any field, if RS'-R'S=q^E then M·(1,0)-M·(1,1-q)=(1-q)q^E/(S(S+(1-q)S')); separately, an even-length continuant block product has determinant q^(alternating digit sum). The link to the rational jump gap and to E=Σa_i-1 is not formalised. |
| degree-equality | proved | partial | For digits ≥2, Σ_{j=2}^k(c_j-1)=s_k-1 iff c_2=...=c_k=2 (k≥3). The bridge to deg S=d-1 and a≡±1 (mod d) is not formalised. |
| length5-complete | statement_only | statement_only | The Lean file only states, and proves nothing (all four theorems are sorry): list-inclusion for 4 <= k <= 24 with k != 5, the k = 5 locus as the list plus (2,2,2,2) and (3,3,3,3), and the counts 10k and 52. The finite check itself is a Python computation. |
| count-law | statement_only | partial | Lean proves that V_i(k) equals the divisibility locus of Phi_k in S_i and that the torsion points of X_i = {U_i=0} form a finite union of torsion cosets, the latter relative to Laurent's theorem, which is stated but not proved; the congruence-system form of Theorem A is not formalised. |
| lemma-l | statement_only | statement_only | Statement only (the Lean proof is sorry): for odd p and a Pell automorph, if the divisibility chain Phi_{p^a} \| C => Phi_{p^j} \| C (j<a) holds for that C, then Phi_{p^a} \| C implies Phi_{p^a} \| A - D; the chain (DC) itself is assumed, not proved. |
| sqrt2-mod2 | statement_only | conditional | Lean proves that any integer power series solving MGO's equation q^2y^2-(q^3-1)y-(q^2+1)=0 has even coefficients at n = 1 mod 3; that [sqrt2]_q is such a series (convergence plus MGO Proposition 4.5) is cited, not proved in Lean. |
| k6-level-six | statement_only | statement_only | Statement only: the Lean file states, without proving, that Phi_6 \| S_i implies [6]_q \| S_i and 6 \| S_i(1); the result is Byakuno-Ren-Yanagawa Proposition 5.3. |
| s-prime-formula | statement_only | statement_only | Statement only: the Lean file states, without proof, the formula 2S'(1) = d deg S + a^-1 - a; it is a known result of Lasker, arXiv:2309.10819, Lemma 6.1 and Corollary 6.2. |

`unreviewed` rows have not been read by a reviewer for faithfulness. For those, `proved` says only
that the file compiles without `sorry`.

Findings behind the table (from that comparison):

- pell-negation: the Lean theorem is the classical integer identity `N Lambda N = Lambda^-1`.
  The q-deformed identity in the ledger row is not formalised, and `neg_sum_pure_sqrt` takes the
  conjugate-root relation as a hypothesis.
- jump-gap: the gap formula is proved for arbitrary field elements with the determinant relation as a
  hypothesis; the link to rational q-numbers and to the exponent `E = sum a_i - 1` is not
  formalised. The determinant lemma gives `q^(alternating digit sum)`, not `sum a_i - 1`.
- degree-equality: only the digit criterion is proved; no polynomial `S`, no degree, no `[d]_q`.
- intertwining: real determinant-1 matrices with distinct fixed points; the `x = b0 sqrt D` clause is not formalised.
- gap-a: conditional. The integer-matrix loop identity is proved; the q-deformation, the mismatch ratio
  and its four transformation laws are hypotheses of the structure `MismatchLaws`, and the sign
  step (`r = q^m`, not `-q^m`) is not formalised.
- twin-primes: the family `m/(m^2-1)` for every `m >= 2`; the theorem over all numerators of `d = p p'` is not formalised. "Two cyclotomic factors" is formalised as the equation `S = Phi_{m-1} Phi_{m+1}`.
- addition-nogo, mult-nogo: same relation and rank-8 certificate; the samples are eight explicit rational pairs chosen for the Lean proof, and the relation is assumed only at rational `x, y > 1`. For mult-nogo the ledger clause that the q-reversal is absent as the obstruction is a computation, not a Lean result.
- t5-scalar, lemma-n: the Lean statements are at least as strong as the ledger rows. "Lemma N" here is the negation lemma; another lemma of that name in the working notes was refuted and is not this one.
- length5-complete: the literal list-inclusion for `k = 5` is false as originally written; at `k = 5` the vanishing locus is the list plus the words (2,2,2,2) and (3,3,3,3) (52 words against 50). `statement.tex` and the Lean statement give list-inclusion for `4 <= k <= 24`, `k != 5`, and the `k = 5` exception separately.
- Two meanings of `S`. In dc-theorem-a, length5, length5-complete, count-law and k6-level-six, `S` is the recurrence `S_{i+1} = [c_{i+1}] S_i - q^(c_i - 1) S_{i-1}`, which is the reduced q-denominator of the NEGATIVE continued fraction `c_1 - 1/(c_2 - 1/...)` (up to a power of `q`), stated for all integer words. In s-prime-formula and sqrt2-mod2, `S` and the coefficients come from R,L words, that is, the regular continued fraction. A bare `S` therefore means different things across these results.
- count-law: the residual `sorry` is Laurent's theorem on torsion points, stated over C for a hypersurface. The write-up's congruence form of Theorem A and Theorems B and C are not formalised.
- lemma-l: the Lean statement assumes only the divisibility chain (DC) for that Pell automorph. The paper's conditional reduction also assumes Lemma L at lower levels; that part is recovered by induction in a working note. dc-theorem-a does not discharge the chain.
- sqrt2-mod2: the cited `sorry` bundles the convergence of the even-length convergents in Z[[q]], the choice of that convergent sequence, and MGO's Proposition 4.5. The Lean proof is an elementary mod-2 induction, not the Christol and Walnut automaton argument. The `n < 40` lemma is a recurrence check and says nothing about the q-real.
- statement-only files (count-law, lemma-l, length5-complete, sqrt2-mod2, k6-level-six, s-prime-formula) contain `sorry`; count-law and sqrt2-mod2 also contain proved lemmas, listed in their file headers.

### Build

Two Lake projects are needed, because degree-equality does not share the Lean version of the others.

| project | directory | Lean | Mathlib | results |
|---|---|---|---|---|
| combined | `lean/` | leanprover/lean4:v4.29.1 | v4.29.1, rev 5e932f97dd25535344f80f9dd8da3aab83df0fe6 (pinned in `lean/lake-manifest.json`) | every result above except degree-equality |
| degreeeq | `results/degree-equality/lean/degreeeq` | leanprover/lean4:v4.31.0 | none | degree-equality |

```
cd lean
lake exe cache get      # optional but recommended: downloads prebuilt Mathlib files
lake build              # builds every module of the combined project

cd ../results/degree-equality/lean/degreeeq
lake build
```

`elan` selects the Lean version from each `lean-toolchain` file. The combined project reads the
module files in place from the per-result folders (`srcDir` in `lean/lakefile.toml`), so no file
is copied. It has one library per result folder, and its top module `lean/QNumbersResults.lean`
imports every module, so a bare `lake build` is enough. Each single-file result is its own
library and its own Lean namespace: `LemmaN` and `DCTheoremA` both define `S`, `qint` and related
names, in different namespaces, and no declaration is shared or renamed. `results/intertwining`
and `results/pell-negation` each hold a copy of `GosperCF/Intertwine.lean`; the two copies are
byte-identical, only the `intertwining` copy is built, and the audit fails if they ever differ.
`results/gap-a` imports `GosperCF.Intertwine`.

Memory: building `results/dc-theorem-a/lean/DCTheoremA.lean` peaked near 8.0 GB resident on the
machine used for the check (a file that only imports Mathlib measures about 5.3 GB). Build it alone
if memory is limited (`lake build DCTheoremA`).

degreeeq is not merged into the combined project because it was checked only under Lean 4.31.0
without Mathlib. Moving it to 4.29.1 would need a new check of that file, which is a different
check from the one on record.

### Audit

```
python3 tools/audit_lean.py
```

The script uses the Python standard library only. For every `results/<id>/` it does the following.

1. Scans each Lean file with comments (nested block comments included) and string and character
   literals removed, and counts `sorry` and `axiom` declarations. A `sorry` inside a comment does
   not count. It also lists uses of `native_decide`, `implemented_by`, `extern` and `unsafe`.
2. Checks that duplicate copies of one module are byte-identical.
3. Runs `lake build` in the owning project.
4. Generates a Lean file with `#print axioms` for every public top-level theorem and lemma, runs it
   with `lake env lean`, and accepts only `propext`, `Classical.choice` and `Quot.sound`.
5. Writes `lean-status.json` at the repository root. Each id gets one status:
   `proved` (built, no `sorry`, no `axiom` declaration, standard axioms only, key theorem
   checked), `statement_only` (built, but `sorry`, an axiom declaration or a non-standard axiom is
   present), `source_only` (Lean source exists but was not built, for example when Lake is not
   installed; the script then says so and skips the build and the axiom check) or `none`.
   Lean files outside `results/<id>/lean/` (for example under `evidence/`) are scanned and listed
   as `unbuilt_files`, and never count as built.
6. Compares each observed status with `expected_state` in `lean/audit-config.json` and exits 1 on a
   difference, so a result that is meant to be `statement_only` does not fail the audit and a result
   that regresses does. Update the config and the table above together.

The audit never edits the `status.json` files. GitHub Actions (`.github/workflows/lean.yml`) runs
the builds and the audit and checks that the committed `lean-status.json` is current.

### Key theorems

`lean-status.json` records, for each result, the key theorem, its location, and the axioms it
depends on. `sorryAx` in the last column marks a statement-only result.

| result | key theorem | location | axioms |
|---|---|---|---|
| t5-scalar | `T5Scalar.t5_scalar` | `results/t5-scalar/lean/T5Scalar.lean:533` | propext, Classical.choice, Quot.sound |
| lemma-n | `LemmaN.S_neg` | `results/lemma-n/lean/LemmaN.lean:181` | propext, Classical.choice, Quot.sound |
| addition-nogo | `AdditionNogo.nogo_ratfunc` | `results/addition-nogo/lean/AdditionNogo.lean:406` | propext, Classical.choice, Quot.sound |
| mult-nogo | `MultNogo.nogo_ratfunc` | `results/mult-nogo/lean/MultNogo.lean:406` | propext, Classical.choice, Quot.sound |
| twin-primes | `TwinPrimes.family_twin` | `results/twin-primes/lean/TwinPrimes.lean:263` | propext, Classical.choice, Quot.sound |
| intertwining | `GosperCF.Intertwine.intertwine_iff_trace_zero` | `results/intertwining/lean/GosperCF/GosperCF/Intertwine.lean:196` | propext, Classical.choice, Quot.sound |
| gap-a | `GapA.example64_step_iff` | `results/gap-a/lean/GapA.lean:226` | propext, Classical.choice, Quot.sound |
| dc-theorem-a | `DCTheoremA.dc_theorem_a_all` | `results/dc-theorem-a/lean/DCTheoremA.lean:962` | propext, Classical.choice, Quot.sound |
| length5 | `Length5.length5_vanishing` | `results/length5/lean/Length5.lean:419` | propext, Classical.choice, Quot.sound |
| pell-negation | `GosperCF.Pell.N_conj_Lambda` | `results/pell-negation/lean/GosperCF/GosperCF/Pell.lean:126` | propext, Classical.choice, Quot.sound |
| jump-gap | `GosperCF.gap_closed_form` | `results/jump-gap/lean/GosperCF/GosperCF/JumpGap.lean:129` | propext, Classical.choice, Quot.sound |
| degree-equality | `DegreeEq.tight_iff_all_two` | `results/degree-equality/lean/degreeeq/Degreeeq.lean:337` | propext, Classical.choice, Quot.sound |
| length5-complete | `Length5Complete.length5_complete` | `results/length5-complete/lean/Length5Complete.lean:270` | propext, sorryAx, Classical.choice, Quot.sound |
| count-law | `CountLaw.count_law_torsion` | `results/count-law/lean/CountLaw.lean:336` | propext, sorryAx, Classical.choice, Quot.sound |
| lemma-l | `LemmaL.lemma_L_prime_power` | `results/lemma-l/lean/LemmaL.lean:82` | propext, sorryAx, Classical.choice, Quot.sound |
| sqrt2-mod2 | `Sqrt2Mod2.sqrt2_mod2` | `results/sqrt2-mod2/lean/Sqrt2Mod2.lean:199` | propext, sorryAx, Classical.choice, Quot.sound |
| k6-level-six | `K6LevelSix.level_six` | `results/k6-level-six/lean/KSix.lean:128` | propext, sorryAx, Classical.choice, Quot.sound |
| s-prime-formula | `SPrimeFormula.s_prime_formula` | `results/s-prime-formula/lean/SPrimeFormula.lean:70` | propext, sorryAx, Classical.choice, Quot.sound |

### Check record

Run on 2026-09-18 with the audit above, on a copy of these files, not on the earlier scratch packages. Mathlib's prebuilt files were reused from a local clone at the pinned rev, not downloaded during this check:
every library of the combined project was built with its own `lake build <Library>` (one at a time, `LEAN_NUM_THREADS=2`), and then a bare `lake build` in `lean/` finished with exit 0 (Lean 4.29.1, Mathlib v4.29.1). `lake build` in the degreeeq project finished with exit 0 (Lean 4.31.0).
The generated `#print axioms` check resolved every public theorem and lemma (377 names in the
combined project, 15 in degreeeq); the only non-standard axiom reported is `sorryAx`, for the six
statement-only results.
The earlier per-result checks are described by the `status.json` fields `lean.compiled`,
`lean.compiled_on` or `lean.checked_on`, `lean.lean_version`, `lean.mathlib_rev` and
`lean.build_command`.

Not verified: a build from an empty machine including the cache download was not run for this
layout, and the GitHub Actions workflow has not been run.

`lean.no_sorry_in_source` and the `sorry` counts in `lean-status.json` are text searches. Coverage
in the table above is a one-time reading, not a script result, and rows marked `unreviewed` have
not been read.

## Results

| id | status | lean | evidence files |
|---|---|---|---|
| gap-a | proved | yes | 9 |
| pell-negation | proved | yes | 16 |
| count-law | proved | yes | 5 |
| dc-theorem-a | proved | yes | 24 |
| t5-scalar | proved | yes | 8 |
| lemma-n | proved | yes | 1 |
| length5 | proved | yes | 4 |
| length5-complete | verified | yes | 3 |
| degree-equality | proved | yes | 3 |
| lemma-l | proved | yes | 27 |
| intertwining | proved | yes | 20 |
| cubic-negation | verified | no | 1 |
| addition-nogo | proved | yes | 8 |
| mult-nogo | proved | yes | 3 |
| sqrt2-mod2 | proved | yes | 33 |
| sqrt2-mod2-biconditional | disproved | no | 3 |
| trace-zero | disproved | no | 3 |
| t1-beta | disproved | no | 44 |
| partition-claim | disproved | no | 3 |
| roots-of-unity | disproved | no | 2 |
| catalan-rival | disproved | no | 2 |
| length5-incomplete | disproved | no | 2 |
| census-window | disproved | no | 1 |
| r1-float-dedup | disproved | no | 0 |
| jump-gap | scooped | yes | 7 |
| s-prime-formula | scooped | yes | 2 |
| k6-level-six | scooped | yes | 1 |
| negation-census | verified | no | 7 |
| twin-primes | proved | yes | 8 |
| realizability | verified | no | 2 |
| k-uniformity | verified | no | 7 |
| q-somos | verified | no | 17 |
| orbit-closure | verified | no | 26 |
| divisor-hypothesis | open | no | 0 |
| negation-criterion | open | no | 5 |
