# q-numbers-results

Statements, evidence files and Lean sources for the results listed on the q-numbers results page.
Each result has its own folder under `results/`. `results.json` at the root is a copy of the site
data file that lists every result (generated_at 2026-09-18, 35 results).

## Layout

```
results.json                  copy of the site results file
LICENSE                       MIT
lean/                         combined Lake project (Lean 4.29.1 + Mathlib): lakefile, manifest, top module, audit config
lean-status.json              output of tools/audit_lean.py, one Lean status per result
tools/audit_lean.py           Lean audit script (standard library only)
.github/workflows/lean.yml    CI: build and audit
results/<id>/
  statement.tex               the LaTeX statement as a minimal snippet, first line names the id and status
  status.json                 id, status, date, lean.flag, lean.files, lean.no_sorry_in_source
  evidence/                   scripts, output files and short reports that back the result
  lean/                       only for results with a Lean file: the exact modules plus lake files (the GosperCF folders are built by the root lean/ project, degreeeq builds on its own)
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

Results with `lean.flag` true carry Lean 4 sources under `results/<id>/lean/`. The modules are
copies of the source files; only comments were edited (redactions), and the code text is
identical. Each folder also keeps the small Lake package it came from (`lakefile.toml`,
`lean-toolchain`, `lake-manifest.json`); the GosperCF `lakefile.toml` files carry an added `roots`
line so that only the copied modules are listed as library roots.

### Build

Two Lake projects are needed, because the four results do not share one Lean version.

| project | directory | Lean | Mathlib | results |
|---|---|---|---|---|
| combined | `lean/` | leanprover/lean4:v4.29.1 | v4.29.1, rev 5e932f97dd25535344f80f9dd8da3aab83df0fe6 (pinned in `lean/lake-manifest.json`) | pell-negation, intertwining, jump-gap |
| degreeeq | `results/degree-equality/lean/degreeeq` | leanprover/lean4:v4.31.0 | none | degree-equality |

```
cd lean
lake exe cache get      # optional but recommended: downloads prebuilt Mathlib files
lake build              # builds every module, including GosperCF.Pell and GosperCF.Intertwine

cd ../results/degree-equality/lean/degreeeq
lake build
```

`elan` selects the Lean version from each `lean-toolchain` file. The combined project reads the
module files in place from the per-result folders (`srcDir` in `lean/lakefile.toml`), so no file
is copied. Its top module `lean/QNumbersResults.lean` imports every module, so a bare `lake build`
is enough. `results/intertwining` and `results/pell-negation` each hold a copy of
`GosperCF/Intertwine.lean`; the two copies are byte-identical, only the `intertwining` copy is
built, and the audit fails if they ever differ.

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

The audit never edits the `status.json` files. GitHub Actions (`.github/workflows/lean.yml`) runs
the builds and the audit and checks that the committed `lean-status.json` is current.

### Key theorems

`lean-status.json` records, for each proved result, the key theorem, its location, and the axioms
it depends on. All four depend on `propext`, `Classical.choice` and `Quot.sound` only.

| result | key theorem | location |
|---|---|---|
| pell-negation | `GosperCF.Pell.N_conj_Lambda` | `results/pell-negation/lean/GosperCF/GosperCF/Pell.lean:126` |
| degree-equality | `DegreeEq.tight_iff_all_two` | `results/degree-equality/lean/degreeeq/Degreeeq.lean:337` |
| intertwining | `GosperCF.Intertwine.intertwine_iff_trace_zero` | `results/intertwining/lean/GosperCF/GosperCF/Intertwine.lean:196` |
| jump-gap | `GosperCF.gap_closed_form` | `results/jump-gap/lean/GosperCF/GosperCF/JumpGap.lean:129` |

### Check record

Run on 2026-09-18 with the audit above, on a copy of these files, not on the earlier scratch packages:
`lake build` in `lean/` finished with exit 0 (8257 jobs, Lean 4.29.1, Mathlib v4.29.1) and built
`GosperCF.Intertwine`, `GosperCF.Negation`, `GosperCF.Pell`, `GosperCF.JumpGap` and
`GosperCF.JumpGapDet`. `lake build` in the degreeeq project finished with exit 0 (Lean 4.31.0).
The generated `#print axioms` check resolved every public theorem and lemma (39 names in the
combined project, 15 in degreeeq) and reported no axiom outside the three standard ones.
The earlier check of 2026-09-18 on the full source packages is described by the `status.json`
fields `lean.compiled`, `lean.checked_on`, `lean.lean_version`, `lean.mathlib_rev` and
`lean.build_command`, which appear only for the four results with Lean sources.

Not verified: a build from an empty machine including the cache download was not run for this
layout, and the GitHub Actions workflow has not been run.

Theorem statements have not been audited for faithfulness to the paper. `lean.no_sorry_in_source`
and the `sorry` counts in `lean-status.json` are text searches and say nothing about statement
fidelity or about modules that are not in this repository.

## Results

| id | status | lean | evidence files |
|---|---|---|---|
| gap-a | proved | no | 9 |
| pell-negation | proved | yes | 16 |
| count-law | proved | no | 5 |
| dc-theorem-a | proved | no | 24 |
| t5-scalar | proved | no | 8 |
| lemma-n | proved | no | 1 |
| length5 | proved | no | 4 |
| length5-complete | verified | no | 3 |
| degree-equality | proved | yes | 3 |
| lemma-l | proved | no | 27 |
| intertwining | proved | yes | 20 |
| cubic-negation | verified | no | 1 |
| addition-nogo | proved | no | 8 |
| mult-nogo | proved | no | 3 |
| sqrt2-mod2 | proved | no | 33 |
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
| s-prime-formula | scooped | no | 2 |
| k6-level-six | scooped | no | 1 |
| negation-census | verified | no | 7 |
| twin-primes | proved | no | 8 |
| realizability | verified | no | 2 |
| k-uniformity | verified | no | 7 |
| q-somos | verified | no | 17 |
| orbit-closure | verified | no | 26 |
| divisor-hypothesis | open | no | 0 |
| negation-criterion | open | no | 5 |
