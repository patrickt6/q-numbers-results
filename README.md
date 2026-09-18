# q-numbers-results

Statements, evidence files and Lean sources for the results listed on the q-numbers results page.
Each result has its own folder under `results/`. `results.json` at the root is a copy of the site
data file that lists every result (generated_at 2026-09-18, 35 results).

## Layout

```
results.json                  copy of the site results file
LICENSE                       MIT
results/<id>/
  statement.tex               the LaTeX statement as a minimal snippet, first line names the id and status
  status.json                 id, status, date, lean.flag, lean.files, lean.no_sorry_in_source
  evidence/                   scripts, output files and short reports that back the result
  lean/                       only for results with a Lean file: the exact modules plus lake files
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

Results with `lean.flag` true carry Lean 4 sources under `results/<id>/lean/`. Each folder is a
Lake package that holds the modules for that result, a `lakefile.toml`, a `lean-toolchain` and a
`lake-manifest.json`. The modules are copies of the source files; only comments were edited
(redactions), and the code text is identical. The `lakefile.toml` of the GosperCF package
carries an added `roots` line so that only the copied modules are listed as library roots.

Compile check, run on 2026-09-18 in a scratch copy of the full source packages (not in these
folders):

| package | Lean | Mathlib | commands | result |
|---|---|---|---|---|
| GosperCF | leanprover/lean4:v4.29.1 | v4.29.1, rev 5e932f97dd25535344f80f9dd8da3aab83df0fe6 | `lake build` (8262 jobs); `lake build GosperCF.Pell GosperCF.Intertwine` | both exit 0 |
| degreeeq | leanprover/lean4:v4.31.0 | none | `lake build` | exit 0 |

`GosperCF.lean` does not import `Pell` or `Intertwine`, so those two modules need the second
command. `#print axioms` on the key theorems reports only `propext`, `Classical.choice` and
`Quot.sound` (`sufficiency` in degreeeq reports `propext` and `Quot.sound`). No `sorryAx` and no
custom axiom appear. Key theorems: `Pell.N_conj_Lambda` (pell-negation, `GosperCF/Pell.lean:126`),
`DegreeEq.tight_iff_all_two` (degree-equality, `Degreeeq.lean:337`),
`Intertwine.intertwine_iff_trace_zero` (intertwining, `GosperCF/Intertwine.lean:196`),
`GosperCF.gap_closed_form` (jump-gap, `GosperCF/JumpGap.lean:129`).

The `status.json` fields `lean.compiled`, `lean.checked_on`, `lean.lean_version`,
`lean.mathlib_rev` and `lean.build_command` record this check and appear only for the four
results with Lean sources. The subset packages in this repository, with the added `roots` line,
were not rebuilt in that check. Theorem statements have not been audited for faithfulness to the
paper. `lean.no_sorry_in_source` is a text search for `sorry` outside comments in the copied
modules and says nothing about statement fidelity or about modules that were not copied.

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
