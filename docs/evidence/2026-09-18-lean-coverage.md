# Lean coverage, 2026-09-18

This note records the Lean audit behind the numbers on the results page. Read it
before quoting any Lean number.

## Two labels per result

Each result with Lean sources has two labels. They answer different questions.

- Compile label (`lean-status.json`, field `status`). Does the Lean build
  with `lake build`, with no `sorry` and only the standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`)? Values: `proved`, `statement_only`.
- Coverage label (`results/<id>/status.json`, field `lean.coverage`). How
  much of the written claim does the Lean state? Values: `full`, `narrower`,
  `conditional`, `partial`, `statement_only`.

A result can compile with no `sorry` and still cover less than the written
claim. The public label is the coverage label. Where the two disagree, the page
uses the more conservative one.

## Counts (35 results)

| Label | Count |
|---|---|
| Compile: `proved` | 12 |
| Compile: `statement_only` | 6 |
| No Lean sources | 17 |
| Coverage: `full` | 5 |
| Coverage: `narrower` | 3 |
| Coverage: `conditional` | 2 |
| Coverage: `partial` | 4 |
| Coverage: `statement_only` | 4 |

Only the 5 `full` results have a Lean proof of the whole written claim.

## Per result

"Result status" is the mathematical status of the claim on paper. It is not a
Lean label.

| Result | Result status | Compile label | Coverage label (public) |
|---|---|---|---|
| [addition-nogo](../../results/addition-nogo/status.json) | proved | proved | full |
| [count-law](../../results/count-law/status.json) | proved | statement_only | partial |
| [dc-theorem-a](../../results/dc-theorem-a/status.json) | proved | proved | full |
| [degree-equality](../../results/degree-equality/status.json) | proved | proved | partial |
| [gap-a](../../results/gap-a/status.json) | proved | proved | conditional |
| [intertwining](../../results/intertwining/status.json) | proved | proved | narrower |
| [jump-gap](../../results/jump-gap/status.json) | scooped | proved | partial |
| [k6-level-six](../../results/k6-level-six/status.json) | scooped | statement_only | statement_only |
| [lemma-l](../../results/lemma-l/status.json) | proved | statement_only | statement_only |
| [lemma-n](../../results/lemma-n/status.json) | proved | proved | full |
| [length5](../../results/length5/status.json) | proved | proved | full |
| [length5-complete](../../results/length5-complete/status.json) | verified | statement_only | statement_only |
| [mult-nogo](../../results/mult-nogo/status.json) | proved | proved | narrower |
| [pell-negation](../../results/pell-negation/status.json) | proved | proved | partial |
| [s-prime-formula](../../results/s-prime-formula/status.json) | scooped | statement_only | statement_only |
| [sqrt2-mod2](../../results/sqrt2-mod2/status.json) | proved | statement_only | conditional |
| [t5-scalar](../../results/t5-scalar/status.json) | proved | proved | full |
| [twin-primes](../../results/twin-primes/status.json) | proved | proved | narrower |

## gap-a

gap-a compiles with no `sorry`, but its coverage is `conditional`. The file
proves the integer-matrix identity and the arithmetic step in full. It takes the
four transformation laws of the mismatch ratio as hypotheses (the structure
`MismatchLaws`) and does not construct the q-deformed ratio. The public label
is conditional. See `results/gap-a/status.json`, fields `lean.scope` and
`lean.faithfulness_note`.

## What "377" means

`tools/audit_lean.py --require-lake` resolved 377 of 377 theorem names in
the main Lean project (`lean/`, Lean 4.29.1, Mathlib v4.29.1) and 15 of 15
in the separate degree-equality project
(`results/degree-equality/lean/degreeeq`). The configuration is
`lean/audit-config.json`.

These are counts of theorem names the audit checked. They are not counts of
theorems proved: they include the theorems in the 6 `statement_only` results,
which depend on `sorry`. Do not write "377 theorems proved" or "392 theorems
proved".

## Double count: 392, not 401

377 + 15 = 392 theorem names in 21 distinct modules. Summing `theorem_count`
over every file listed in `lean-status.json` gives 401, because the module
`GosperCF.Intertwine` is listed under both pell-negation and intertwining. The
same kind of double count produced an earlier figure of 229. Count distinct
modules.

## Re-check

```
cd lean && lake build
python3 tools/audit_lean.py --require-lake
```

The `lean` workflow in `.github/workflows/lean.yml` runs the build. One file
(dc-theorem-a) needs about 8 GB of memory to build.
