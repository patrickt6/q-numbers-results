# dc-theorem-a

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: full claim](https://img.shields.io/badge/Lean%204-full%20claim-222222) ![logged: 2026-08](https://img.shields.io/badge/logged-2026--08-999999)

**In short.** Proved downward closure: Phi_{p^a l} dividing S forces Phi_l to divide S, for l in {2,3,4,5}, at every word length.

## Statement

Downward closure: for l in {2,3,4,5}, any prime p and any a >= 1, Phi_{p^a l} dividing S forces Phi_l to divide S, at every word length.

```math
\begin{aligned}
&l\in\{2,3,4,5\},\ \ p\ \text{prime},\ \ a\ge1,\ \ k=p^{a}l\\
&\Phi_k\mid S\ \Longrightarrow\ \Phi_l\mid S\\
&S=S_i,\ \ \text{every }i\ge1\ \text{and every integer word}
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

Lean proves, with no hypothesis and no sorry, that for l in {2,3,4,5}, any prime p and any a, if Phi_{p^a l} divides the continuant S of an integer word c_2..c_i then Phi_l divides it, at every length; it does not cover l >= 6 or any statement about C-entries of Lambda_q.

- `DCTheoremA.lean`

Build: `cd lean && lake build DCTheoremA`

## Evidence

- [`01_anchor.py`](evidence/01_anchor.py)
- [`02_dc_exhaustive.py`](evidence/02_dc_exhaustive.py)
- [`02_output.log`](evidence/02_output.log)
- [`03_value_sets.py`](evidence/03_value_sets.py)
- [`04_obstruction.py`](evidence/04_obstruction.py)
- [`05_lift_hunt.py`](evidence/05_lift_hunt.py)
- [`05_output.log`](evidence/05_output.log)
- [`06_coverage.py`](evidence/06_coverage.py)
- [`07_lemma2_on_hits.py`](evidence/07_lemma2_on_hits.py)
- [`08_units_norms.py`](evidence/08_units_norms.py)
- [`audit.py`](evidence/audit.py)
- [`audit2.py`](evidence/audit2.py)
- [`audit3.py`](evidence/audit3.py)
- [`audit3b.py`](evidence/audit3b.py)
- [`dc84_sweep.py`](evidence/dc84_sweep.py)
- [`downward-closure-hits.csv`](evidence/downward-closure-hits.csv)
- [`downward_closure.py`](evidence/downward_closure.py)
- [`full_run_output.txt`](evidence/full_run_output.txt)
- [`n2_dc_check.py`](evidence/n2_dc_check.py)
- [`phi8_divides_s_search.py`](evidence/phi8_divides_s_search.py)
- [`phi8_search_result.json`](evidence/phi8_search_result.json)
- [`ring.py`](evidence/ring.py)
- [`run_output.log`](evidence/run_output.log)
- [`verify_multiplicative_step.py`](evidence/verify_multiplicative_step.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
