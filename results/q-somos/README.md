# q-somos

![status: Verified by computation](https://img.shields.io/badge/status-Verified%20by%20computation-2f5bd3) ![logged: 2026-06](https://img.shields.io/badge/logged-2026--06-999999)

**In short.** Checked all 49 integer pairs for the q-twisted Somos-4 recurrence stay Laurent through x_4 to x_11; 48 of 49 are non-trivial reparametrisations.

## Statement

All 49 integer pairs (a,b) in {-3..3}^2 for the q-twisted Somos-4 recurrence stay Laurent through x_4 to x_11, and 48 of the 49 are not trivial reparametrisations.

```math
\begin{aligned}
&x_{n+4}\,x_n=q^{a}\,x_{n+3}\,x_{n+1}+q^{b}\,x_{n+2}^{2}\\
&x_4,\dots,x_{11}\in\mathbb{Z}[q^{\pm1}][x_0^{\pm1},\dots,x_3^{\pm1}]\ \ \text{for all }(a,b)\in\{-3,\dots,3\}^{2}\\
&\{(a,b):\ b=\tfrac{4a}{3}\}\cap\{-3,\dots,3\}^{2}=\{(0,0)\}
\end{aligned}
```

*Verified by computation:* Established by exact computation over a stated search range. Not a proof.

## Evidence

- [`2_README.md`](evidence/2_README.md)
- [`2_tables.tex`](evidence/2_tables.tex)
- [`3_README.md`](evidence/3_README.md)
- [`3_tables.tex`](evidence/3_tables.tex)
- [`README.md`](evidence/README.md)
- [`laurent_examples.csv`](evidence/laurent_examples.csv)
- [`proof_check.csv`](evidence/proof_check.csv)
- [`qsomos_twist_results.csv`](evidence/qsomos_twist_results.csv)
- [`run.py`](evidence/run.py)
- [`somos_check.csv`](evidence/somos_check.csv)
- [`somos_repro.py`](evidence/somos_repro.py)
- [`somos_table.csv`](evidence/somos_table.csv)
- [`summary.csv`](evidence/summary.csv)
- [`tables.tex`](evidence/tables.tex)
- [`twist_proof_check.py`](evidence/twist_proof_check.py)
- [`twist_search.csv`](evidence/twist_search.csv)
- [`twist_search.py`](evidence/twist_search.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
