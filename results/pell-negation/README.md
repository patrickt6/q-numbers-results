# pell-negation

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: part of the claim](https://img.shields.io/badge/Lean%204-part%20of%20the%20claim-222222) ![logged: 2026-07](https://img.shields.io/badge/logged-2026--07-999999)

**In short.** Proved [sqrt d]_q + [-sqrt d]_q = (A-D)/C from the fundamental Pell automorph, turning an infinite search into one divisibility check.

## Statement

For any nonsquare d, the quantity [sqrt d]_q + [-sqrt d]_q equals (A-D)/C read off the fundamental Pell automorph, reducing an infinite question to one divisibility check.

```math
\begin{aligned}
&d\ \text{nonsquare},\ \ r^{2}-ds^{2}=1\ (s\ge1\ \text{minimal})\\
&\rho\begin{pmatrix}r&ds\\ s&r\end{pmatrix}=\begin{pmatrix}A&B\\ C&D\end{pmatrix}\\
&[\sqrt d\,]_q+[-\sqrt d\,]_q=\frac{A-D}{C}\\
&[\sqrt d\,]_q+[-\sqrt d\,]_q\in\mathbb{Z}[q,q^{-1}]\iff C\mid A-D
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

Lean verifies N·Λ·N=Λ⁻¹ (and k-th powers) for the integer Pell automorph; the q-deformed identity [√d]_q+[-√d]_q=(A-D)/C is not formalised.

- `Intertwine.lean`
- `Negation.lean`
- `Pell.lean`

Build: `lake build && lake build GosperCF.Pell GosperCF.Intertwine`

## Evidence

- [`mgo_engine.py`](evidence/mgo_engine.py)
- [`pell.py`](evidence/pell.py)
- [`proof_verification.py`](evidence/proof_verification.py)
- [`task1_negpell.csv`](evidence/task1_negpell.csv)
- [`task1_negpell.py`](evidence/task1_negpell.py)
- [`task2_crosstab.csv`](evidence/task2_crosstab.csv)
- [`task2_negpell_all.csv`](evidence/task2_negpell_all.csv)
- [`task2_stratify.py`](evidence/task2_stratify.py)
- [`task2_stratify_output.txt`](evidence/task2_stratify_output.txt)
- [`task3_cfshape.py`](evidence/task3_cfshape.py)
- [`task3_cfshape_output.txt`](evidence/task3_cfshape_output.txt)
- [`task4_mechanism.py`](evidence/task4_mechanism.py)
- [`task4_mechanism_output.txt`](evidence/task4_mechanism_output.txt)
- [`task5_widersearch.py`](evidence/task5_widersearch.py)
- [`task5_widersearch_output.txt`](evidence/task5_widersearch_output.txt)
- [`verify_pell_and_certification_split.py`](evidence/verify_pell_and_certification_split.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
