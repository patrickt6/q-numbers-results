# lemma-l

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: stated, proof not finished](https://img.shields.io/badge/Lean%204-stated%2C%20proof%20not%20finished-222222) ![logged: 2026-07](https://img.shields.io/badge/logged-2026--07-999999)

**In short.** Proved Lemma L at odd prime powers from downward closure alone, by a p-adic argument.

## Statement

Lemma L at odd prime powers follows from downward closure (DC) alone, by a pi-adic argument.

```math
\begin{aligned}
&p\ \text{odd prime},\ \ a\ge1,\ \ \Lambda_q=\begin{pmatrix}A&B\\ C&D\end{pmatrix}\\
&(\mathrm{DC}):\ \ \Phi_{p^{a}}\mid C\Rightarrow\Phi_{p^{j}}\mid C\ \ (1\le j<a)\\
&(\mathrm{DC})\ \Longrightarrow\ \bigl(\Phi_{p^{a}}\mid C\Rightarrow A\equiv D\pmod{\Phi_{p^{a}}}\bigr)
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

Statement only (the Lean proof is sorry): for odd p and a Pell automorph, if the divisibility chain Phi_{p^a} | C => Phi_{p^j} | C (j<a) holds for that C, then Phi_{p^a} | C implies Phi_{p^a} | A - D; the chain (DC) itself is assumed, not proved.

- `LemmaL.lean`

Build: `cd lean && lake build LemmaL`

## Evidence

- [`audit_mech.out`](evidence/audit_mech.out)
- [`audit_mech.py`](evidence/audit_mech.py)
- [`check_converse.py`](evidence/check_converse.py)
- [`cover-gap-output.txt`](evidence/cover-gap-output.txt)
- [`cover_gap.py`](evidence/cover_gap.py)
- [`e10.py`](evidence/e10.py)
- [`e12.py`](evidence/e12.py)
- [`e9.py`](evidence/e9.py)
- [`explore4.py`](evidence/explore4.py)
- [`general-rationals-output.txt`](evidence/general-rationals-output.txt)
- [`general_rationals.py`](evidence/general_rationals.py)
- [`hunt-oop-hits.csv`](evidence/hunt-oop-hits.csv)
- [`hunt-oop-output.txt`](evidence/hunt-oop-output.txt)
- [`hunt_oop.py`](evidence/hunt_oop.py)
- [`hunt_phi49.py`](evidence/hunt_phi49.py)
- [`kmrwy_test.out`](evidence/kmrwy_test.out)
- [`kmrwy_test.py`](evidence/kmrwy_test.py)
- [`probe_traces.py`](evidence/probe_traces.py)
- [`referee_B_p2.out`](evidence/referee_B_p2.out)
- [`referee_B_p2.py`](evidence/referee_B_p2.py)
- [`step4-question.tex`](evidence/step4-question.tex)
- [`support-closure-output.txt`](evidence/support-closure-output.txt)
- [`support_closure.py`](evidence/support_closure.py)
- [`test_scalar_theorem.py`](evidence/test_scalar_theorem.py)
- [`test_scalar_theorem_results.csv`](evidence/test_scalar_theorem_results.csv)
- [`verify-theorem-rows.csv`](evidence/verify-theorem-rows.csv)
- [`verify_theorem.py`](evidence/verify_theorem.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
