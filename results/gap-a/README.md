# gap-a

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: under stated hypotheses](https://img.shields.io/badge/Lean%204-under%20stated%20hypotheses-222222) ![logged: 2026-07-24](https://img.shields.io/badge/logged-2026--07--24-999999)

**In short.** Closed the open half of a 2020 quadratic-irrationals theorem (Example 6.4); the closing argument and its mismatch-ratio consequence are new.

## Statement

Closed the main open step behind one direction of a 2020 result on quadratic irrationals (Example 6.4), though the governing principle behind the closing argument was already partially present in the published literature; the composite argument and its consequence for the mismatch ratio are the new part.

```math
\begin{aligned}
&x\ \text{quadratic irrational},\ \ t=x+x^{\sigma}\in\mathbb{Z}\ \Longrightarrow\ \kappa(x)=q^{t}\\
&\kappa(x)=q^{\mu+1}\,\overline{C}/C,\qquad \overline{C}(q)=C(q^{-1}),\qquad \kappa(x)=\pm1\iff x+x^{\sigma}=0\\
&[x]_q+[-x]_q\in\mathbb{Z}[q,q^{-1}]\ \Longrightarrow\ x=\pm\sqrt{d},\ \ d\ \text{a positive nonsquare integer}
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

Lean 4 checks the integer-matrix identity R^m N M N R^-m = M^-1 and, taking four published transformation laws of the mismatch ratio as hypotheses, derives r(M)^2 = q^{2m} and r(M) = +-1 iff x + x^sigma = 0. The q-deformation and the four laws themselves are not formalised.

- [`GapA.lean`](lean/GapA.lean)

Build: `cd lean && lake build GapA`

## Evidence

- [`abstained-forms-output.txt`](evidence/abstained-forms-output.txt)
- [`abstained_forms.py`](evidence/abstained_forms.py)
- [`box_coverage.py`](evidence/box_coverage.py)
- [`check_chain.py`](evidence/check_chain.py)
- [`extended_checks.py`](evidence/extended_checks.py)
- [`probe_invariance_and_k.py`](evidence/probe_invariance_and_k.py)
- [`spotcheck_table.py`](evidence/spotcheck_table.py)
- [`verify_g1.py`](evidence/verify_g1.py)
- [`verify_ratio.py`](evidence/verify_ratio.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
