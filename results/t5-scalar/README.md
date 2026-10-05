# t5-scalar

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: full claim](https://img.shields.io/badge/Lean%204-full%20claim-222222) ![logged: 2026-07](https://img.shields.io/badge/logged-2026--07-999999)

**In short.** Settled the scalar congruence conjecture with the exact identity q(A-D) = (q-1)(qB+C).

## Statement

The scalar congruence conjecture is settled by the exact identity q(A-D) = (q-1)(qB+C).

```math
\begin{aligned}
&\Lambda_q=\begin{pmatrix}A&B\\ C&D\end{pmatrix}\\
&q\,(A-D)=(q-1)\,(qB+C)\\
&C\mid B\iff C\mid A-D
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

For every positive Pell automorph, the R,L-word q-deformation Λ_q satisfies q(A-D)=(q-1)(qB+C) and C|B iff C|A-D in ℤ[q,q⁻¹].

- `T5Scalar.lean`

Build: `cd lean && lake build T5Scalar`

## Evidence

- [`RESULT.md`](evidence/RESULT.md)
- [`cong_charact.py`](evidence/cong_charact.py)
- [`control_scan.csv`](evidence/control_scan.csv)
- [`general_law.py`](evidence/general_law.py)
- [`global_scan.csv`](evidence/global_scan.csv)
- [`local_data.csv`](evidence/local_data.csv)
- [`scan_t5.py`](evidence/scan_t5.py)
- [`verify_identity.py`](evidence/verify_identity.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
