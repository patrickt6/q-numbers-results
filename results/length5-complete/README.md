# length5-complete

![status: Verified by computation](https://img.shields.io/badge/status-Verified%20by%20computation-2f5bd3) ![Lean 4: stated, proof not finished](https://img.shields.io/badge/Lean%204-stated%2C%20proof%20not%20finished-222222) ![logged: 2026-08](https://img.shields.io/badge/logged-2026--08-999999)

**In short.** Verified the length-5 list is complete (no other word vanishes) for 4 <= k <= 24; not proved for all k.

## Statement

That the length-5 list is complete, so no other word vanishes, is verified for 4 <= k <= 24 and is not proved.

```math
\begin{aligned}
&\Phi_k\mid S_5\ \Longrightarrow\ (c_2,c_3,c_4,c_5)\bmod k\ \text{lies in the list}\qquad(\text{checked for }4\le k\le 24,\ k\ne5)\\
&k=5:\ \ \Phi_5\mid S_5\ \Longrightarrow\ (c_2,c_3,c_4,c_5)\bmod 5\ \text{lies in the list or is}\ (2,2,2,2)\ \text{or}\ (3,3,3,3)\\
&|V_5(k)|=10k\ \ (4\le k\le 24,\ k\ne5),\qquad |V_5(5)|=52=50+2
\end{aligned}
```

*Verified by computation:* Established by exact computation over a stated search range. Not a proof.

## Lean 4

The Lean file only states, and proves nothing (all four theorems are sorry): list-inclusion for 4 <= k <= 24 with k != 5, the k = 5 locus as the list plus (2,2,2,2) and (3,3,3,3), and the counts 10k and 52. The finite check itself is a Python computation.

- `Length5Complete.lean`

Build: `cd lean && lake build Length5Complete`

## Evidence

- [`P4-length5-verify.py`](evidence/P4-length5-verify.py)
- [`closure_check.py`](evidence/closure_check.py)
- [`vanishing_locus.py`](evidence/vanishing_locus.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
