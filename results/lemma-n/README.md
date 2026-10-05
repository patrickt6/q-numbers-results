# lemma-n

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: full claim](https://img.shields.io/badge/Lean%204-full%20claim-222222) ![logged: 2026-08-12](https://img.shields.io/badge/logged-2026--08--12-999999)

**In short.** Proved negation closure (Lemma N) at all lengths, not only the lengths checked by hand.

## Statement

Lemma N gives negation closure at all lengths, not only the lengths that were checked by hand.

```math
\begin{aligned}
&S_j(\omega;-c_2,\dots,-c_j)=(-1)^{j-1}\,\omega^{-(j-1)}\,S_j(\omega^{-1};c_2,\dots,c_j)\\
&V_j(k)=-V_j(k)\ \ \text{for all }j,k
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

Negation symmetry of the cyclotomic vanishing locus V_j(k), every length, every k>1.

- `LemmaN.lean`

Build: `cd lean && lake build LemmaN`

## Evidence

- [`lemma_n_probe.py`](evidence/lemma_n_probe.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
