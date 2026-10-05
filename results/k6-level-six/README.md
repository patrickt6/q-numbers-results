# k6-level-six

![status: Already published](https://img.shields.io/badge/status-Already%20published-7c3aed) ![Lean 4: stated, proof not finished](https://img.shields.io/badge/Lean%204-stated%2C%20proof%20not%20finished-222222) ![logged: 2026-08](https://img.shields.io/badge/logged-2026--08-999999)

**In short.** Proved the level-six divisibility claim independently; matches Byakuno-Ren-Yanagawa arXiv:2603.08439 Proposition 5.3, with the A_i profile as the new part.

## Statement

The level-six claim that Phi6 dividing S_i forces [6]_q to divide S_i is Byakuno-Ren-Yanagawa, arXiv:2603.08439, Proposition 5.3. Only the A_i profile in that write-up is new.

```math
i\ge1,\ c_1,\dots,c_i\in\mathbb{Z}:\qquad \Phi_6\mid S_i\ \Longrightarrow\ [6]_q\mid S_i,\quad\text{hence }6\mid S_i(1)
```

*Already published:* Correct, but already in the literature. Found during a novelty check.

## Lean 4

Statement only: the Lean file states, without proving, that Phi_6 | S_i implies [6]_q | S_i and 6 | S_i(1); the result is Byakuno-Ren-Yanagawa Proposition 5.3.

- `KSix.lean`

Build: `cd lean && lake build KSix`

## Evidence

- [`k6proofnew.tex`](evidence/k6proofnew.tex)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
