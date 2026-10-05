# length5

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: full claim](https://img.shields.io/badge/Lean%204-full%20claim-222222) ![logged: 2026-08](https://img.shields.io/badge/logged-2026--08-999999)

**In short.** Proved every word in the length-5 list vanishes for all k: five parametrised shapes plus ten identically zero words.

## Statement

Every word in the length-5 list vanishes for all k: five parametrised shapes plus ten identically zero words.

```math
\begin{aligned}
&k\ge7:\quad \Phi_k\mid S_5\ \Longleftarrow\ (c_2,c_3,c_4,c_5)\bmod k\ \text{lies in one of}\\
&(0,t,\varepsilon,\varepsilon),\ \ (\varepsilon,\varepsilon,t,0),\ \ (t,0,\varepsilon-t,\varepsilon),\ \ (\varepsilon,t,0,\varepsilon-t),\ \ (t,\varepsilon,\varepsilon,\varepsilon-t),\ \ \text{or}\ W\\
&\varepsilon=\pm1,\ \ t\in\mathbb{Z}/k\\
&W=\pm\{(1,2,2,1),\,(1,3,1,2),\,(2,1,3,1),\,(2,2,1,3),\,(3,1,2,2)\}
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

Proved in Lean: for every k > 1 and every integer word whose residues mod k lie in the five shapes or the ten words, Phi_k divides S_5 (the converse is not proved).

- `Length5.lean`

Build: `cd lean && lake build Length5`

## Evidence

- [`P4-length5-verify.py`](evidence/P4-length5-verify.py)
- [`RESULTS.md`](evidence/RESULTS.md)
- [`families_length5.py`](evidence/families_length5.py)
- [`results.json`](evidence/results.json)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
