# s-prime-formula

![status: Already published](https://img.shields.io/badge/status-Already%20published-7c3aed) ![Lean 4: stated, proof not finished](https://img.shields.io/badge/Lean%204-stated%2C%20proof%20not%20finished-222222) ![logged: 2026-07-11](https://img.shields.io/badge/logged-2026--07--11-999999)

**In short.** Derived 2S'(1) = d deg S + a^-1 - a independently; already known (Lasker, arXiv:2309.10819, Lemma 6.1 and Corollary 6.2).

## Statement

The S'(1) formula 2S'(1) = d deg S + a^-1 - a is already known: Lasker, arXiv:2309.10819, Lemma 6.1 and Corollary 6.2.

```math
\begin{aligned}
&x=\tfrac ad,\ \ 0<a<d,\ \ \gcd(a,d)=1\\
&S\ \text{reduced monic denominator of }[x]_q\\
&2S'(1)=d\,\deg S+a^{-1}-a\qquad(a^{-1}\in(0,d)\ \text{the inverse of }a\bmod d)
\end{aligned}
```

*Already published:* Correct, but already in the literature. Found during a novelty check.

## Lean 4

Statement only: the Lean file states, without proof, the formula 2S'(1) = d deg S + a^-1 - a; it is a known result of Lasker, arXiv:2309.10819, Lemma 6.1 and Corollary 6.2.

- `SPrimeFormula.lean`

Build: `cd lean && lake build SPrimeFormula`

## Evidence

- [`harness.py`](evidence/harness.py)
- [`t1.py`](evidence/t1.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
