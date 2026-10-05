# sqrt2-mod2-biconditional

![status: Found false](https://img.shields.io/badge/status-Found%20false-c2410c) ![logged: 2026-06](https://img.shields.io/badge/logged-2026--06-999999)

**In short.** Disproved the biconditional version of the same law: 4,446 counterexamples in range.

## Statement

The biconditional version of the same statement is false, with 4446 counterexamples in range.

```math
\begin{aligned}
&\neg\,\forall n\ \bigl(c_n\equiv0\ (\mathrm{mod}\ 2)\iff n\equiv1\ (\mathrm{mod}\ 3)\bigr),\qquad c_2=0\\
&\#\{\,0\le n<20000:\ c_n\equiv0\ (\mathrm{mod}\ 2),\ n\not\equiv1\ (\mathrm{mod}\ 3)\,\}=4446
\end{aligned}
```

*Found false:* A claim that was believed, tested, and found false. Includes my own.

## Evidence

- [`coefficient_check.csv`](evidence/coefficient_check.csv)
- [`construct_automaton.py`](evidence/construct_automaton.py)
- [`verify_against_atlas.py`](evidence/verify_against_atlas.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
