# trace-zero

![status: Found false](https://img.shields.io/badge/status-Found%20false-c2410c) ![logged: 2026-06-04](https://img.shields.io/badge/logged-2026--06--04-999999)

**In short.** Disproved my own trace-zero finiteness criterion; counterexamples sqrt(19), sqrt(43), sqrt(46), sqrt(53).

## Statement

The claim that the negation sum is finite exactly for trace-zero quadratics is false. Counterexamples: sqrt(19), sqrt(43), sqrt(46), sqrt(53), all trace zero with infinite sum.

```math
\begin{aligned}
&d\in\{19,43,46,53\}\\
&\sqrt d+(\sqrt d)^{\sigma}=0,\qquad [\sqrt d\,]_q+[-\sqrt d\,]_q\notin\mathbb{Z}[q,q^{-1}]
\end{aligned}
```

*Found false:* A claim that was believed, tested, and found false. Includes my own.

## Evidence

- [`README.md`](evidence/README.md)
- [`negation_scan.py`](evidence/negation_scan.py)
- [`negation_table.csv`](evidence/negation_table.csv)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
