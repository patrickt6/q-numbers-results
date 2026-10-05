# partition-claim

![status: Found false](https://img.shields.io/badge/status-Found%20false-c2410c) ![logged: 2026-07-11](https://img.shields.io/badge/logged-2026--07--11-999999)

**In short.** Disproved the manuscript's partition claim; smallest counterexample d = 60, a = 11.

## Statement

The manuscript partition claim is false. Smallest counterexample d = 60, a = 11, where S = Phi2 Phi3 Phi4 Phi5 Phi6 admits no valid partition.

```math
\begin{aligned}
&x=\tfrac{11}{60}\\
&S=\Phi_2\Phi_3\Phi_4\Phi_5\Phi_6\ \Bigm|\ [60]_q,\qquad T=\{2,3,4,5,6\}\\
&T\ \text{matches no partition of }\{4,3,5\}\\
&\Phi_6\mid S\ \text{forces }4,3\ \text{into one part, whose }q\text{-analogue }[12]_q\ \text{needs}\ \Phi_{12}\mid S,\ \ \text{but }\Phi_{12}\nmid S
\end{aligned}
```

*Found false:* A claim that was believed, tested, and found false. Includes my own.

## Evidence

- [`census.py`](evidence/census.py)
- [`p1_summary.md`](evidence/p1_summary.md)
- [`patch-partition-claim.tex`](evidence/patch-partition-claim.tex)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
