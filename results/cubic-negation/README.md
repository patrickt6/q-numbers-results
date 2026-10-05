# cubic-negation

![status: Verified by computation](https://img.shields.io/badge/status-Verified%20by%20computation-2f5bd3) ![logged: 2026-06](https://img.shields.io/badge/logged-2026--06-999999)

**In short.** Checked a panel of cubic irrationals: none gives a finite negation sum or product, exact to N = 320. Not proved for all cubics.

## Statement

In a tested panel of cubic irrationals (heptagon, nonagon and S_3 cubics), the negation sum and product are not finite, checked exactly to N = 320. No proof for all cubics is written.

```math
\begin{aligned}
&x\ \text{in the tested cubic panel (heptagon, nonagon, }S_3\text{ cubics)}\\
&[x]_q+[-x]_q\ \notin\ \mathbb{Z}[q,q^{-1}]\\
&[x]_q\,[-x]_q\ \notin\ \mathbb{Z}[q,q^{-1}]\qquad(\text{checked to }N=320)
\end{aligned}
```

*Verified by computation:* Established by exact computation over a stated search range. Not a proof.

## Evidence

- [`negation_scan.py`](evidence/negation_scan.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
