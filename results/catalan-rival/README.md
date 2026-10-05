# catalan-rival

![status: Found false](https://img.shields.io/badge/status-Found%20false-c2410c) ![logged: 2026-08](https://img.shields.io/badge/logged-2026--08-999999)

**In short.** Refuted the rival count-law formula 2(4^m-1)/3: it predicts 170 at length 9, the true value is 168.

## Statement

The rival count-law formula 2(4^m - 1)/3 predicts 170 at length 9. The observed value is 168, which refutes it. Leading coefficients are Catalan numbers at even lengths.

```math
\begin{aligned}
&L_i=\text{leading coefficient of }|V_i(k)|\ \text{in }k\\
&(L_3,\dots,L_9)=(2,2,10,5,42,14,168),\qquad L_{2m}=C_m\ \ (C_m\ \text{Catalan})\\
&\frac{2\,(4^{m}-1)}{3}\Big|_{m=4}=170\ \neq\ 168=L_9
\end{aligned}
```

*Found false:* A claim that was believed, tested, and found false. Includes my own.

## Evidence

- [`polygon.py`](evidence/polygon.py)
- [`results.json`](evidence/results.json)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
