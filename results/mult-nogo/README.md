# mult-nogo

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: narrower claim](https://img.shields.io/badge/Lean%204-narrower%20claim-222222) ![logged: 2026-06](https://img.shields.io/badge/logged-2026--06-999999)

**In short.** Proved [xy]_q is likewise not bihomographic, with the q-reversal obstruction absent this time.

## Statement

[xy]_q is likewise not bihomographic, and unlike the addition case the q-reversal is absent as the obstruction.

```math
\begin{aligned}
&\nexists\ (a,\dots,h)\in\mathbb{Q}(q)^{8}\setminus\{0\}:\\
&(aXY+bX+cY+d)-T\,(eXY+fX+gY+h)=0\ \ \text{for all }x,y>1\\
&X=[x]_q,\ \ Y=[y]_q,\ \ T=[xy]_q\\
&\operatorname{rank}_{\mathbb{Q}(q)}\bigl[\,XY,\ X,\ Y,\ 1,\ -TXY,\ -TX,\ -TY,\ -T\,\bigr]=8
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

Lean 4 proves [xy]_q is not bihomographic in [x]_q and [y]_q over Q(q), with the same relation and rank-8 certificate as for addition. That the q-reversal is not the obstruction here is a computation, not a Lean result.

- [`MultNogo.lean`](lean/MultNogo.lean)

Build: `cd lean && lake build MultNogo`

## Evidence

- [`README.md`](evidence/README.md)
- [`impossibility_search.py`](evidence/impossibility_search.py)
- [`mult_impossibility_search.py`](evidence/mult_impossibility_search.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
