# addition-nogo

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: full claim](https://img.shields.io/badge/Lean%204-full%20claim-222222) ![logged: 2026-06](https://img.shields.io/badge/logged-2026--06-999999)

**In short.** Proved [x+y]_q is not bihomographic in [x]_q and [y]_q over Q(q): the 8-wide relation matrix has full rank 8.

## Statement

[x+y]_q is not a bihomographic function of [x]_q and [y]_q over Q(q): the 8-wide relation matrix has full rank 8, so the kernel is trivial.

```math
\begin{aligned}
&\nexists\ (a,\dots,h)\in\mathbb{Q}(q)^{8}\setminus\{0\}:\\
&(aXY+bX+cY+d)-T\,(eXY+fX+gY+h)=0\ \ \text{for all }x,y>1\\
&X=[x]_q,\ \ Y=[y]_q,\ \ T=[x+y]_q\\
&\operatorname{rank}_{\mathbb{Q}(q)}\bigl[\,XY,\ X,\ Y,\ 1,\ -TXY,\ -TX,\ -TY,\ -T\,\bigr]=8
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

Lean 4 proves that no nonzero (a,...,h) in Q(q)^8 satisfies (aXY+bX+cY+d) - [x+y]_q (eXY+fX+gY+h) = 0 for all rational x,y > 1 (X=[x]_q, Y=[y]_q, MGO continued-fraction definition). The 8x8 relation matrix at eight explicit samples has rank 8.

- [`AdditionNogo.lean`](lean/AdditionNogo.lean)

Build: `cd lean && lake build AdditionNogo`

## Evidence

- [`Multiplication.lean`](evidence/Multiplication.lean)
- [`README.md`](evidence/README.md)
- [`deficit_closed_forms.csv`](evidence/deficit_closed_forms.csv)
- [`make_deficit_dataset.py`](evidence/make_deficit_dataset.py)
- [`make_mult_deficit_dataset.py`](evidence/make_mult_deficit_dataset.py)
- [`mult_deficit_search.py`](evidence/mult_deficit_search.py)
- [`q_gosper.py`](evidence/q_gosper.py)
- [`tables.tex`](evidence/tables.tex)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
