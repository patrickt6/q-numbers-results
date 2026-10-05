# negation-criterion

![status: Open](https://img.shields.io/badge/status-Open-6b7280) ![logged: 2026-06](https://img.shields.io/badge/logged-2026--06-999999)

**In short.** The finiteness criterion for the negation sum is still open; the palindrome-period argument fails at d = 19.

## Statement

The true criterion for finiteness of the negation sum is a continued-fraction period condition, and it remains open. The palindrome-period argument fails at d = 19, whose period is palindromic.

```math
\begin{aligned}
&\{\,d\ \text{nonsquare}:\ [\sqrt d\,]_q+[-\sqrt d\,]_q\in\mathbb{Z}[q,q^{-1}]\,\}\ \ \text{not characterised}\\
&\sqrt{19}=[4;\overline{2,1,3,1,2,8}],\ \ \text{palindromic core}\\
&[\sqrt{19}\,]_q+[-\sqrt{19}\,]_q\notin\mathbb{Z}[q,q^{-1}]
\end{aligned}
```

*Open:* Stated precisely, not settled.

## Evidence

- [`2_README.md`](evidence/2_README.md)
- [`README.md`](evidence/README.md)
- [`mine_report.md`](evidence/mine_report.md)
- [`negation_scan.py`](evidence/negation_scan.py)
- [`negation_table.csv`](evidence/negation_table.csv)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
