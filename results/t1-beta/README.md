# t1-beta

![status: Found false](https://img.shields.io/badge/status-Found%20false-c2410c) ![logged: 2026-07-21](https://img.shields.io/badge/logged-2026--07--21-999999)

**In short.** Disproved the beta tail-degree bound; counterexample x = -16 + (48/7)sqrt(3), confirmed by three independent implementations.

## Statement

The beta tail-degree bound is false. Canonical counterexample x = -16 + (48/7) sqrt 3, confirmed by three independent attempts.

```math
\begin{aligned}
&G(x)=[x]_q+[-x]_q,\qquad x=-16+\tfrac{48}{7}\sqrt3\\
&\beta(x)=3,\ \ \beta(-x)=5,\ \ \max\bigl(\beta(x),\beta(-x)\bigr)=5\\
&[q^{n}]\,G(x)=0\ \ (6\le n\le18),\qquad [q^{19}]\,G(x)\neq0
\end{aligned}
```

*Found false:* A claim that was believed, tested, and found false. Includes my own.

## Evidence

- [`2_RESULT.md`](evidence/2_RESULT.md)
- [`RESULT.md`](evidence/RESULT.md)
- [`algebraic.py`](evidence/algebraic.py)
- [`beta_check.py`](evidence/beta_check.py)
- [`boundary.log`](evidence/boundary.log)
- [`boundary.py`](evidence/boundary.py)
- [`cert_test.out`](evidence/cert_test.out)
- [`cert_test.py`](evidence/cert_test.py)
- [`committed.out`](evidence/committed.out)
- [`committed.py`](evidence/committed.py)
- [`consequence_check.py`](evidence/consequence_check.py)
- [`core.log`](evidence/core.log)
- [`core_check.py`](evidence/core_check.py)
- [`core_full.log`](evidence/core_full.log)
- [`d5check.out`](evidence/d5check.out)
- [`d5check.py`](evidence/d5check.py)
- [`deep.py`](evidence/deep.py)
- [`exact.py`](evidence/exact.py)
- [`exceedance_scan.py`](evidence/exceedance_scan.py)
- [`gtools.py`](evidence/gtools.py)
- [`large_pred_scan.py`](evidence/large_pred_scan.py)
- [`longrun.out`](evidence/longrun.out)
- [`longrun.py`](evidence/longrun.py)
- [`longrun2.out`](evidence/longrun2.out)
- [`out.csv`](evidence/out.csv)
- [`quick.py`](evidence/quick.py)
- [`reduction_check.py`](evidence/reduction_check.py)
- [`reversal.log`](evidence/reversal.log)
- [`reversal_check.py`](evidence/reversal_check.py)
- [`scan.py`](evidence/scan.py)
- [`sweep.csv`](evidence/sweep.csv)
- [`sweep.log`](evidence/sweep.log)
- [`sweep.py`](evidence/sweep.py)
- [`theorem.csv`](evidence/theorem.csv)
- [`theorem.log`](evidence/theorem.log)
- [`theorem_check.py`](evidence/theorem_check.py)
- [`thmB.py`](evidence/thmB.py)
- [`unresolved.out`](evidence/unresolved.out)
- [`unresolved.py`](evidence/unresolved.py)
- [`unresolved2.out`](evidence/unresolved2.out)
- [`word_search.py`](evidence/word_search.py)
- [`words.py`](evidence/words.py)
- [`words_sys.csv`](evidence/words_sys.csv)
- [`words_sys.log`](evidence/words_sys.log)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
