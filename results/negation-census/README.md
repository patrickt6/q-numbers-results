# negation-census

![status: Verified by computation](https://img.shields.io/badge/status-Verified%20by%20computation-2f5bd3) ![logged: 2026-06-11](https://img.shields.io/badge/logged-2026--06--11-999999)

**In short.** Swept 668,745 canonical quadratic irrationals; the negation sum is finite for exactly two, sqrt(2) and sqrt(3).

## Statement

Among all 668745 canonical quadratic irrationals in (1,2) with D <= 20000 and height <= 10, the negation sum is finite for exactly two constants: sqrt(2) and sqrt(3).

```math
\begin{aligned}
&\mathcal{Q}=\{x\in(1,2)\ \text{canonical quadratic irrational},\ D\le20000,\ \operatorname{ht}(x)\le10\}\\
&|\mathcal{Q}|=668745\\
&\{x\in\mathcal{Q}:\ [x]_q+[-x]_q\ \text{observed finite}\}=\{\sqrt2,\sqrt3\}\qquad(304\ \text{undecided})
\end{aligned}
```

*Verified by computation:* Established by exact computation over a stated search range. Not a proof.

## Evidence

- [`README.md`](evidence/README.md)
- [`REPORT-2026-06-11.md`](evidence/REPORT-2026-06-11.md)
- [`RUNS.csv`](evidence/RUNS.csv)
- [`census_d2_6000.csv`](evidence/census_d2_6000.csv)
- [`manifest_d2_100k_v1.json`](evidence/manifest_d2_100k_v1.json)
- [`mgo_engine.py`](evidence/mgo_engine.py)
- [`verify_census_6000_and_monomial_law.py`](evidence/verify_census_6000_and_monomial_law.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
