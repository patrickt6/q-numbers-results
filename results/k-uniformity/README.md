# k-uniformity

![status: Verified by computation](https://img.shields.io/badge/status-Verified%20by%20computation-2f5bd3) ![logged: 2026-08](https://img.shields.io/badge/logged-2026--08-999999)

**In short.** Confirmed k-independence of the vanishing-locus congruence conditions for k = 2 through 13.

## Statement

The k-independence of the vanishing-locus congruence conditions is confirmed exactly for k = 2 through 13.

```math
\begin{aligned}
&7\le k\le13:\qquad |V_3(k)|=2,\quad |V_4(k)|=2k+3,\quad |V_5(k)|=10k\\
&V_i(k)^{\le3}\ \text{is the same set of words for all }9\le k\le13\\
&|V_3^{\le3}|,\ |V_4^{\le3}|,\ |V_5^{\le3}|=2,\ 17,\ 64
\end{aligned}
```

*Verified by computation:* Established by exact computation over a stated search range. Not a proof.

## Evidence

- [`RESULTS.md`](evidence/RESULTS.md)
- [`chain_normal_form.py`](evidence/chain_normal_form.py)
- [`closure_check.py`](evidence/closure_check.py)
- [`families_length5.py`](evidence/families_length5.py)
- [`length6.py`](evidence/length6.py)
- [`results.json`](evidence/results.json)
- [`vanishing_locus.py`](evidence/vanishing_locus.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
