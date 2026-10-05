# realizability

![status: Verified by computation](https://img.shields.io/badge/status-Verified%20by%20computation-2f5bd3) ![logged: 2026-07](https://img.shields.io/badge/logged-2026--07-999999)

**In short.** The realizability index-set law matches 166 of 166 census cases exactly; recorded as unproved, since the proof is still open.

## Statement

The realizability index-set law, stated as connectivity closure minus the n with 4 | n and n not a power of 2, matches 166 of 166 census cases exactly. The proof is open.

```math
\begin{aligned}
&T(d)=\{\,n>1:\ n\mid s_d,\ \Phi_n\mid S\,\}\quad\text{over the 166 proper cyclotomic collapses, }d\le6000\\
&T(d)=\mathcal{C}(d)\setminus\{\,n:\ 4\mid n,\ n\neq2^{j}\,\}\qquad(\text{matches 166 of 166})\\
&\mathcal{C}(d)=\text{connectivity closure of }T(d)\ \text{on the primes dividing }s_d
\end{aligned}
```

*Verified by computation:* Established by exact computation over a stated search range. Not a proof.

## Evidence

- [`census_verify.py`](evidence/census_verify.py)
- [`check_constraints.py`](evidence/check_constraints.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
