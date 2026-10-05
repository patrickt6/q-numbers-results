# twin-primes

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: narrower claim](https://img.shields.io/badge/Lean%204-narrower%20claim-222222) ![logged: 2026-06-17](https://img.shields.io/badge/logged-2026--06--17-999999)

**In short.** Proved the reduced q-denominator of m/(m^2-1) collapses to two cyclotomic factors exactly when m-1 and m+1 are twin primes.

## Statement

For x = m/(m^2 - 1), the reduced q-denominator collapses to exactly two cyclotomic factors precisely when m-1 and m+1 are twin primes.

```math
\begin{aligned}
&x=\frac{m}{m^{2}-1}:\qquad [x]_q=\frac{q^{\,m-1}[m]_q}{[m-1]_q\,[m+1]_q},\qquad S=[m-1]_q\,[m+1]_q\\
&S=\Phi_{m-1}\,\Phi_{m+1}\ \ (\text{two cyclotomic factors})\iff m-1\ \text{and}\ m+1\ \text{are both prime}
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

For every m >= 2, the q-rational of m/(m^2-1) is q^(m-1)[m]_q/([m-1]_q[m+1]_q) in lowest terms, and its reduced denominator equals Phi_{m-1} Phi_{m+1} exactly when m-1 and m+1 are both prime (Lean 4). The wider claim over all numerators of d = p p' is not formalised.

- [`TwinPrimes.lean`](lean/TwinPrimes.lean)

Build: `cd lean && lake build TwinPrimes`

## Evidence

- [`engine.py`](evidence/engine.py)
- [`fullscan.py`](evidence/fullscan.py)
- [`grounding-twin-primes.md`](evidence/grounding-twin-primes.md)
- [`mgo_engine.py`](evidence/mgo_engine.py)
- [`patch-twin-primes.tex`](evidence/patch-twin-primes.tex)
- [`probe.py`](evidence/probe.py)
- [`sweep.py`](evidence/sweep.py)
- [`verify_twin_primes_tail.py`](evidence/verify_twin_primes_tail.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
