# degree-equality

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: part of the claim](https://img.shields.io/badge/Lean%204-part%20of%20the%20claim-222222) ![logged: 2026-07-11](https://img.shields.io/badge/logged-2026--07--11-999999)

**In short.** Proved the degree-equality clause by a continuant tightness induction.

## Statement

The degree equality clause is proved by a continuant tightness induction.

```math
\begin{aligned}
&x=\tfrac{a}{d},\ \ 0<a<d,\ \ \gcd(a,d)=1\\
&\deg S=d-1\iff a\equiv\pm1\pmod d,\qquad\text{and then }S=[d]_q
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

For digits ≥2, Σ_{j=2}^k(c_j-1)=s_k-1 iff c_2=...=c_k=2 (k≥3). The bridge to deg S=d-1 and a≡±1 (mod d) is not formalised.

- `Degreeeq.lean`

Build: `lake build`

## Evidence

- [`mgo_engine.py`](evidence/mgo_engine.py)
- [`p2_degree_check.md`](evidence/p2_degree_check.md)
- [`verify_degree_equality_d400.py`](evidence/verify_degree_equality_d400.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
