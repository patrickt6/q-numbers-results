# count-law

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: part of the claim](https://img.shields.io/badge/Lean%204-part%20of%20the%20claim-222222) ![logged: 2026-08-12](https://img.shields.io/badge/logged-2026--08--12-999999)

**In short.** Proved the vanishing locus is the torsion of a fixed hypersurface in a torus (Theorem A), via Laurent's theorem.

## Statement

Theorem A: the vanishing locus is the torsion of a fixed hypersurface in a torus, which turns an observed pattern into a theorem by way of Laurent's theorem (Invent. Math. 78, 1984).

```math
\begin{aligned}
&U_0=0,\ \ U_1=1,\ \ U_{j+1}=t\,(x_{j+1}-1)\,U_j-t\,(t-1)^{2}\,x_j\,U_{j-1}\\
&S_i(q)=\frac{U_i(q,q^{c_2},\dots,q^{c_i})}{\bigl(q(q-1)\bigr)^{i-1}},\qquad X_i=\{U_i=0\}\subset\mathbb{G}_m^{\,i}\\
&V_i(k)=\{c\in(\mathbb{Z}/k)^{i-1}:\ (\omega,\omega^{c_2},\dots,\omega^{c_i})\in X_i\},\quad \omega\ \text{a primitive }k\text{th root of unity}\\
&\{\text{torsion points of }X_i\}=\textstyle\bigcup_{\nu}y_\nu H_\nu\ \ (\text{finite union of torsion cosets, independent of }k)
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

Lean proves that V_i(k) equals the divisibility locus of Phi_k in S_i and that the torsion points of X_i = {U_i=0} form a finite union of torsion cosets, the latter relative to Laurent's theorem, which is stated but not proved; the congruence-system form of Theorem A is not formalised.

- `CountLaw.lean`

Build: `cd lean && lake build CountLaw`

## Evidence

- [`chain_normal_form.py`](evidence/chain_normal_form.py)
- [`closure_check.py`](evidence/closure_check.py)
- [`polygon.py`](evidence/polygon.py)
- [`results.json`](evidence/results.json)
- [`vanishing_locus.py`](evidence/vanishing_locus.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
