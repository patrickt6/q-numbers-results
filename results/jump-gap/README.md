# jump-gap

![status: Already published](https://img.shields.io/badge/status-Already%20published-7c3aed) ![Lean 4: part of the claim](https://img.shields.io/badge/Lean%204-part%20of%20the%20claim-222222) ![logged: 2026-08-05](https://img.shields.io/badge/logged-2026--08--05-999999)

**In short.** Derived the closed form (1-q)q^E/(S+S-) for the rational jump gap independently, then found it published (Etingof arXiv:2508.08440; Jouteur, Paris-Romaskevich and Thomas arXiv:2603.04295v2).

## Statement

The rational jump gap has the universal closed form (1-q) q^E / (S+ S-). Derived independently, then found published: Etingof arXiv:2508.08440 Proposition 4.11 in continuant form, and Jouteur, Paris-Romaskevich and Thomas arXiv:2603.04295v2 Proposition 3.22 in this closed form.

```math
\begin{aligned}
&\tfrac rs=[a_0;a_1,\dots,a_{2n-1}],\qquad M_q=\begin{pmatrix}R&R'\\ S&S'\end{pmatrix}\\
&S^{+}=S,\qquad S^{-}=S+(1-q)S'\\
&[\tfrac rs]_q^{+}-[\tfrac rs]_q^{-}=\frac{(1-q)\,q^{E}}{S^{+}(q)\,S^{-}(q)},\qquad E=\Bigl(\sum_{i}a_i\Bigr)-1
\end{aligned}
```

*Already published:* Correct, but already in the literature. Found during a novelty check.

## Lean 4

Over any field, if RS'-R'S=q^E then M·(1,0)-M·(1,1-q)=(1-q)q^E/(S(S+(1-q)S')); separately, an even-length continuant block product has determinant q^(alternating digit sum). The link to the rational jump gap and to E=Σa_i-1 is not formalised.

- `JumpGap.lean`
- `JumpGapDet.lean`

Build: `lake build`

## Evidence

- [`JumpGap.lean`](evidence/JumpGap.lean)
- [`README.md`](evidence/README.md)
- [`gap_general.py`](evidence/gap_general.py)
- [`gap_scan.py`](evidence/gap_scan.py)
- [`jump_catalog.py`](evidence/jump_catalog.py)
- [`jump_gaps.csv`](evidence/jump_gaps.csv)
- [`tables.tex`](evidence/tables.tex)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
