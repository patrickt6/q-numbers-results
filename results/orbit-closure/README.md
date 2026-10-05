# orbit-closure

![status: Verified by computation](https://img.shields.io/badge/status-Verified%20by%20computation-2f5bd3) ![logged: 2026-06](https://img.shields.io/badge/logged-2026--06-999999)

**In short.** Recovered the Ovsienko-Ustinov degree-3 functional equation from the heptagon and nonagon cyclic cubics, residual zero to q^4950.

## Statement

The heptagon and nonagon cyclic cubics recover the Ovsienko-Ustinov degree-3 functional equation exactly, with residual zero to q^4950. Non-cyclic S_3 cubics admit no such equation.

```math
\begin{aligned}
&x\in\bigl\{2\cos\tfrac{2\pi}{7},\ 2\cos\tfrac{2\pi}{9}\bigr\}\ \ (x^{3}+x^{2}-2x-1=0,\ \ x^{3}-3x+1=0)\\
&P\bigl(q,[x]_q\bigr)=O\bigl(q^{4951}\bigr),\qquad \deg_X P=3\\
&\text{coefficient of }X^{2}\ \text{in }P\ \text{is}\ -\bigl([x_1]_q+[x_2]_q+[x_3]_q\bigr)\\
&\text{non-cyclic }S_3\text{ cubics: no such }P
\end{aligned}
```

*Verified by computation:* Established by exact computation over a stated search range. Not a proof.

## Evidence

- [`2_README.md`](evidence/2_README.md)
- [`2_cubic_modular_atlas.csv`](evidence/2_cubic_modular_atlas.csv)
- [`2_tables.tex`](evidence/2_tables.tex)
- [`3_README.md`](evidence/3_README.md)
- [`3_tables.tex`](evidence/3_tables.tex)
- [`README.md`](evidence/README.md)
- [`cbrt2_search_results.csv`](evidence/cbrt2_search_results.csv)
- [`cubic_atlas_compute.sage`](evidence/cubic_atlas_compute.sage)
- [`cubic_modular_atlas.csv`](evidence/cubic_modular_atlas.csv)
- [`cyclic_cubic_modular_atlas.csv`](evidence/cyclic_cubic_modular_atlas.csv)
- [`cyclic_cubics.csv`](evidence/cyclic_cubics.csv)
- [`dichotomy_summary.csv`](evidence/dichotomy_summary.csv)
- [`finite_kernel_search.csv`](evidence/finite_kernel_search.csv)
- [`functional_equation_search.sage`](evidence/functional_equation_search.sage)
- [`functional_equations_validation.csv`](evidence/functional_equations_validation.csv)
- [`galois_conjugate_verification.csv`](evidence/galois_conjugate_verification.csv)
- [`modular_atlas_compute.sage`](evidence/modular_atlas_compute.sage)
- [`modular_atlas_results.csv`](evidence/modular_atlas_results.csv)
- [`orbit_closed_forms.py`](evidence/orbit_closed_forms.py)
- [`orbit_elements_summary.csv`](evidence/orbit_elements_summary.csv)
- [`part2_track_a_laurent.csv`](evidence/part2_track_a_laurent.csv)
- [`part2_track_b_polynomial.csv`](evidence/part2_track_b_polynomial.csv)
- [`part2_validation_controls.csv`](evidence/part2_validation_controls.csv)
- [`q_continued_fraction.sage`](evidence/q_continued_fraction.sage)
- [`residuals_per_q.csv`](evidence/residuals_per_q.csv)
- [`tables.tex`](evidence/tables.tex)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
