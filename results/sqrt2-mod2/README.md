# sqrt2-mod2

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: under stated hypotheses](https://img.shields.io/badge/Lean%204-under%20stated%20hypotheses-222222) ![logged: 2026-06](https://img.shields.io/badge/logged-2026--06-999999)

**In short.** Proved a q-real modular law end to end with Christol's theorem plus the Walnut automatic prover: n = 1 mod 3 implies c_n is even.

## Statement

First q-real modular law proved end to end by Christol's theorem plus the Walnut automatic-theorem prover: n congruent to 1 mod 3 implies c_n is even.

```math
\begin{aligned}
&[\sqrt2\,]_q=\sum_{n\ge0}c_n\,q^{n}\\
&n\equiv1\pmod 3\ \Longrightarrow\ c_n\equiv0\pmod 2\qquad(\text{all }n\ge0)
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

Lean proves that any integer power series solving MGO's equation q^2y^2-(q^3-1)y-(q^2+1)=0 has even coefficients at n = 1 mod 3; that [sqrt2]_q is such a series (convergence plus MGO Proposition 4.5) is cited, not proved in Lean.

- `Sqrt2Mod2.lean`

Build: `cd lean && lake build Sqrt2Mod2`

## Evidence

- [`2_README.md`](evidence/2_README.md)
- [`2_walnut_commands.txt`](evidence/2_walnut_commands.txt)
- [`C2.txt`](evidence/C2.txt)
- [`C2_lsd.txt`](evidence/C2_lsd.txt)
- [`P5.txt`](evidence/P5.txt)
- [`P5_states.json`](evidence/P5_states.json)
- [`README.md`](evidence/README.md)
- [`Result-sqrt2_mod7_conv.txt`](evidence/Result-sqrt2_mod7_conv.txt)
- [`Result-sqrt2_mod7_fwd.txt`](evidence/Result-sqrt2_mod7_fwd.txt)
- [`Result-sqrt2_mod7_iff.txt`](evidence/Result-sqrt2_mod7_iff.txt)
- [`S7.txt`](evidence/S7.txt)
- [`S7_states.json`](evidence/S7_states.json)
- [`algebraic_equation_F2q.md`](evidence/algebraic_equation_F2q.md)
- [`build_phi_mod5_dfao.py`](evidence/build_phi_mod5_dfao.py)
- [`build_sqrt2_mod7_dfao.py`](evidence/build_sqrt2_mod7_dfao.py)
- [`coefficient_check.csv`](evidence/coefficient_check.csv)
- [`construct_automaton.py`](evidence/construct_automaton.py)
- [`hankel_summary.csv`](evidence/hankel_summary.csv)
- [`phi_mod5_fwd.txt`](evidence/phi_mod5_fwd.txt)
- [`phi_mod5_iff.txt`](evidence/phi_mod5_iff.txt)
- [`phi_walnut_commands.txt`](evidence/phi_walnut_commands.txt)
- [`sqrt2_mod2.py`](evidence/sqrt2_mod2.py)
- [`sqrt2_mod2_lambda_0.csv`](evidence/sqrt2_mod2_lambda_0.csv)
- [`sqrt2_mod2_lambda_1.csv`](evidence/sqrt2_mod2_lambda_1.csv)
- [`sqrt2_mod2_lambda_2.csv`](evidence/sqrt2_mod2_lambda_2.csv)
- [`sqrt2_mod2_lambda_3.csv`](evidence/sqrt2_mod2_lambda_3.csv)
- [`sqrt2_mod2_lambda_4.csv`](evidence/sqrt2_mod2_lambda_4.csv)
- [`sqrt2_mod2_lambda_5.csv`](evidence/sqrt2_mod2_lambda_5.csv)
- [`sqrt2_mod2_lambda_6.csv`](evidence/sqrt2_mod2_lambda_6.csv)
- [`states.json`](evidence/states.json)
- [`tables.tex`](evidence/tables.tex)
- [`verify_against_atlas.py`](evidence/verify_against_atlas.py)
- [`walnut_commands.txt`](evidence/walnut_commands.txt)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
