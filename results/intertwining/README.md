# intertwining

![status: Proved](https://img.shields.io/badge/status-Proved-1f7a4d) ![Lean 4: narrower claim](https://img.shields.io/badge/Lean%204-narrower%20claim-222222) ![logged: 2026-07](https://img.shields.io/badge/logged-2026--07-999999)

**In short.** Proved NMN = M^-1 holds for the strictly wider family x = b0 sqrt(D), b0 rational, not just the pure square roots the manuscript assumed.

## Statement

The intertwining relation NMN = M^-1 holds exactly when x = b0 sqrt(D) with b0 rational, which is a strictly larger family than the pure square roots the manuscript hypothesis assumed.

```math
\begin{aligned}
&N=\begin{pmatrix}-1&0\\ 0&1\end{pmatrix},\ \ M\ \text{an automorph of the quadratic irrational }x\\
&NMN=M^{-1}\iff x+x^{\sigma}=0\\
&x+x^{\sigma}=0\iff x=b_0\sqrt{D},\ \ b_0\in\mathbb{Q}\setminus\{0\}
\end{aligned}
```

*Proved:* Proved on paper, and in some cases machine-checked in Lean.

## Lean 4

For det-1 real M fixing distinct x, x^σ (m3≠0), NMN=M⁻¹ iff x+x^σ=0; the equivalence with x=b0√D is not formalised.

- `Intertwine.lean`

Build: `lake build GosperCF.Pell GosperCF.Intertwine`

## Evidence

- [`broad_sweep.py`](evidence/broad_sweep.py)
- [`check_oracle.py`](evidence/check_oracle.py)
- [`falsification-record.json`](evidence/falsification-record.json)
- [`falsification-record.txt`](evidence/falsification-record.txt)
- [`falsify_beyond_pure.py`](evidence/falsify_beyond_pure.py)
- [`fast_word.py`](evidence/fast_word.py)
- [`gap_a_form.log`](evidence/gap_a_form.log)
- [`gap_a_search.py`](evidence/gap_a_search.py)
- [`gap_a_word.log`](evidence/gap_a_word.log)
- [`nonzero_trace.log`](evidence/nonzero_trace.log)
- [`nonzero_trace_extension.py`](evidence/nonzero_trace_extension.py)
- [`qperiod.py`](evidence/qperiod.py)
- [`runA.log`](evidence/runA.log)
- [`runB.log`](evidence/runB.log)
- [`scan_trace_zero.py`](evidence/scan_trace_zero.py)
- [`trace-zero-scan.json`](evidence/trace-zero-scan.json)
- [`trace-zero-scan.txt`](evidence/trace-zero-scan.txt)
- [`twisted_surd_test.py`](evidence/twisted_surd_test.py)
- [`verify-output.txt`](evidence/verify-output.txt)
- [`verify.py`](evidence/verify.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
