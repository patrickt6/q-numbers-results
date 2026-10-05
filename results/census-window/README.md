# census-window

![status: Found false](https://img.shields.io/badge/status-Found%20false-c2410c) ![logged: 2026-07](https://img.shields.io/badge/logged-2026--07-999999)

**In short.** Traced a 100.0000 percent, zero-exception census result to a window-floor bug; corrected figure is 97.36 percent with 15,929 exceptions.

## Statement

The off-axis census result of 100.0000 percent with zero exceptions was a window-floor bug, not an effect. The corrected run gives 97.36 percent with 15929 exceptions.

```math
\underbrace{100.0000\%,\ 0\ \text{exceptions}}_{\text{window-floor bug}}\ \longrightarrow\ \underbrace{97.36\%,\ 15929\ \text{exceptions}}_{\text{corrected}}
```

*Found false:* A claim that was believed, tested, and found false. Includes my own.

## Evidence

- [`acceptance_check.py`](evidence/acceptance_check.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
