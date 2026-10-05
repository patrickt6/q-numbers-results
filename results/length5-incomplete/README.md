# length5-incomplete

![status: Found false](https://img.shields.io/badge/status-Found%20false-c2410c) ![logged: 2026-08](https://img.shields.io/badge/logged-2026--08-999999)

**In short.** Found the nine hand-derived length-5 cases individually correct but incomplete; missing families appear at every k >= 3.

## Statement

The nine hand-derived length-5 cases are each individually correct but the list is not complete. Missing families appear at every k >= 3.

```math
\begin{aligned}
&\text{words in }V_5(k)\ \text{missing from the nine-case list},\ \ k=3,\dots,9:\\
&1,\ 8,\ 12,\ 12,\ 14,\ 16,\ 18\\
&\text{missing families:}\ \ \{c_3=c_4=1,\ c_2+c_5=1\},\ \ \{c_2=-1,\ c_4=0,\ c_3+c_5=-1\},\\
&(\varepsilon,3\varepsilon,\varepsilon,2\varepsilon),\ \ (1,2,2,1)
\end{aligned}
```

*Found false:* A claim that was believed, tested, and found false. Includes my own.

## Evidence

- [`P4-length5-verify.py`](evidence/P4-length5-verify.py)
- [`families_length5.py`](evidence/families_length5.py)

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
