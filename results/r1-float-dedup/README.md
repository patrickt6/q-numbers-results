# r1-float-dedup

![status: Found false](https://img.shields.io/badge/status-Found%20false-c2410c) ![logged: 2026-07](https://img.shields.io/badge/logged-2026--07-999999)

**In short.** Traced a misdiagnosed pilot disagreement to a floating-point bug treating sqrt(6) and sqrt(2)*sqrt(3) as distinct catalog entries.

## Statement

A pilot disagreement was misdiagnosed as a truncation artifact. The real cause was a floating-point deduplication bug that treated sqrt(6) and sqrt(2) times sqrt(3) as distinct catalog entries.

```math
\begin{aligned}
&\bigl|\operatorname{fl}(\sqrt6)-\operatorname{fl}(\sqrt2)\operatorname{fl}(\sqrt3)\bigr|=1\ \text{ulp}\\
&\sqrt6=\sqrt2\,\sqrt3\ \Longrightarrow\ [\sqrt6\,]_q=[\sqrt2\,\sqrt3\,]_q
\end{aligned}
```

*Found false:* A claim that was believed, tested, and found false. Includes my own.

## Evidence

No shippable evidence file for this result. See the repository README for why some folders are empty.

Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).

[All results](../../RESULTS.md)
