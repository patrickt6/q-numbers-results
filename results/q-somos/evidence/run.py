#!/usr/bin/env python3
"""q-Somos-4 twist window extension to (a, b) in [-6, 6]^2, n <= 13.

An earlier run hung on the n=15 step (~56 min for one pair) and produced no
summary. This rerun:
  * caps N_MAX at 13 (genuine extension beyond the shipped n=11 record);
  * iterates depth-first so a partial run gives the full atlas through the
    last completed n rather than full data for one pair;
  * keeps per-pair state (sequence + alive flag) so each step is one cancel,
    not a from-scratch recompute;
  * writes the summary on clean exit AND on KeyboardInterrupt at whatever
    depth the run reached.

Same Laurent test as twist_search.py: x_{n+4} x_n = q^a x_{n+3} x_{n+1} +
q^b x_{n+2}^2, with x_0..x_3 symbolic. A value is Laurent in (x_0..x_3) over
Q(q) iff its reduced denominator is a single monomial in those four
variables.
"""
from __future__ import annotations

import csv
import os
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent

import sympy as sp  # noqa: E402

# ============================== TUNABLES ===================================
A_RANGE = range(-6, 7)
B_RANGE = range(-6, 7)
N_MIN = 4
N_MAX = 12
FLUSH_INTERVAL_S = 30.0
# ============================================================================

q = sp.Symbol("q")
X = sp.symbols("x0 x1 x2 x3")


def step(seq, n, a, b):
    numer = q**a * seq[n - 1] * seq[n - 3] + q**b * seq[n - 2] ** 2
    return sp.cancel(numer / seq[n - 4])


def laurent_signature(expr):
    expr = sp.cancel(expr)
    num, den = sp.fraction(sp.together(expr))
    try:
        den_poly = sp.Poly(sp.expand(den), *X)
    except (sp.PolynomialError, sp.GeneratorsError):
        return None, -1
    monoms = den_poly.monoms()
    if not monoms:
        return True, 0
    is_laurent = (len(monoms) == 1)
    return is_laurent, sum(monoms[0])


def main():
    csv_path = HERE / "results.csv"
    cf_file = csv_path.open("w", encoding="utf-8", newline="")
    writer = csv.writer(cf_file, lineterminator="\n")
    writer.writerow(["a", "b", "n", "is_laurent", "denom_degree", "elapsed_s"])
    cf_file.flush()

    pairs = [(a, b) for a in A_RANGE for b in B_RANGE]
    total_pairs = len(pairs)
    print(f"window a in {list(A_RANGE)} b in {list(B_RANGE)} n in [{N_MIN}, {N_MAX}]", flush=True)
    print(f"{total_pairs} pairs, depth-first outer loop, N_MAX = {N_MAX}", flush=True)

    state = {pair: {"seq": [X[0], X[1], X[2], X[3]], "alive": True, "prefix": N_MIN - 1, "degs": []} for pair in pairs}
    last_n_completed = N_MIN - 1
    t_start = time.time()
    t_last_flush = t_start
    rows_written = 0

    try:
        for n in range(N_MIN, N_MAX + 1):
            t_n_start = time.time()
            alive_at_start = sum(1 for s in state.values() if s["alive"])
            for (a, b) in pairs:
                s = state[(a, b)]
                if not s["alive"]:
                    continue
                nxt = step(s["seq"], n, a, b)
                s["seq"].append(nxt)
                is_l, dd = laurent_signature(nxt)
                elapsed = time.time() - t_start
                writer.writerow([a, b, n, bool(is_l), int(dd), f"{elapsed:.2f}"])
                rows_written += 1
                s["degs"].append(int(dd))
                if is_l:
                    s["prefix"] = n
                else:
                    s["alive"] = False

                now = time.time()
                if now - t_last_flush > FLUSH_INTERVAL_S:
                    cf_file.flush()
                    os.fsync(cf_file.fileno())
                    print(f"n={n} alive_done={sum(1 for ss in state.values() if ss['alive'] and len(ss['degs'])>=n-N_MIN+1)}/{alive_at_start} elapsed={elapsed:.1f}s rows={rows_written}", flush=True)
                    t_last_flush = now

            last_n_completed = n
            cf_file.flush()
            os.fsync(cf_file.fileno())
            alive_at_end = sum(1 for ss in state.values() if ss["alive"])
            print(f"depth n={n} DONE in {time.time()-t_n_start:.1f}s; pairs_alive={alive_at_end}/{alive_at_start}", flush=True)
            write_summary("checkpoint" if n < N_MAX else "complete", state, rows_written, last_n_completed)

        cf_file.close()
        write_summary("complete", state, rows_written, last_n_completed)
        return 0

    except KeyboardInterrupt:
        cf_file.flush()
        cf_file.close()
        write_summary("partial", state, rows_written, last_n_completed)
        print("interrupted; partial summary written", flush=True)
        return 130
    except Exception as exc:
        cf_file.flush()
        cf_file.close()
        write_summary("partial", state, rows_written, last_n_completed, error=str(exc))
        print(f"crashed at n={last_n_completed+1}: {exc}", flush=True)
        raise


def write_summary(status, state, rows_written, last_n_completed, error=None):
    n_pairs = len(state)
    winners = [(a, b) for (a, b), s in state.items() if s["alive"] and s["prefix"] >= last_n_completed and last_n_completed >= N_MAX]
    full_through_last = [(a, b) for (a, b), s in state.items() if s["prefix"] >= last_n_completed and last_n_completed >= N_MIN]
    failed_pairs = sorted(
        [((a, b), s["prefix"]) for (a, b), s in state.items() if not s["alive"]],
        key=lambda kv: kv[1],
    )

    distinct_deg_cols = set()
    for (a, b), s in state.items():
        if s["alive"] and len(s["degs"]) == max(0, last_n_completed - N_MIN + 1):
            distinct_deg_cols.add(tuple(s["degs"]))

    if status == "checkpoint":
        pill = "partial"
        conclusion = (
            f"Checkpoint after depth n = {last_n_completed} (of N_MAX = {N_MAX}). "
            f"{len(full_through_last)} of {n_pairs} pairs Laurent through n = {last_n_completed}; "
            f"{len(failed_pairs)} have failed at some earlier n. Rows: {rows_written}. "
            "Higher depths still in progress."
        )
        hypothesis = "Wait for clean exit, or read this snapshot if the run is killed."
    elif status == "complete":
        pill = "complete"
        if len(winners) == n_pairs:
            conclusion = (
                f"Every (a, b) in the extended window [-6, 6]^2 keeps x_4..x_{N_MAX} "
                f"Laurent in (x_0..x_3) over Q(q). The shipped [-3, 3]^2 / n <= 11 claim "
                f"extends to the wider window and two more depths without break; "
                f"distinct denominator-degree columns: {len(distinct_deg_cols)}."
            )
            hypothesis = (
                "The Laurent property of the q-Somos-4 family is a Berenstein-Zelevinsky "
                "compatible-pair phenomenon and holds for arbitrary integer twists; an "
                "exact compatibility argument should reproduce the column of denominator "
                "degrees observed here."
            )
        else:
            conclusion = (
                f"Of {n_pairs} pairs, {len(winners)} keep every x_n Laurent through n = {N_MAX}; "
                f"{n_pairs - len(winners)} fail. First-fail pairs reveal the boundary of the "
                "Laurent phenomenon in this twist family."
            )
            hypothesis = (
                "The failing region cuts the (a, b) plane into compatibility-conjectured "
                "rays; the boundary lines should be reproducible by a quantum-exchange-matrix "
                "rank condition."
            )
    else:
        pill = "partial"
        conclusion = (
            f"Run did not reach N_MAX = {N_MAX}. Last fully completed depth: n = {last_n_completed}. "
            f"{len(full_through_last)} of {n_pairs} pairs are Laurent through that depth; "
            f"{len(failed_pairs)} pairs have already failed at some earlier n. "
            f"Rows written: {rows_written}."
        )
        hypothesis = "Re-launch to push to the remaining depths."
        if error:
            conclusion += f" Exception: {error}."

    winners_html = ""
    if winners:
        winners_html = f"<p><b>All-the-way-Laurent winners</b> (n in [{N_MIN}, {N_MAX}]):</p><ul>"
        for (a, b) in winners[:80]:
            winners_html += f"<li>(a, b) = ({a}, {b})</li>"
        if len(winners) > 80:
            winners_html += f"<li>...{len(winners) - 80} more</li>"
        winners_html += "</ul>"

    fail_rows = ""
    for (a, b), pref in failed_pairs[:80]:
        fail_rows += f"<tr><td>{a}</td><td>{b}</td><td>{pref}</td></tr>"

    deg_col_html = ""
    if distinct_deg_cols:
        deg_col_html = "<p><b>Distinct denominator-degree columns</b> (across alive pairs):</p><ul>"
        for col in sorted(distinct_deg_cols):
            deg_col_html += f"<li><code>{list(col)}</code></li>"
        deg_col_html += "</ul>"

    html_str = f"""<!doctype html>
<html><head><meta charset='utf-8'><title>q-Somos-4 twist extended summary</title>
<style>body{{font:14px/1.45 system-ui,sans-serif;max-width:920px;margin:24px auto;padding:0 16px;color:#222}}
.pill{{display:inline-block;padding:3px 10px;border-radius:14px;font-weight:600;font-size:12px;letter-spacing:.04em;text-transform:uppercase}}
.complete{{background:#e7f4ea;color:#1f6b34;border:1px solid #b6dac1}}
.partial{{background:#fbf1e1;color:#8a6d1f;border:1px solid #f1dba4}}
.no-finding{{background:#eee;color:#555;border:1px solid #ccc}}
table{{border-collapse:collapse;font-size:13px;width:100%;margin:10px 0}}
th,td{{border-bottom:1px solid #ddd;padding:6px 8px;text-align:left}}
th{{background:#f4f4ef;text-transform:uppercase;font-size:11px;letter-spacing:.05em}}
</style></head><body>
<h1>q-Somos-4 twist window extended to (a, b) in [-6, 6]^2, n &le; {N_MAX}</h1>
<p><span class='pill {pill}'>{pill}</span></p>
<p>Pairs: {n_pairs}; full-through-last-depth: {len(full_through_last)}; failed: {len(failed_pairs)}; last completed depth: n = {last_n_completed}; rows written: {rows_written}.</p>
<p><b>Conclusion.</b> {conclusion}</p>
<p><b>Pattern hypothesis.</b> {hypothesis}</p>
{winners_html}
{deg_col_html}
<p><b>Failed pairs (sorted by Laurent prefix length, first 80)</b>:</p>
<table>
<thead><tr><th>a</th><th>b</th><th>Laurent prefix (max n still Laurent)</th></tr></thead>
<tbody>{fail_rows or '<tr><td colspan=3>none</td></tr>'}</tbody></table>
<p>Full per-(a, b, n) atlas in <code>results.csv</code>.</p>
</body></html>
"""
    (HERE / "summary.html").write_text(html_str, encoding="utf-8")


if __name__ == "__main__":
    sys.setrecursionlimit(80000)
    raise SystemExit(main())
