"""Write a README.md for each result folder and a RESULTS.md index.

Reads results.json and results/<id>/status.json. Standard library only.
Run from the repository root: python tools/make_pages.py
"""
import json
from pathlib import Path
from urllib.parse import quote

ROOT = Path(__file__).resolve().parent.parent
ORDER = ["proved", "verified", "disproved", "scooped", "open"]
COLOR = {"proved": "1f7a4d", "verified": "2f5bd3", "disproved": "c2410c",
         "scooped": "7c3aed", "open": "6b7280"}
LABEL = {"proved": "Proved", "verified": "Verified by computation",
         "disproved": "Found false", "scooped": "Already published", "open": "Open"}
COVER = {"full": "full claim", "narrower": "narrower claim", "conditional": "under stated hypotheses",
         "partial": "part of the claim", "statement_only": "stated, proof not finished"}


def badge(key, value, color):
    v = quote(value.replace("-", "--").replace("_", "__"), safe="")
    return f"![{key}: {value}](https://img.shields.io/badge/{quote(key)}-{v}-{color})"


def lean_line(lean):
    if not lean.get("flag"):
        return None
    cov = lean.get("coverage") or "statement_only"
    return f"Lean 4: {COVER.get(cov, cov)}"


def page(r, st, legend):
    rid, status = r["id"], r["status"]
    lean = st.get("lean", {})
    badges = [badge("status", LABEL[status], COLOR[status])]
    ll = lean_line(lean)
    if ll:
        badges.append(badge("Lean 4", ll.split(": ", 1)[1], "222222"))
    badges.append(badge("logged", r["date"], "999999"))
    out = [f"# {rid}", "", " ".join(badges), "", f"**In short.** {r['plain']}", "",
           "## Statement", "", r["statement"], ""]
    if r.get("latex"):
        out += ["```math", r["latex"].strip(), "```", ""]
    out += [f"*{LABEL[status]}:* {legend[status]}", ""]
    if lean.get("flag"):
        out += ["## Lean 4", ""]
        if lean.get("covers"):
            out += [lean["covers"], ""]
        for f in lean.get("files", []):
            name = Path(f).name
            out.append(f"- [`{name}`]({f})" if (ROOT / "results" / rid / f).exists() else f"- `{f}`")
        if lean.get("build_command"):
            out += ["", f"Build: `{lean['build_command']}`"]
        out.append("")
    ev = sorted(p for p in (ROOT / "results" / rid / "evidence").glob("*") if p.name != ".gitkeep")
    out += ["## Evidence", ""]
    if ev:
        out += [f"- [`{p.name}`](evidence/{quote(p.name)})" for p in ev]
    else:
        out.append("No shippable evidence file for this result. See the repository README for why some folders are empty.")
    out += ["", "Statement as LaTeX: [`statement.tex`](statement.tex). Raw record: [`status.json`](status.json).",
            "", "[All results](../../RESULTS.md)", ""]
    return "\n".join(out)


def main():
    data = json.loads((ROOT / "results.json").read_text())
    legend, results = data["legend"], data["results"]
    for r in results:
        st = json.loads((ROOT / "results" / r["id"] / "status.json").read_text())
        (ROOT / "results" / r["id"] / "README.md").write_text(page(r, st, legend))
    counts = {s: sum(r["status"] == s for r in results) for s in ORDER}
    idx = ["# All results", "",
           f"{len(results)} results, generated from `results.json` ({data['generated_at']}). "
           "Click a result for its statement, Lean status and evidence files.", "",
           " ".join(badge(LABEL[s], str(counts[s]), COLOR[s]) for s in ORDER if counts[s]), "",
           data["note"], ""]
    for s in ORDER:
        rows = sorted((r for r in results if r["status"] == s), key=lambda r: r["date"])
        if not rows:
            continue
        idx += [f"## {LABEL[s]} ({len(rows)})", "", legend[s], "", "| Result | Logged | In short |", "|---|---|---|"]
        idx += [f"| [{r['id']}](results/{r['id']}/) | {r['date']} | {r['plain'].replace('|', '/')} |" for r in rows]
        idx.append("")
    (ROOT / "RESULTS.md").write_text("\n".join(idx))


if __name__ == "__main__":
    main()
