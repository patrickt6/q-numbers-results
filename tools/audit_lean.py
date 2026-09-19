#!/usr/bin/env python3
"""Audit the Lean sources of every result and write lean-status.json.

Standard library only (Python 3.8+). Run from anywhere:

    python3 tools/audit_lean.py                 # build, check, write lean-status.json
    python3 tools/audit_lean.py --require-lake  # exit 2 instead of skipping when Lake is missing
    python3 tools/audit_lean.py --skip-lake     # source scan only (no build, no axiom check)
    python3 tools/audit_lean.py --no-write      # print the report, do not write the file

What it does, per results/<id>/:

1. Source scan. Every .lean file is stripped of comments (block comments nest) and
   string and character literals, then searched for `sorry` and `axiom`
   declarations, plus a few trust flags (native_decide, implemented_by, extern,
   unsafe). A `sorry` written inside a comment or a string does not count.
2. Duplicate check. If two files in one project map to the same module name, they
   must be byte-identical (a copy that could diverge from the built module would
   otherwise go unnoticed).
3. Build. `lake build` in the Lake project that owns the result (see
   lean/audit-config.json). Lake is skipped, and this is said so, when it is not
   installed or when --skip-lake is given.
4. Axiom check. A Lean file is generated with `#print axioms` for every public
   top-level theorem and lemma, run with `lake env lean`, and the output is parsed.
   Only propext, Classical.choice and Quot.sound are accepted.
5. lean-status.json at the repository root, one entry per results/<id>/:
     proved          built, no sorry, no axiom declaration, every checked theorem
                     depends on standard axioms only, key theorem checked
     statement_only  built, but the source has sorry or an axiom declaration, or a
                     theorem depends on sorryAx or a non-standard axiom
     source_only     Lean sources exist but were not built or checked (Lake missing,
                     build failed, or a duplicate copy differs)
     none            no Lean sources

lean/audit-config.json gives an expected_state per result (default proved). The exit
code is 1 when a built result is observed in a state other than the expected one,
so a result that is meant to be statement_only does not fail the audit, and a
result that regresses does.

This script never edits the per-result status.json files. It does not judge whether
a theorem statement is faithful to the paper.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONFIG = os.path.join(ROOT, "lean", "audit-config.json")
OUT = os.path.join(ROOT, "lean-status.json")

TRUST_FLAGS = ["native_decide", "implemented_by", "extern", "unsafe"]


# ---------------------------------------------------------------- source scan

_CHAR_LIT = re.compile(
    r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'"
)


def strip_lean(src):
    """Return src with comments, string literals and char literals blanked out.

    Newlines are kept, so line numbers of the result match the original.
    Block comments nest, as in Lean 4.
    """
    out = []
    i, n = 0, len(src)

    def blank(chunk):
        return "".join("\n" if c == "\n" else " " for c in chunk)

    while i < n:
        c = src[i]
        two = src[i:i + 2]
        if two == "--":
            j = src.find("\n", i)
            j = n if j == -1 else j
            out.append(blank(src[i:j]))
            i = j
        elif two == "/-":
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                elif src.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            out.append(blank(src[i:j]))
            i = j
        elif c == "r" and re.match(r'r#*"', src[i:i + 8]) and (i == 0 or not re.match(r"[\w'.]", src[i - 1])):
            hashes = len(re.match(r"r(#*)", src[i:]).group(1))
            close = '"' + "#" * hashes
            j = src.find(close, i + 2 + hashes)
            j = n if j == -1 else j + len(close)
            out.append(blank(src[i:j]))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(blank(src[i:j]))
            i = j
        elif c == "'" and (i == 0 or not re.match(r"[\w'.»]", src[i - 1])):
            m = _CHAR_LIT.match(src, i)
            if m:
                out.append(blank(m.group(0)))
                i = m.end()
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


_PRINT_AXIOMS = re.compile(r"#print\s+axioms?\b")
_SORRY = re.compile(r"(?<![\w.'])sorry(?:Ax)?(?![\w'])")
_AXIOM = re.compile(r"(?<![\w.'])axiom(?![\w'])")
_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?P<mods>(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*)"
    r"(?P<kw>theorem|lemma)\s+(?P<name>[^\s:({\[]+)"
)
_NS = re.compile(r"^\s*namespace\s+(\S+)")
_SEC = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
_END = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")


def scan_file(path):
    """Scan one Lean file. Returns a dict of findings."""
    with open(path, encoding="utf-8") as fh:
        raw = fh.read()
    clean = _PRINT_AXIOMS.sub(lambda m: " " * len(m.group(0)), strip_lean(raw))
    sorries = [clean.count("\n", 0, m.start()) + 1 for m in _SORRY.finditer(clean)]
    axioms = [clean.count("\n", 0, m.start()) + 1 for m in _AXIOM.finditer(clean)]
    flags = {}
    for f in TRUST_FLAGS:
        hits = len(re.findall(r"(?<![\w.'])" + f + r"(?![\w'])", clean))
        if hits:
            flags[f] = hits

    theorems, private = [], []
    stack = []  # frames: ("ns", name) or ("sec", name or None)
    for lineno, line in enumerate(clean.split("\n"), 1):
        m = _NS.match(line)
        if m:
            stack.append(("ns", m.group(1)))
            continue
        m = _SEC.match(line)
        if m:
            stack.append(("sec", m.group(1)))
            continue
        m = _END.match(line)
        if m and stack:
            stack.pop()
            continue
        m = _DECL.match(line)
        if m:
            name = m.group("name")
            if "private" in m.group("mods").split():
                private.append(name)
                continue
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                prefix = ".".join(n for kind, n in stack if kind == "ns")
                full = prefix + "." + name if prefix else name
            theorems.append({"name": full, "line": lineno})
    return {
        "sorry_lines": sorries,
        "axiom_lines": axioms,
        "trust_flags": flags,
        "theorems": theorems,
        "private_theorems_skipped": len(private),
        "sha256": hashlib.sha256(raw.encode("utf-8")).hexdigest(),
    }


# ----------------------------------------------------------------- discovery

def rel(path):
    return os.path.relpath(path, ROOT).replace(os.sep, "/")


def package_root(path, stop):
    """Nearest ancestor directory of `path` (below `stop`) holding a lakefile."""
    d = os.path.dirname(path)
    while True:
        if os.path.exists(os.path.join(d, "lakefile.toml")) or os.path.exists(os.path.join(d, "lakefile.lean")):
            return d
        if os.path.abspath(d) == os.path.abspath(stop) or d == os.path.dirname(d):
            return None
        d = os.path.dirname(d)


def lean_files(result_dir):
    found = []
    for dirpath, dirnames, filenames in os.walk(result_dir):
        dirnames[:] = [d for d in dirnames if d not in (".lake", "build", ".git")]
        for f in filenames:
            if f.endswith(".lean") and f != "lakefile.lean":
                found.append(os.path.join(dirpath, f))
    return sorted(found)


def module_name(path, result_dir):
    pkg = package_root(path, result_dir)
    base = pkg if pkg else os.path.dirname(path)
    r = os.path.relpath(path, base)[: -len(".lean")]
    return r.replace(os.sep, ".")


# ------------------------------------------------------------------- running

def run(cmd, cwd, log=None, timeout=None):
    p = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       universal_newlines=True, timeout=timeout,
                       env=dict(os.environ, LEAN_NUM_THREADS=os.environ.get("LEAN_NUM_THREADS", "2")))
    return p.returncode, p.stdout


_AX_OUT = re.compile(
    r"'(?P<name>.+?)' (?:depends on axioms: \[(?P<ax>.*?)\]|does not depend on any axioms)", re.S)


def parse_axioms(text):
    got = {}
    for m in _AX_OUT.finditer(text):
        ax = m.group("ax")
        got[m.group("name")] = [a.strip() for a in re.split(r",\s*", " ".join(ax.split()))] if ax else []
    return got


def pinned_versions():
    info = {}
    try:
        with open(os.path.join(ROOT, "lean", "lean-toolchain")) as fh:
            info["mathlib_project_toolchain"] = fh.read().strip()
        with open(os.path.join(ROOT, "results", "degree-equality", "lean", "degreeeq", "lean-toolchain")) as fh:
            info["degreeeq_toolchain"] = fh.read().strip()
        with open(os.path.join(ROOT, "lean", "lake-manifest.json")) as fh:
            man = json.load(fh)
        for p in man.get("packages", []):
            if p.get("name") == "mathlib":
                info["mathlib_rev"] = p.get("rev")
                info["mathlib_tag"] = p.get("inputRev")
    except (OSError, ValueError):
        pass
    return info


# ---------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--skip-lake", action="store_true", help="scan sources only; do not build or check")
    ap.add_argument("--require-lake", action="store_true", help="exit 2 if Lake is not available")
    ap.add_argument("--no-write", action="store_true", help="print the report instead of writing lean-status.json")
    args = ap.parse_args()

    with open(CONFIG, encoding="utf-8") as fh:
        cfg = json.load(fh)
    standard = set(cfg["standard_axioms"])

    lake = None if args.skip_lake else shutil.which("lake")
    if lake is None:
        why = "skipped by --skip-lake" if args.skip_lake else "lake not found on PATH"
        print("NOTE: Lake is not available (%s). Sources are scanned, but nothing is built and no "
              "#print axioms check runs. Lean results are reported as source_only." % why)
        if args.require_lake and not args.skip_lake:
            print("ERROR: --require-lake was given.")
            return 2

    results_dir = os.path.join(ROOT, "results")
    ids = sorted(d for d in os.listdir(results_dir) if os.path.isdir(os.path.join(results_dir, d)))

    # 1. scan
    # Only files under results/<id>/lean/ belong to a Lake project and get built.
    # Any other .lean file (for example under evidence/) is scanned and listed,
    # but it is never built and never counts towards a status of proved.
    scans = {}   # id -> {file_rel: (module, scan)}   (project files)
    loose = {}   # id -> {file_rel: scan}             (not part of a Lake project)
    for rid in ids:
        rdir = os.path.join(results_dir, rid)
        ldir = os.path.join(rdir, "lean") + os.sep
        for f in lean_files(rdir):
            if f.startswith(ldir):
                scans.setdefault(rid, {})[rel(f)] = (module_name(f, rdir), scan_file(f))
            else:
                loose.setdefault(rid, {})[rel(f)] = scan_file(f)

    # 2. duplicate-module check, per project
    reasons = {rid: [] for rid in scans}
    by_mod = {}
    for rid, files in scans.items():
        proj = cfg["results"].get(rid, {}).get("project")
        for path, (mod, sc) in files.items():
            by_mod.setdefault((proj, mod), []).append((rid, path, sc["sha256"]))
    for (proj, mod), entries in by_mod.items():
        if len({e[2] for e in entries}) > 1:
            for rid, path, _ in entries:
                reasons[rid].append("module %s has copies that differ: %s" %
                                    (mod, ", ".join(e[1] for e in entries)))

    # 3 and 4. build and axiom check, per project
    build = {}   # project -> dict(exit=..., ok=bool)
    axioms = {}  # project -> {name: [axioms]}
    checked_ok = {}  # project -> bool (axiom run completed)
    tool_versions = {}
    if lake:
        for pname, pcfg in cfg["projects"].items():
            pdir = os.path.join(ROOT, pcfg["dir"])
            users = [rid for rid in scans if cfg["results"].get(rid, {}).get("project") == pname]
            if not users:
                continue
            print("== building project %s (%s)" % (pname, pcfg["dir"]))
            code, out = run([lake, "build"], pdir)
            build[pname] = {"exit": code, "ok": code == 0}
            print("   lake build exit %d" % code)
            if code != 0:
                print("\n".join(out.splitlines()[-30:]))
                continue
            code_v, out_v = run([lake, "env", "lean", "--version"], pdir)
            mv = re.search(r"version (\S+?),", out_v)
            tool_versions[pname] = ("Lean " + mv.group(1)) if code_v == 0 and mv else None
            mods = sorted({scans[rid][p][0] for rid in users for p in scans[rid]
                           if scans[rid][p][1]["theorems"]})
            names = sorted({t["name"] for rid in users for p in scans[rid] for t in scans[rid][p][1]["theorems"]})
            gen = ["-- generated by tools/audit_lean.py"] + ["import " + m for m in mods] + [""]
            gen += ["#print axioms " + n for n in names]
            with tempfile.TemporaryDirectory() as td:
                gpath = os.path.join(td, "AuditAxioms.lean")
                with open(gpath, "w", encoding="utf-8") as fh:
                    fh.write("\n".join(gen) + "\n")
                code, out = run([lake, "env", "lean", gpath], pdir)
            axioms[pname] = parse_axioms(out)
            checked_ok[pname] = True
            print("   #print axioms: %d of %d theorem names resolved (lean exit %d)" %
                  (len(axioms[pname]), len(names), code))
            if code != 0:
                print("\n".join(out.splitlines()[-30:]))

    # 5. classify
    report = {}
    def loose_entries(rid):
        return [{"path": p, "sorry_count": len(sc["sorry_lines"]),
                 "axiom_decl_count": len(sc["axiom_lines"]), "theorem_count": len(sc["theorems"])}
                for p, sc in loose.get(rid, {}).items()]

    for rid in ids:
        if rid not in scans:
            if rid in loose:
                report[rid] = {"status": "source_only",
                               "reasons": ["Lean file only outside results/<id>/lean/; not part of a Lake project, not built"],
                               "unbuilt_files": loose_entries(rid)}
            else:
                report[rid] = {"status": "none"}
            continue
        rc = cfg["results"].get(rid)
        proj = rc["project"] if rc else None
        files = scans[rid]
        entry = {"project": proj, "files": [], "reasons": reasons[rid]}
        if rid in loose:
            entry["unbuilt_files"] = loose_entries(rid)
        all_thms = []
        has_sorry = has_axiom = False
        for path, (mod, sc) in files.items():
            entry["files"].append({
                "path": path, "module": mod,
                "sorry_count": len(sc["sorry_lines"]), "axiom_decl_count": len(sc["axiom_lines"]),
                "theorem_count": len(sc["theorems"]),
                "private_theorems_skipped": sc["private_theorems_skipped"],
                "trust_flags": sc["trust_flags"],
            })
            has_sorry |= bool(sc["sorry_lines"])
            has_axiom |= bool(sc["axiom_lines"])
            all_thms += [(path, t) for t in sc["theorems"]]
        if has_sorry:
            entry["reasons"].append("source contains sorry")
        if has_axiom:
            entry["reasons"].append("source declares an axiom")
        if rc is None:
            entry["reasons"].append("no entry in lean/audit-config.json")
            entry["status"] = "source_only"
            report[rid] = entry
            continue

        status = "source_only"
        if lake is None:
            entry["reasons"].append("not built: Lake unavailable")
        elif not build.get(proj, {}).get("ok"):
            entry["reasons"].append("lake build failed in project %s" % proj)
        elif any(r.startswith("module ") for r in entry["reasons"]):
            entry["reasons"].append("not built as shipped: duplicate copies differ")
        else:
            ax = axioms.get(proj, {})
            bad, unresolved = [], []
            for path, t in all_thms:
                if t["name"] not in ax:
                    unresolved.append(t["name"])
                elif set(ax[t["name"]]) - standard:
                    bad.append(t["name"])
            key = rc.get("key_theorem")
            key_loc = next(((p, t["line"]) for p, t in all_thms if t["name"] == key), None)
            entry["key_theorem"] = {"name": key}
            if key_loc:
                entry["key_theorem"]["file"] = key_loc[0]
                entry["key_theorem"]["line"] = key_loc[1]
            entry["key_theorem"]["axioms"] = ax.get(key)
            entry["theorems_checked"] = len(all_thms) - len(unresolved)
            entry["theorems_unresolved"] = sorted(set(unresolved))
            entry["theorems_nonstandard_axioms"] = sorted(set(bad))
            entry["compiled"] = True
            key_ok = key in ax and not (set(ax[key]) - standard)
            if has_sorry or has_axiom or bad:
                status = "statement_only"
                if bad:
                    entry["reasons"].append("non-standard axioms (or sorryAx) in: " + ", ".join(sorted(set(bad))))
            elif not key_ok:
                status = "source_only"
                entry["reasons"].append("key theorem %s was not resolved by #print axioms" % key)
            else:
                status = "proved"
                if unresolved:
                    entry["reasons"].append("note: %d theorem names not resolved by #print axioms" % len(set(unresolved)))
        entry["status"] = status
        entry["expected_state"] = rc.get("expected_state", "proved")
        entry["toolchain"] = tool_versions.get(proj)
        report[rid] = entry

    doc = {
        "schema": 1,
        "generated_by": "tools/audit_lean.py",
        "meaning": {
            "proved": "compiled with lake build, no sorry, no axiom declaration, every checked theorem depends on standard axioms only",
            "statement_only": "compiled, but the source has sorry or an axiom declaration, or a theorem depends on a non-standard axiom",
            "source_only": "Lean sources exist but were not built or checked",
            "none": "no Lean sources",
        },
        "standard_axioms": sorted(standard),
        "lake_available": lake is not None,
        "pinned": pinned_versions(),
        "note": "Statement faithfulness to the paper is not audited.",
        "results": report,
    }
    text = json.dumps(doc, indent=2, sort_keys=False) + "\n"
    if args.no_write:
        sys.stdout.write(text)
    else:
        with open(OUT, "w", encoding="utf-8") as fh:
            fh.write(text)
        print("wrote " + rel(OUT))
    print("\nsummary:")
    bad_exit = False
    for rid, e in report.items():
        if e["status"] != "none":
            print("  %-16s %s" % (rid, e["status"]))
            if lake is not None and e.get("files"):
                expected = cfg["results"].get(rid, {}).get("expected_state", "proved")
                if e["status"] != expected:
                    print("    MISMATCH: expected %s (lean/audit-config.json)" % expected)
                    bad_exit = True
    return 1 if bad_exit else 0


if __name__ == "__main__":
    sys.exit(main())
