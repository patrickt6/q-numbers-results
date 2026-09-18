"""Batch q-real coefficient compute for Paper 2 modular atlas.

Buildout 13 (Paper 2 Modular Atlas), Deliverable 2.

Reads `<path>` and produces one
`<path>` per row, registering each in provstore
with content-hashing on the CSV path.

The file extension is `.sage` per phase-1 `02-todo.md`'s preference. The
heavy lifting (provstore registration, manifest writing, halves-differ check,
filename contract enforcement) is in pure Python and lives in
`<path>`. The per-constant compute
itself uses the FLINT-backed Newton iteration in
`<path>` (the same
backend D1.5 used for the two anchors at N=20000).

This `.sage` wrapper exists so the Sage runtime is on PATH for the
FLINT backend. The batch_runner_d2 module is import-safe under either
Sage's `sage <file.sage>` invocation or plain `python <runner>.py`; this
file is the recommended entry point for the production batch.

CLI (env vars; defaults shown):
  START_IDX=0
  END_IDX=<input csv length>
  N_TARGET=20000
  OUTPUT_DIR=<path>
  BACKEND=sage                                # passthrough to engine
  INPUT_CSV=<path>
  HARD_CEILING_S=10800                        # 3 hours per constant
  REQUIRE_VALIDATION_GATE=1                   # refuse if gate didn't pass

Usage (canonical WSL store):
  cd /path/to/qnumbers
  ~/.local/bin/micromamba run -n sage sage \
      <path>
"""
import os
import sys
import runpy

# Locate the repo root from the script's path.
_HERE_CANDS = [
    os.path.join(os.getcwd(), "qnumbers"),
    os.getcwd(),
]
REPO_ROOT = None
for _p in _HERE_CANDS:
    if os.path.isdir(_p):
        REPO_ROOT = _p
        break
if REPO_ROOT is None:
    raise RuntimeError("could not locate qnumbers repo root")

_RUNNER = os.path.join(REPO_ROOT, "computations", "modular_atlas", "batch_runner_d2.py")
if not os.path.isfile(_RUNNER):
    raise FileNotFoundError(_RUNNER)

# Exec the runner as if it were the main script. runpy preserves __name__
# so the runner's `if __name__ == "__main__"` block fires.
if __name__ in ("__main__", "sage.all"):
    runpy.run_path(_RUNNER, run_name="__main__")
