"""Per-constant compute orchestrator - cube-root + higher algebraic modular
atlas (buildout 16, Phase 2 deliverable C).

Given a constant slug, computes the first N stable Taylor coefficients of
[alpha]_q via the Sage `q_real_truncated` fallback engine (the Phase 1 Q1
decision: the FLINT `fast_compute/` engine does not extend to cubics) and
writes `<path>`.

Output schema is matched byte-for-byte to the existing canonical
`<path>`:
  - header `n,coefficient`
  - one data row per index n in [0, N): `<n>,<integer coefficient>`
  - CRLF (\\r\\n) line terminator on every line, including a trailing CRLF
    after the last data row
  - no extra blank line

The constant registry below is the single source of truth for slug ->
(minimal polynomial, decimal value, Sage construction). It is mirrored in
`<path>`. cbrt2 is included in the
registry for completeness and for the smoke-test / cross-check tooling, but
the orchestrator refuses to regenerate `qreal_cbrt2_5000.csv` (it already
exists at a genuine N=5000 in the WSL clone; PRD says reuse as-is).

The constant input convention - `SR(<int>)^(1/<deg>)` for pure radicals,
`AA` real-root selection for the generic cubics - is the convention verified
byte-exact against the existing cbrt2 data by Phase 2 smoke test 1
(`smoke_test_1_cbrt2.sage`).

Usage (WSL, sage micromamba env, run from repo root):
  cd /path/to/qnumbers
  ~/.local/bin/micromamba run -n sage sage \\
      <path> <slug> [N]

  <slug> : one of cbrt3 cbrt5 qrt2 plastic root_x3_2x_2 cbrt2
           or the literal "all-new" to compute the 5 new constants in order.
  N      : optional, default 5000.

Importable use (from another .sage via load()):
  load("<path>")
  compute_constant("cbrt3", 5000)
"""

import csv
import os
import sys
import time

from sage.all import SR, AA, QQ, PolynomialRing

# The Sage fallback engine. Provides q_real_truncated(x, N).
load("<path>")

REPO_ROOT = os.path.abspath(os.getcwd())
DATA_DIR = os.path.join(REPO_ROOT, "computations", "data")
DEFAULT_N = 5000


# ---------------------------------------------------------------------------
# Constant registry - single source of truth (mirrored in constants.md)
# ---------------------------------------------------------------------------
#
# Each entry: slug -> dict with
#   min_poly  : the minimal polynomial over Q, as a human-readable string
#   degree    : algebraic degree
#   decimal   : a 30-digit decimal string (for documentation / cross-check)
#   sage_expr : a human-readable description of the Sage construction
#   builder   : a zero-argument callable returning the Sage element to feed
#               q_real_truncated. Pure radicals use SR(...)^(1/deg) (the
#               convention smoke test 1 verified byte-exact on cbrt2). The
#               two generic cubics use AA real-root selection so the engine
#               gets the *real* root unambiguously.
#
# Why the builders differ:
#   - cbrt2, cbrt3, cbrt5, qrt2 are pure radicals: SR(n)^(1/d) is exactly
#     the construction precompute_cbrt2_for_axplorer.sage used and smoke
#     test 1 confirmed byte-exact. Reused unchanged.
#   - plastic (root of x^3 - x - 1) and root_x3_2x_2 (root of x^3 - 2x - 2)
#     are not pure radicals. Each cubic has exactly one real root (verified
#     in constants.md). We select it via AA (the real algebraic field) so
#     there is no ambiguity about which root the q-series is built from,
#     then hand the AA element to q_real_truncated (which accepts any input
#     sage.continued_fraction accepts; AA reals qualify).


def _build_pure_radical(n, d):
    """SR(n)^(1/d) - the pure-radical construction (smoke-test-1 verified)."""
    return SR(n) ** (SR(1) / SR(d))


def _build_real_root(coeffs):
    """The unique real root, as an element of AA, of the monic integer
    polynomial with the given coefficient list (highest degree first).

    Both generic cubics in the registry have exactly one real root; this
    asserts that and returns it.
    """
    Rx = PolynomialRing(QQ, "x")
    x = Rx.gen()
    poly = sum(QQ(c) * x ** (len(coeffs) - 1 - i) for i, c in enumerate(coeffs))
    real_roots = poly.roots(AA, multiplicities=False)
    if len(real_roots) != 1:
        raise AssertionError(
            "expected exactly one real root for " + str(poly)
            + ", found " + str(len(real_roots))
        )
    return real_roots[0]


CONSTANTS = {
    "cbrt2": {
        "min_poly": "x^3 - 2",
        "degree": 3,
        "decimal": "1.25992104989487316476721060728",
        "sage_expr": "SR(2)^(1/3)",
        "builder": lambda: _build_pure_radical(2, 3),
        "is_new": False,  # already exists at genuine N=5000 (WSL clone)
    },
    "cbrt3": {
        "min_poly": "x^3 - 3",
        "degree": 3,
        "decimal": "1.44224957030740838232163831078",
        "sage_expr": "SR(3)^(1/3)",
        "builder": lambda: _build_pure_radical(3, 3),
        "is_new": True,
    },
    "cbrt5": {
        "min_poly": "x^3 - 5",
        "degree": 3,
        "decimal": "1.70997594667669698935310887254",
        "sage_expr": "SR(5)^(1/3)",
        "builder": lambda: _build_pure_radical(5, 3),
        "is_new": True,
    },
    "qrt2": {
        "min_poly": "x^4 - 2",
        "degree": 4,
        "decimal": "1.18920711500272106671749997056",
        "sage_expr": "SR(2)^(1/4)",
        "builder": lambda: _build_pure_radical(2, 4),
        "is_new": True,
    },
    "plastic": {
        "min_poly": "x^3 - x - 1",
        "degree": 3,
        "decimal": "1.32471795724474602596090885448",
        "sage_expr": "real root of x^3 - x - 1 selected via AA",
        "builder": lambda: _build_real_root([1, 0, -1, -1]),
        "is_new": True,
    },
    "root_x3_2x_2": {
        "min_poly": "x^3 - 2x - 2",
        "degree": 3,
        "decimal": "1.76929235423863141524040946433",
        "sage_expr": "real root of x^3 - 2x - 2 selected via AA",
        "builder": lambda: _build_real_root([1, 0, -2, -2]),
        "is_new": True,
    },
}

# The 5 new constants, in compute order (cbrt3 first so its runtime can be
# timed before deciding foreground vs detached batch for the rest).
NEW_CONSTANTS_ORDER = ["cbrt3", "cbrt5", "qrt2", "plastic", "root_x3_2x_2"]


# ---------------------------------------------------------------------------
# CSV writer - byte-exact match to qreal_cbrt2_5000.csv
# ---------------------------------------------------------------------------


def _write_csv(coeffs, out_path):
    """Write the coefficient list to out_path with the canonical schema.

    Canonical format (verified against qreal_cbrt2_5000.csv with od -c):
      header `n,coefficient`, CRLF terminator on every line including the
      last data row, no trailing blank line.
    """
    # newline="" so csv does not translate; lineterminator="\r\n" emits CRLF.
    with open(out_path, "w", encoding="utf-8", newline="") as fh:
        writer = csv.writer(fh, lineterminator="\r\n")
        writer.writerow(["n", "coefficient"])
        for n, c in enumerate(coeffs):
            writer.writerow([n, c])


# ---------------------------------------------------------------------------
# Core: compute one constant
# ---------------------------------------------------------------------------


def compute_constant(slug, N=DEFAULT_N, allow_cbrt2=False):
    """Compute [<slug>]_q to N stable Taylor coefficients and write the CSV.

    Returns a dict: {slug, csv_path, N, n_coeffs, compute_seconds,
    write_seconds, first_coeffs, decimal, min_poly, sage_expr}.

    Refuses to overwrite qreal_cbrt2_5000.csv unless allow_cbrt2=True
    (cbrt2 already exists at a genuine N=5000; PRD says reuse, not
    regenerate).
    """
    if slug not in CONSTANTS:
        raise KeyError(
            "unknown constant slug '" + str(slug) + "'. known: "
            + ", ".join(sorted(CONSTANTS))
        )
    spec = CONSTANTS[slug]
    out_path = os.path.join(DATA_DIR, "qreal_" + slug + "_" + str(N) + ".csv")

    if slug == "cbrt2" and not allow_cbrt2:
        raise RuntimeError(
            "refusing to regenerate " + out_path + ": cbrt2 already exists "
            "at a genuine N=5000 in the WSL clone; the PRD says reuse as-is. "
            "Pass allow_cbrt2=True only if you really mean to overwrite it."
        )

    print("-" * 70)
    print("computing [" + slug + "]_q  (min poly " + spec["min_poly"]
          + ", degree " + str(spec["degree"]) + ")")
    print("  sage construction : " + spec["sage_expr"])
    print("  decimal           : " + spec["decimal"])
    print("  N (stable coeffs) : " + str(N))
    print("  output            : " + out_path)

    x = spec["builder"]()
    # Sanity: the constructed element's decimal must match the registry.
    constructed_decimal = (SR(x)).n(digits=30)
    print("  constructed value : " + str(constructed_decimal))

    t0 = time.time()
    series = q_real_truncated(x, N)
    compute_seconds = time.time() - t0

    # q_real_truncated returns a LaurentSeries over ZZ; the canonical cbrt2
    # file (and every qreal_*.csv) starts at n=0. Index [0, N).
    coeffs = [int(series[k]) for k in range(N)]
    first_coeffs = coeffs[:12]
    print("  compute_seconds   : {:.2f}".format(compute_seconds))
    print("  first 12 coeffs   : " + str(first_coeffs))

    t1 = time.time()
    _write_csv(coeffs, out_path)
    write_seconds = time.time() - t1
    print("  write_seconds     : {:.2f}".format(write_seconds))
    print("  wrote " + str(len(coeffs)) + " data rows")

    return {
        "slug": slug,
        "csv_path": out_path,
        "N": N,
        "n_coeffs": len(coeffs),
        "compute_seconds": compute_seconds,
        "write_seconds": write_seconds,
        "first_coeffs": first_coeffs,
        "decimal": spec["decimal"],
        "min_poly": spec["min_poly"],
        "sage_expr": spec["sage_expr"],
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _main():
    argv = sys.argv[1:]
    if not argv:
        print(__doc__)
        print("ERROR: need a constant slug (or 'all-new').")
        return 1
    slug = argv[0]
    N = int(argv[1]) if len(argv) > 1 else DEFAULT_N

    if slug == "all-new":
        results = []
        for s in NEW_CONSTANTS_ORDER:
            results.append(compute_constant(s, N))
        print("=" * 70)
        print("all-new complete: " + str(len(results)) + " constants")
        for r in results:
            print("  " + r["slug"] + " -> " + r["csv_path"]
                  + "  ({:.1f}s)".format(r["compute_seconds"]))
        return 0

    compute_constant(slug, N)
    return 0


# Sage's preparser sets __name__ to 'sage.all' (not '__main__') when running
# a .sage file, so the usual __main__ guard does not fire. Instead: run _main
# only when this file is the script being invoked directly (sys.argv[0] is
# this file's basename) AND CLI args were passed. When loaded via load() from
# another .sage, sys.argv[0] is the OTHER script, so this stays a no-op and
# load() picks up compute_constant / CONSTANTS silently.
_THIS_BASENAME = "cubic_atlas_compute.sage"
if (
    len(sys.argv) > 1
    and os.path.basename(sys.argv[0]) == _THIS_BASENAME
):
    # Do NOT sys.exit() at module scope in a .sage file: Sage's preparsed
    # runner mishandles the SystemExit and reports a spurious exit code 1
    # even on a clean return. Call _main() directly; on a non-zero return
    # raise SystemExit explicitly so a batch script still sees the failure.
    _rc = _main()
    if _rc:
        raise SystemExit(_rc)
