"""Linear-algebra functional-equation search for [alpha]_q.

For target alpha and search box (d_X, d_q_minus, d_q_plus, B), find
polynomials P(X, q) in Z[q, q^-1][X] of degree <= d_X in X, q-degree in
[-d_q_minus, d_q_plus], such that P([alpha]_q, q) == 0 mod q^N (where the
Laurent series is truncated above q^{N-1}, with the q^{-d_q_minus} ... q^{N-1}
window required to vanish). The lattice of such P is the right kernel of
an (N + d_q_minus) x ((d_X + 1)(d_q_minus + d_q_plus + 1)) integer matrix;
primitive integer basis is returned and intersected with the box |c| <= B.

Part 1 operated with d_q_minus = 0 (pure-polynomial in q).
Part 2 extends to Laurent in q via D_Q_MINUS env var, and
adds a KERNEL_RING=QQ mode for speed at large bidegrees (n_unknowns > 100).

Math precedent (MGO reals.pdf Section 4):
  Eq (17):  q^2 [sqrt(2)]_q^2 - (q^3 - 1) [sqrt(2)]_q - (q^2 + 1) = 0
  Eq (18):  q^2 [sqrt(3)]_q^2 - (q^3 + q^2 - q - 1) [sqrt(3)]_q - (q^2 + q + 1) = 0
  Eq (19):  q^3 [sqrt(5)]_q^2 - (q^5 + q^3 - q^2 - 1) [sqrt(5)]_q - (q^4 + q^3 + q^2 + q + 1) = 0
All three have all coefficients in {-1, 0, 1}. The sqrt(2) case is the
validation control for this script.

Usage (Sage 10.8's CLI does not pass argv to scripts, so parameters are
read from environment variables):
  cd ~/qnumbers
  ALPHA=sqrt2 D_X=2 D_Q=12 B=12 N=100 \
      sage <path>

Optional env vars:
  OUT          - JSON path
  VERIFY_TO    - re-check at higher N (default 0 = no re-check)
  USE_CSV=1    - read [alpha]_q from existing CSVs for verification
  D_Q_MINUS    - Laurent lower q-degree (default 0; Part 1 backwards-compatible)
  D_Q_PLUS     - Laurent upper q-degree (default = D_Q if set, else 0)
  KERNEL_RING  - "ZZ" (default) or "QQ"; QQ is much faster at n_unknowns > 100

Output: a JSON report (if OUT is given) plus stdout summary.
"""

import csv
import json
import os
import sys
import time

from sage.all import (
    SR, ZZ, QQ, sqrt, log, pi, e, zeta, cot, gcd, lcm, Matrix, vector, Rational,
)


# Pull in q_real_truncated. Sage's load() resolves relative to cwd, so this
# script must be run from the repo root (qnumbers/). The runner
# script (run_funcsearch.sh) cd's there before invoking.
_QCF_REL = "<path>"
_QCF_ABS = _QCF_REL  # set to an absolute path to your local checkout if needed
if os.path.exists(_QCF_REL):
    load(_QCF_REL)
elif os.path.exists("q_continued_fraction.sage"):
    load("q_continued_fraction.sage")
else:
    load(_QCF_ABS)


# ----- Targets -----
# Each entry: human-readable name, a sage symbolic value of alpha, and an
# optional CSV name (for --use_csv shortcut).
ALPHA_SPECS = {
    "sqrt2":   {"name": "[sqrt(2)]_q",  "value": sqrt(SR(2)),               "csv_name": "sqrt2"},
    "sqrt3":   {"name": "[sqrt(3)]_q",  "value": sqrt(SR(3)),               "csv_name": "sqrt3"},
    "sqrt5":   {"name": "[sqrt(5)]_q",  "value": sqrt(SR(5)),               "csv_name": "sqrt5"},
    "phi":     {"name": "[phi]_q",      "value": (1 + sqrt(SR(5))) / 2,     "csv_name": "phi"},
    "cbrt2":   {"name": "[cbrt(2)]_q",  "value": SR(2)**(SR(1)/SR(3)),      "csv_name": "cbrt2"},
    "cbrt3":   {"name": "[cbrt(3)]_q",  "value": SR(3)**(SR(1)/SR(3)),      "csv_name": "cbrt3"},
    "cbrt5":   {"name": "[cbrt(5)]_q",  "value": SR(5)**(SR(1)/SR(3)),      "csv_name": "cbrt5"},
    "qrt2":    {"name": "[2^(1/4)]_q",  "value": SR(2)**(SR(1)/SR(4)),      "csv_name": "qrt2"},
}


class Args:
    """Lightweight argparse-namespace replacement for env-var inputs."""

    def __init__(self, alpha, d_X, d_q_minus, d_q_plus, B, N, out=None,
                 verify_to=0, use_csv=False, kernel_ring="ZZ"):
        self.alpha = alpha
        self.d_X = d_X
        self.d_q_minus = d_q_minus
        self.d_q_plus = d_q_plus
        self.B = B
        self.N = N
        self.out = out
        self.verify_to = verify_to
        self.use_csv = use_csv
        self.kernel_ring = kernel_ring

    @property
    def d_q(self):
        """Backwards-compat: legacy d_q is total span d_q_minus + d_q_plus."""
        return self.d_q_minus + self.d_q_plus

    @property
    def laurent(self):
        return self.d_q_minus > 0


def parse_env():
    """Read parameters from environment variables (Sage's CLI does not
    propagate sys.argv to the script).

    Required: ALPHA, D_X, B, N. One of {D_Q, D_Q_PLUS} is required.
    Optional: D_Q_MINUS (default 0), D_Q_PLUS (default = D_Q),
              KERNEL_RING (default ZZ).
    """
    missing = [k for k in ("ALPHA", "D_X", "B", "N") if k not in os.environ]
    if missing:
        raise SystemExit(
            "Missing required environment variables: " + ", ".join(missing)
            + ". Example: ALPHA=sqrt2 D_X=2 D_Q=12 B=12 N=100 sage "
            + "<path>")
    if "D_Q" not in os.environ and "D_Q_PLUS" not in os.environ:
        raise SystemExit(
            "Must set either D_Q (legacy) or D_Q_PLUS (Part 2). "
            "Optionally set D_Q_MINUS for Laurent.")
    alpha = os.environ["ALPHA"]
    if alpha not in ALPHA_SPECS:
        raise SystemExit("Unknown ALPHA=" + alpha
                         + "; choices: " + ", ".join(sorted(ALPHA_SPECS)))
    d_q_plus = int(os.environ.get("D_Q_PLUS", os.environ.get("D_Q", "0")))
    d_q_minus = int(os.environ.get("D_Q_MINUS", "0"))
    if d_q_plus < 0 or d_q_minus < 0:
        raise SystemExit("D_Q_PLUS and D_Q_MINUS must be non-negative.")
    kernel_ring = os.environ.get("KERNEL_RING", "ZZ").upper()
    if kernel_ring not in ("ZZ", "QQ"):
        raise SystemExit("KERNEL_RING must be ZZ or QQ; got " + kernel_ring)
    return Args(
        alpha=alpha,
        d_X=int(os.environ["D_X"]),
        d_q_minus=d_q_minus,
        d_q_plus=d_q_plus,
        B=int(os.environ["B"]),
        N=int(os.environ["N"]),
        out=os.environ.get("OUT") or None,
        verify_to=int(os.environ.get("VERIFY_TO", "0")),
        use_csv=os.environ.get("USE_CSV", "") not in ("", "0", "false", "False"),
        kernel_ring=kernel_ring,
    )


# ----- [alpha]_q^k construction -----

def alpha_powers_from_sage(alpha_value, d_X, N):
    """Compute coefficients of [alpha]_q^k for k = 0..d_X to N coefficients each.

    Returns a list of (d_X + 1) lists, each of length N. coeffs[k] is the
    Taylor coefficients of [alpha]_q^k from q^0 up.
    """
    # PRECISION: q_real_truncated guarantees N stable coefficients; we ask for
    # a small safety margin so the multiplications below still have N valid
    # coefficients in the product.
    series = q_real_truncated(alpha_value, N + 5)
    coeffs0 = [1] + [0] * (N - 1)
    coeffs1 = [int(series[k]) for k in range(N)]
    coeffs_list = [coeffs0, coeffs1]
    cur = series
    for _ in range(2, d_X + 1):
        cur = cur * series
        coeffs_list.append([int(cur[k]) for k in range(N)])
    return coeffs_list


def alpha_powers_from_csv(csv_path, d_X, N):
    """Load [alpha]_q from CSV and compute the k = 2..d_X powers via integer
    convolution. Returns same shape as alpha_powers_from_sage.

    CSV format (run_qreal_50k.sage): header "n,coefficient", then rows.
    """
    coeffs1 = [0] * N
    with open(csv_path, newline="") as fh:
        rd = csv.reader(fh)
        next(rd)  # header
        for row in rd:
            if not row:
                continue
            k = int(row[0])
            if k >= N:
                break
            coeffs1[k] = int(row[1])
    coeffs0 = [1] + [0] * (N - 1)
    coeffs_list = [coeffs0, coeffs1]
    for _ in range(2, d_X + 1):
        prev = coeffs_list[-1]
        prod = [0] * N
        for i in range(N):
            ai = prev[i]
            if ai == 0:
                continue
            for j in range(N - i):
                bj = coeffs1[j]
                if bj == 0:
                    continue
                prod[i + j] += ai * bj
        coeffs_list.append(prod)
    return coeffs_list


# ----- Constraint matrix and kernel -----

def col_index(i, j, d_q_minus, d_q_plus):
    """Linear column index for the (i, j) coefficient.

    j ranges over [-d_q_minus, d_q_plus]; offset by d_q_minus so the
    column block for fixed i is contiguous and starts at j = -d_q_minus.
    Reduces to Part 1's row-major layout when d_q_minus = 0.
    """
    return i * (d_q_minus + d_q_plus + 1) + (j + d_q_minus)


def build_constraint_matrix(power_coeffs, d_X, d_q_minus, d_q_plus, N):
    """Build the (N + d_q_minus) x ((d_X + 1)(d_q_minus + d_q_plus + 1))
    integer matrix M.

    Columns are indexed by (i, j), 0 <= i <= d_X, -d_q_minus <= j <= d_q_plus.
    Rows are indexed by k in [-d_q_minus, N - 1]; row r = k + d_q_minus.
    Total rows = N + d_q_minus.

    Row r (i.e. q^k coefficient with k = r - d_q_minus) of P([alpha]_q, q)
    = sum_{i, j} c_{i, j} * (q^j * [alpha]_q^i)[k]
    where (q^j * [alpha]_q^i)[k] = power_coeffs[i][k - j] if k - j >= 0,
    else 0 (since [alpha]_q has zero negative coefficients).

    With d_q_minus = 0, this reduces to Part 1's matrix exactly.
    """
    n_cols = (d_X + 1) * (d_q_minus + d_q_plus + 1)
    n_rows = N + d_q_minus
    M = Matrix(ZZ, n_rows, n_cols, sparse=True)
    for i in range(d_X + 1):
        ci = power_coeffs[i]
        for j in range(-d_q_minus, d_q_plus + 1):
            col = col_index(i, j, d_q_minus, d_q_plus)
            # k - j >= 0 and k - j < N. So k >= max(j, -d_q_minus) and k < N + j.
            # In row coordinates: r = k + d_q_minus.
            k_lo = max(j, -d_q_minus)
            k_hi = min(N - 1, N - 1)  # k ranges to N-1
            for k in range(k_lo, N):
                m = k - j
                if m < 0 or m >= N:
                    continue
                v = ci[m]
                if v != 0:
                    M[k + d_q_minus, col] = v
    return M


def primitive_integer_basis_from_zz(K):
    """Return basis vectors of an integer kernel K as primitive integer
    vectors with positive leading nonzero entry."""
    out = []
    for v in K.basis():
        v = vector(ZZ, [int(c) for c in v])
        g = 0
        for c in v:
            g = gcd(g, int(c))
        if g not in (0, 1):
            v = vector(ZZ, [int(c) // g for c in v])
        for c in v:
            if c != 0:
                if c < 0:
                    v = -v
                break
        out.append(v)
    return out


def primitive_integer_basis_from_qq(K):
    """Convert a QQ kernel basis to primitive integer vectors with positive
    leading nonzero entry. Each basis vector is a list of Rationals; multiply
    by lcm of denominators to clear, then reduce by gcd of numerators.
    """
    out = []
    for v in K.basis():
        rationals = [Rational(c) for c in v]
        denom = 1
        for r in rationals:
            denom = lcm(denom, r.denominator())
        cleared = [int(r * denom) for r in rationals]
        g = 0
        for c in cleared:
            g = gcd(g, int(c))
        if g not in (0, 1):
            cleared = [int(c) // int(g) for c in cleared]
        for c in cleared:
            if c != 0:
                if c < 0:
                    cleared = [-c2 for c2 in cleared]
                break
        out.append(vector(ZZ, cleared))
    return out


def in_box(v, B):
    return all(abs(int(c)) <= B for c in v)


# ----- Pretty-printing -----

def vector_to_terms(v, d_X, d_q_minus, d_q_plus):
    """Return list of (i, j, c) triples with c != 0, in order
    (i ascending, then j ascending from -d_q_minus to d_q_plus).
    """
    terms = []
    for i in range(d_X + 1):
        for j in range(-d_q_minus, d_q_plus + 1):
            c = int(v[col_index(i, j, d_q_minus, d_q_plus)])
            if c != 0:
                terms.append((i, j, c))
    return terms


def pretty_polynomial(terms):
    if not terms:
        return "0"
    out = []
    for idx, (i, j, c) in enumerate(terms):
        ac = abs(c)
        if c < 0:
            sign = "-" if idx == 0 else " - "
        else:
            sign = "" if idx == 0 else " + "
        coeff_str = "" if (ac == 1 and (i > 0 or j != 0)) else str(ac)
        x_str = "" if i == 0 else ("X" if i == 1 else "X^" + str(i))
        if j == 0:
            q_str = ""
        elif j == 1:
            q_str = "q"
        elif j > 0:
            q_str = "q^" + str(j)
        elif j == -1:
            q_str = "q^-1"
        else:
            q_str = "q^" + str(j)
        body = "*".join(p for p in (coeff_str, x_str, q_str) if p)
        if body == "":
            body = "1"
        out.append(sign + body)
    return "".join(out)


# ----- Verification -----

def verify_polynomial_to_depth(v, power_coeffs_long, d_X, d_q_minus, d_q_plus, depth):
    """Verify that polynomial encoded by v annihilates [alpha]_q to q^depth.

    Checks every q^k coefficient of P([alpha]_q, q) for k in [-d_q_minus, depth-1].
    Returns (True, depth) on success, (False, k) where k is the first failing
    q-power index.
    """
    for k in range(-d_q_minus, depth):
        s = 0
        for i in range(d_X + 1):
            ci = power_coeffs_long[i]
            for j in range(-d_q_minus, d_q_plus + 1):
                m = k - j
                if m < 0 or m >= len(ci):
                    continue
                c = int(v[col_index(i, j, d_q_minus, d_q_plus)])
                if c == 0:
                    continue
                s += c * ci[m]
        if s != 0:
            return False, k
    return True, depth


# ----- Main -----

def main():
    args = parse_env()
    spec = ALPHA_SPECS[args.alpha]

    n_unknowns = (args.d_X + 1) * (args.d_q_minus + args.d_q_plus + 1)
    n_rows = args.N + args.d_q_minus
    overdet = n_rows / float(n_unknowns) if n_unknowns else float("inf")

    print("=== Functional equation search for " + spec["name"] + " ===")
    if args.laurent:
        print("  search box: d_X=" + str(args.d_X)
              + ", d_q_minus=" + str(args.d_q_minus)
              + ", d_q_plus=" + str(args.d_q_plus)
              + ", B=" + str(args.B)
              + ", N=" + str(args.N)
              + " (LAURENT)")
    else:
        print("  search box: d_X=" + str(args.d_X)
              + ", d_q=" + str(args.d_q_plus)
              + ", B=" + str(args.B)
              + ", N=" + str(args.N))
    print("  unknowns:   " + str(n_unknowns))
    print("  matrix:     " + str(n_rows) + " x " + str(n_unknowns)
          + "  overdet=" + ("%.2f" % overdet) + "x")
    print("  kernel ring:" + args.kernel_ring)

    print("\n[1/4] Computing [alpha]_q^k for k = 0..." + str(args.d_X)
          + " to " + str(args.N) + " coefficients each...")
    t0 = time.time()
    power_coeffs = alpha_powers_from_sage(spec["value"], args.d_X, args.N)
    sys.stdout.flush()
    print("      done in " + ("%.2f" % (time.time() - t0)) + "s")
    print("      [alpha]_q first 10 coeffs: " + str(power_coeffs[1][:10]))
    if args.d_X >= 2:
        print("      [alpha]_q^2 first 10 coeffs: " + str(power_coeffs[2][:10]))
    if args.d_X >= 3:
        print("      [alpha]_q^3 first 10 coeffs: " + str(power_coeffs[3][:10]))

    print("\n[2/4] Building " + str(n_rows) + " x " + str(n_unknowns)
          + " constraint matrix M...")
    t0 = time.time()
    M = build_constraint_matrix(power_coeffs, args.d_X,
                                args.d_q_minus, args.d_q_plus, args.N)
    print("      done in " + ("%.2f" % (time.time() - t0)) + "s")
    print("      M shape: " + str(M.nrows()) + " x " + str(M.ncols()))

    print("\n[3/4] Computing right kernel of M over " + args.kernel_ring + "...")
    t0 = time.time()
    if args.kernel_ring == "ZZ":
        K = M.right_kernel()
    else:
        K = M.change_ring(QQ).right_kernel()
    elapsed_kernel = time.time() - t0
    kdim = K.dimension()
    print("      done in " + ("%.2f" % elapsed_kernel) + "s")
    print("      kernel dimension: " + str(kdim))

    if kdim == 0:
        print("\n[4/4] NEGATIVE RESULT: no functional equation exists in the box "
              "(d_X=" + str(args.d_X)
              + ", d_q_minus=" + str(args.d_q_minus)
              + ", d_q_plus=" + str(args.d_q_plus)
              + ") modulo q^" + str(args.N) + ".")
        result = {
            "alpha": args.alpha,
            "d_X": int(args.d_X),
            "d_q": int(args.d_q),
            "d_q_minus": int(args.d_q_minus),
            "d_q_plus": int(args.d_q_plus),
            "laurent": bool(args.laurent),
            "kernel_ring_used": args.kernel_ring,
            "B": int(args.B), "N": int(args.N),
            "kernel_dim": int(0), "kernel_basis": [],
            "verification": None,
        }
        if args.out:
            os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
            with open(args.out, "w") as fh:
                json.dump(result, fh, indent=2)
            print("\nWrote " + args.out)
        return

    if args.kernel_ring == "ZZ":
        basis = primitive_integer_basis_from_zz(K)
    else:
        basis = primitive_integer_basis_from_qq(K)

    print("\n[4/4] Kernel basis (primitive integer, leading-positive):")
    for idx, v in enumerate(basis):
        terms = vector_to_terms(v, args.d_X, args.d_q_minus, args.d_q_plus)
        max_c = max(abs(int(c)) for c in v) if any(int(c) for c in v) else 0
        in_b = in_box(v, args.B)
        tag = " [in box]" if in_b else " [OUT of box]"
        print("  [" + str(idx) + "] max|c|=" + str(max_c) + tag)
        print("       " + pretty_polynomial(terms))

    in_box_polys = [v for v in basis if in_box(v, args.B)]
    print("\n  basis size: " + str(len(basis))
          + ", with |c| <= " + str(args.B) + ": " + str(len(in_box_polys)))

    verification_records = []
    if args.verify_to and args.verify_to > args.N:
        print("\n[verify] Re-computing [alpha]_q^k to N = " + str(args.verify_to)
              + " for verification...")
        t0 = time.time()
        long_coeffs = None
        if args.use_csv:
            csv_path = ("<path>"
                        + spec["csv_name"] + "_5000.csv")
            if os.path.exists(csv_path):
                print("[verify] reading [alpha]_q from " + csv_path)
                long_coeffs = alpha_powers_from_csv(
                    csv_path, args.d_X, args.verify_to)
            else:
                csv_path_alt = ("<path>"
                                + spec["csv_name"] + "_50000.csv")
                if os.path.exists(csv_path_alt):
                    print("[verify] reading [alpha]_q from " + csv_path_alt)
                    long_coeffs = alpha_powers_from_csv(
                        csv_path_alt, args.d_X, args.verify_to)
        if long_coeffs is None:
            long_coeffs = alpha_powers_from_sage(
                spec["value"], args.d_X, args.verify_to)
        print("[verify] done in " + ("%.2f" % (time.time() - t0)) + "s")
        for idx, v in enumerate(basis):
            ok, where = verify_polynomial_to_depth(
                v, long_coeffs, args.d_X,
                args.d_q_minus, args.d_q_plus, args.verify_to)
            verification_records.append({
                "basis_index": int(idx), "verify_to": int(args.verify_to),
                "ok": bool(ok),
                "first_failure_k": None if ok else int(where),
            })
            status = ("OK to N = " + str(args.verify_to)) if ok \
                else ("FAIL at q^" + str(where))
            print("[verify] basis[" + str(idx) + "]: " + status)

    result = {
        "alpha": args.alpha,
        "alpha_name": spec["name"],
        "d_X": int(args.d_X),
        "d_q": int(args.d_q),
        "d_q_minus": int(args.d_q_minus),
        "d_q_plus": int(args.d_q_plus),
        "laurent": bool(args.laurent),
        "kernel_ring_used": args.kernel_ring,
        "B": int(args.B), "N": int(args.N),
        "kernel_dim": int(kdim),
        "kernel_basis": [
            {
                "max_abs_coeff": int(max(abs(int(c)) for c in v)) if any(int(c) for c in v) else 0,
                "in_box": bool(in_box(v, args.B)),
                "terms": [{"i": int(i), "j": int(j), "c": int(c)}
                          for (i, j, c) in vector_to_terms(
                              v, args.d_X, args.d_q_minus, args.d_q_plus)],
                "string": pretty_polynomial(
                    vector_to_terms(v, args.d_X,
                                    args.d_q_minus, args.d_q_plus)),
            }
            for v in basis
        ],
        "verification": verification_records or None,
    }
    if args.out:
        out_dir = os.path.dirname(args.out) or "."
        os.makedirs(out_dir, exist_ok=True)
        with open(args.out, "w") as fh:
            json.dump(result, fh, indent=2)
        print("\nWrote " + args.out)


main()
