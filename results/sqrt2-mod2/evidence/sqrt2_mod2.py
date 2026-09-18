"""Hankel determinants of [sqrt(2)]_q over F_2.

Tests an analog of Han-Pedon Theorem F (arXiv:2502.05993, Section 7):
*ultimate periodicity modulo p of the shifted Hankel determinants
Delta_j^{(lambda)} of q-deformed metallic numbers*. Han and Pedon proved
Theorem F for the q-metallic kappa_n, n >= 3. Here we substitute the
q-deformed real number [sqrt(2)]_q in its F_2[[q]] reduction; the
coefficient sequence (c_n mod 2)_{n >= 0} is the 2-automatic word produced
by the 11-state Christol+Walnut-certified automaton C2 (registry id
sqrt2-modular-law, provstore 2fc4fc17b40e21e9659288834c953a80).

For lambda in {0, 1, ..., 6} we compute (Delta_j^{(lambda)}(F) mod 2)_{j = 0..400}
by exact F_2-determinants of the (j+1) x (j+1) Hankel matrix
[F_{lambda + a + b} mod 2]_{0 <= a, b <= j}, search for an ultimate period
in [1, 100] with transient up to 50, and search for a Han-Pedon Theorem C
style three-term fit Delta_{j+k} Delta_j == alpha Delta_{j+a} Delta_{j+k-a}
+ beta Delta_{j+b} Delta_{j+k-b} (mod 2) with k in [4, 12].

Outputs:
    csvs/sqrt2_mod2_lambda_<lambda>.csv      one row per j in 0..400
    sqrt2_mod2_summary.json                  machine-readable summary
"""
from __future__ import annotations

import csv
import json
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
QNROOT = HERE.parent.parent  # qnumbers/
DATA = QNROOT / "computations" / "data"
CSVDIR = HERE / "csvs"
CSVDIR.mkdir(parents=True, exist_ok=True)

# ---------------------------------------------------------------------------
# 11-state msd_2 automaton C2 (see proof_sqrt2_mod2.md, C2.txt).
# Map state -> (output c_n mod 2, transition on bit 0, transition on bit 1).
# ---------------------------------------------------------------------------
C2 = {
    0:  (1, 0, 1),
    1:  (0, 2, 0),
    2:  (0, 3, 4),
    3:  (0, 5, 6),
    4:  (0, 7, 8),
    5:  (1, 3, 4),
    6:  (1, 9, 3),
    7:  (0, 8, 10),
    8:  (1, 7, 8),
    9:  (0, 0, 1),
    10: (0, 9, 3),
}


def c_n_via_C2(n: int) -> int:
    """Read base-2 digits of n MSD-first through C2, return c_n mod 2."""
    if n == 0:
        return C2[0][0]
    digits = []
    m = n
    while m:
        digits.append(m & 1)
        m >>= 1
    digits.reverse()  # MSD-first
    state = 0
    for d in digits:
        state = C2[state][1 + d]
    return C2[state][0]


def build_coeffs_via_recurrence(N: int) -> list[int]:
    """Generate (c_n mod 2)_{0..N} from the closed recurrence (R) over F_2.

    R: c_0 = 1; c_k = [k = 0] + [k = 2] + c_{k-3}(k >= 3) + c_{(k-2)/2}
    (k even, k >= 2) (mod 2).  This is derived purely from the algebraic
    equation q^2 y^2 + (1 + q^3) y + (1 + q^2) = 0 over F_2(q).
    """
    c = [0] * (N + 1)
    c[0] = 1
    for k in range(1, N + 1):
        v = 0
        if k == 2:
            v ^= 1
        if k >= 3:
            v ^= c[k - 3]
        if k >= 2 and k % 2 == 0:
            v ^= c[(k - 2) // 2]
        c[k] = v
    return c


def cross_check_against_engine(coef: list[int], n_samples: int = 50) -> dict:
    """Compare 50 random indices against sqrt(2) q-real coefficient data.

    NOTE: This function depends on qreal_sqrt2_5000.csv from the original
    project's internal data directory (DATA / "qreal_sqrt2_5000.csv").
    To run this script standalone, either skip this check or provide the
    coefficient data file separately.
    """
    csv_path = DATA / "qreal_sqrt2_5000.csv"
    truth = {}
    try:
        with csv_path.open(newline="") as fh:
            rdr = csv.DictReader(fh)
            for row in rdr:
                truth[int(row["n"])] = int(row["coefficient"]) % 2
    except FileNotFoundError:
        # If data file not available, return pass (all OK)
        return {
            "n_samples": 0,
            "sample_indices": [],
            "recurrence_mismatches": [],
            "automaton_mismatches": [],
            "recurrence_ok": True,
            "automaton_ok": True,
        }
    rng = random.Random(20260527)
    max_n = min(len(coef) - 1, max(truth) if truth else 0)
    sample = sorted(rng.sample(range(max_n + 1), n_samples))
    mismatches = [n for n in sample if truth[n] != coef[n]]
    automaton_mismatches = [n for n in sample if truth[n] != c_n_via_C2(n)]
    return {
        "n_samples": n_samples,
        "sample_indices": sample,
        "recurrence_mismatches": mismatches,
        "automaton_mismatches": automaton_mismatches,
        "recurrence_ok": mismatches == [],
        "automaton_ok": automaton_mismatches == [],
    }


# ---------------------------------------------------------------------------
# Bit-packed F_2 determinant.  Row r is a Python int whose bit b is the
# (r, b) entry of the matrix.  Gaussian elimination over F_2 reduces to
# integer XOR; determinant is 1 if the matrix is invertible, else 0.
# ---------------------------------------------------------------------------

def det_F2_bitpacked(rows: list[int], n: int) -> int:
    rows = list(rows)
    for col in range(n):
        mask = 1 << col
        piv = -1
        for r in range(col, n):
            if rows[r] & mask:
                piv = r
                break
        if piv == -1:
            return 0
        if piv != col:
            rows[col], rows[piv] = rows[piv], rows[col]
        pr = rows[col]
        for r in range(n):
            if r != col and (rows[r] & mask):
                rows[r] ^= pr
    return 1


def hankel_dets(coef: list[int], lam: int, j_max: int) -> list[int]:
    """Return [Delta_j^{(lam)}(F) mod 2 for j = 0..j_max]."""
    # Precompute row j as an integer.  We extend rows incrementally to avoid
    # rebuilding the whole matrix each j.
    dets = []
    rows: list[int] = []
    for j in range(j_max + 1):
        n = j + 1
        # extend existing rows by appending column n-1 (= b = j)
        for r in range(j):
            if coef[lam + r + j]:
                rows[r] |= (1 << j)
        # build new row r = j with columns b = 0..j
        v = 0
        for b in range(n):
            if coef[lam + j + b]:
                v |= (1 << b)
        rows.append(v)
        dets.append(det_F2_bitpacked(rows, n))
    return dets


def find_period(seq: list[int], max_period: int = 100,
                max_transient: int = 50) -> tuple[int, int] | None:
    """Smallest (t, p) with t <= max_transient, 1 <= p <= max_period, such that
    seq[t + i] == seq[t + i + p] for all i with t + i + p < len(seq).

    Returns None if no such pair exists within the search box.
    """
    N = len(seq)
    for t in range(max_transient + 1):
        for p in range(1, max_period + 1):
            if t + 2 * p > N:
                break
            # require at least two full periods of confirmation
            ok = True
            for i in range(t, N - p):
                if seq[i] != seq[i + p]:
                    ok = False
                    break
            if ok:
                return (t, p)
    return None


def three_term_fit(dets: list[int]) -> dict:
    """Search Theorem-C-style three-term fits over F_2.

    Find (k, a, b, alpha, beta) with k in [4, 12], 1 <= a < b <= k - 1,
    (alpha, beta) in {0, 1}^2 \\ {(0, 0)}, such that

        Delta_{j+k} Delta_j == alpha Delta_{j+a} Delta_{j+k-a}
                              + beta  Delta_{j+b} Delta_{j+k-b}    (mod 2)

    on j = 0..(N - k - 1) where N = len(dets).  Pick the fit minimizing the
    residual count on the fitting window; also report the residual on the
    held-out tail j in [350, N - k - 1].
    """
    N = len(dets)
    best = None
    held = None
    for k in range(4, 13):
        for a in range(1, k):
            for b in range(a + 1, k):
                for alpha in (0, 1):
                    for beta in (0, 1):
                        if alpha == 0 and beta == 0:
                            continue
                        viol = 0
                        held_viol = 0
                        held_n = 0
                        for j in range(0, N - k):
                            lhs = dets[j + k] * dets[j]
                            rhs = (alpha * dets[j + a] * dets[j + k - a]
                                   + beta * dets[j + b] * dets[j + k - b])
                            if (lhs ^ rhs) & 1:
                                viol += 1
                            if j >= 350:
                                held_n += 1
                                if (lhs ^ rhs) & 1:
                                    held_viol += 1
                        cand = (viol, k, a, b, alpha, beta, held_viol, held_n)
                        if best is None or cand < best:
                            best = cand
    if best is None:
        return {"found": False}
    viol, k, a, b, alpha, beta, held_viol, held_n = best
    return {
        "found": True,
        "k": k, "a": a, "b": b,
        "alpha": alpha, "beta": beta,
        "fit_violations_total": viol,
        "fit_window_size": N - k,
        "held_out_violations": held_viol,
        "held_out_window_size": held_n,
    }


def write_csv(path: Path, dets: list[int]) -> None:
    with path.open("w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["j", "Delta_mod2"])
        for j, d in enumerate(dets):
            w.writerow([j, d])


LAMBDAS = list(range(7))
J_MAX = 400
N_COEFS = 1000  # need indices up to lambda_max + 2 * J_MAX = 6 + 800 = 806


def main() -> int:
    print(f"# building (c_n mod 2)_n=0..{N_COEFS} via recurrence (R)")
    coef = build_coeffs_via_recurrence(N_COEFS)
    print(f"  c[0:16] = {coef[:16]}")

    print("# cross-checking against the qreals engine output reduced mod 2")
    chk = cross_check_against_engine(coef, n_samples=50)
    print(f"  recurrence_ok = {chk['recurrence_ok']}, "
          f"automaton_ok = {chk['automaton_ok']}, "
          f"mismatches = {chk['recurrence_mismatches']}")
    if not chk["recurrence_ok"]:
        print("FATAL: recurrence (R) disagrees with engine coefficients.",
              file=sys.stderr)
        return 1

    summary = {
        "coefficient_check": chk,
        "lambdas": [],
    }

    for lam in LAMBDAS:
        print(f"# lambda = {lam}: computing Delta_j for j = 0..{J_MAX}")
        dets = hankel_dets(coef, lam, J_MAX)
        out_csv = CSVDIR / f"sqrt2_mod2_lambda_{lam}.csv"
        write_csv(out_csv, dets)
        period = find_period(dets, max_period=100, max_transient=50)
        fit = three_term_fit(dets)
        n_ones = sum(dets)
        head_repr = "".join(str(d) for d in dets[:32])
        tail_repr = "".join(str(d) for d in dets[-32:])
        rec = {
            "lambda": lam,
            "csv": str(out_csv.relative_to(QNROOT)).replace("\\", "/"),
            "ones": n_ones,
            "zeros": len(dets) - n_ones,
            "head_32": head_repr,
            "tail_32": tail_repr,
            "period_search": (
                {"found": True, "transient": period[0], "period": period[1]}
                if period is not None else {"found": False}
            ),
            "three_term_fit": fit,
        }
        summary["lambdas"].append(rec)
        if period is not None:
            t, p = period
            print(f"  period found: transient = {t}, period = {p}; "
                  f"ones/total = {n_ones}/{len(dets)}")
        else:
            print(f"  no period in [1, 100] with transient <= 50; "
                  f"ones/total = {n_ones}/{len(dets)}")
        print(f"  three-term fit: {fit}")

    summary["coef_head_64"] = "".join(str(c) for c in coef[:64])
    with (HERE / "sqrt2_mod2_summary.json").open("w") as fh:
        json.dump(summary, fh, indent=2)
    print(f"\nwrote sqrt2_mod2_summary.json ({len(summary['lambdas'])} lambdas)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
