r"""Finiteness of [sqrt(D)]_q + [-sqrt(D)]_q over squarefree D, with CF-period data.

[-x]_q is the Jouteur arXiv:2503.02122 eq (2) negation (qreals.arithmetic._jouteur_neg);
negation_sum(x,N) returns the Laurent series of [x]_q + [-x]_q. sqrt2 control:
(q^3-1)/q^2 (valuation -2, coeffs -1 at q^-2 and +1 at q).

ROBUST finiteness detector (two-order stability, to beat the fragile low-order
trailing-zero heuristic that produced the refuted trace-zero criterion):
  finite  iff  last-nonzero index is identical at N=N1 and N=N2 (N1<N2) AND sits well
  below N1. infinite iff the last-nonzero index grows with N (the series keeps
  producing terms). The sqrt(D) anchors (2,3,5,6,7,13 finite; 19,43,46,53 infinite)
  must reproduce before any new row is trusted.

CF of sqrt(D): classical periodic CF [a0; a1,...,aL (period)], with period length L,
palindrome check, parity, central element, and the Pell/fundamental-unit norm.

Run:  install qreals, then from the qreals source tree
      PYTHONPATH=src python negation_scan.py
The qreals package supplies qreals.arithmetic.negation_sum.
Set OUT below to the directory where the CSV should be written.
"""
import sys, os, csv, time
from math import isqrt, gcd
import sympy as sp
sys.setrecursionlimit(100000)
sys.stdout.reconfigure(line_buffering=True)
# Ensure the qreals package is importable (e.g. point this at the qreals src tree).
# sys.path.insert(0, "<path-to-qreals-src>")
from qreals.arithmetic import negation_sum
q = sp.Symbol("q")
# Directory where the output CSV is written (defaults to the current directory).
OUT = os.environ.get("NEGATION_OUT", ".")

N1, N2 = 140, 420   # two orders for the stability test

def sqrt_cf_period(D):
    """Classical CF of sqrt(D): returns (a0, period_list). D not a perfect square."""
    a0 = isqrt(D)
    if a0*a0 == D:
        return a0, []
    m, d, a = 0, 1, a0
    period = []
    while a != 2*a0:
        m = d*a - m
        d = (D - m*m)//d
        a = (a0 + m)//d
        period.append(a)
    return a0, period

def pell_norm(D):
    """Fundamental unit norm: +1 if CF period length even, -1 if odd (classical)."""
    _, per = sqrt_cf_period(D)
    return -1 if len(per) % 2 == 1 else 1

def last_nonzero(x, N):
    _, c = negation_sum(x, N)
    return max([i for i, ci in enumerate(c) if ci != 0], default=-1)

def finiteness(x):
    l1 = last_nonzero(x, N1)
    l2 = last_nonzero(x, N2)
    fin = (l1 == l2) and (l1 < N1 - 20)
    return fin, l1, l2

def reduced_denom_if_finite(x):
    """When finite, the sum is a Laurent polynomial; return its (valuation, poly_str)."""
    v, c = negation_sum(x, N1)
    # strip trailing zeros
    last = max([i for i, ci in enumerate(c) if ci != 0], default=-1)
    coeffs = c[:last+1]
    expr = sum(ci*q**(v+i) for i, ci in enumerate(coeffs))
    return v, str(sp.expand(expr))

def main():
    t0 = time.time()
    # squarefree D in 2..200, excluding perfect squares
    Ds = [D for D in range(2, 201) if sp.factorint(D) and all(e == 1 for e in sp.factorint(D).values())]
    rows = []
    anchors_fin = {2,3,5,6,7,13}
    anchors_inf = {19,43,46,53}
    anchor_ok = True
    for D in Ds:
        x = f"sqrt({D})"
        fin, l1, l2 = finiteness(x)
        a0, per = sqrt_cf_period(D)
        L = len(per)
        paldifferent = per[:-1]  # CF palindrome: period minus last element is a palindrome
        is_pal = (palindrome_part := per[:-1]) == per[:-1][::-1] if L >= 1 else True
        central = None
        if L >= 1:
            body = per[:-1]
            if len(body) % 2 == 1:
                central = body[len(body)//2]
        rdenom = ""
        if fin:
            v, rdenom = reduced_denom_if_finite(x)
        if D in anchors_fin and not fin: anchor_ok = False
        if D in anchors_inf and fin: anchor_ok = False
        rows.append({
            "D": D, "finite": fin, "lastnz_N1": l1, "lastnz_N2": l2,
            "cf_a0": a0, "period": " ".join(map(str, per)), "period_len": L,
            "period_parity": "odd" if L % 2 else "even",
            "palindrome": is_pal, "central": central if central is not None else "",
            "pell_norm": pell_norm(D),
            "reduced_sum": rdenom,
        })
        flag = "FIN" if fin else "inf"
        print(f"  D={D:3d} {flag}  L={L} parity={'odd' if L%2 else 'even'} "
              f"central={central} pellN={pell_norm(D)}  ({time.time()-t0:.0f}s)", flush=True)

    with open(os.path.join(OUT, "negation_table.csv"), "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)

    fin_Ds = [r["D"] for r in rows if r["finite"]]
    inf_Ds = [r["D"] for r in rows if not r["finite"]]
    print(f"\nDONE {time.time()-t0:.0f}s; anchors reproduce: {anchor_ok}")
    print(f"FINITE D ({len(fin_Ds)}): {fin_Ds}")
    print(f"INFINITE D ({len(inf_Ds)}): {inf_Ds[:40]}...")
    # candidate separators
    print("\n--- separator analysis (over the scanned D) ---")
    def split_by(pred, label):
        fy = [r["D"] for r in rows if r["finite"] and pred(r)]
        fn = [r["D"] for r in rows if r["finite"] and not pred(r)]
        iy = [r["D"] for r in rows if not r["finite"] and pred(r)]
        ina = [r["D"] for r in rows if not r["finite"] and not pred(r)]
        # perfect separator if (pred <=> finite)
        mis = len(fn) + len(iy)  # finite-but-not-pred + infinite-but-pred
        print(f"  [{label}] finite&pred={len(fy)} finite&!pred={len(fn)} "
              f"inf&pred={len(iy)} inf&!pred={len(ina)}  misclass={mis}")
    split_by(lambda r: r["period_len"] == 1, "period_len==1")
    split_by(lambda r: r["period_parity"] == "even", "period even")
    split_by(lambda r: r["period_parity"] == "odd", "period odd")
    split_by(lambda r: r["pell_norm"] == -1, "pell_norm==-1")
    split_by(lambda r: r["period_len"] <= 2, "period_len<=2")

if __name__ == "__main__":
    main()
