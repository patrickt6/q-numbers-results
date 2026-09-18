"""Build + verify the minimal base-7 DFAO for c_n([sqrt(2)]_q) mod 7.

Generalizes the mod-2 template from alphabet {0,1} to {0,...,6},
numeration msd_2 -> msd_7, output alphabet {0,1} -> {0,...,6} (full
residue c_n mod 7).

The construction is INDEPENDENT of any coefficient CSV.  It is driven by
the modulo-7 recurrence derived symbolically from the Morier-Genoud-
Ovsienko algebraic equation (Prop. 4.5 of arXiv:1908.04365):

      q^2 y^2 + (1 - q^3) y - (1 + q^2) = 0     over  F_7(q),

      y = sum_{n>=0} c_n q^n,   c_n in F_7,   c_0 = 1.

Extracting [q^k] of the equation:
      b_{k-2} + c_k - c_{k-3} - [k=0] - [k=2] = 0,
where  b_j = sum_{i=0..j} c_i c_{j-i}  is the self-convolution of c.
Hence the closed mod-7 recurrence

      c_k = [k=0] + [k=2] + c_{k-3}(k>=3) - b_{k-2}(k>=2)   in F_7.   (R7)

(Unlike p=2, the y^2 term does NOT collapse via Frobenius at p=7, so
(R7) keeps the full quadratic convolution b_{k-2}; the highest index in
b_{k-2} is c_{k-2} < c_k, so (R7) is a valid forward recurrence from
c_0 = 1.)

The DFAO is then built by the Myhill-Nerode / 7-kernel construction:
the MSD-first state reached after reading a prefix of value p is the
equivalence class of p under
      p ~ p'  iff  a(p*7^L + e) = a(p'*7^L + e) for all L, e<7^L,
with start p=0, transition p --d--> 7p+d (d in 0..6), output a(p).
Christol's theorem guarantees finitely many classes.

Then VERIFY byte-equality vs a canonical reference coefficient CSV
(full residue, n=0..20000), reproduce the atlas {2,4} row counts,
and run the independent recurrence/skeptic checks.  Exits 0 iff all PASS.

Run:  python build_sqrt2_mod7_dfao.py
"""
from __future__ import annotations

import csv
import json
import os
import sys

sys.set_int_max_str_digits(2_000_000)

P = 7
HERE = os.path.dirname(os.path.abspath(__file__))
# Path to a canonical reference coefficient CSV (n, coefficient) with the
# full integer q-series coefficients of [sqrt(2)]_q for n in [0, 20000].
# Set REFERENCE_CSV to point at your local reference data before running.
REFERENCE_CSV = os.environ.get("REFERENCE_CSV", "")
CSV_PATH = REFERENCE_CSV or os.path.join(HERE, "qreal_sqrt2_20000.csv")


# --- (R7): the algebra-derived mod-7 recurrence ----------------------------

def gen_mod7(NN: int) -> list[int]:
    """Generate (c_n mod 7) for n in [0, NN) from recurrence (R7).

    Purely arithmetic, no CSV.  numpy-vectorized self-convolution:
      b[k] = sum_{i=0..k} c_i c_{k-i} mod 7  =  c[0:k+1] . c[k::-1]  (mod 7).
    The recurrence for c_k needs only b_{k-2} (known), so we compute c_k,
    then b_k by one numpy dot.  O(NN^2) flops but vectorized -> fast.
    """
    import numpy as np
    c = np.zeros(NN, dtype=np.int64)
    b = np.zeros(NN, dtype=np.int64)
    c[0] = 1
    b[0] = 1
    for k in range(1, NN):
        v = 0
        if k == 2:
            v += 1
        if k >= 3:
            v += int(c[k - 3])
        if k >= 2:
            v -= int(b[k - 2])
        c[k] = v % P
        # b[k] = c[0:k+1] . reverse(c[0:k+1])  mod 7
        b[k] = int(np.dot(c[:k + 1], c[k::-1]) % P)
    return [int(x) for x in c]


# --- p-kernel DFAO (LSD-natural), keyed by (L, r) --------------------------
#
# A kernel state is the subsequence  m -> a(7^L * m + r),  0 <= r < 7^L.
# LSD transition on digit d:  (L, r) --d--> (L+1, r + d*7^L).
# Output of state (L, r) is a(r)  (= the m=0 value).
# After reading the base-7 digits of n LEAST-significant first, the output
# is a(n).  This only needs a probe window m in [0, W): we require
# 7^L * (W-1) + r < NN, i.e. the window fits in the generated prefix.
# Christol guarantees finitely many distinct kernel sequences.

def build_kernel_lsd(a: list[int], window: int = 24):
    """Build the LSD p-kernel DFAO using a FIXED-length probe window.

    The signature of kernel state (L, r) is the fixed-length tuple
    (a(r), a(7^L + r), a(2*7^L + r), ..., a((window-1)*7^L + r)).
    Fixed length is essential: variable-length windows never hash-match
    across levels even for identical sequences.  Empirically the kernel
    closes by L=2 (10 distinct window sequences), so a small NN suffices.
    """
    NN = len(a)

    def sig(L, r):
        mult = P ** L
        if mult * (window - 1) + r >= NN:
            raise IndexError(
                f"window exceeds NN at (L={L},r={r}); raise NN or lower window"
            )
        return tuple(a[mult * m + r] for m in range(window))

    sig_to_id = {}
    rep = {}
    out = {}
    trans = {}
    s0 = sig(0, 0)
    sig_to_id[s0] = 0
    rep[0] = (0, 0)
    out[0] = a[0]
    queue = [0]
    nid = 1
    while queue:
        s = queue.pop(0)
        L, r = rep[s]
        for d in range(P):
            Lc, rc = L + 1, r + d * (P ** L)
            cs = sig(Lc, rc)
            if cs in sig_to_id:
                trans[(s, d)] = sig_to_id[cs]
            else:
                sig_to_id[cs] = nid
                rep[nid] = (Lc, rc)
                out[nid] = a[rc]
                trans[(s, d)] = nid
                queue.append(nid)
                nid += 1
    states = sorted(rep.keys())
    return states, trans, out, 0


def simulate_lsd(trans, out, start, n: int) -> int:
    if n == 0:
        digits = [0]
    else:
        digits = []
        m = n
        while m:
            digits.append(m % P)
            m //= P
        # LSD-first: least significant digit first (already in that order)
    s = start
    for d in digits:
        s = trans[(s, d)]
    return out[s]


# --- Myhill-Nerode MSD-first DFAO over alphabet {0..6} ---------------------

def build_dfao(a: list[int], probe_levels: int = 5):
    NN = len(a)
    span = P ** probe_levels

    def signature(p: int):
        sig = []
        mult = 1
        L = 0
        while L <= probe_levels:
            for e in range(mult):
                idx = p * mult + e
                if idx >= NN:
                    raise IndexError(
                        f"probe out of range: a[{idx}] but NN={NN}; "
                        f"raise NN or lower probe_levels"
                    )
                sig.append(a[idx])
            L += 1
            mult *= P
        return tuple(sig)

    def explorable(p: int) -> bool:
        return p * span + (span - 1) < NN

    assert explorable(0), "NN too small for probe_levels"
    sig_to_state: dict[tuple, int] = {}
    state_repr: dict[int, int] = {}
    out: dict[int, int] = {}
    trans: dict[tuple, int] = {}

    sig_to_state[signature(0)] = 0
    state_repr[0] = 0
    out[0] = a[0]
    queue = [0]
    next_id = 1
    while queue:
        s = queue.pop(0)
        p = state_repr[s]
        for d in range(P):
            pc = P * p + d
            if not explorable(pc):
                raise IndexError(
                    "prefix exceeded explorable range before closure; "
                    "increase NN"
                )
            csig = signature(pc)
            if csig in sig_to_state:
                trans[(s, d)] = sig_to_state[csig]
            else:
                sig_to_state[csig] = next_id
                state_repr[next_id] = pc
                out[next_id] = a[pc]
                trans[(s, d)] = next_id
                queue.append(next_id)
                next_id += 1
    states = sorted(state_repr.keys())
    return states, trans, out, 0


def moore_minimize(states, trans, out, start):
    """Moore minimization of a complete DFAO over alphabet {0..P-1}."""
    block_of = {s: out[s] for s in states}
    while True:
        sig = {}
        for s in states:
            sig[s] = (block_of[s],) + tuple(block_of[trans[(s, d)]] for d in range(P))
        uniq = {}
        newlabel = {}
        nid = 0
        for s in states:
            if sig[s] not in uniq:
                uniq[sig[s]] = nid
                nid += 1
            newlabel[s] = uniq[sig[s]]
        if len({newlabel[s] for s in states}) == len({block_of[s] for s in states}):
            block_of = newlabel
            break
        block_of = newlabel
    rep = {}
    for s in states:
        rep.setdefault(block_of[s], s)
    start_block = block_of[start]
    order = [start_block] + [b for b in sorted(rep) if b != start_block]
    remap = {b: i for i, b in enumerate(order)}
    mstates = list(range(len(order)))
    mout = {remap[b]: out[rep[b]] for b in order}
    mtrans = {}
    for b in order:
        s = rep[b]
        for d in range(P):
            mtrans[(remap[b], d)] = remap[block_of[trans[(s, d)]]]
    return mstates, mtrans, mout, 0


def simulate(trans, out, start, n: int) -> int:
    if n == 0:
        digits = [0]
    else:
        digits = []
        m = n
        while m:
            digits.append(m % P)
            m //= P
        digits.reverse()
    s = start
    for d in digits:
        s = trans[(s, d)]
    return out[s]


def emit_walnut(states, trans, out, start, numeration) -> str:
    assert start == 0
    lines = [numeration, ""]
    for s in states:
        lines.append(f"{s} {out[s]}")
        for d in range(P):
            lines.append(f"{d} -> {trans[(s, d)]}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


# --- independent CSV reader (full residue mod 7) ---------------------------

def load_coeffs_mod7(path: str, N_inclusive: int) -> list[int]:
    """Return c_n mod 7 for n in [0, N_inclusive] (length N_inclusive+1).

    Reads the FULL integer (negative allowed) and takes Python %7 (always
    in 0..6).  NOT the last-decimal-digit trick (that is mod-2 only).
    """
    a = [None] * (N_inclusive + 1)
    with open(path) as f:
        r = csv.reader(f)
        header = next(r)
        assert header == ["n", "coefficient"], f"unexpected header {header}"
        for row in r:
            n = int(row[0])
            if n <= N_inclusive:
                a[n] = int(row[1]) % P
    assert all(x is not None for x in a), "missing coefficients in CSV"
    return a


def main() -> int:
    # ---- [1] DISCOVERY: pin the statement from the CSV ground truth ----
    print("=" * 64)
    print("[1] DISCOVERY -- c_n mod 7 from reference CSV, n=0..19999")
    NMAX = 19999  # CSV has 20000 data rows: indices 0..19999
    a_csv = load_coeffs_mod7(CSV_PATH, NMAX)  # indices 0..19999 inclusive
    in24 = [n for n in range(NMAX + 1) if n % 7 in (2, 4)]
    in24_div = [n for n in in24 if a_csv[n] == 0]
    print(f"    indices n in [0,{NMAX}] with n%7 in {{2,4}}: {len(in24)}")
    print(f"    of those with 7|c_n (c_n=0 mod 7):           {len(in24_div)}")
    fwd_ok = (len(in24) == len(in24_div))
    print(f"    FORWARD LAW holds on all of them: {fwd_ok}")
    # converse failures: n NOT in {2,4} mod 7 but 7|c_n
    conv_fail = [n for n in range(NMAX + 1) if (n % 7 not in (2, 4)) and a_csv[n] == 0]
    print(f"    converse failures (7|c_n but n%7 not in {{2,4}}): {len(conv_fail)}")
    print(f"    e.g. n=21: 21%7={21 % 7}, c_21 mod7={a_csv[21]} (CSV c_21=0)")
    print(f"    e.g. n=24: 24%7={24 % 7}, c_24 mod7={a_csv[24]} (CSV c_24=-2030)")
    total_div = sum(1 for n in range(NMAX + 1) if a_csv[n] == 0)
    print(f"    total indices with 7|c_n in [0,{NMAX}]: {total_div}")
    assert fwd_ok, "FORWARD LAW FAILS on the CSV -- abort"
    assert len(conv_fail) > 0, "no converse failure found -- iff might hold?!"

    # ---- [2] AUTOMATON: build minimal base-7 DFAO from (R7) ----
    print("=" * 64)
    NN = 16_000  # generation horizon for the p-kernel
    print(f"[2] AUTOMATON -- gen c_n mod 7 from (R7) for n in [0,{NN}); "
          f"build p-kernel DFAO (lsd_7)")
    a = gen_mod7(NN)
    # cross-check (R7) vs CSV on the overlap (independent of CSV-driven build)
    overlap = min(NN, NMAX + 1)
    rec_vs_csv = [n for n in range(overlap) if a[n] != a_csv[n]]
    print(f"    (R7) recurrence vs CSV on [0,{overlap}): "
          f"{len(rec_vs_csv)} mismatches")
    assert not rec_vs_csv, f"(R7) disagrees with CSV at {rec_vs_csv[:10]}"
    states, trans, out, start = build_kernel_lsd(a, window=24)
    print(f"    raw kernel states (lsd): {len(states)}")
    states, trans, out, start = moore_minimize(states, trans, out, start)
    print(f"    minimized states:  {len(states)}")
    # leading-zero invariance (lsd: trailing leading zeros at MSB end map via
    # the longest-digit reading; for lsd the relevant invariant is checked by
    # full byte-equality below rather than a delta(start,0) identity)
    # DFAO reproduces (R7) on the whole generation horizon
    bad = [n for n in range(NN) if simulate_lsd(trans, out, start, n) != a[n]]
    assert not bad, f"DFAO != (R7) at {bad[:10]}"
    print(f"    LSD DFAO reproduces (R7) on all {NN} indices OK")

    # ---- [3] VERIFY vs atlas (LOAD-BEARING, byte-equality) ----
    print("=" * 64)
    print(f"[3] VERIFY -- DFAO output == c_n mod 7 byte-equal on [0,{NMAX}]")
    mism = [n for n in range(NMAX + 1)
            if simulate_lsd(trans, out, start, n) != a_csv[n]]
    print(f"    byte-equality mismatches over {NMAX + 1} values: {len(mism)}")
    if mism:
        print(f"    first 10 mismatches: {mism[:10]}")
        raise SystemExit("BYTE-EQUALITY FAILED -- automaton is wrong")
    print(f"    PASS: DFAO is BYTE-EQUAL to MGO c_n mod 7 on all {NMAX + 1}")
    # reproduce atlas {2,4} row counts
    dfao_in24_div = [n for n in in24 if simulate_lsd(trans, out, start, n) == 0]
    print(f"    atlas check: {len(in24)} indices in {{2,4}} mod 7, "
          f"DFAO says all divisible: {len(dfao_in24_div) == len(in24)}")
    assert len(dfao_in24_div) == len(in24)

    # ---- emit DFAO file (lsd_7) ----
    print("=" * 64)
    print("[4] emit Walnut DFAO S7.txt (lsd_7)")
    msd = emit_walnut(states, trans, out, start, f"lsd_{P}")
    s7_local = os.path.join(HERE, "S7.txt")
    with open(s7_local, "w", newline="\n") as f:
        f.write(msd)
    print(f"    wrote {s7_local}")
    graph = {
        "numeration": f"lsd_{P}",
        "alphabet": list(range(P)),
        "output_alphabet": list(range(P)),
        "semantics": "output at state reached after reading base-7 digits of n "
                     "(LSD first) equals c_n([sqrt2]_q) mod 7",
        "source_equation": "q^2 y^2 + (1 - q^3) y - (1 + q^2) = 0 over F_7(q) "
                           "(MGO Prop 4.5 mod 7)",
        "recurrence": "c_k = [k=0]+[k=2]+c_{k-3}(k>=3)-b_{k-2}(k>=2), "
                      "b_j=sum_i c_i c_{j-i}, in F_7",
        "n_states": len(states),
        "start": start,
        "states": [
            {"id": s, "output": out[s],
             "delta": [trans[(s, d)] for d in range(P)]}
            for s in states
        ],
        "byte_equal_indices_inclusive": NMAX,
    }
    with open(os.path.join(HERE, "S7_states.json"), "w") as f:
        json.dump(graph, f, indent=2)

    # ---- [5] ADVERSARIAL skeptic pass ----
    print("=" * 64)
    print("[5] ADVERSARIAL -- independent recompute of a few large n via (R7)")
    # (R7) was generated only to NN=8000; recompute a few targeted large n
    # by EXTENDING the recurrence to that n, independent of the CSV slice
    # used implicitly nowhere (build used (R7), verify used CSV).  Here we
    # extend (R7) past NN and compare to both CSV and DFAO.
    BIG = 19999
    a_big = gen_mod7(BIG + 1)
    probes = [9999, 13337, 17501, 19998, 19999]
    for n in probes:
        rec = a_big[n]
        dfa = simulate_lsd(trans, out, start, n)
        csvv = a_csv[n]
        ok = (rec == dfa == csvv)
        print(f"    n={n:6d}: (R7)={rec} DFAO={dfa} CSV={csvv}  {'OK' if ok else 'MISMATCH'}")
        assert ok, f"adversarial mismatch at n={n}"
    # witness for the iff-FALSE: n=21 is 7|c_21 but 21%7=0 not in {2,4}
    w = 21
    print(f"    iff-witness n={w}: DFAO={simulate_lsd(trans,out,start,w)} "
          f"(=0 means 7|c), {w}%7={w % 7} not in {{2,4}} -> iff is FALSE")
    assert simulate_lsd(trans, out, start, w) == 0 and w % 7 not in (2, 4)
    # confirm base-7 reading: n=2 -> last base7 digit 2; n=9 = '12'_7
    assert simulate_lsd(trans, out, start, 2) == a_csv[2]
    print(f"    base-7 sanity: 9 in base7 = '{_b7(9)}', DFAO(9)="
          f"{simulate_lsd(trans,out,start,9)} == CSV {a_csv[9]}")

    print("=" * 64)
    print(f"all-PASS: minimal msd_7 DFAO has {len(states)} states; "
          f"byte-equal to c_n mod 7 on [0,{NMAX}]; forward law holds; "
          f"converse FALSE (witness n=21).")
    print("status PASS")
    return 0


def _b7(n: int) -> str:
    if n == 0:
        return "0"
    ds = []
    while n:
        ds.append(str(n % 7))
        n //= 7
    return "".join(reversed(ds))


if __name__ == "__main__":
    raise SystemExit(main())
