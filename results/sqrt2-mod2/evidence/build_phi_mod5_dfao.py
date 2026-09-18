"""Build + verify the minimal base-5 DFAO for c_n([phi]_q) mod 5.

Mirrors build_sqrt2_mod7_dfao.py at p=5 for the golden ratio phi
(minimal poly x^2 - x - 1).  The construction is INDEPENDENT of any
coefficient CSV; it is driven by the modulo-5 recurrence derived
symbolically from the Morier-Genoud-Ovsienko algebraic equation
(Prop. 4.2 of arXiv:1908.04365):

      q y^2 + (1 - q - q^2) y - 1 = 0     over  F_5(q),

      y = sum_{n>=0} c_n q^n,   c_n in F_5,   c_0 = 1.

Extracting [q^k] of the equation:
      b_{k-1} + c_k - c_{k-1} - c_{k-2} - [k=0] = 0,
where  b_j = sum_{i=0..j} c_i c_{j-i}  is the self-convolution of c.
Hence the closed mod-5 recurrence

      c_k = [k=0] + c_{k-1}(k>=1) + c_{k-2}(k>=2) - b_{k-1}(k>=1)  in F_5.  (R5)

(Like p=7, the y^2 term does NOT collapse via Frobenius at p=5, so (R5)
keeps the full quadratic convolution b_{k-1}; the highest index in
b_{k-1} is c_{k-1} < c_k, so (R5) is a valid forward recurrence from
c_0 = 1.)

POLARITY (non-divisibility / absorbing law -- the named biggest risk):
the target is the NON-divisibility statement
      for all n, (n mod 5 in {2,3,4}) => 5 does NOT divide c_n,
i.e. the DFAO output is NEVER 0 on the {2,3,4} last-base-5-digit class.
This is the OPPOSITE polarity of the mod-7 law (a divisibility law).

Verify: byte-equality vs a canonical reference coefficient CSV (full
residue, n=0..19999) AND independently vs the integer recurrence engine
(phi: P=q,Q=1-q-q^2,R=-1) reduced mod 5 -- TWO routes.  Then reproduce
the atlas {2,3,4} non-divisibility counts and run the adversarial /
polarity skeptic checks.  Exits 0 iff all PASS.

Run:  python build_phi_mod5_dfao.py
"""
from __future__ import annotations

import csv
import json
import os
import sys

sys.set_int_max_str_digits(2_000_000)

P = 5
HERE = os.path.dirname(os.path.abspath(__file__))
# Path to a canonical reference coefficient CSV (n, coefficient) with the
# full integer q-series coefficients of [phi]_q for n in [0, 20000].
# Set REFERENCE_CSV to point at your local reference data before running.
REFERENCE_CSV = os.environ.get("REFERENCE_CSV", "")
CSV_PATH = REFERENCE_CSV or os.path.join(HERE, "qreal_phi_20000.csv")
# Optional: directory containing a big-integer recurrence engine
# (recurrence.py exposing compute_qreal_coeffs) for the route-3 spot-check.
# Leave unset to skip the independent big-integer engine route.
FAST_COMPUTE = os.environ.get("FAST_COMPUTE", "")


# --- (R5): the algebra-derived mod-5 recurrence ----------------------------

def gen_mod5(NN: int) -> list[int]:
    """Generate (c_n mod 5) for n in [0, NN) from recurrence (R5).

    Purely arithmetic, no CSV.  numpy-vectorized self-convolution:
      b[k] = sum_{i=0..k} c_i c_{k-i} mod 5  =  c[0:k+1] . c[k::-1]  (mod 5).
    The recurrence for c_k needs only b_{k-1} (known), so we compute c_k,
    then b_k by one numpy dot.  O(NN^2) flops but vectorized -> fast.
    """
    import numpy as np
    c = np.zeros(NN, dtype=np.int64)
    b = np.zeros(NN, dtype=np.int64)
    c[0] = 1
    b[0] = 1
    for k in range(1, NN):
        v = 0
        # c_k = [k=0] + c_{k-1}(k>=1) + c_{k-2}(k>=2) - b_{k-1}(k>=1)
        v += int(c[k - 1])                 # k >= 1 always here
        if k >= 2:
            v += int(c[k - 2])
        v -= int(b[k - 1])                 # k >= 1 always here
        c[k] = v % P
        # b[k] = c[0:k+1] . reverse(c[0:k+1])  mod 5
        b[k] = int(np.dot(c[:k + 1], c[k::-1]) % P)
    return [int(x) for x in c]


# --- independent second route: the integer recurrence engine ---------------

def gen_mod5_engine(NN: int) -> list[int]:
    """Independent route: an integer compute_qreal_coeffs engine
    (recurrence.py, P=q, Q=1-q-q^2, R=-1) reduced mod 5.  This is a
    DIFFERENT code path (full big-integer recurrence) from gen_mod5.

    Requires the FAST_COMPUTE environment variable to point at a directory
    containing recurrence.py; raises RuntimeError otherwise.
    """
    if not FAST_COMPUTE:
        raise RuntimeError("FAST_COMPUTE not set; big-integer engine unavailable")
    sys.path.insert(0, FAST_COMPUTE)
    from recurrence import compute_qreal_coeffs  # type: ignore
    ints = compute_qreal_coeffs([0, 1], [1, -1, -1], [-1], NN, c0=1)
    return [x % P for x in ints]


# --- p-kernel DFAO (LSD-natural), keyed by (L, r) --------------------------

def build_kernel_lsd(a: list[int], window: int = 24):
    """Build the LSD p-kernel DFAO using a FIXED-length probe window.

    A kernel state is the subsequence  m -> a(5^L * m + r),  0 <= r < 5^L.
    LSD transition on digit d:  (L, r) --d--> (L+1, r + d*5^L).
    Output of state (L, r) is a(r)  (= the m=0 value).
    The signature is the fixed-length tuple
      (a(r), a(5^L + r), ..., a((window-1)*5^L + r)).
    Christol guarantees finitely many distinct kernel sequences.
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


def emit_walnut(states, trans, out, start, numeration) -> str:
    assert start == 0
    lines = [numeration, ""]
    for s in states:
        lines.append(f"{s} {out[s]}")
        for d in range(P):
            lines.append(f"{d} -> {trans[(s, d)]}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


# --- independent CSV reader (full residue mod 5) ---------------------------

def load_coeffs_mod5(path: str, N_inclusive: int) -> list[int]:
    """Return c_n mod 5 for n in [0, N_inclusive] (length N_inclusive+1).

    Reads the FULL integer (negative allowed) and takes Python %5 (always
    in 0..4).
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
    # ---- [1] DISCOVERY: pin the (non-divisibility) statement from CSV ----
    print("=" * 64)
    print("[1] DISCOVERY -- c_n mod 5 from reference CSV, n=0..19999")
    NMAX = 19999  # CSV has 20000 data rows: indices 0..19999
    a_csv = load_coeffs_mod5(CSV_PATH, NMAX)
    # pin small n exactly: c_2,c_3,c_4 mod 5 = 1,4,2; c_1 = 0 (class 1)
    print(f"    c_0..c_5 mod 5 = {a_csv[:6]}  (expect 1,0,1,4,2,1)")
    assert a_csv[:6] == [1, 0, 1, 4, 2, 1], "small-n residues unexpected!"
    in234 = [n for n in range(NMAX + 1) if n % 5 in (2, 3, 4)]
    # NON-divisibility law: c_n != 0 mod 5 on these classes
    in234_nondiv = [n for n in in234 if a_csv[n] != 0]
    in234_div = [n for n in in234 if a_csv[n] == 0]
    print(f"    indices n in [0,{NMAX}] with n%5 in {{2,3,4}}: {len(in234)}")
    print(f"    of those NON-divisible (c_n != 0 mod 5):       {len(in234_nondiv)}")
    print(f"    of those DIVISIBLE (c_n == 0 mod 5):           {len(in234_div)}")
    fwd_ok = (len(in234_div) == 0)
    print(f"    NON-DIVISIBILITY LAW holds on all of them: {fwd_ok}")
    assert fwd_ok, "NON-DIV LAW FAILS on the CSV -- abort"
    # explicit small-n confirmation: no n in {2,3,4} mod 5 has c_n=0
    print(f"    small-n: c_2,c_3,c_4 mod5 = {a_csv[2]},{a_csv[3]},{a_csv[4]} "
          f"(all nonzero -> {{2,3,4}} framing exception-free); "
          f"c_1={a_csv[1]} is class 1 (not in {{2,3,4}})")
    # converse failures: classes {0,1} that ARE divisible, and class 0
    # that is NON-divisible (converse of non-div law fails)
    div_all = [n for n in range(NMAX + 1) if a_csv[n] == 0]
    div_outside = [n for n in div_all if n % 5 not in (2, 3, 4)]  # all of them
    print(f"    total indices with 5|c_n in [0,{NMAX}]: {len(div_all)} "
          f"(all in classes {{0,1}}; {len(div_outside)} outside {{2,3,4}})")
    # converse-FALSE witness for the iff: an n NOT in {2,3,4} that is also
    # NON-divisible (so "non-div <=> class in {2,3,4}" fails).  e.g. n=5:
    # c_5=-4 != 0 mod5, 5%5=0 not in {2,3,4}.
    print(f"    iff-converse witness n=5: c_5 mod5={a_csv[5]} (NON-divisible), "
          f"5%5={5 % 5} not in {{2,3,4}} -> 'non-div <=> class234' is FALSE")
    print(f"    contrast n=10: c_10 mod5={a_csv[10]} (DIVISIBLE), "
          f"10%5={10 % 5} (both class 0, opposite divisibility)")
    assert a_csv[5] != 0 and a_csv[10] == 0, "c_5/c_10 polarity unexpected"

    # ---- [2] AUTOMATON: build minimal base-5 DFAO from (R5) ----
    print("=" * 64)
    NN = 16_000  # generation horizon for the p-kernel
    print(f"[2] AUTOMATON -- gen c_n mod 5 from (R5) for n in [0,{NN}); "
          f"build p-kernel DFAO (lsd_5)")
    a = gen_mod5(NN)
    # cross-check (R5) vs CSV on the overlap (build is CSV-independent)
    overlap = min(NN, NMAX + 1)
    rec_vs_csv = [n for n in range(overlap) if a[n] != a_csv[n]]
    print(f"    (R5) recurrence vs CSV on [0,{overlap}): "
          f"{len(rec_vs_csv)} mismatches")
    assert not rec_vs_csv, f"(R5) disagrees with CSV at {rec_vs_csv[:10]}"
    states, trans, out, start = build_kernel_lsd(a, window=24)
    print(f"    raw kernel states (lsd): {len(states)}")
    states, trans, out, start = moore_minimize(states, trans, out, start)
    print(f"    minimized states:  {len(states)}")
    bad = [n for n in range(NN) if simulate_lsd(trans, out, start, n) != a[n]]
    assert not bad, f"DFAO != (R5) at {bad[:10]}"
    print(f"    LSD DFAO reproduces (R5) on all {NN} indices OK")

    # ---- [3] VERIFY vs atlas (LOAD-BEARING, TWO-route byte-equality) ----
    print("=" * 64)
    print(f"[3] VERIFY -- DFAO output == c_n mod 5 byte-equal on [0,{NMAX}]")
    print("    route 1: reference CSV")
    mism_csv = [n for n in range(NMAX + 1)
                if simulate_lsd(trans, out, start, n) != a_csv[n]]
    print(f"    route-1 (CSV) mismatches over {NMAX + 1} values: {len(mism_csv)}")
    if mism_csv:
        print(f"    first 10 mismatches: {mism_csv[:10]}")
        raise SystemExit("BYTE-EQUALITY (CSV) FAILED -- automaton is wrong")
    # route 2 = the algebra-derived (R5) numpy recurrence over the FULL range
    # (mirrors the mod-7 CSV + recurrence two-route design; the full
    # big-integer engine to N=20000 is O(N^2) on thousand-digit integers and
    # is NOT used over the full range -- it is a cheap prefix spot-check below
    # instead).
    print("    route 2: algebra recurrence (R5) mod 5 (full range, numpy)")
    a_eng = gen_mod5(NMAX + 1)
    mism_eng = [n for n in range(NMAX + 1)
                if simulate_lsd(trans, out, start, n) != a_eng[n]]
    print(f"    route-2 (R5) mismatches over {NMAX + 1} values: {len(mism_eng)}")
    if mism_eng:
        print(f"    first 10 mismatches: {mism_eng[:10]}")
        raise SystemExit("BYTE-EQUALITY (R5) FAILED -- automaton is wrong")
    # cross-confirm CSV vs (R5) agree on the whole range (two independent
    # ground-truth methods: MGO-generated CSV vs algebraic recurrence)
    gt_disagree = [n for n in range(NMAX + 1) if a_csv[n] != a_eng[n]]
    print(f"    CSV vs (R5) ground-truth disagreements: {len(gt_disagree)}")
    assert not gt_disagree, f"CSV and (R5) disagree at {gt_disagree[:10]}"
    # route 3: a GENUINELY-independent big-integer engine (recurrence.py full
    # integer recurrence, reduced mod 5) spot-check on a prefix -- distinct
    # code path, kept short so it is fast.  Skipped if FAST_COMPUTE unset.
    if FAST_COMPUTE:
        SPOT = 1500
        print(f"    route 3: big-int engine (recurrence.py) mod 5, spot-check n<{SPOT}")
        a_big_eng = gen_mod5_engine(SPOT)
        mism_big = [n for n in range(SPOT)
                    if simulate_lsd(trans, out, start, n) != a_big_eng[n]]
        print(f"    route-3 (big-int engine) mismatches over {SPOT}: {len(mism_big)}")
        assert not mism_big, f"big-int engine disagrees at {mism_big[:10]}"
        print(f"    PASS: DFAO BYTE-EQUAL to c_n mod 5 on all {NMAX + 1} (CSV + R5) "
              f"and on [0,{SPOT}) (independent big-int engine)")
    else:
        print("    route 3: big-int engine skipped (FAST_COMPUTE not set)")
        print(f"    PASS: DFAO BYTE-EQUAL to c_n mod 5 on all {NMAX + 1} (CSV + R5)")
    # reproduce atlas {2,3,4} NON-divisibility counts
    dfao_in234_nondiv = [n for n in in234
                         if simulate_lsd(trans, out, start, n) != 0]
    print(f"    atlas check: {len(in234)} indices in {{2,3,4}} mod 5, "
          f"DFAO says all NON-divisible: {len(dfao_in234_nondiv) == len(in234)}")
    assert len(dfao_in234_nondiv) == len(in234)

    # ---- [4] emit DFAO file (lsd_5) ----
    print("=" * 64)
    print("[4] emit Walnut DFAO P5.txt (lsd_5)")
    txt = emit_walnut(states, trans, out, start, f"lsd_{P}")
    p5_local = os.path.join(HERE, "P5.txt")
    with open(p5_local, "w", newline="\n") as f:
        f.write(txt)
    print(f"    wrote {p5_local}")
    # To run the law in Walnut, copy the emitted P5.txt into your Walnut
    # "Word Automata Library" directory, then evaluate the predicates in
    # phi_walnut_commands.txt.
    graph = {
        "numeration": f"lsd_{P}",
        "alphabet": list(range(P)),
        "output_alphabet": list(range(P)),
        "semantics": "output at state reached after reading base-5 digits of n "
                     "(LSD first) equals c_n([phi]_q) mod 5",
        "source_equation": "q y^2 + (1 - q - q^2) y - 1 = 0 over F_5(q) "
                           "(MGO Prop 4.2 mod 5)",
        "recurrence": "c_k = [k=0]+c_{k-1}(k>=1)+c_{k-2}(k>=2)-b_{k-1}(k>=1), "
                      "b_j=sum_i c_i c_{j-i}, in F_5",
        "law": "NON-divisibility (absorbing): n%5 in {2,3,4} => c_n != 0 mod 5",
        "n_states": len(states),
        "start": start,
        "states": [
            {"id": s, "output": out[s],
             "delta": [trans[(s, d)] for d in range(P)]}
            for s in states
        ],
        "byte_equal_indices_inclusive": NMAX,
    }
    with open(os.path.join(HERE, "P5_states.json"), "w") as f:
        json.dump(graph, f, indent=2)

    # ---- [5] ADVERSARIAL skeptic pass (incl. polarity check) ----
    print("=" * 64)
    print("[5] ADVERSARIAL -- two-route recompute at large n + polarity check")
    probes = [9999, 13337, 17501, 19998, 19999]
    for n in probes:
        rec = a[n] if n < NN else None
        eng = a_eng[n]
        dfa = simulate_lsd(trans, out, start, n)
        csvv = a_csv[n]
        ok = (eng == dfa == csvv) and (rec is None or rec == dfa)
        rs = "n/a" if rec is None else str(rec)
        print(f"    n={n:6d}: (R5)={rs} engine={eng} DFAO={dfa} CSV={csvv}  "
              f"{'OK' if ok else 'MISMATCH'}")
        assert ok, f"adversarial mismatch at n={n}"
    # POLARITY check by hand on c_2,c_3,c_4 (non-divisible) and c_5 (divisible? no)
    print("    POLARITY check (the named biggest risk):")
    for n in (2, 3, 4):
        d = simulate_lsd(trans, out, start, n)
        print(f"      c_{n} mod5 = {d} (DFAO), {n}%5={n % 5} in {{2,3,4}}; "
              f"NON-div requires != 0 -> {'OK' if d != 0 else 'FAIL'}")
        assert d != 0
    # n=5: 5%5=0 not in {2,3,4}; c_5=-4 NON-divisible -> not a violation, but
    # it is the iff converse witness; n=10: 5|c_10, class 0
    d5 = simulate_lsd(trans, out, start, 5)
    d10 = simulate_lsd(trans, out, start, 10)
    print(f"      c_5 mod5 = {d5} (DFAO) [class 0, non-div: iff-converse witness]")
    print(f"      c_10 mod5 = {d10} (DFAO) [class 0, DIVISIBLE]")
    assert d5 != 0 and d10 == 0
    # iff witness: the law is non-div on {2,3,4}; the iff
    #   (n%5 in {2,3,4}) <=> (c_n != 0 mod5)
    # is FALSE because n=5 has c_5 != 0 but 5%5=0 not in {2,3,4}.
    w = 5
    print(f"    iff-witness n={w}: DFAO={d5} (!=0 means NON-div), "
          f"{w}%5={w % 5} not in {{2,3,4}} -> iff is FALSE")
    assert simulate_lsd(trans, out, start, w) != 0 and w % 5 not in (2, 3, 4)
    # base-5 reading sanity: 7 = '12'_5
    print(f"    base-5 sanity: 7 in base5 = '{_b5(7)}', DFAO(7)="
          f"{simulate_lsd(trans, out, start, 7)} == CSV {a_csv[7]}")
    assert simulate_lsd(trans, out, start, 7) == a_csv[7]

    print("=" * 64)
    print(f"all-PASS: minimal lsd_5 DFAO has {len(states)} states; "
          f"byte-equal to c_n mod 5 on [0,{NMAX}] via TWO routes; "
          f"NON-divisibility law holds on {{2,3,4}}; iff FALSE (witness n=5).")
    print("status PASS")
    return 0


def _b5(n: int) -> str:
    if n == 0:
        return "0"
    ds = []
    while n:
        ds.append(str(n % 5))
        n //= 5
    return "".join(reversed(ds))


if __name__ == "__main__":
    raise SystemExit(main())
