"""Independent verifier for the c_n([sqrt2]_q) mod 2 automaton.

This script does NOT import the construction.  It parses the Walnut word
automaton file C2.txt, simulates it on the base-2 digits of every n, and
checks the predictions against the canonical Morier-Genoud-Ovsienko
coefficient file <path> reduced mod 2.

It then reproduces the modular-atlas anchor for (sqrt2, p=2, d=3):
  - forward direction  n = 1 (mod 3)  ==>  c_n even, on all 6667 indices,
    independently on the first half [0,10000) and second half [10000,20000);
  - the converse fails, with the smallest counterexample exhibited.

Run:  python verify_against_atlas.py
Exit code 0 and "status PASS" iff every check passes.
"""
from __future__ import annotations

import csv
import os
import sys

sys.set_int_max_str_digits(2_000_000)

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
CSV_PATH = os.path.join(REPO, "computations", "data", "qreal_sqrt2_20000.csv")
AUT_PATH = os.path.join(HERE, "C2.txt")


def parse_walnut_word_automaton(path: str):
    """Parse a Walnut ?msd_2 / ?lsd_2 word automaton.

    Returns (numeration, start, out, trans) where out[s] is the output of
    state s and trans[(s,d)] the d-successor.  Start state is 0 by Walnut
    convention (the first declared state).
    """
    with open(path) as f:
        raw = [ln.strip() for ln in f]
    lines = [ln for ln in raw if ln != ""]
    numeration = lines[0]
    out: dict[int, int] = {}
    trans: dict[tuple, int] = {}
    i = 1
    cur = None
    while i < len(lines):
        ln = lines[i]
        if "->" in ln:
            left, right = ln.split("->")
            d = int(left.strip())
            dest = int(right.strip())
            trans[(cur, d)] = dest
            i += 1
        else:
            parts = ln.split()
            cur = int(parts[0])
            out[cur] = int(parts[1])
            i += 1
    start = 0
    return numeration, start, out, trans


def simulate_msd(start, out, trans, n: int) -> int:
    if n == 0:
        digits = [0]
    else:
        digits = [int(b) for b in bin(n)[2:]]
    s = start
    for d in digits:
        s = trans[(s, d)]
    return out[s]


def load_coeffs_mod2(path: str, N: int) -> list[int]:
    a = [None] * N
    with open(path) as f:
        r = csv.reader(f)
        header = next(r)
        assert header == ["n", "coefficient"], f"unexpected header {header}"
        for row in r:
            n = int(row[0])
            if n < N:
                s = row[1].lstrip("-")
                a[n] = int(s[-1]) % 2  # parity from last decimal digit
    assert all(x is not None for x in a), "missing coefficients"
    return a


def main() -> int:
    N = 20000
    print(f"reading automaton:   {AUT_PATH}")
    numeration, start, out, trans = parse_walnut_word_automaton(AUT_PATH)
    print(f"  numeration={numeration}  states={len(out)}  start={start}")
    assert numeration == "msd_2", "verifier expects the msd_2 automaton"

    print(f"reading coefficients: {CSV_PATH}")
    a = load_coeffs_mod2(CSV_PATH, N)

    print("[check 1] automaton output == c_n mod 2, byte-equal on [0,N)")
    mism = [n for n in range(N) if simulate_msd(start, out, trans, n) != a[n]]
    if mism:
        print(f"  FAIL: {len(mism)} mismatches, first 10: {mism[:10]}")
        return 1
    print(f"  PASS: {N} indices agree (automaton is byte-equal to MGO data)")

    print("[check 2] atlas anchor (sqrt2, p=2, d=3): forward direction")
    cls1 = [n for n in range(N) if n % 3 == 1]
    h1 = [n for n in cls1 if n < N // 2]
    h2 = [n for n in cls1 if n >= N // 2]
    odd_first = [n for n in h1 if a[n] == 1]
    odd_second = [n for n in h2 if a[n] == 1]
    print(f"  class 1 mod 3: {len(cls1)} indices "
          f"(first half {len(h1)}, second half {len(h2)})")
    print(f"  odd coefficients in class 1: first half {len(odd_first)}, "
          f"second half {len(odd_second)}")
    if odd_first or odd_second:
        print("  FAIL: forward direction violated")
        return 1
    both_halves_agree = (len(odd_first) == 0 and len(odd_second) == 0)
    print(f"  PASS: all {len(cls1)} indices in class 1 are even; "
          f"both halves agree = {both_halves_agree}")
    assert len(cls1) == 6667, f"expected 6667 indices, got {len(cls1)}"

    print("[check 3] converse fails (this is a forward-only law, not iff)")
    ce = [n for n in range(N) if (a[n] == 0) != (n % 3 == 1)]
    print(f"  biconditional 'even iff n=1 mod 3' counterexamples: {len(ce)}")
    print(f"  smallest counterexample: n={ce[0]} "
          f"(n mod 3 = {ce[0] % 3}, c_n is even)")

    # tally evens per class for the record
    from collections import Counter
    ev = Counter(); tot = Counter()
    for n in range(N):
        tot[n % 3] += 1
        if a[n] == 0:
            ev[n % 3] += 1
    print("  parity by class mod 3 (even/total): "
          + ", ".join(f"{c}:{ev[c]}/{tot[c]}" for c in (0, 1, 2)))

    print("\nstatus PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
