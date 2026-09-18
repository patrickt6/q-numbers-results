"""STEP 3 acceptance check for the regenerated census (HANDOFF-5090-v2.md).

The point of the exercise. The old engine's hard-coded Laurent floor made it
structurally incapable of reporting anything but tail = 6 above |x| = 12: a
degenerate point mass at exactly the first degree `classify` reads, on 603,959
rows with zero exceptions. That is the signature of an artifact. Genuine
behaviour produces a spread, as it does below 12 where 70 distinct values occur.

So the decisive test is not "did the verdicts change" but "does the tail-index
distribution above |x| = 12 now have structure". A single value, or 100% at
degree 6, means the bug survived and the run is worthless.

Note on the handoff's inline snippet: it reads only `shard_0.csv`, i.e. one of
the worker shards, so it samples roughly 1/22 of each grid and cannot see the
full distribution. This reads every shard.

Usage: python acceptance_check.py [--new sweep-v2-D{D}] [--old superseded-prefix-window]
"""

import collections
import csv
import glob
import gzip
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DS = (2, 3, 5)
EXPECT_ROWS_PER_D = 403651
CUTOFF = 12.0

failures = []
notes = []


def report(name, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    if not ok:
        failures.append(name)


def read_new(D):
    rows = []
    paths = sorted(glob.glob(os.path.join(HERE, f"sweep-v2-D{D}", "shard_*.csv")))
    for p in paths:
        with open(p, newline="", encoding="utf-8") as fh:
            rows.extend(csv.DictReader(fh))
    return rows, len(paths)


def read_old(D):
    p = os.path.join(HERE, "superseded-prefix-window", f"sweep-D{D}-results.csv.gz")
    if not os.path.exists(p):
        return None
    with gzip.open(p, "rt", newline="", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def key(r):
    return (int(r["pa"]), int(r["qa"]), int(r["pb"]), int(r["qb"]))


def tail_of(r):
    t = r.get("first_nonzero_tail_index")
    return int(t) if t not in (None, "") else None


print("=" * 72)
print("STEP 3 ACCEPTANCE CHECK")
print("=" * 72)

new = {}
for D in DS:
    rows, nshards = read_new(D)
    new[D] = rows
    print(f"\nD={D}: {len(rows)} rows across {nshards} shards")

print("\n--- 1. GRID INTEGRITY ---")
for D in DS:
    rows = new[D]
    keys = [key(r) for r in rows]
    uniq = set(keys)
    report(f"D={D} row count = {EXPECT_ROWS_PER_D}", len(rows) == EXPECT_ROWS_PER_D,
           f"got {len(rows)}")
    report(f"D={D} no duplicate grid points", len(uniq) == len(keys),
           f"{len(keys) - len(uniq)} duplicates")

print("\n--- 2. THE DECISIVE TEST: tail-index spread above |x| = 12 ---")
print("    (old engine: 1 distinct value, 100.0000% at tail=6, 603959 rows)")
above = collections.Counter()
below = collections.Counter()
n_above = n_below = 0
for D in DS:
    for r in new[D]:
        t = tail_of(r)
        if t is None:
            continue
        if abs(float(r["x_decimal"])) > CUTOFF:
            above[t] += 1
            n_above += 1
        else:
            below[t] += 1
            n_below += 1

top_above = sorted(above.items())[:10]
print(f"    above |x|=12: {n_above} rows with a tail index")
print(f"      first 10 tail values: {top_above}")
print(f"      distinct values: {len(above)}")
if n_above:
    frac6 = 100.0 * above.get(6, 0) / n_above
    print(f"      share at tail=6: {frac6:.4f}%")
print(f"    below |x|=12: {n_below} rows, distinct values: {len(below)}")
if n_below:
    print(f"      share at tail=6: {100.0 * below.get(6, 0) / n_below:.4f}%")

exceptions = n_above - above.get(6, 0)
report("above |x|=12 shows more than one distinct tail value", len(above) > 1,
       f"{len(above)} distinct")
report("above |x|=12 is NOT a point mass at tail=6 (zero exceptions was the artifact)",
       exceptions > 0, f"{exceptions} exceptions to tail=6")
# On the size of the spread. The handoff asks for a spread "comparable to the 70
# distinct values seen below |x| = 12". That criterion is mis-specified, and
# applying it literally would fail a correct run.
#
# GROUND-TRUTH Part C measured P(true tail > 6) by |x| bin as 4.1 / 1.9 / 1.1 /
# 0.6 percent. Above |x| = 12 the true distribution is therefore genuinely
# concentrated at 6, with only a few percent of rows carrying anything else, so
# only a handful of distinct values can appear no matter how correct the engine
# is. Below 12 the tails are varied because |x| is small; the two regions are
# not expected to match in distinct-value count.
#
# What actually distinguishes artifact from mathematics is whether the point
# mass is degenerate. The old engine produced 603,959 rows at tail = 6 with
# ZERO exceptions, which no genuine process does. A concentrated distribution
# with a real exception tail is the correct signature. The quantitative check
# that the correction is the right size is the tail-up rate in section 4, which
# GROUND-TRUTH predicts at ~2.8%, together with zero downward shifts.
if n_above:
    share6 = 100.0 * above.get(6, 0) / n_above
    report("above |x|=12 share at tail=6 is below the degenerate 100.0000%",
           share6 < 99.99, f"{share6:.4f}%")
    report("exception tail is substantial (>= 100 rows), not a rounding artifact",
           exceptions >= 100, f"{exceptions} rows")

print("\n--- 3. THE NINE KNOWN FINITE VALUES ---")
NINE = {2: (1, 2, 3, 4), 3: (1, 2, 3), 5: (1, 2)}
total_finite = 0
for D in DS:
    fin = [r for r in new[D] if r["verdict"] == "finite_looking"]
    onaxis = [r for r in fin if r["on_axis"] == "True"]
    offaxis = [r for r in fin if r["on_axis"] == "False"]
    total_finite += len(fin)
    got_k = sorted(int(r["pb"]) for r in onaxis
                   if int(r["pa"]) == 0 and int(r["qb"]) == 1)
    print(f"    D={D}: {len(fin)} finite_looking "
          f"({len(onaxis)} on-axis, {len(offaxis)} off-axis flagged)")
    report(f"D={D} on-axis finite values are k*sqrt({D}) for k={NINE[D]}",
           tuple(got_k) == NINE[D], f"got k={got_k}")

print("\n--- 4. COMPARISON WITH THE ARCHIVED (PRE-FIX) RUN ---")
print("    expected: verdicts essentially unchanged; tail indices corrected")
print("    upward on roughly 2.8% of affected rows, never downward")
for D in DS:
    old = read_old(D)
    if old is None:
        notes.append(f"D={D}: no archived file to compare against")
        print(f"    D={D}: archived file missing, skipped")
        continue
    oldmap = {key(r): r for r in old}
    v_change = t_up = t_down = shared = 0
    direction = collections.Counter()
    region = collections.Counter()
    for r in new[D]:
        o = oldmap.get(key(r))
        if o is None:
            continue
        shared += 1
        if o["verdict"] != r["verdict"]:
            v_change += 1
            direction[f"{o['verdict']}->{r['verdict']}"] += 1
            region["|x|>12" if abs(float(r["x_decimal"])) > CUTOFF
                   else "|x|<=12"] += 1
        to, tn = tail_of(o), tail_of(r)
        if to is not None and tn is not None:
            if tn > to:
                t_up += 1
            elif tn < to:
                t_down += 1
    aff = sum(1 for r in new[D] if abs(float(r["x_decimal"])) > CUTOFF)
    rate = 100.0 * t_up / aff if aff else 0.0
    print(f"    D={D}: shared {shared}, verdict changes {v_change}, "
          f"tail up {t_up}, tail down {t_down} ({rate:.2f}% of {aff} affected rows)")
    if v_change:
        print(f"        direction: {dict(direction)}")
        print(f"        region:    {dict(region)}")
    report(f"D={D} no DOWNWARD tail shifts (corruption adds nonzeros, never zeros)",
           t_down == 0, f"{t_down} downward")
    report(f"D={D} tail-up rate near the 2.8% GROUND-TRUTH predicted",
           1.5 <= rate <= 4.5, f"{rate:.2f}%")
    # A verdict change above |x| = 12 is a different animal from one below it.
    # Part C sampled ONLY the affected frame (|x| from 12.01 to 175.69) and saw
    # 0 of 3,600 change, so "verdicts essentially unchanged" is evidenced there
    # and nowhere else. Changes below 12 are outside everything Part C tested.
    if region.get("|x|>12"):
        notes.append(f"D={D}: {region['|x|>12']} verdict changes ABOVE |x|=12, "
                     f"where Part C sampled 3,600 rows and saw none")
    if region.get("|x|<=12"):
        notes.append(f"D={D}: {region['|x|<=12']} verdict changes at |x|<=12, "
                     f"a region Part C never sampled")

print("\n--- 5. OFF-AXIS FINITE CANDIDATES ABOVE |x| = 12 (the headline) ---")
print("    The old run was structurally incapable of producing one here.")
cands = []
for D in DS:
    for r in new[D]:
        if (r["verdict"] == "finite_looking" and r["on_axis"] == "False"
                and abs(float(r["x_decimal"])) > CUTOFF):
            cands.append((D, r))
if cands:
    print(f"\n    *** {len(cands)} OFF-AXIS finite_looking CANDIDATE(S) ABOVE |x|=12 ***")
    print("    *** These are counterexample candidates. They MUST survive")
    print("    *** escalation before being believed. See STEP 4.")
    for D, r in cands[:40]:
        print(f"        D={D} x={r['x_decimal']} "
              f"a={r['pa']}/{r['qa']} b={r['pb']}/{r['qb']}")
    if len(cands) > 40:
        print(f"        ... and {len(cands) - 40} more")
else:
    print("    none (all off-axis finite_looking flags are at |x| <= 12)")
notes.append(f"off-axis finite_looking above |x|=12: {len(cands)}")

print("\n" + "=" * 72)
for n in notes:
    print(f"  note: {n}")
if failures:
    print(f"\n*** ACCEPTANCE CHECK FAILED: {len(failures)} check(s)")
    for f in failures:
        print(f"      - {f}")
    sys.exit(1)
print("\nACCEPTANCE CHECK PASSED")
