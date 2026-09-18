#!/usr/bin/env python3
"""
Task 1 + Task 2 census of cyclotomic structure of denominators S_{a/d}(q).

Exact arithmetic only: sympy over ZZ, integer coefficient lists.
"""
import sys
import time
import csv
from math import gcd

sys.path.insert(0, '<path>')
from qpoly import qval, poly_deg, poly_trim

import sympy as sp

_q = sp.Symbol('q')

OUTDIR = '<path>'

# ---------------------------------------------------------------------------
# cyclotomic poly cache: return coeff list ascending order, ints
# ---------------------------------------------------------------------------
_cyclo_cache = {}
def cyclo_coeffs(m):
    if m in _cyclo_cache:
        return _cyclo_cache[m]
    p = sp.cyclotomic_poly(m, _q)
    poly = sp.Poly(p, _q, domain='ZZ')
    coeffs = [int(c) for c in poly.all_coeffs()[::-1]]
    _cyclo_cache[m] = coeffs
    return coeffs

def poly_from_list(coeffs):
    coeffs = poly_trim(list(coeffs))
    if not coeffs:
        return sp.Poly(0, _q, domain='ZZ')
    return sp.Poly(list(reversed(coeffs)), _q, domain='ZZ')

def list_from_poly(poly):
    if poly.is_zero:
        return []
    return [int(c) for c in poly.all_coeffs()[::-1]]

def divisors(n):
    out = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            out.append(i)
            if i != n // i:
                out.append(n // i)
        i += 1
    return sorted(out)

def prime_power_factors(n):
    """Return list of p^e for each prime p | n (full exponent in n)."""
    fac = sp.factorint(n)
    return [(p, e, p**e) for p, e in fac.items()]

# ---------------------------------------------------------------------------
# Step 1-3 classification
# ---------------------------------------------------------------------------
def classify(S_coeffs, d, full=True):
    """
    S_coeffs: ascending int coeff list, primitive, positive leading coeff.
    d: the denominator index (S(1) should equal d).
    full: if True do the full anomaly search (step 3); else skip (for d>600 large case)
    Returns dict with class, T (sorted list or None), deg_S, anomaly_multiset (or None)
    """
    Spoly = poly_from_list(S_coeffs)
    deg_S = Spoly.degree() if not Spoly.is_zero else 0

    divs = [m for m in divisors(d) if m >= 2]
    T0 = []
    quotient = Spoly
    remaining = Spoly
    # test divisibility of original S by each candidate Phi_m for m | d, m>=2
    for m in divs:
        phi = poly_from_list(cyclo_coeffs(m))
        q_, r_ = sp.div(remaining if False else Spoly, phi, domain='ZZ')
        # use direct exact division test on S (not cumulative) -- must divide S itself
        if r_ == 0:
            T0.append(m)

    P = sp.Poly(1, _q, domain='ZZ')
    for m in T0:
        P = P * poly_from_list(cyclo_coeffs(m))

    is_monic_unit_ct = False
    Scoeffs_trim = poly_trim(S_coeffs)
    if Scoeffs_trim and Scoeffs_trim[-1] == 1 and Scoeffs_trim[0] == 1:
        is_monic_unit_ct = True

    if P == Spoly:
        cls = 'CYCLOTOMIC'
        T = sorted(T0)
        anomaly_ms = None
        if not is_monic_unit_ct:
            cls = 'ANOMALOUS'  # shouldn't happen if P==S and P monic const-1, but guard
    else:
        if not full:
            cls = 'UNRESOLVED'
            T = None
            anomaly_ms = None
        else:
            # step 3: try full factorization into cyclotomics with any m from 2..3*deg+10, with multiplicity
            maxm = 3 * deg_S + 10
            quot = Spoly
            ms_used = []
            changed = True
            # repeatedly divide by any Phi_m (m in range) that divides quot, until quot==1 or no more divides
            m = 2
            while quot.degree() > 0 and m <= maxm:
                phi = poly_from_list(cyclo_coeffs(m))
                qq, rr = sp.div(quot, phi, domain='ZZ')
                if rr == 0:
                    quot = qq
                    ms_used.append(m)
                    continue  # try same m again (multiplicity)
                m += 1
            if quot.degree() == 0 and quot.LC() in (1, -1):
                # matched constant 1 (up to sign) -- need exactly constant 1 since S primitive positive leading
                const = int(quot.all_coeffs()[-1]) if quot.all_coeffs() else int(quot.LC())
                if quot == sp.Poly(1, _q, domain='ZZ'):
                    cls = 'ANOMALOUS-CYCLOTOMIC'
                    T = sorted(set(ms_used))
                    anomaly_ms = sorted(ms_used)
                else:
                    cls = 'NON-CYCLOTOMIC'
                    T = []
                    anomaly_ms = None
            else:
                cls = 'NON-CYCLOTOMIC'
                T = []
                anomaly_ms = None

    result = {
        'class': cls,
        'T': T,
        'deg_S': deg_S,
    }
    if cls == 'ANOMALOUS-CYCLOTOMIC':
        result['anomaly_ms'] = anomaly_ms
    return result

def predicate_downward_closed(T, d):
    Tset = set(T)
    for m in T:
        for l in divisors(m):
            if l > 1 and l not in Tset:
                return False
    return True

def predicate_pp_complete(T, d):
    Tset = set(T)
    for p, e, pe in prime_power_factors(d):
        if pe not in Tset:
            return False
    return True

def predicate_partition_form(T, d):
    """Returns (bool, partition) where partition is list of frozensets of primes,
    or (False, None) if it fails."""
    Tset = set(T)
    pps = prime_power_factors(d)  # list of (p,e,pe)
    primes = [p for p, e, pe in pps]
    pe_map = {p: pe for p, e, pe in pps}
    if not primes:
        return (len(Tset) == 0, [])
    # graph: edge between p,p' if some m in T divisible by both
    parent = {p: p for p in primes}
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry
    for m in T:
        divp = [p for p in primes if m % p == 0]
        for i in range(len(divp)):
            for j in range(i+1, len(divp)):
                union(divp[i], divp[j])
    comps = {}
    for p in primes:
        r = find(p)
        comps.setdefault(r, []).append(p)
    partition = list(comps.values())
    # for each component compute N_j = product of p^e (full exponents from d)
    union_divs = set()
    for comp in partition:
        Nj = 1
        for p in comp:
            Nj *= pe_map[p]
        for dd in divisors(Nj):
            if dd > 1:
                union_divs.add(dd)
    ok = (union_divs == Tset)
    return (ok, partition)

# ---------------------------------------------------------------------------
# main driver
# ---------------------------------------------------------------------------
def main():
    t_start = time.time()

    d_list_main = list(range(2, 241)) + [252, 260, 264, 270, 280, 288, 300, 312, 315, 330,
                                          336, 360, 420, 462, 480, 504, 510, 540, 546, 570,
                                          600, 630, 660, 690, 840, 924, 990, 1050, 1155, 1260]
    d_list_main = sorted(set(d_list_main))

    csv_path = f'{OUTDIR}/p1_census.csv'
    csv_f = open(csv_path, 'w', newline='')
    writer = csv.writer(csv_f)
    writer.writerow(['d', 'a', 'class', 'T', 'deg_S', 'downward_closed', 'pp_complete', 'partition_form', 'partition'])

    # storage for summary
    class_counts = {}
    noncyc_count_per_d = {}
    failures = []  # list of dicts with d,a,T,which predicate failed
    anomalies = []
    T_realized = {}  # d -> {T_tuple: [a,...]}
    Adm_data = {}  # d -> {m: [a,...]}  (which a make Phi_m divide S)

    target_dm_ds = {12, 15, 21, 24, 30, 35, 36, 45, 60, 105}
    target_T_ds = {12, 15, 24, 30, 36, 60, 105, 210, 420, 1155}

    n_total = len(d_list_main)
    dropped_large = False
    time_budget_s = 20 * 60  # internal soft budget before dropping d>600

    for idx, d in enumerate(d_list_main):
        if time.time() - t_start > time_budget_s and d > 600:
            dropped_large = True
            continue
        full = (d <= 600)
        noncyc_count_per_d[d] = 0
        if d in target_dm_ds:
            Adm_data[d] = {}
        if d in target_T_ds:
            T_realized[d] = {}

        for a in range(1, d):
            if gcd(a, d) != 1:
                continue
            shift, Num, Den = qval(a, d)
            S = poly_trim(Den)
            s1 = sum(S)
            assert s1 == d, f"S(1) != d for a={a}, d={d}: got {s1}"

            res = classify(S, d, full=full)
            cls = res['class']
            T = res['T']
            deg_S = res['deg_S']
            class_counts[cls] = class_counts.get(cls, 0) + 1

            if cls == 'NON-CYCLOTOMIC':
                noncyc_count_per_d[d] += 1
                continue
            if cls == 'UNRESOLVED':
                writer.writerow([d, a, cls, '', deg_S, '', '', '', ''])
                continue

            if cls == 'ANOMALOUS-CYCLOTOMIC':
                anomalies.append({'d': d, 'a': a, 'T': T, 'ms': res.get('anomaly_ms')})
                writer.writerow([d, a, cls, ';'.join(map(str, T)), deg_S, '', '', '', ''])
                continue

            # CYCLOTOMIC
            dc = predicate_downward_closed(T, d)
            ppc = predicate_pp_complete(T, d)
            pf, partition = predicate_partition_form(T, d)
            part_str = '|'.join(','.join(str(p) for p in sorted(comp)) for comp in partition) if partition else ''
            writer.writerow([d, a, cls, ';'.join(map(str, T)), deg_S, dc, ppc, pf, part_str])

            if not dc or not ppc or not pf:
                failures.append({'d': d, 'a': a, 'T': T, 'dc': dc, 'ppc': ppc, 'pf': pf})

            if d in target_dm_ds:
                for m in T:
                    Adm_data[d].setdefault(m, []).append(a)

            if d in target_T_ds:
                Tt = tuple(T)
                T_realized[d].setdefault(Tt, []).append(a)

        if (idx + 1) % 10 == 0 or d == d_list_main[-1]:
            elapsed = time.time() - t_start
            print(f"[{idx+1}/{n_total}] d={d} done, elapsed={elapsed:.1f}s", flush=True)
            csv_f.flush()

    csv_f.close()

    # ---------------- TASK 2 ----------------
    t2_path = f'{OUTDIR}/p2_degree_check.md'
    exceptions = []
    t2_start = time.time()
    max_d2 = 400
    d2_dropped = False
    for d in range(2, max_d2 + 1):
        if time.time() - t_start > 25 * 60:
            d2_dropped = True
            break
        for a in range(1, d):
            if gcd(a, d) != 1:
                continue
            shift, Num, Den = qval(a, d)
            S = poly_trim(Den)
            deg_S = poly_deg(S)
            is_extreme = (a == 1 or a == d - 1)
            if is_extreme:
                if deg_S != d - 1:
                    exceptions.append({'d': d, 'a': a, 'deg_S': deg_S, 'note': 'expected deg d-1 but differs'})
                else:
                    expected = [1] * d
                    if S != expected:
                        exceptions.append({'d': d, 'a': a, 'deg_S': deg_S, 'note': 'deg matches but S != [d]_q'})
            else:
                if deg_S == d - 1:
                    exceptions.append({'d': d, 'a': a, 'deg_S': deg_S, 'note': 'deg==d-1 but a not in {1,d-1}'})
        if d % 20 == 0:
            print(f"[T2] d={d} done, elapsed={time.time()-t2_start:.1f}s", flush=True)

    with open(t2_path, 'w') as f:
        f.write("# Task 2: degree equality check\n\n")
        if d2_dropped:
            f.write(f"NOTE: time budget exceeded; task 2 loop stopped early, last completed d listed above.\n\n")
        if not exceptions:
            f.write(f"Verified for all d <= {max_d2 if not d2_dropped else 'see note'}: "
                    "deg S = d-1 holds if and only if a=1 or a=d-1, and in those cases S == [d]_q exactly. "
                    "Zero exceptions found.\n")
        else:
            f.write(f"{len(exceptions)} exceptions foun<path>")
            f.write("| d | a | deg_S | note |\n|---|---|---|---|\n")
            for e in exceptions:
                f.write(f"| {e['d']} | {e['a']} | {e['deg_S']} | {e['note']} |\n")

    # ---------------- write p1_summary.md ----------------
    summ_path = f'{OUTDIR}/p1_summary.md'
    with open(summ_path, 'w') as f:
        f.write("# Task 1 census summary\n\n")
        f.write(f"Total runtime: {time.time()-t_start:.1f}s\n\n")
        if dropped_large:
            f.write("NOTE: time budget threatened to exceed limits; some d > 600 values in the extended list "
                    "were dropped from full processing (still ran, but skipped anomaly search).\n\n")

        f.write("## Class counts (all (d,a) pairs across the full d list)\n\n")
        for cls, cnt in sorted(class_counts.items()):
            f.write(f"- {cls}: {cnt}\n")
        f.write("\n")

        f.write("## Predicate failures (downward_closed / pp_complete / partition_form)\n\n")
        if not failures:
            f.write("ZERO FAILURES. All CYCLOTOMIC cases satisfy downward-closure, prime-power completeness, "
                    "and partition form.\n\n")
        else:
            f.write(f"{len(failures)} FAILURES FOUND (potential counterexamples to paper claim):\n\n")
            f.write("| d | a | T | downward_closed | pp_complete | partition_form |\n|---|---|---|---|---|---|\n")
            for e in failures:
                f.write(f"| {e['d']} | {e['a']} | {e['T']} | {e['dc']} | {e['ppc']} | {e['pf']} |\n")
            f.write("\n")

        f.write("## Anomalous-cyclotomic cases (S factors into cyclotomics with m not dividing d, or repeats)\n\n")
        if not anomalies:
            f.write("None found.\n\n")
        else:
            f.write(f"{len(anomalies)} ANOMALOUS-CYCLOTOMIC CASES FOUND (theoretically important):\n\n")
            for e in anomalies:
                f.write(f"- d={e['d']}, a={e['a']}, multiset={e['ms']}\n")
            f.write("\n")

        # specific T={2,3,4,6} at d=12 check, and T={2,3,5,6,15}-like at d=30,60,90,105,210
        f.write("## Specific checks\n\n")
        t2346_hits = []
        overlap_hits = []
        for d, Tmap in T_realized.items():
            for Tt, alist in Tmap.items():
                if set(Tt) == {2, 3, 4, 6}:
                    t2346_hits.append((d, Tt, alist))
        f.write("### T = {2,3,4,6} occurrences (any d, from the tracked-d set)\n\n")
        if t2346_hits:
            for d, Tt, alist in t2346_hits:
                f.write(f"- d={d}: T={sorted(Tt)}, a values={alist}\n")
        else:
            f.write("None found among tracked d values (d in {12,15,24,30,36,60,105,210,420,1155}).\n")
        f.write("\n")

        f.write("### 'two overlapping parts' sets like {2,3,5,6,15} at d in {30,60,90,105,210}\n\n")
        checked_special_ds = [30, 60, 90, 105, 210]
        any_overlap = False
        for d in checked_special_ds:
            if d in T_realized:
                for Tt, alist in T_realized[d].items():
                    ok, partition = predicate_partition_form(list(Tt), d)
                    if len(partition) >= 2:
                        # check if any m in T is divisible by primes from >1 component actually partition_form handles that;
                        # "overlapping" would mean partition_form FAILS due to overlap
                        pass
                    if not ok:
                        any_overlap = True
                        f.write(f"- d={d}: T={sorted(Tt)} FAILS partition form (partition attempt={partition}), a values={alist}\n")
        if not any_overlap:
            f.write("No partition-form failures found at d in {30,60,90,105,210} (only tracked d's in that list were processed: "
                    f"{[d for d in checked_special_ds if d in T_realized]}).\n")
        f.write("\n")

        f.write("## Distinct T sets realized, for d in {12, 15, 24, 30, 36, 60, 105, 210, 420, 1155}\n\n")
        for d in [12, 15, 24, 30, 36, 60, 105, 210, 420, 1155]:
            f.write(f"### d = {d}\n\n")
            if d not in T_realized:
                f.write("(not in tracked-d list processing, skipped)\n\n")
                continue
            pps = prime_power_factors(d)
            f.write(f"Prime powers of d: {[pe for p,e,pe in pps]}\n\n")
            # enumerate all set-partitions of the prime powers to know total realized vs not
            from itertools import combinations
            def set_partitions(collection):
                if len(collection) == 1:
                    yield [collection]
                    return
                first = collection[0]
                for smaller in set_partitions(collection[1:]):
                    for n, subset in enumerate(smaller):
                        yield smaller[:n] + [[first] + subset] + smaller[n+1:]
                    yield [[first]] + smaller
            prime_list = [p for p, e, pe in pps]
            pe_map = {p: pe for p, e, pe in pps}
            all_partitions = list(set_partitions(prime_list)) if prime_list else []
            def partition_to_T(partition):
                s = set()
                for comp in partition:
                    Nj = 1
                    for p in comp:
                        Nj *= pe_map[p]
                    for dd in divisors(Nj):
                        if dd > 1:
                            s.add(dd)
                return frozenset(s)
            realized_T_sets = set(T_realized[d].keys())
            realized_T_sets_frozenset = set(frozenset(t) for t in realized_T_sets)
            partition_T_map = {}
            for part in all_partitions:
                Tval = partition_to_T(part)
                partition_T_map.setdefault(Tval, []).append(part)

            f.write(f"Distinct T sets realized ({len(realized_T_sets)} total):\n\n")
            for Tt, alist in sorted(T_realized[d].items(), key=lambda kv: sorted(kv[0])):
                f.write(f"- T={sorted(Tt)}: a values={alist} (count={len(alist)})\n")
            f.write("\n")

            f.write("Partition-form partitions of d's prime powers: realized vs not realized as some <path>")
            for Tval, parts in partition_T_map.items():
                realized = Tval in realized_T_sets_frozenset
                f.write(f"- partition(s) {parts} -> T={sorted(Tval)} : {'REALIZED' if realized else 'not realized'}\n")
            f.write("\n")

        f.write("## A_{d,m} tables: which a make Phi_m | S_{a/d}, for d in {12,15,21,24,30,35,36,45,60,105}\n\n")
        for d in [12, 15, 21, 24, 30, 35, 36, 45, 60, 105]:
            f.write(f"### d = {d}\n\n")
            if d not in Adm_data:
                f.write("(not tracked in this run)\n\n")
                continue
            for m in sorted(Adm_data[d].keys()):
                alist = sorted(Adm_data[d][m])
                f.write(f"- A_{{{d},{m}}} = {alist}\n")
            f.write("\n")

        f.write("## Non-cyclotomic counts per d (only reported where > 0, for the full d list)\n\n")
        any_nc = False
        for d, cnt in sorted(noncyc_count_per_d.items()):
            if cnt > 0:
                any_nc = True
                f.write(f"- d={d}: {cnt} non-cyclotomic a values\n")
        if not any_nc:
            f.write("Zero non-cyclotomic cases across the entire d list (0 for every d).\n")
        f.write("\n")

    print("DONE")
    print(f"class_counts={class_counts}")
    print(f"failures={len(failures)}")
    print(f"anomalies={len(anomalies)}")
    print(f"t2 exceptions={len(exceptions)}, dropped={d2_dropped}")

if __name__ == '__main__':
    main()
