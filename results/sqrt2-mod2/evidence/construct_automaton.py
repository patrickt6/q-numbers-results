"""Construct the minimal 2-automaton (DFAO) for c_n([sqrt(2)]_q) mod 2.

This is the Christol-Furstenberg automaton: by Christol's theorem the
reduction modulo 2 of any series algebraic over F_2(q) is 2-automatic,
so there is a finite deterministic automaton-with-output (DFAO) reading
the base-2 digits of n and emitting c_n mod 2.

The construction is INDEPENDENT of any coefficient CSV.  It is driven by
the modulo-2 recurrence derived symbolically from the Morier-Genoud
-Ovsienko algebraic equation (Prop. 4.5 of arXiv:1908.04365), reduced
mod 2:

      q^2 y^2 + (1 + q^3) y + (1 + q^2) = 0      over  F_2(q),     (*)

      y = sum_{n>=0} c_n q^n,   c_n in F_2.

Extracting the coefficient of q^k in (*) and using the characteristic-2
Frobenius identity  y(q)^2 = y(q^2)  (so [q^k] q^2 y^2 = c_{(k-2)/2}
when k is even and >= 2) gives the closed mod-2 recurrence

      c_k = [k=0] + [k=2]
            + c_{k-3}          (when k >= 3)
            + c_{(k-2)/2}      (when k is even and k >= 2)         (R)

all sums taken in F_2.  (R) determines the whole sequence from c_0 = 1
because k-3 < k and (k-2)/2 < k.

The DFAO is then built by the Myhill-Nerode / 2-kernel construction:
the MSD-first state reached after reading a prefix of value p is the
equivalence class of p under

      p ~ p'  iff  a(p*2^L + e) = a(p'*2^L + e) for all L >= 0, e<2^L,

with start state p=0, transition  p --d-->  2p+d, and output a(p).
Christol's theorem guarantees the number of classes is finite.

Outputs (all written next to this script):
  - C2.txt          Walnut word-automaton (?msd_2), output = c_n mod 2
  - C2_lsd.txt      the same automaton in ?lsd_2 (digit-reversed twin)
  - states.json     full state graph: states, outputs, transitions
  - transitions.dot Graphviz rendering of the state graph

Run:  python construct_automaton.py
"""
from __future__ import annotations

import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))

# --- (R): the algebra-derived mod-2 recurrence -----------------------------

def gen_mod2(NN: int) -> list[int]:
    """Generate (c_n mod 2) for n in [0, NN) from recurrence (R).

    Purely arithmetic, no CSV.  O(NN) time and space.
    """
    a = [0] * NN
    for k in range(NN):
        v = 0
        if k == 0:
            v ^= 1
        if k == 2:
            v ^= 1
        if k >= 3:
            v ^= a[k - 3]
        if k >= 2 and (k % 2 == 0):
            v ^= a[(k - 2) // 2]
        a[k] = v
    return a


# --- Myhill-Nerode MSD-first DFAO construction -----------------------------

def build_dfao(a: list[int], probe_levels: int = 9):
    """Build the minimal MSD-first DFAO computing a(n).

    State of prefix-value p is identified by its signature: the tuple of
    a(p*2^L + e) for L in [0, probe_levels], e in [0, 2^L).  Two prefixes
    with equal signatures are the same state.  Transition p --d--> 2p+d,
    start p=0, output(p)=a(p).

    Returns (states, trans, out, start) where states maps a canonical
    representative prefix value to a small integer state id.
    """
    NN = len(a)
    span = 1 << probe_levels  # largest 2^L used in a signature

    def signature(p: int):
        sig = []
        base = p
        L = 0
        mult = 1
        while L <= probe_levels:
            for e in range(mult):
                idx = base * mult + e
                if idx >= NN:
                    raise IndexError(
                        f"probe out of range: need a[{idx}] but NN={NN}; "
                        f"raise NN or lower probe_levels"
                    )
                sig.append(a[idx])
            L += 1
            mult <<= 1
        return tuple(sig)

    # BFS over prefix values, merging equal signatures into states.
    sig_to_state: dict[tuple, int] = {}
    state_repr: dict[int, int] = {}      # state id -> representative prefix p
    out: dict[int, int] = {}
    trans: dict[tuple, int] = {}         # (state, digit) -> state

    # only explore prefixes p whose full signature fits inside [0, NN)
    def explorable(p: int) -> bool:
        return p * span + (span - 1) < NN

    assert explorable(0), "NN too small for probe_levels"
    start_sig = signature(0)
    sig_to_state[start_sig] = 0
    state_repr[0] = 0
    out[0] = a[0]
    queue = [0]
    next_id = 1
    while queue:
        s = queue.pop(0)
        p = state_repr[s]
        for d in (0, 1):
            pc = 2 * p + d
            if not explorable(pc):
                # fall back to a deeper representative search: find any
                # already-known prefix with the same signature at a lower
                # probe depth.  In practice the kernel closes before this
                # branch is needed (verified by simulate() below).
                # Use a reduced-depth signature for matching.
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


def hopcroft_minimize(states, trans, out, start):
    """Moore-style minimization of a complete DFAO on alphabet {0,1}."""
    # initial partition by output
    block_of = {}
    for s in states:
        block_of[s] = out[s]
    changed = True
    while changed:
        changed = False
        # refine: signature = (current block, block of 0-succ, block of 1-succ)
        sig = {}
        for s in states:
            sig[s] = (block_of[s], block_of[trans[(s, 0)]], block_of[trans[(s, 1)]])
        # relabel signatures to dense ids
        uniq = {}
        newlabel = {}
        nid = 0
        for s in states:
            if sig[s] not in uniq:
                uniq[sig[s]] = nid
                nid += 1
            newlabel[s] = uniq[sig[s]]
        if nid != len(set(block_of.values())):
            changed = True
        if any(newlabel[s] != block_of[s] for s in states):
            # only count as changed if the partition actually got finer
            if len({newlabel[s] for s in states}) != len({block_of[s] for s in states}):
                changed = True
        block_of = newlabel
    # build minimized machine; map old start's block to new id 0
    rep = {}
    for s in states:
        rep.setdefault(block_of[s], s)
    blocks = sorted(rep.keys())
    # renumber so the start's block is 0
    start_block = block_of[start]
    order = [start_block] + [b for b in blocks if b != start_block]
    remap = {b: i for i, b in enumerate(order)}
    mstates = list(range(len(order)))
    mout = {remap[b]: out[rep[b]] for b in order}
    mtrans = {}
    for b in order:
        s = rep[b]
        for d in (0, 1):
            mtrans[(remap[b], d)] = remap[block_of[trans[(s, d)]]]
    return mstates, mtrans, mout, 0


def simulate(states, trans, out, start, n: int) -> int:
    """Run the MSD-first DFAO on the base-2 digits of n."""
    if n == 0:
        digits = [0]
    else:
        digits = [int(b) for b in bin(n)[2:]]
    s = start
    for d in digits:
        s = trans[(s, d)]
    return out[s]


# --- Walnut emitters --------------------------------------------------------

def emit_walnut_msd(states, trans, out, start) -> str:
    """Emit a Walnut ?msd_2 word automaton.  Start must be state 0."""
    assert start == 0
    lines = ["msd_2", ""]
    for s in states:
        lines.append(f"{s} {out[s]}")
        lines.append(f"0 -> {trans[(s, 0)]}")
        lines.append(f"1 -> {trans[(s, 1)]}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def emit_walnut_lsd_from_msd(a: list[int], probe_levels: int = 9) -> str:
    """Build the LSD-first twin directly from the kernel (Lambda_d ops).

    LSD construction is the textbook clean one: state = a kernel sequence
    s, transition s --d--> Lambda_d(s) where Lambda_d(s)(m) = s(2m+d),
    output s(0).  After reading d_1 d_2 ... d_j LSD-first the output is
    a(d_1 + 2 d_2 + ... + 2^{j-1} d_j).
    """
    NN = len(a)
    span = 1 << probe_levels

    # a kernel state is identified by (k, r): the sequence m -> a(2^k m + r)
    def sig(k, r):
        mult = 1 << k
        s = []
        for m in range(span):
            idx = mult * m + r
            if idx >= NN:
                raise IndexError("LSD probe out of range; raise NN")
            s.append(a[idx])
        return tuple(s)

    sig_to_id = {}
    rep = {}
    out = {}
    trans = {}
    sig_to_id[sig(0, 0)] = 0
    rep[0] = (0, 0)
    out[0] = a[0]
    queue = [0]
    nid = 1
    while queue:
        s = queue.pop(0)
        k, r = rep[s]
        for d in (0, 1):
            kc, rc = k + 1, r + d * (1 << k)
            if (1 << kc) * (span - 1) + rc >= NN:
                raise IndexError("LSD child probe out of range; raise NN")
            cs = sig(kc, rc)
            if cs in sig_to_id:
                trans[(s, d)] = sig_to_id[cs]
            else:
                sig_to_id[cs] = nid
                rep[nid] = (kc, rc)
                out[nid] = a[rc]  # a(2^kc * 0 + rc) = a(rc)
                trans[(s, d)] = nid
                queue.append(nid)
                nid += 1
    states = sorted(rep.keys())
    states, trans, out, start = hopcroft_minimize(states, trans, out, 0)
    lines = ["lsd_2", ""]
    for s in states:
        lines.append(f"{s} {out[s]}")
        lines.append(f"0 -> {trans[(s, 0)]}")
        lines.append(f"1 -> {trans[(s, 1)]}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n", states, trans, out


def emit_dot(states, trans, out, start) -> str:
    lines = ["digraph C2 {", '  rankdir=LR;', '  node [shape=circle];']
    lines.append(f'  start [shape=point];')
    lines.append(f'  start -> {start};')
    for s in states:
        shape = "doublecircle" if out[s] == 1 else "circle"
        lines.append(f'  {s} [label="{s}/{out[s]}", shape={shape}];')
    for s in states:
        lines.append(f'  {s} -> {trans[(s,0)]} [label="0"];')
        lines.append(f'  {s} -> {trans[(s,1)]} [label="1"];')
    lines.append("}")
    return "\n".join(lines) + "\n"


def main():
    NN = 1_000_000
    PROBE = 9
    print(f"[1] generating c_n mod 2 from recurrence (R) for n in [0,{NN})")
    a = gen_mod2(NN)

    print("[2] building minimal MSD-first DFAO (Myhill-Nerode kernel)")
    states, trans, out, start = build_dfao(a, probe_levels=PROBE)
    print(f"    raw states: {len(states)}")
    states, trans, out, start = hopcroft_minimize(states, trans, out, start)
    print(f"    minimized states: {len(states)}")

    print("[3] verifying DFAO reproduces a(n) for all n in [0,NN) ...")
    bad = 0
    for n in range(NN):
        if simulate(states, trans, out, start, n) != a[n]:
            bad += 1
            if bad <= 5:
                print(f"    MISMATCH at n={n}")
    if bad:
        raise SystemExit(f"DFAO simulation FAILED on {bad} indices")
    print(f"    OK: simulation matches recurrence on all {NN} indices")

    print("[4] checking kernel closure (each state's children are states)")
    for s in states:
        for d in (0, 1):
            assert trans[(s, d)] in states
    print("    OK: state set is closed under both digit transitions")

    # leading-zero invariance: delta(start,0) == start
    assert trans[(start, 0)] == start, "leading zeros not absorbed!"
    print("    OK: delta(start,0)=start (leading-zero invariant)")

    print("[5] emitting artifacts")
    msd = emit_walnut_msd(states, trans, out, start)
    with open(os.path.join(HERE, "C2.txt"), "w") as f:
        f.write(msd)
    lsd_txt, lst, ltr, lout = emit_walnut_lsd_from_msd(a, probe_levels=PROBE)
    with open(os.path.join(HERE, "C2_lsd.txt"), "w") as f:
        f.write(lsd_txt)
    # cross-check lsd twin reproduces a(n) by reversed-digit reading
    def sim_lsd(n):
        if n == 0:
            digs = [0]
        else:
            digs = [int(b) for b in bin(n)[2:][::-1]]  # lsd first
        s = 0
        for d in digs:
            s = ltr[(s, d)]
        return lout[s]
    lbad = sum(1 for n in range(NN) if sim_lsd(n) != a[n])
    if lbad:
        raise SystemExit(f"LSD twin FAILED on {lbad} indices")
    print(f"    LSD twin states: {len(lst)}, simulation OK on all {NN} indices")

    graph = {
        "numeration": "msd_2",
        "alphabet": [0, 1],
        "output_alphabet": [0, 1],
        "semantics": "output at state reached after reading base-2 digits of n (MSD first) equals c_n([sqrt2]_q) mod 2",
        "source_equation": "q^2 y^2 + (1+q^3) y + (1+q^2) = 0 over F_2(q)  (MGO Prop 4.5 mod 2)",
        "recurrence": "c_k = [k=0]+[k=2]+c_{k-3}(k>=3)+c_{(k-2)/2}(k even>=2)  in F_2",
        "n_states": len(states),
        "start": start,
        "states": [
            {"id": s, "output": out[s],
             "delta0": trans[(s, 0)], "delta1": trans[(s, 1)]}
            for s in states
        ],
        "verified_indices": NN,
        "lsd_twin_states": len(lst),
    }
    with open(os.path.join(HERE, "states.json"), "w") as f:
        json.dump(graph, f, indent=2)
    with open(os.path.join(HERE, "transitions.dot"), "w") as f:
        f.write(emit_dot(states, trans, out, start))
    print("    wrote C2.txt, C2_lsd.txt, states.json, transitions.dot")
    print(f"\nDONE. minimal MSD DFAO has {len(states)} states.")
    # print the transition table for the record
    print("\nstate | out | --0--> | --1-->")
    for s in states:
        print(f"  {s:3d} |  {out[s]}  |  {trans[(s,0)]:3d}  |  {trans[(s,1)]:3d}")


if __name__ == "__main__":
    main()
