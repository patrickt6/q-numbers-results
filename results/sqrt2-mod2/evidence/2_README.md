# modular-walnut-laws

## Summary

Two coefficient-divisibility laws for the q-series coefficients c_n of quadratic-irrational q-reals, each proved by the automatic-sequence theorem prover Walnut acting on an explicit minimal deterministic finite-state automaton with output (DFAO). Law 1 (sqrt(2) mod 7): for all n, if n mod 7 is in {2, 4} then 7 divides c_n([sqrt(2)]_q); this is forward-only, the converse is false (witness n = 21). Law 2 (phi mod 5): for all n, if n mod 5 is in {2, 3, 4} then 5 does NOT divide c_n([phi]_q); also forward-only, converse false (witness n = 5).

## What was computed

For each q-real, the coefficient sequence (c_n mod p) is a p-automatic word (Christol's theorem applied to the algebraic series y = sum c_n q^n satisfying the Morier-Genoud-Ovsienko equation reduced mod p). The two computations are:

1. sqrt(2) mod 7. The minimal equation is q^2 y^2 + (1 - q^3) y - (1 + q^2) = 0 over F_7(q). This yields the closed mod-7 recurrence c_k = [k=0] + [k=2] + c_{k-3} - b_{k-2}, where b_j = sum_i c_i c_{j-i} is the self-convolution, so the residue stream is produced with no external data. A 7-kernel (Myhill-Nerode) construction with Moore minimization produces a minimal base-7 DFAO of 10 states reading n least-significant-digit first.

2. phi mod 5. The minimal equation is q y^2 + (1 - q - q^2) y - 1 = 0 over F_5(q), giving c_k = [k=0] + c_{k-1} + c_{k-2} - b_{k-1} over F_5. The 5-kernel construction with Moore minimization produces a minimal base-5 DFAO of 9 states reading n least-significant-digit first.

The method: build the DFAO purely from the algebraic recurrence, certify it byte-equal to reference coefficient data on [0, 19999], then state each divisibility law as a first-order predicate over the natural numbers in Walnut and let Walnut decide it for ALL n by deciding emptiness of the corresponding automaton. A "true" verdict from Walnut is a proof of the all-n statement (conditional on the DFAO equalling the true coefficient sequence). The converse direction is checked the same way and returns "false", with an explicit small-n witness.

## Files

DFAO state files (top level):

- S7.txt: the minimal base-7 DFAO for c_n([sqrt(2)]_q) mod 7, in Walnut Word-Automata format (numeration lsd_7, 10 states, each line "state output" followed by "digit -> next-state").
- S7_states.json: the same DFAO as a JSON transition graph, with the alphabet, output alphabet, semantics, source equation, recurrence, state list (id, output, delta), and the byte-equality horizon (19999).
- P5.txt: the minimal base-5 DFAO for c_n([phi]_q) mod 5 (numeration lsd_5, 9 states), Walnut format.
- P5_states.json: the same DFAO as a JSON transition graph, with the absorbing non-divisibility law field included.

Walnut command files (top level):

- walnut_commands.txt: the four Walnut "eval" predicates for the sqrt(2) mod 7 law (smoke test, forward implication, converse, iff).
- phi_walnut_commands.txt: the two Walnut "eval" predicates for the phi mod 5 non-divisibility law (forward implication, iff).

Walnut result files (top level), each holding the boolean verdict Walnut returned:

- Result-sqrt2_mod7_fwd.txt: "true". The forward law holds for all n: n mod 7 in {2,4} implies 7 | c_n.
- Result-sqrt2_mod7_conv.txt: "false". The converse fails: some n with 7 | c_n is not in classes {2,4} (e.g. n = 21).
- Result-sqrt2_mod7_iff.txt: "false". The biconditional fails (the forward law is one-directional).
- phi_mod5_fwd.txt: "true". The forward law holds for all n: n mod 5 in {2,3,4} implies 5 does not divide c_n.
- phi_mod5_iff.txt: "false". The biconditional fails (forward-only; witness n = 5).

Builder scripts (code/):

- code/build_sqrt2_mod7_dfao.py: derives the mod-7 recurrence, generates the residue stream, builds and Moore-minimizes the base-7 DFAO, verifies byte-equality against a reference coefficient CSV on [0, 19999], emits S7.txt and S7_states.json, and runs adversarial recompute and witness checks. Set the REFERENCE_CSV environment variable to point at a coefficient CSV (columns n, coefficient) before running.
- code/build_phi_mod5_dfao.py: the mod-5 analog for phi, with a two-route byte-equality check (algebraic recurrence plus reference CSV) and an optional third route via an external big-integer recurrence engine (enabled by setting FAST_COMPUTE). Emits P5.txt and P5_states.json.

## The finding

Both laws are forward-only divisibility statements, decided for every n by Walnut on a small minimal automaton:

- sqrt(2) mod 7 (10-state DFAO): n mod 7 in {2,4} forces 7 | c_n; the converse is false, the smallest witness being n = 21 (which is 0 mod 7 yet has 7 | c_21).
- phi mod 5 (9-state DFAO): n mod 5 in {2,3,4} forces 5 not dividing c_n (an absorbing non-divisibility law); the converse is false, the smallest witness being n = 5 (which is 0 mod 5 yet has c_5 not divisible by 5).

Each all-n law is rigorous CONDITIONAL on identifying the DFAO with the true coefficient sequence. That identification rests on three pillars: byte-equality of the DFAO output to reference coefficient data on the full window [0, 19999]; Christol's theorem guaranteeing the mod-p coefficient sequence is p-automatic so a finite DFAO exists; and Myhill-Nerode minimality guaranteeing the minimal DFAO is unique, so an automaton matching the data on a sufficiently long window is the correct one.

## References

- Walnut: a theorem prover for automatic sequences (decides first-order statements about automatic words), https://cs.uwaterloo.ca/~shallit/walnut.html
- Christol's theorem: a power series over a finite field is algebraic if and only if its coefficient sequence is automatic. G. Christol, Ensembles presque periodiques k-reconnaissables, Theoretical Computer Science 9 (1979).
- Source algebraic equations for the q-reals: Morier-Genoud and Ovsienko, q-deformed rationals and q-continued fractions, arXiv:1908.04365.
