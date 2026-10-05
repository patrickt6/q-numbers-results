# All results

35 results, generated from `results.json` (2026-09-18). Click a result for its statement, Lean status and evidence files.

![Proved: 14](https://img.shields.io/badge/Proved-14-1f7a4d) ![Verified by computation: 7](https://img.shields.io/badge/Verified%20by%20computation-7-2f5bd3) ![Found false: 9](https://img.shields.io/badge/Found%20false-9-c2410c) ![Already published: 3](https://img.shields.io/badge/Already%20published-3-7c3aed) ![Open: 2](https://img.shields.io/badge/Open-2-6b7280)

One row per result. Status is not editorial. A result that turned out false stays in the table with status 'disproved', because the record of what failed is the point.

## Proved (14)

Proved on paper, and in some cases machine-checked in Lean.

| Result | Logged | In short |
|---|---|---|
| [addition-nogo](results/addition-nogo/) | 2026-06 | Proved [x+y]_q is not bihomographic in [x]_q and [y]_q over Q(q): the 8-wide relation matrix has full rank 8. |
| [mult-nogo](results/mult-nogo/) | 2026-06 | Proved [xy]_q is likewise not bihomographic, with the q-reversal obstruction absent this time. |
| [sqrt2-mod2](results/sqrt2-mod2/) | 2026-06 | Proved a q-real modular law end to end with Christol's theorem plus the Walnut automatic prover: n = 1 mod 3 implies c_n is even. |
| [twin-primes](results/twin-primes/) | 2026-06-17 | Proved the reduced q-denominator of m/(m^2-1) collapses to two cyclotomic factors exactly when m-1 and m+1 are twin primes. |
| [pell-negation](results/pell-negation/) | 2026-07 | Proved [sqrt d]_q + [-sqrt d]_q = (A-D)/C from the fundamental Pell automorph, turning an infinite search into one divisibility check. |
| [t5-scalar](results/t5-scalar/) | 2026-07 | Settled the scalar congruence conjecture with the exact identity q(A-D) = (q-1)(qB+C). |
| [lemma-l](results/lemma-l/) | 2026-07 | Proved Lemma L at odd prime powers from downward closure alone, by a p-adic argument. |
| [intertwining](results/intertwining/) | 2026-07 | Proved NMN = M^-1 holds for the strictly wider family x = b0 sqrt(D), b0 rational, not just the pure square roots the manuscript assumed. |
| [degree-equality](results/degree-equality/) | 2026-07-11 | Proved the degree-equality clause by a continuant tightness induction. |
| [gap-a](results/gap-a/) | 2026-07-24 | Closed the open half of a 2020 quadratic-irrationals theorem (Example 6.4); the closing argument and its mismatch-ratio consequence are new. |
| [dc-theorem-a](results/dc-theorem-a/) | 2026-08 | Proved downward closure: Phi_{p^a l} dividing S forces Phi_l to divide S, for l in {2,3,4,5}, at every word length. |
| [length5](results/length5/) | 2026-08 | Proved every word in the length-5 list vanishes for all k: five parametrised shapes plus ten identically zero words. |
| [count-law](results/count-law/) | 2026-08-12 | Proved the vanishing locus is the torsion of a fixed hypersurface in a torus (Theorem A), via Laurent's theorem. |
| [lemma-n](results/lemma-n/) | 2026-08-12 | Proved negation closure (Lemma N) at all lengths, not only the lengths checked by hand. |

## Verified by computation (7)

Established by exact computation over a stated search range. Not a proof.

| Result | Logged | In short |
|---|---|---|
| [cubic-negation](results/cubic-negation/) | 2026-06 | Checked a panel of cubic irrationals: none gives a finite negation sum or product, exact to N = 320. Not proved for all cubics. |
| [q-somos](results/q-somos/) | 2026-06 | Checked all 49 integer pairs for the q-twisted Somos-4 recurrence stay Laurent through x_4 to x_11; 48 of 49 are non-trivial reparametrisations. |
| [orbit-closure](results/orbit-closure/) | 2026-06 | Recovered the Ovsienko-Ustinov degree-3 functional equation from the heptagon and nonagon cyclic cubics, residual zero to q^4950. |
| [negation-census](results/negation-census/) | 2026-06-11 | Swept 668,745 canonical quadratic irrationals; the negation sum is finite for exactly two, sqrt(2) and sqrt(3). |
| [realizability](results/realizability/) | 2026-07 | The realizability index-set law matches 166 of 166 census cases exactly; recorded as unproved, since the proof is still open. |
| [length5-complete](results/length5-complete/) | 2026-08 | Verified the length-5 list is complete (no other word vanishes) for 4 <= k <= 24; not proved for all k. |
| [k-uniformity](results/k-uniformity/) | 2026-08 | Confirmed k-independence of the vanishing-locus congruence conditions for k = 2 through 13. |

## Found false (9)

A claim that was believed, tested, and found false. Includes my own.

| Result | Logged | In short |
|---|---|---|
| [sqrt2-mod2-biconditional](results/sqrt2-mod2-biconditional/) | 2026-06 | Disproved the biconditional version of the same law: 4,446 counterexamples in range. |
| [trace-zero](results/trace-zero/) | 2026-06-04 | Disproved my own trace-zero finiteness criterion; counterexamples sqrt(19), sqrt(43), sqrt(46), sqrt(53). |
| [census-window](results/census-window/) | 2026-07 | Traced a 100.0000 percent, zero-exception census result to a window-floor bug; corrected figure is 97.36 percent with 15,929 exceptions. |
| [r1-float-dedup](results/r1-float-dedup/) | 2026-07 | Traced a misdiagnosed pilot disagreement to a floating-point bug treating sqrt(6) and sqrt(2)*sqrt(3) as distinct catalog entries. |
| [partition-claim](results/partition-claim/) | 2026-07-11 | Disproved the manuscript's partition claim; smallest counterexample d = 60, a = 11. |
| [t1-beta](results/t1-beta/) | 2026-07-21 | Disproved the beta tail-degree bound; counterexample x = -16 + (48/7)sqrt(3), confirmed by three independent implementations. |
| [roots-of-unity](results/roots-of-unity/) | 2026-08 | Showed the vanishing-sums-of-roots-of-unity route cannot prove the length-5 classification; the weight condition holds trivially, so the argument is vacuous. |
| [catalan-rival](results/catalan-rival/) | 2026-08 | Refuted the rival count-law formula 2(4^m-1)/3: it predicts 170 at length 9, the true value is 168. |
| [length5-incomplete](results/length5-incomplete/) | 2026-08 | Found the nine hand-derived length-5 cases individually correct but incomplete; missing families appear at every k >= 3. |

## Already published (3)

Correct, but already in the literature. Found during a novelty check.

| Result | Logged | In short |
|---|---|---|
| [s-prime-formula](results/s-prime-formula/) | 2026-07-11 | Derived 2S'(1) = d deg S + a^-1 - a independently; already known (Lasker, arXiv:2309.10819, Lemma 6.1 and Corollary 6.2). |
| [k6-level-six](results/k6-level-six/) | 2026-08 | Proved the level-six divisibility claim independently; matches Byakuno-Ren-Yanagawa arXiv:2603.08439 Proposition 5.3, with the A_i profile as the new part. |
| [jump-gap](results/jump-gap/) | 2026-08-05 | Derived the closed form (1-q)q^E/(S+S-) for the rational jump gap independently, then found it published (Etingof arXiv:2508.08440; Jouteur, Paris-Romaskevich and Thomas arXiv:2603.04295v2). |

## Open (2)

Stated precisely, not settled.

| Result | Logged | In short |
|---|---|---|
| [negation-criterion](results/negation-criterion/) | 2026-06 | The finiteness criterion for the negation sum is still open; the palindrome-period argument fails at d = 19. |
| [divisor-hypothesis](results/divisor-hypothesis/) | 2026-06-17 | The divisor hypothesis holds for n <= 6 (Kogiso-Miyamoto-Ren-Wakui-Yanagawa; Byakuno-Ren-Yanagawa); open for n >= 7. |
