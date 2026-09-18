# Grounding report: section-twin-primes.tex, "Relation to the divisor literature"

Scope: literature claims in `final/section-twin-primes.tex`, focus on the
"Relation to the divisor literature" subsection (lines 309 to 338), plus the
standard cyclotomic identity used in the proof. Read-only verification against
the actual source PDFs.

Sources consulted:
- [1] Kogiso, Miyamoto, Ren, Wakui, Yanagawa, "Arithmetic on q-deformed
  rational numbers", arXiv:2403.08446v2. PDF at
  <path>
- [4] Byakuno, Ren, Yanagawa, "Finiteness of specializations of the q-deformed
  modular group at roots of unity", arXiv:2603.08439v1. PDF at
  <path>
- Morier-Genoud, Ovsienko, "q-deformed rationals and q-continued fractions",
  arXiv:1812.00170v3 (the MGO rationals paper). PDF at
  review-documents/rationals.pdf.

Note on notation: the section writes the reduced q-denominator as S(q) with
S(1) = d; the source papers write it as S_{r/s}(q) with denominator s. So the
section's "e | d" is the papers' "e | s".

---

## Claim 1: e = 3, 4 from Kogiso, Miyamoto, Ren, Wakui, Yanagawa [1]

Section text (lines 313 to 314): "the cases e=3,4 follow from Kogiso, Miyamoto,
Ren, Wakui and Yanagawa [1]".

VERDICT: GROUNDED.

Locations:
- e = 3: Abstract and Corollary 7.2 (Section 7, "Special values"). The abstract
  states "s is a multiple of 3 (resp. 4) if and only if S_{r/s}(zeta) = 0 for
  zeta = (-1 + sqrt(-3))/2 (resp. zeta = i)". Corollary 7.2(1) (p. 22 of the
  PDF, txt line 2220): if s is a multiple of 3 then [3]_q divides S_{r/s}(q),
  and the converse via S_{r/s}(omega) = 0. Since Phi_3 | S is exactly
  S(omega) = 0, this gives Phi_3 | S => 3 | s (= 3 | d).
- e = 4: Theorem 7.6 (txt line 2382): the following are equivalent, (1) s is a
  multiple of 4, ... with S_{r/s}(i) = 0. Since Phi_4 | S is exactly S(i) = 0,
  this gives Phi_4 | S => 4 | s (= 4 | d).

Paraphrase: [1] proves S vanishes at the primitive cube (resp. fourth) root of
unity if and only if 3 (resp. 4) divides the denominator, which is the divisor
implication at e = 3 and e = 4.

Attribution: correct. Five authors, exactly as cited.

Needed correction: none.

---

## Claim 2: e = 5, 6 from Byakuno, Ren, Yanagawa [4], residue condition at e=5,
##            Eisenstein-norm descent at e=6

Section text (lines 314 to 317): "and the cases e=5,6 from Byakuno, Ren and
Yanagawa [4], the latter under an extra residue condition on the numerator at
e=5 and by an Eisenstein-norm descent at e=6".

VERDICT: GROUNDED (one wording nuance to tighten).

Locations:
- e = 5: Corollary 3.8(2) (Section 3.3, p. 9 to 10 of the PDF, txt line 1006):
  "S_{r/s}(zeta_5) = 0 if and only if s in 5Z and r ≡ 1, 4 (mod 5)." Since
  Phi_5 | S is exactly S(zeta_5) = 0, the forward direction gives
  Phi_5 | S => 5 | s (= 5 | d). The residue condition r ≡ 1, 4 (mod 5) is the
  numerator condition described in the section.
- e = 6: Proposition 5.3 (Section 5, p. 11 to 12 of the PDF, txt line 1339):
  "If S_{r/s}(-omega) = 0, or equivalently, q^2 - q + 1 divides S_{r/s}(q), then
  s is a multiple of 6." Here q^2 - q + 1 = Phi_6(q) and -omega = zeta_6. The
  proof (txt lines 1341 to 1346) is exactly an Eisenstein-norm descent: S(-1)
  in {0, +-1} forces s even, then using the Eisenstein norm
  N(a + b*omega) = a^2 - ab + b^2 on Z[omega] forces f(omega) = 0, hence 3 | s,
  hence 6 | s.

Paraphrase: [4] proves that Phi_5 dividing S forces 5 | d with an added
numerator residue r ≡ 1 or 4 mod 5 for the full biconditional, and that Phi_6
dividing S forces 6 | d by a two-step norm argument over the Eisenstein
integers.

Attribution: correct. Three authors (Byakuno, Ren, Yanagawa), exactly as cited.
Both e = 5 and e = 6 are genuinely theirs. The "Eisenstein-norm descent"
description of e = 6 is exact to the paper's proof. The "residue condition on
the numerator at e = 5" is exact to Corollary 3.8(2).

Needed correction (minor, precision only): the strict implication
Phi_5 | S => 5 | d at e = 5 is itself unconditional (it is the forward direction
of Corollary 3.8(2) and needs no numerator condition). The residue condition
r ≡ 1, 4 (mod 5) governs the converse, i.e. when 5 | d actually forces Phi_5 | S.
The sentence as written can be read as if the implication needs the residue
condition, which slightly understates the e = 5 result. Recommended tightening
below; this does not change any attribution.

---

## Claim 3 (NEGATIVE): no prior statement connects twin primes, or the
##            two-cyclotomic form, to the family x = m/(m^2 - 1)

Section text (lines 318 to 320): "A search of that literature did not find any
prior statement connecting twin primes, or the two-cyclotomic form of a
q-denominator, to the family m/(m^2-1), so the characterization below appears to
be new."

VERDICT: GROUNDED (negative claim holds; NO novelty-breaker).

Evidence:
- [1] Kogiso et al.: grep for "twin", "consecutive prime", "prime pair",
  "difference of squares", "m^2-1", "(m-1)(m+1)", "m/(m..." returns no
  substantive hits. The only near-matches ("m2", "m^2") are bibliography labels
  ([LeM21], [KW19], txt lines 83, 481, 2788), not the family.
- [4] Byakuno, Ren, Yanagawa: same search returns zero hits for twin primes,
  consecutive primes, or the difference-of-squares family.
- MGO rationals paper (rationals.pdf): same search returns zero hits for twin
  primes, consecutive primes, or the m/(m^2-1) family.

None of the three papers states or approaches a twin-prime characterization or
the two-cyclotomic-factor phenomenon for the m/(m^2-1) family. The negative
claim is accurate. No paper comes close, so there is no novelty-breaker.

Needed correction: none.

---

## Claim 4 (internal standard identity): [k]_q = prod_{e | k, e > 1} Phi_e(q)
##            and the "exactly two cyclotomic factors iff both prime" logic

Section text: eq. (eq:cyclofact) at lines 215 to 218, plus the counting argument
in Theorem 3.x (thm:twin) and Remark rem:edge.

VERDICT: GROUNDED.

This is the standard cyclotomic factorization. From q^k - 1 = prod_{e | k}
Phi_e(q) and Phi_1(q) = q - 1, dividing by q - 1 gives
[k]_q = (q^k - 1)/(q - 1) = prod_{e | k, e > 1} Phi_e(q), a product of
tau(k) - 1 distinct cyclotomic polynomials. The section states this correctly,
including tau(k) - 1 = 0 for k = 1 and tau(k) - 1 = 1 exactly when k is prime
(then [k]_q = Phi_k). The two-factor count for S = [m-1]_q [m+1]_q as
(tau(m-1) - 1) + (tau(m+1) - 1), equal to 2 with no repeat iff both m-1 and m+1
are prime (with the even-m coprimality handling the shared Phi_2 case), is
internally consistent with the identity.

Attribution: the section attributes this identity to its own "Section 1", not to
[1] or [4]. There is no misattribution of the standard identity to the source
papers. Correct.

Needed correction: none.

---

## Summary of verdicts

| Claim | Verdict | Key location |
|-------|---------|--------------|
| 1. e=3,4 from Kogiso et al. [1] | GROUNDED | [1] Cor. 7.2 (e=3), Thm. 7.6 (e=4), Sec. 7 |
| 2. e=5,6 from BRY [4]; residue at e=5, Eisenstein at e=6 | GROUNDED (tighten wording) | [4] Cor. 3.8(2) (e=5), Prop. 5.3 (e=6) |
| 3. Negative: no prior twin-prime / family link | GROUNDED, no novelty-breaker | absent from [1], [4], MGO rationals |
| 4. Standard cyclotomic identity, not misattributed | GROUNDED | own Section 1; standard |

Both attribution splits are exactly right: e = 3, 4 belong to the five-author
Kogiso paper, and e = 5, 6 belong to the three-author Byakuno-Ren-Yanagawa
paper. No novelty-breaker found.

---

## Required section edits

Only one small precision edit is warranted; everything else is grounded as
written.

1. (Recommended, precision) At lines 313 to 317, the phrase "the latter under an
   extra residue condition on the numerator at e=5" can read as though the
   divisor implication itself needs the residue condition. The forward
   implication Phi_5 | S => 5 | d is unconditional; the residue condition
   r ≡ 1, 4 (mod 5) is what upgrades it to the full biconditional. Suggested
   rewrite of the clause:

   "... and the cases e=5,6 from Byakuno, Ren and Yanagawa [4]; at e=5 the full
   biconditional additionally requires a residue condition on the numerator
   (r ≡ 1, 4 mod 5), and e=6 is obtained by an Eisenstein-norm descent."

   This keeps the (correct) statement that the implication is known
   unconditionally while accurately locating where the numerator residue enters.

No other edits required. The two-cyclotomic identity, the twin-prime
characterization, and the novelty claim are all consistent with the sources.
