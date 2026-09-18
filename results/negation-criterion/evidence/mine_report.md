# mine_report: candidate criteria for negation finiteness

Snapshot of results.csv at 2026-07-08 23:54 UTC: 182 rows, 84 finite, 87 infinite, 11 undecided. Undecided rows are listed in features.csv and excluded from mining.

## Convention

Each d is squarefree and the labeled object is F(d) = [sqrt d]_q + [-sqrt d]_q, where [sqrt d]_q is the MGO q-deformation of the representative sqrt(d) (branch selected against the q-deformation of a deep rational convergent) and the negation is the Jouteur PGL_2(Z) action, arXiv:2503.02122 eq. (2). Labels are exact, not observational: finite means the exactly reduced denominator of F is a monomial in q, infinite means it has two or more terms. The features den_terms and den_degree encode this label by construction and are barred from every rule below; they appear in features.csv for description only.

## Candidates (100 percent consistent on labeled rows)

None. No single rule, boolean pair, or depth-2 tree over the allowed features is fully consistent with the labels.

## Named hypotheses

The parity of the CF period length of sqrt(d) equals the norm of the Pell fundamental unit of Z[sqrt d]: the norm is -1 exactly when the period length is odd. So the first hypothesis is a statement about the Pell equation x^2 - d y^2 = -1 being solvable.

- finite iff period length odd (equivalently the Pell fundamental unit of Z[sqrt d] has norm -1): errors = 82 of 171
  - TP(finite right)=22, FN(finite called infinite)=62, FP(infinite called finite)=20, TN(infinite right)=67
- finite iff d mod 4 in {1, 2}: errors = 90 of 171
  - TP(finite right)=52, FN(finite called infinite)=32, FP(infinite called finite)=58, TN(infinite right)=29
- finite iff max partial quotient <= K, best K = 16: errors = 65 of 171
  - TP(finite right)=34, FN(finite called infinite)=50, FP(infinite called finite)=15, TN(infinite right)=72

## Top 10 trends (below 100 percent)

- finite iff depth-2 tree: root [d_mod8 in {2, 3, 5, 6}], if root then split on [period_len <= 4] with labels (true: finite, false: infinite), else split on [period_len <= 6] with labels (true: finite, false: infinite): errors = 10 of 171
  - TP(finite right)=78, FN(finite called infinite)=6, FP(infinite called finite)=4, TN(infinite right)=83
- finite iff (period_len <= 4) or (word_sum <= 14): errors = 12 of 171
  - TP(finite right)=75, FN(finite called infinite)=9, FP(infinite called finite)=3, TN(infinite right)=84
- finite iff (period_len <= 4) or (word_sum <= 10): errors = 13 of 171
  - TP(finite right)=74, FN(finite called infinite)=10, FP(infinite called finite)=3, TN(infinite right)=84
- finite iff (period_len <= 4) or (word_sum <= 16): errors = 13 of 171
  - TP(finite right)=75, FN(finite called infinite)=9, FP(infinite called finite)=4, TN(infinite right)=83
- finite iff period_len <= 4: errors = 14 of 171
  - TP(finite right)=73, FN(finite called infinite)=11, FP(infinite called finite)=3, TN(infinite right)=84
- finite iff (period_len <= 4) or (word_max <= 8): errors = 14 of 171
  - TP(finite right)=75, FN(finite called infinite)=9, FP(infinite called finite)=5, TN(infinite right)=82
- finite iff (period_len <= 4) or (word_sum <= 17): errors = 14 of 171
  - TP(finite right)=75, FN(finite called infinite)=9, FP(infinite called finite)=5, TN(infinite right)=82
- finite iff (period_len <= 4) or (word_sum <= 24): errors = 14 of 171
  - TP(finite right)=78, FN(finite called infinite)=6, FP(infinite called finite)=8, TN(infinite right)=79
- finite iff (period_len <= 4) and (h_forms_4d <= 8): errors = 15 of 171
  - TP(finite right)=72, FN(finite called infinite)=12, FP(infinite called finite)=3, TN(infinite right)=84
- finite iff (period_len <= 4) and (not word_sum <= 2): errors = 15 of 171
  - TP(finite right)=72, FN(finite called infinite)=12, FP(infinite called finite)=3, TN(infinite right)=84

## Notes

h_forms_4d is the number of cycles of reduced primitive indefinite binary quadratic forms of discriminant 4d, computed by exact integer arithmetic; it equals the narrow class number of the order of discriminant 4d. It is checked against hand-derived anchors (d = 2, 3, 7, 10) and against a second independent implementation before any mining runs.
For every finite row the stored denominator is a monomial q^k; that is the definition of the label, which is why denominator-derived columns are excluded from rules.
word_max always includes the closing period term 2*floor(sqrt d), which grows with d regardless of the verdict; this is why every threshold on word_max performs poorly.
