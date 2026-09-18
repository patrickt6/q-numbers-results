# negation_criterion

Stage 0 of the negation finiteness pipeline for Ovsienko Example 6.4. For each
squarefree d, label_negation.py computes an exact three-way verdict on whether
F(d) = [sqrt d]_q + [-sqrt d]_q is a finite Laurent polynomial, using the Jouteur
negation (arXiv:2503.02122, eq. (2)); verdicts append to results.csv (resumable).
mine_criterion.py reads a snapshot of results.csv, builds arithmetic features per d
(period word stats, d mod 3/4/8, form class number of 4d), and searches threshold,
congruence, pair, and depth-2 tree rules, writing features.csv and mine_report.md.

Calibrate: `/opt/anaconda3/bin/python label_negation.py --calibrate`
Scan: `/opt/anaconda3/bin/python label_negation.py --min 2 --max 300 --timeout 120`
Retry undecided rows with two exact routes (primary and resultant), 600 s each,
adding a verdict_source column: `/opt/anaconda3/bin/python label_negation.py --retry`
Mine: `/opt/anaconda3/bin/python mine_criterion.py`
