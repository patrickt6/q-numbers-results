"""
T5 scalar-congruence scan.

For each nonsquare d, Lambda_q = rho(fundamental automorph) = [[A,B],[C,D]].
Tests, exactly over Z (all entries are Laurent polynomials; divisibility is
taken in Z[q, 1/q], i.e. up to monomial factors, after normalizing every
polynomial so its lowest exponent is 0):

  GLOBAL  T1: C | A-D          (finiteness of F_d, by the Pell reduction)
          T2: C | B            (the other side of the scalar congruence)
          T3: C^2 | T^2-4q^m   (the q-Pell candidate, T = A+D, det = q^m)

  LOCAL   for each irreducible factor phi of C (phi != q):
          k = mult of phi in C, a = mult in A-D, b = mult in B,
          w = mult in T^2 - 4 q^m.
          The conjecture in local form is (a>=k) <=> (b>=k).

  CONTROL non-pure automorphs M_a = automorph of a + sqrt(d)
          = [[r+as, ds-a^2 s],[s, r-as]], a != 0, where the diagonal-equality
          structure (N M N = M^{-1}) is broken. Same tests.

All arithmetic is exact integer arithmetic. Division uses the fact that C
(and every entry, after normalization) has leading coefficient +-1 only when
it does; the general exact-division routine works over Q via Fraction and
certifies divisibility exactly.
"""
import sys
import csv
import time
from fractions import Fraction

sys.path.insert(0, '<path>')
from fastlam import lam_q_fast, rho_fast, p_add, p_mul, sl2_word_from_L  # noqa
sys.path.insert(0, '<path>')
from proof_verification import sl2_word  # noqa
from qcore import pell_plus1  # noqa

import sympy as sp
q = sp.symbols('q')


# ---------- dict-poly helpers ----------

def norm(p):
    """Shift exponents so min exponent is 0; return coeff list low->high.
    Zero polynomial returns []."""
    if not p:
        return []
    lo = min(p)
    hi = max(p)
    out = [0] * (hi - lo + 1)
    for e, c in p.items():
        out[e - lo] = c
    return out


def sub(p1, p2):
    return p_add(p1, p2, scale=-1)


def det_exponent(A, B, C, D):
    det = sub(p_mul(A, D), p_mul(B, C))
    assert len(det) == 1, det
    (e, c), = det.items()
    assert c in (1, -1), det
    return e, c


def list_to_dict(lst):
    return {i: c for i, c in enumerate(lst) if c}


def divmod_exact(f, g):
    """Long division f = g*qt + r over Q, exact. f, g coeff lists low->high,
    g != []. Returns (qt, r) as lists of Fractions."""
    f = [Fraction(c) for c in f]
    dg = len(g) - 1
    lg = Fraction(g[-1])
    qt = [Fraction(0)] * max(0, len(f) - dg)
    while len(f) - 1 >= dg and any(f):
        df = len(f) - 1
        while df >= 0 and f[df] == 0:
            df -= 1
        if df < dg:
            break
        coef = f[df] / lg
        qt[df - dg] = coef
        for i in range(dg + 1):
            f[df - dg + i] -= coef * Fraction(g[i])
        f = f[:df]  # top coeff now zero
    # strip trailing zeros of remainder
    while f and f[-1] == 0:
        f.pop()
    return qt, f


def divides(g, f):
    """Does g | f in Q[q]? f == [] counts as divisible."""
    if not f:
        return True
    if not g or len(g) == 1:
        return bool(g)
    _, r = divmod_exact(f, g)
    return not r


def multiplicity(g, f, cap=64):
    """Largest e with g^e | f (f != []). Exact over Q."""
    if not f:
        return cap  # infinity marker
    e = 0
    cur = [Fraction(c) for c in f]
    while e < cap:
        qt, r = divmod_exact(cur, g)
        if r:
            return e
        cur = qt
        e += 1
    return e


def is_cyclotomic(phi_list):
    """Return n if phi (coeff list) equals the n-th cyclotomic polynomial."""
    d = len(phi_list) - 1
    if d < 1:
        return None
    P = sp.Poly(phi_list[::-1], q)
    for n in range(1, 20 * d + 20):
        if sp.totient(n) == d:
            if P == sp.Poly(sp.cyclotomic_poly(n, q), q):
                return n
    return None


def entries_from_word(w):
    A, B, C, D = rho_fast(w)
    return A, B, C, D


def is_square(n):
    r = sp.integer_nthroot(n, 2)[0]
    return r * r == n


def run_global(dmax, out):
    """Global iff scan over nonsquare d in [2, dmax]."""
    n_fin = n_inf = 0
    mismatches = []
    t3_true = t3_false_fin = t3_false_inf = 0
    for d in range(2, dmax + 1):
        if is_square(d):
            continue
        (r, s), (A, B, C, D) = lam_q_fast(d)
        f = sub(A, D)
        Cl, fl, Bl = norm(C), norm(f), norm(B)
        t1 = divides(Cl, fl)
        t2 = divides(Cl, Bl)
        m, _ = det_exponent(A, B, C, D)
        T = p_add(A, D)
        w2 = sub(p_mul(T, T), {m: 4})
        C2 = norm(p_mul(C, C))
        t3 = divides(C2, norm(w2))
        if t1:
            n_fin += 1
        else:
            n_inf += 1
        if t1 != t2:
            mismatches.append(d)
            print(f"  MISMATCH d={d}: C|A-D={t1}  C|B={t2}")
        if t3:
            t3_true += 1
        else:
            if t1:
                t3_false_fin += 1
            else:
                t3_false_inf += 1
        out.writerow([d, r % 10**8, s % 10**8, len(Cl) - 1,
                      int(t1), int(t2), int(t3)])
    return n_fin, n_inf, mismatches, t3_true, t3_false_fin, t3_false_inf


def run_local(dmax, out):
    """Per-irreducible-factor valuation table."""
    rows = 0
    viol = []
    for d in range(2, dmax + 1):
        if is_square(d):
            continue
        (r, s), (A, B, C, D) = lam_q_fast(d)
        f = sub(A, D)
        Cl, fl, Bl = norm(C), norm(f), norm(B)
        m, _ = det_exponent(A, B, C, D)
        T = p_add(A, D)
        w2l = norm(sub(p_mul(T, T), {m: 4}))
        glob_fin = divides(Cl, fl)
        P = sp.Poly(Cl[::-1], q)
        fac = sp.factor_list(P)[1]
        for phi, k in fac:
            phil = [int(c) for c in sp.Poly(phi, q).all_coeffs()[::-1]]
            if len(phil) == 1:
                continue
            a = multiplicity(phil, fl)
            b = multiplicity(phil, Bl)
            w = multiplicity(phil, w2l)
            n = is_cyclotomic(phil)
            ok = (a >= k) == (b >= k)
            if not ok:
                viol.append((d, phil, k, a, b, w))
                print(f"  LOCAL VIOLATION d={d} phi={phil} k={k} a={a} b={b} w={w}")
            out.writerow([d, int(glob_fin), len(phil) - 1,
                          n if n else '', k, a, b, w, int(ok),
                          ' '.join(map(str, phil))])
            rows += 1
    return rows, viol


def run_control(dmax, amax, out):
    """Automorphs of a + sqrt d, a in [1, amax]: same global tests."""
    n_iff_holds = 0
    n_mismatch = 0
    mismatches = []
    for d in range(2, dmax + 1):
        if is_square(d):
            continue
        r, s = pell_plus1(d)
        for a in range(1, amax + 1):
            M = [[r + a * s, (d - a * a) * s], [s, r - a * s]]
            if M[0][1] <= 0:
                continue
            Msp = sp.Matrix(M)
            try:
                w = sl2_word(Msp)
            except Exception:
                continue
            A, B, C, D = entries_from_word(w)
            # verify word decodes to M at q=1 (up to sign)
            f = sub(A, D)
            Cl, fl, Bl = norm(C), norm(f), norm(B)
            t1 = divides(Cl, fl)
            t2 = divides(Cl, Bl)
            if t1 != t2:
                n_mismatch += 1
                mismatches.append((d, a, t1, t2))
            else:
                n_iff_holds += 1
            out.writerow([d, a, int(t1), int(t2)])
    return n_iff_holds, n_mismatch, mismatches


if __name__ == '__main__':
    base = ('<path>'
            '2026-07-21-next-steps/problems/T5-scalar-congruence/attempts/fable')
    dmax_global = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    dmax_local = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    dmax_ctrl = int(sys.argv[3]) if len(sys.argv) > 3 else 60

    print('== R_q S_q check ==')
    RS = entries_from_word([('R', 1), ('S', 0)])
    print('R_q S_q =', RS, '(expect A=1,B=-1,C=1,D=0)')

    t0 = time.time()
    print(f'== global scan d in [2,{dmax_global}] ==')
    with open(f'{base}/global_scan.csv', 'w', newline='') as fh:
        wcsv = csv.writer(fh)
        wcsv.writerow(['d', 'r_mod1e8', 's_mod1e8', 'degC',
                       'C_div_AminusD', 'C_div_B', 'C2_div_T2minus4qm'])
        res = run_global(dmax_global, wcsv)
    n_fin, n_inf, mism, t3t, t3ff, t3fi = res
    print(f'finite {n_fin}, infinite {n_inf}, iff-mismatches {mism}')
    print(f'q-Pell C^2|T^2-4q^m: holds {t3t}, fails(finite) {t3ff}, '
          f'fails(infinite) {t3fi}   [{time.time()-t0:.1f}s]')

    t0 = time.time()
    print(f'== local scan d in [2,{dmax_local}] ==')
    with open(f'{base}/local_data.csv', 'w', newline='') as fh:
        wcsv = csv.writer(fh)
        wcsv.writerow(['d', 'finite', 'deg_phi', 'cyclotomic_n',
                       'k_in_C', 'a_in_AminusD', 'b_in_B',
                       'w_in_T2minus4qm', 'local_iff_ok', 'phi_coeffs'])
        rows, viol = run_local(dmax_local, wcsv)
    print(f'{rows} factor instances, local violations: {len(viol)}'
          f'   [{time.time()-t0:.1f}s]')

    t0 = time.time()
    print(f'== control: automorphs of a+sqrt(d), d<= {dmax_ctrl}, a<=3 ==')
    with open(f'{base}/control_scan.csv', 'w', newline='') as fh:
        wcsv = csv.writer(fh)
        wcsv.writerow(['d', 'a', 'C_div_AminusD', 'C_div_B'])
        okc, bad, badlist = run_control(dmax_ctrl, 3, wcsv)
    print(f'iff holds {okc}, iff fails {bad}')
    for row in badlist[:20]:
        print('   control mismatch (d,a,C|A-D,C|B):', row)
    print(f'[{time.time()-t0:.1f}s]')
