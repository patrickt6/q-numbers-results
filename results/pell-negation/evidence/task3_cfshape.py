#!/usr/bin/env python3
"""Task 3: regular CF of sqrt(d) for the two family branches
   n = 25k+7  -> d = 25k^2+14k+2   (period length 3, per census)
   n = 25k+18 -> d = 25k^2+36k+13  (period length 5, per census)
for k=0..10. Print [a0; a1,...,a_l] and look for a linear-in-k pattern.
"""
import math

def sqrt_cf(d, max_period=50):
    a0 = math.isqrt(d)
    assert a0 * a0 != d
    m, den, a = 0, 1, a0
    period = []
    while True:
        m = den * a - m
        den = (d - m * m) // den
        a = (a0 + m) // den
        period.append(a)
        if a == 2 * a0 or len(period) > max_period:
            break
    return a0, period


print("=== branch n=25k+7, d=25k^2+14k+2 (expect period length 3) ===")
for k in range(11):
    n = 25 * k + 7
    d = 25 * k * k + 14 * k + 2
    a0, period = sqrt_cf(d)
    print(f"k={k:2d} n={n:4d} d={d:6d}  sqrt(d)=[{a0}; {', '.join(map(str,period))}]  a0={a0}")

print()
print("=== branch n=25k+18, d=25k^2+36k+13 (expect period length 5) ===")
for k in range(11):
    n = 25 * k + 18
    d = 25 * k * k + 36 * k + 13
    a0, period = sqrt_cf(d)
    print(f"k={k:2d} n={n:4d} d={d:6d}  sqrt(d)=[{a0}; {', '.join(map(str,period))}]  a0={a0}")

print()
print("=== interleaved family order by increasing d (first several members) ===")
fam = []
for k in range(11):
    d7 = 25*k*k+14*k+2
    fam.append((d7, 'n=25k+7', k))
    d18 = 25*k*k+36*k+13
    fam.append((d18, 'n=25k+18', k))
fam.sort()
for d, branch, k in fam[:14]:
    a0, period = sqrt_cf(d)
    print(f"d={d:6d}  ({branch}, k={k})  sqrt(d)=[{a0}; {', '.join(map(str,period))}]")
