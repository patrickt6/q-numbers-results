"""Which pairs (k, l), l | k, 1 < l < k, does the theorem close?

Rule: DC(top -> bottom) is proved by the theorem when bottom is in
{2, 3, 4, 5} and top/bottom is a prime power. Proved pairs compose along
divisor chains. Everything else is OPEN (as a theorem; exhaustive
length-slices in 02 cover more, but only per length).
"""


def is_prime_power(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            while n % d == 0:
                n //= d
            return n == 1
        d += 1
    return True


GOOD = {2, 3, 4, 5}
KMAX = 60

# direct edges
proved = set()
for k in range(4, KMAX + 1):
    for l in range(2, k):
        if k % l == 0 and l in GOOD and is_prime_power(k // l):
            proved.add((k, l))
# transitive closure through divisor chains
changed = True
while changed:
    changed = False
    for k in range(4, KMAX + 1):
        for m in range(2, k):
            if k % m == 0 and (k, m) in proved:
                for l in range(2, m):
                    if m % l == 0 and (m, l) in proved and (k, l) not in proved:
                        proved.add((k, l))
                        changed = True

open_pairs = []
for k in range(4, KMAX + 1):
    for l in range(2, k):
        if k % l == 0 and (k, l) not in proved:
            open_pairs.append((k, l))

print(f"proved pairs up to k={KMAX}: {len(proved)}")
print(f"open pairs up to k={KMAX}: {len(open_pairs)}")
print("open pairs with k <= 36:")
for k, l in open_pairs:
    if k <= 36:
        print(f"  ({k}, {l})")
