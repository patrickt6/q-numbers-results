# Task 1 census summary

Total runtime: 189.6s

## Class counts (all (d,a) pairs across the full d list)

- ANOMALOUS-CYCLOTOMIC: 166
- CYCLOTOMIC: 661
- NON-CYCLOTOMIC: 19064
- UNRESOLVED: 2124

## Predicate failures (downward_closed / pp_complete / partition_form)

22 FAILURES FOUND (potential counterexamples to paper claim):

| d | a | T | downward_closed | pp_complete | partition_form |
|---|---|---|---|---|---|
| 60 | 11 | [2, 3, 4, 5, 6] | True | True | False |
| 60 | 19 | [2, 3, 4, 5, 6] | True | True | False |
| 60 | 41 | [2, 3, 4, 5, 6] | True | True | False |
| 60 | 49 | [2, 3, 4, 5, 6] | True | True | False |
| 84 | 13 | [2, 3, 4, 6, 7] | True | True | False |
| 84 | 71 | [2, 3, 4, 6, 7] | True | True | False |
| 180 | 19 | [2, 3, 4, 5, 9, 10] | True | True | False |
| 180 | 161 | [2, 3, 4, 5, 9, 10] | True | True | False |
| 220 | 21 | [2, 4, 5, 10, 11] | True | True | False |
| 220 | 199 | [2, 4, 5, 10, 11] | True | True | False |
| 420 | 29 | [2, 3, 4, 5, 7, 14, 15] | True | True | False |
| 420 | 391 | [2, 3, 4, 5, 7, 14, 15] | True | True | False |
| 504 | 55 | [2, 3, 4, 6, 7, 8, 9] | True | True | False |
| 504 | 71 | [2, 3, 4, 6, 7, 8, 9] | True | True | False |
| 504 | 433 | [2, 3, 4, 6, 7, 8, 9] | True | True | False |
| 504 | 449 | [2, 3, 4, 6, 7, 8, 9] | True | True | False |
| 924 | 43 | [2, 3, 4, 7, 11, 21, 22] | True | True | False |
| 924 | 881 | [2, 3, 4, 7, 11, 21, 22] | True | True | False |
| 990 | 89 | [2, 3, 5, 6, 9, 10, 11] | True | True | False |
| 990 | 109 | [2, 3, 5, 6, 9, 10, 11] | True | True | False |
| 990 | 881 | [2, 3, 5, 6, 9, 10, 11] | True | True | False |
| 990 | 901 | [2, 3, 5, 6, 9, 10, 11] | True | True | False |

## Anomalous-cyclotomic cases (S factors into cyclotomics with m not dividing d, or repeats)

166 ANOMALOUS-CYCLOTOMIC CASES FOUND (theoretically important):

- d=8, a=3, multiset=[2, 2, 4]
- d=8, a=5, multiset=[2, 2, 4]
- d=16, a=7, multiset=[2, 2, 4, 4]
- d=16, a=9, multiset=[2, 2, 4, 4]
- d=24, a=5, multiset=[2, 2, 3, 4, 6]
- d=24, a=7, multiset=[2, 3, 4, 4]
- d=24, a=11, multiset=[2, 2, 3, 4, 6]
- d=24, a=13, multiset=[2, 2, 3, 4, 6]
- d=24, a=17, multiset=[2, 3, 4, 4]
- d=24, a=19, multiset=[2, 2, 3, 4, 6]
- d=32, a=15, multiset=[2, 2, 4, 4, 8]
- d=32, a=17, multiset=[2, 2, 4, 4, 8]
- d=40, a=9, multiset=[2, 4, 4, 5]
- d=40, a=11, multiset=[2, 2, 4, 5]
- d=40, a=19, multiset=[2, 2, 4, 5, 10]
- d=40, a=21, multiset=[2, 2, 4, 5, 10]
- d=40, a=29, multiset=[2, 2, 4, 5]
- d=40, a=31, multiset=[2, 4, 4, 5]
- d=45, a=19, multiset=[3, 3, 5]
- d=45, a=26, multiset=[3, 3, 5]
- d=48, a=7, multiset=[2, 2, 3, 4, 6, 8]
- d=48, a=17, multiset=[2, 2, 2, 3, 4, 6]
- d=48, a=23, multiset=[2, 2, 3, 4, 4, 6, 12]
- d=48, a=25, multiset=[2, 2, 3, 4, 4, 6, 12]
- d=48, a=31, multiset=[2, 2, 2, 3, 4, 6]
- d=48, a=41, multiset=[2, 2, 3, 4, 6, 8]
- d=56, a=27, multiset=[2, 2, 4, 7, 14]
- d=56, a=29, multiset=[2, 2, 4, 7, 14]
- d=64, a=31, multiset=[2, 2, 4, 4, 8, 16]
- d=64, a=33, multiset=[2, 2, 4, 4, 8, 16]
- d=72, a=19, multiset=[2, 2, 3, 3, 4, 6]
- d=72, a=35, multiset=[2, 2, 3, 4, 6, 9, 18]
- d=72, a=37, multiset=[2, 2, 3, 4, 6, 9, 18]
- d=72, a=53, multiset=[2, 2, 3, 3, 4, 6]
- d=80, a=9, multiset=[2, 2, 4, 5, 8, 10]
- d=80, a=31, multiset=[2, 2, 2, 4, 5]
- d=80, a=39, multiset=[2, 2, 4, 4, 5, 10, 20]
- d=80, a=41, multiset=[2, 2, 4, 4, 5, 10, 20]
- d=80, a=49, multiset=[2, 2, 2, 4, 5]
- d=80, a=71, multiset=[2, 2, 4, 5, 8, 10]
- d=88, a=43, multiset=[2, 2, 4, 11, 22]
- d=88, a=45, multiset=[2, 2, 4, 11, 22]
- d=90, a=19, multiset=[2, 3, 3, 5, 6]
- d=90, a=71, multiset=[2, 3, 3, 5, 6]
- d=96, a=17, multiset=[2, 2, 2, 2, 3, 4, 6, 6]
- d=96, a=47, multiset=[2, 2, 3, 4, 4, 6, 8, 12, 24]
- d=96, a=49, multiset=[2, 2, 3, 4, 4, 6, 8, 12, 24]
- d=96, a=79, multiset=[2, 2, 2, 2, 3, 4, 6, 6]
- d=104, a=51, multiset=[2, 2, 4, 13, 26]
- d=104, a=53, multiset=[2, 2, 4, 13, 26]
- d=112, a=15, multiset=[2, 4, 4, 7, 8]
- d=112, a=55, multiset=[2, 2, 4, 4, 7, 14, 28]
- d=112, a=57, multiset=[2, 2, 4, 4, 7, 14, 28]
- d=112, a=97, multiset=[2, 4, 4, 7, 8]
- d=120, a=11, multiset=[2, 2, 3, 4, 5, 6, 10, 12]
- d=120, a=19, multiset=[2, 2, 3, 4, 5, 6, 6]
- d=120, a=29, multiset=[2, 2, 3, 4, 5, 6, 6]
- d=120, a=49, multiset=[2, 3, 4, 4, 5]
- d=120, a=59, multiset=[2, 2, 3, 4, 5, 6, 10, 15, 30]
- d=120, a=61, multiset=[2, 2, 3, 4, 5, 6, 10, 15, 30]
- d=120, a=71, multiset=[2, 3, 4, 4, 5]
- d=120, a=91, multiset=[2, 2, 3, 4, 5, 6, 6]
- d=120, a=101, multiset=[2, 2, 3, 4, 5, 6, 6]
- d=120, a=109, multiset=[2, 2, 3, 4, 5, 6, 10, 12]
- d=128, a=63, multiset=[2, 2, 4, 4, 8, 16, 32]
- d=128, a=65, multiset=[2, 2, 4, 4, 8, 16, 32]
- d=136, a=67, multiset=[2, 2, 4, 17, 34]
- d=136, a=69, multiset=[2, 2, 4, 17, 34]
- d=144, a=17, multiset=[2, 3, 4, 4, 8, 9]
- d=144, a=71, multiset=[2, 2, 3, 4, 4, 6, 9, 12, 18, 36]
- d=144, a=73, multiset=[2, 2, 3, 4, 4, 6, 9, 12, 18, 36]
- d=144, a=127, multiset=[2, 3, 4, 4, 8, 9]
- d=152, a=75, multiset=[2, 2, 4, 19, 38]
- d=152, a=77, multiset=[2, 2, 4, 19, 38]
- d=160, a=49, multiset=[2, 2, 4, 4, 4, 5]
- d=160, a=79, multiset=[2, 2, 4, 4, 5, 8, 10, 20, 40]
- d=160, a=81, multiset=[2, 2, 4, 4, 5, 8, 10, 20, 40]
- d=160, a=111, multiset=[2, 2, 4, 4, 4, 5]
- d=168, a=13, multiset=[2, 2, 3, 4, 6, 7, 12, 14]
- d=168, a=29, multiset=[2, 2, 3, 4, 6, 7]
- d=168, a=83, multiset=[2, 2, 3, 4, 6, 7, 14, 21, 42]
- d=168, a=85, multiset=[2, 2, 3, 4, 6, 7, 14, 21, 42]
- d=168, a=139, multiset=[2, 2, 3, 4, 6, 7]
- d=168, a=155, multiset=[2, 2, 3, 4, 6, 7, 12, 14]
- d=176, a=87, multiset=[2, 2, 4, 4, 11, 22, 44]
- d=176, a=89, multiset=[2, 2, 4, 4, 11, 22, 44]
- d=184, a=91, multiset=[2, 2, 4, 23, 46]
- d=184, a=93, multiset=[2, 2, 4, 23, 46]
- d=192, a=95, multiset=[2, 2, 3, 4, 4, 6, 8, 12, 16, 24, 48]
- d=192, a=97, multiset=[2, 2, 3, 4, 4, 6, 8, 12, 16, 24, 48]
- d=200, a=99, multiset=[2, 2, 4, 5, 10, 25, 50]
- d=200, a=101, multiset=[2, 2, 4, 5, 10, 25, 50]
- d=208, a=103, multiset=[2, 2, 4, 4, 13, 26, 52]
- d=208, a=105, multiset=[2, 2, 4, 4, 13, 26, 52]
- d=210, a=29, multiset=[2, 3, 5, 6, 6, 7]
- d=210, a=41, multiset=[2, 3, 5, 6, 6, 7]
- d=210, a=169, multiset=[2, 3, 5, 6, 6, 7]
- d=210, a=181, multiset=[2, 3, 5, 6, 6, 7]
- d=216, a=107, multiset=[2, 2, 3, 4, 6, 9, 18, 27, 54]
- d=216, a=109, multiset=[2, 2, 3, 4, 6, 9, 18, 27, 54]
- d=224, a=15, multiset=[2, 2, 4, 7, 8, 14, 16]
- d=224, a=111, multiset=[2, 2, 4, 4, 7, 8, 14, 28, 56]
- d=224, a=113, multiset=[2, 2, 4, 4, 7, 8, 14, 28, 56]
- d=224, a=209, multiset=[2, 2, 4, 7, 8, 14, 16]
- d=232, a=115, multiset=[2, 2, 4, 29, 58]
- d=232, a=117, multiset=[2, 2, 4, 29, 58]
- d=240, a=31, multiset=[2, 3, 4, 5, 8, 8]
- d=240, a=41, multiset=[2, 2, 3, 4, 5, 6, 8]
- d=240, a=49, multiset=[2, 2, 2, 3, 4, 5, 6, 10]
- d=240, a=71, multiset=[2, 2, 3, 4, 4, 5]
- d=240, a=89, multiset=[2, 2, 3, 4, 4, 5]
- d=240, a=119, multiset=[2, 2, 3, 4, 4, 5, 6, 10, 12, 15, 20, 30, 60]
- d=240, a=121, multiset=[2, 2, 3, 4, 4, 5, 6, 10, 12, 15, 20, 30, 60]
- d=240, a=151, multiset=[2, 2, 3, 4, 4, 5]
- d=240, a=169, multiset=[2, 2, 3, 4, 4, 5]
- d=240, a=191, multiset=[2, 2, 2, 3, 4, 5, 6, 10]
- d=240, a=199, multiset=[2, 2, 3, 4, 5, 6, 8]
- d=240, a=209, multiset=[2, 3, 4, 5, 8, 8]
- d=264, a=23, multiset=[2, 3, 4, 4, 6, 11, 12]
- d=264, a=131, multiset=[2, 2, 3, 4, 6, 11, 22, 33, 66]
- d=264, a=133, multiset=[2, 2, 3, 4, 6, 11, 22, 33, 66]
- d=264, a=241, multiset=[2, 3, 4, 4, 6, 11, 12]
- d=280, a=99, multiset=[2, 2, 4, 5, 7]
- d=280, a=139, multiset=[2, 2, 4, 5, 7, 10, 14, 35, 70]
- d=280, a=141, multiset=[2, 2, 4, 5, 7, 10, 14, 35, 70]
- d=280, a=181, multiset=[2, 2, 4, 5, 7]
- d=288, a=17, multiset=[2, 2, 3, 4, 6, 8, 9, 16, 18]
- d=288, a=127, multiset=[2, 2, 2, 3, 3, 4, 4, 6]
- d=288, a=143, multiset=[2, 2, 3, 4, 4, 6, 8, 9, 12, 18, 24, 36, 72]
- d=288, a=145, multiset=[2, 2, 3, 4, 4, 6, 8, 9, 12, 18, 24, 36, 72]
- d=288, a=161, multiset=[2, 2, 2, 3, 3, 4, 4, 6]
- d=288, a=271, multiset=[2, 2, 3, 4, 6, 8, 9, 16, 18]
- d=312, a=25, multiset=[2, 3, 4, 4, 6, 12, 13]
- d=312, a=155, multiset=[2, 2, 3, 4, 6, 13, 26, 39, 78]
- d=312, a=157, multiset=[2, 2, 3, 4, 6, 13, 26, 39, 78]
- d=312, a=287, multiset=[2, 3, 4, 4, 6, 12, 13]
- d=315, a=134, multiset=[3, 3, 5, 7]
- d=315, a=181, multiset=[3, 3, 5, 7]
- d=336, a=41, multiset=[2, 2, 3, 4, 6, 6, 7, 8]
- d=336, a=55, multiset=[2, 2, 3, 4, 6, 6, 7, 8]
- d=336, a=97, multiset=[2, 3, 4, 4, 4, 7]
- d=336, a=167, multiset=[2, 2, 3, 4, 4, 6, 7, 12, 14, 21, 28, 42, 84]
- d=336, a=169, multiset=[2, 2, 3, 4, 4, 6, 7, 12, 14, 21, 28, 42, 84]
- d=336, a=239, multiset=[2, 3, 4, 4, 4, 7]
- d=336, a=281, multiset=[2, 2, 3, 4, 6, 6, 7, 8]
- d=336, a=295, multiset=[2, 2, 3, 4, 6, 6, 7, 8]
- d=360, a=19, multiset=[2, 2, 3, 4, 5, 6, 9, 10, 18, 20]
- d=360, a=179, multiset=[2, 2, 3, 4, 5, 6, 9, 10, 15, 18, 30, 45, 90]
- d=360, a=181, multiset=[2, 2, 3, 4, 5, 6, 9, 10, 15, 18, 30, 45, 90]
- d=360, a=341, multiset=[2, 2, 3, 4, 5, 6, 9, 10, 18, 20]
- d=480, a=31, multiset=[2, 3, 4, 4, 5, 8, 15, 16]
- d=480, a=49, multiset=[2, 2, 2, 2, 3, 4, 5, 6, 10, 10]
- d=480, a=209, multiset=[2, 2, 3, 4, 4, 4, 5]
- d=480, a=239, multiset=[2, 2, 3, 4, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120]
- d=480, a=241, multiset=[2, 2, 3, 4, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120]
- d=480, a=271, multiset=[2, 2, 3, 4, 4, 4, 5]
- d=480, a=431, multiset=[2, 2, 2, 2, 3, 4, 5, 6, 10, 10]
- d=480, a=449, multiset=[2, 3, 4, 4, 5, 8, 15, 16]
- d=504, a=251, multiset=[2, 2, 3, 4, 6, 7, 9, 14, 18, 21, 42, 63, 126]
- d=504, a=253, multiset=[2, 2, 3, 4, 6, 7, 9, 14, 18, 21, 42, 63, 126]
- d=540, a=161, multiset=[2, 3, 3, 3, 4, 5, 6]
- d=540, a=379, multiset=[2, 3, 3, 3, 4, 5, 6]
- d=600, a=251, multiset=[2, 2, 3, 4, 5, 5]
- d=600, a=299, multiset=[2, 2, 3, 4, 5, 6, 10, 15, 25, 30, 50, 75, 150]
- d=600, a=301, multiset=[2, 2, 3, 4, 5, 6, 10, 15, 25, 30, 50, 75, 150]
- d=600, a=349, multiset=[2, 2, 3, 4, 5, 5]

## Specific checks

### T = {2,3,4,6} occurrences (any d, from the tracked-d set)

None found among tracked d values (d in {12,15,24,30,36,60,105,210,420,1155}).

### 'two overlapping parts' sets like {2,3,5,6,15} at d in {30,60,90,105,210}

- d=60: T=[2, 3, 4, 5, 6] FAILS partition form (partition attempt=[[2, 3], [5]]), a values=[11, 19, 41, 49]

## Distinct T sets realized, for d in {12, 15, 24, 30, 36, 60, 105, 210, 420, 1155}

### d = 12

Prime powers of d: [4, 3]

Distinct T sets realized (2 total):

- T=[2, 3, 4]: a values=[5, 7] (count=2)
- T=[2, 3, 4, 6, 12]: a values=[1, 11] (count=2)

Partition-form partitions of d's prime powers: realized vs not realized as some T:

- partition(s) [[[2, 3]]] -> T=[2, 3, 4, 6, 12] : REALIZED
- partition(s) [[[2], [3]]] -> T=[2, 3, 4] : REALIZED

### d = 15

Prime powers of d: [3, 5]

Distinct T sets realized (2 total):

- T=[3, 5]: a values=[4, 11] (count=2)
- T=[3, 5, 15]: a values=[1, 14] (count=2)

Partition-form partitions of d's prime powers: realized vs not realized as some T:

- partition(s) [[[3, 5]]] -> T=[3, 5, 15] : REALIZED
- partition(s) [[[3], [5]]] -> T=[3, 5] : REALIZED

### d = 24

Prime powers of d: [8, 3]

Distinct T sets realized (1 total):

- T=[2, 3, 4, 6, 8, 12, 24]: a values=[1, 23] (count=2)

Partition-form partitions of d's prime powers: realized vs not realized as some T:

- partition(s) [[[2, 3]]] -> T=[2, 3, 4, 6, 8, 12, 24] : REALIZED
- partition(s) [[[2], [3]]] -> T=[2, 3, 4, 8] : not realized

### d = 30

Prime powers of d: [2, 3, 5]

Distinct T sets realized (2 total):

- T=[2, 3, 5]: a values=[11, 19] (count=2)
- T=[2, 3, 5, 6, 10, 15, 30]: a values=[1, 29] (count=2)

Partition-form partitions of d's prime powers: realized vs not realized as some T:

- partition(s) [[[2, 3, 5]]] -> T=[2, 3, 5, 6, 10, 15, 30] : REALIZED
- partition(s) [[[2], [3, 5]]] -> T=[2, 3, 5, 15] : not realized
- partition(s) [[[2, 3], [5]]] -> T=[2, 3, 5, 6] : not realized
- partition(s) [[[3], [2, 5]]] -> T=[2, 3, 5, 10] : not realized
- partition(s) [[[2], [3], [5]]] -> T=[2, 3, 5] : REALIZED

### d = 36

Prime powers of d: [4, 9]

Distinct T sets realized (2 total):

- T=[2, 3, 4, 6, 9, 12, 18, 36]: a values=[1, 35] (count=2)
- T=[2, 3, 4, 9]: a values=[17, 19] (count=2)

Partition-form partitions of d's prime powers: realized vs not realized as some T:

- partition(s) [[[2, 3]]] -> T=[2, 3, 4, 6, 9, 12, 18, 36] : REALIZED
- partition(s) [[[2], [3]]] -> T=[2, 3, 4, 9] : REALIZED

### d = 60

Prime powers of d: [4, 3, 5]

Distinct T sets realized (3 total):

- T=[2, 3, 4, 5, 6]: a values=[11, 19, 41, 49] (count=4)
- T=[2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60]: a values=[1, 59] (count=2)
- T=[2, 3, 4, 5, 15]: a values=[29, 31] (count=2)

Partition-form partitions of d's prime powers: realized vs not realized as some T:

- partition(s) [[[2, 3, 5]]] -> T=[2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60] : REALIZED
- partition(s) [[[2], [3, 5]]] -> T=[2, 3, 4, 5, 15] : REALIZED
- partition(s) [[[2, 3], [5]]] -> T=[2, 3, 4, 5, 6, 12] : not realized
- partition(s) [[[3], [2, 5]]] -> T=[2, 3, 4, 5, 10, 20] : not realized
- partition(s) [[[2], [3], [5]]] -> T=[2, 3, 4, 5] : not realized

### d = 105

Prime powers of d: [3, 5, 7]

Distinct T sets realized (1 total):

- T=[3, 5, 7, 15, 21, 35, 105]: a values=[1, 104] (count=2)

Partition-form partitions of d's prime powers: realized vs not realized as some T:

- partition(s) [[[3, 5, 7]]] -> T=[3, 5, 7, 15, 21, 35, 105] : REALIZED
- partition(s) [[[3], [5, 7]]] -> T=[3, 5, 7, 35] : not realized
- partition(s) [[[3, 5], [7]]] -> T=[3, 5, 7, 15] : not realized
- partition(s) [[[5], [3, 7]]] -> T=[3, 5, 7, 21] : not realized
- partition(s) [[[3], [5], [7]]] -> T=[3, 5, 7] : not realized

### d = 210

Prime powers of d: [2, 3, 5, 7]

Distinct T sets realized (1 total):

- T=[2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210]: a values=[1, 209] (count=2)

Partition-form partitions of d's prime powers: realized vs not realized as some T:

- partition(s) [[[2, 3, 5, 7]]] -> T=[2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210] : REALIZED
- partition(s) [[[2], [3, 5, 7]]] -> T=[2, 3, 5, 7, 15, 21, 35, 105] : not realized
- partition(s) [[[2, 3], [5, 7]]] -> T=[2, 3, 5, 6, 7, 35] : not realized
- partition(s) [[[3], [2, 5, 7]]] -> T=[2, 3, 5, 7, 10, 14, 35, 70] : not realized
- partition(s) [[[2], [3], [5, 7]]] -> T=[2, 3, 5, 7, 35] : not realized
- partition(s) [[[2, 3, 5], [7]]] -> T=[2, 3, 5, 6, 7, 10, 15, 30] : not realized
- partition(s) [[[3, 5], [2, 7]]] -> T=[2, 3, 5, 7, 14, 15] : not realized
- partition(s) [[[2], [3, 5], [7]]] -> T=[2, 3, 5, 7, 15] : not realized
- partition(s) [[[2, 5], [3, 7]]] -> T=[2, 3, 5, 7, 10, 21] : not realized
- partition(s) [[[5], [2, 3, 7]]] -> T=[2, 3, 5, 6, 7, 14, 21, 42] : not realized
- partition(s) [[[2], [5], [3, 7]]] -> T=[2, 3, 5, 7, 21] : not realized
- partition(s) [[[2, 3], [5], [7]]] -> T=[2, 3, 5, 6, 7] : not realized
- partition(s) [[[3], [2, 5], [7]]] -> T=[2, 3, 5, 7, 10] : not realized
- partition(s) [[[3], [5], [2, 7]]] -> T=[2, 3, 5, 7, 14] : not realized
- partition(s) [[[2], [3], [5], [7]]] -> T=[2, 3, 5, 7] : not realized

### d = 420

Prime powers of d: [4, 3, 5, 7]

Distinct T sets realized (4 total):

- T=[2, 3, 4, 5, 6, 7, 10, 12, 14, 15, 20, 21, 28, 30, 35, 42, 60, 70, 84, 105, 140, 210, 420]: a values=[1, 419] (count=2)
- T=[2, 3, 4, 5, 6, 7, 12]: a values=[71, 349] (count=2)
- T=[2, 3, 4, 5, 7, 14, 15]: a values=[29, 391] (count=2)
- T=[2, 3, 4, 5, 7, 15, 21, 35, 105]: a values=[209, 211] (count=2)

Partition-form partitions of d's prime powers: realized vs not realized as some T:

- partition(s) [[[2, 3, 5, 7]]] -> T=[2, 3, 4, 5, 6, 7, 10, 12, 14, 15, 20, 21, 28, 30, 35, 42, 60, 70, 84, 105, 140, 210, 420] : REALIZED
- partition(s) [[[2], [3, 5, 7]]] -> T=[2, 3, 4, 5, 7, 15, 21, 35, 105] : REALIZED
- partition(s) [[[2, 3], [5, 7]]] -> T=[2, 3, 4, 5, 6, 7, 12, 35] : not realized
- partition(s) [[[3], [2, 5, 7]]] -> T=[2, 3, 4, 5, 7, 10, 14, 20, 28, 35, 70, 140] : not realized
- partition(s) [[[2], [3], [5, 7]]] -> T=[2, 3, 4, 5, 7, 35] : not realized
- partition(s) [[[2, 3, 5], [7]]] -> T=[2, 3, 4, 5, 6, 7, 10, 12, 15, 20, 30, 60] : not realized
- partition(s) [[[3, 5], [2, 7]]] -> T=[2, 3, 4, 5, 7, 14, 15, 28] : not realized
- partition(s) [[[2], [3, 5], [7]]] -> T=[2, 3, 4, 5, 7, 15] : not realized
- partition(s) [[[2, 5], [3, 7]]] -> T=[2, 3, 4, 5, 7, 10, 20, 21] : not realized
- partition(s) [[[5], [2, 3, 7]]] -> T=[2, 3, 4, 5, 6, 7, 12, 14, 21, 28, 42, 84] : not realized
- partition(s) [[[2], [5], [3, 7]]] -> T=[2, 3, 4, 5, 7, 21] : not realized
- partition(s) [[[2, 3], [5], [7]]] -> T=[2, 3, 4, 5, 6, 7, 12] : REALIZED
- partition(s) [[[3], [2, 5], [7]]] -> T=[2, 3, 4, 5, 7, 10, 20] : not realized
- partition(s) [[[3], [5], [2, 7]]] -> T=[2, 3, 4, 5, 7, 14, 28] : not realized
- partition(s) [[[2], [3], [5], [7]]] -> T=[2, 3, 4, 5, 7] : not realized

### d = 1155

Prime powers of d: [3, 5, 7, 11]

Distinct T sets realized (2 total):

- T=[3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155]: a values=[1, 1154] (count=2)
- T=[3, 5, 7, 11, 33, 35]: a values=[34, 1121] (count=2)

Partition-form partitions of d's prime powers: realized vs not realized as some T:

- partition(s) [[[3, 5, 7, 11]]] -> T=[3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155] : REALIZED
- partition(s) [[[3], [5, 7, 11]]] -> T=[3, 5, 7, 11, 35, 55, 77, 385] : not realized
- partition(s) [[[3, 5], [7, 11]]] -> T=[3, 5, 7, 11, 15, 77] : not realized
- partition(s) [[[5], [3, 7, 11]]] -> T=[3, 5, 7, 11, 21, 33, 77, 231] : not realized
- partition(s) [[[3], [5], [7, 11]]] -> T=[3, 5, 7, 11, 77] : not realized
- partition(s) [[[3, 5, 7], [11]]] -> T=[3, 5, 7, 11, 15, 21, 35, 105] : not realized
- partition(s) [[[5, 7], [3, 11]]] -> T=[3, 5, 7, 11, 33, 35] : REALIZED
- partition(s) [[[3], [5, 7], [11]]] -> T=[3, 5, 7, 11, 35] : not realized
- partition(s) [[[3, 7], [5, 11]]] -> T=[3, 5, 7, 11, 21, 55] : not realized
- partition(s) [[[7], [3, 5, 11]]] -> T=[3, 5, 7, 11, 15, 33, 55, 165] : not realized
- partition(s) [[[3], [7], [5, 11]]] -> T=[3, 5, 7, 11, 55] : not realized
- partition(s) [[[3, 5], [7], [11]]] -> T=[3, 5, 7, 11, 15] : not realized
- partition(s) [[[5], [3, 7], [11]]] -> T=[3, 5, 7, 11, 21] : not realized
- partition(s) [[[5], [7], [3, 11]]] -> T=[3, 5, 7, 11, 33] : not realized
- partition(s) [[[3], [5], [7], [11]]] -> T=[3, 5, 7, 11] : not realized

## A_{d,m} tables: which a make Phi_m | S_{a/d}, for d in {12,15,21,24,30,35,36,45,60,105}

NOTE: these sets are computed over ALL coprime a (divisibility of S by Phi_m tested directly), including a whose S is NON-CYCLOTOMIC or ANOMALOUS-CYCLOTOMIC; they are therefore supersets of the exact-match cyclotomic data in the CSV.

### d = 12

- A_{12,2} = [1, 5, 7, 11]
- A_{12,3} = [1, 5, 7, 11]
- A_{12,4} = [1, 5, 7, 11]
- A_{12,6} = [1, 11]
- A_{12,12} = [1, 11]

### d = 15

- A_{15,3} = [1, 2, 4, 7, 8, 11, 13, 14]
- A_{15,5} = [1, 4, 11, 14]
- A_{15,15} = [1, 14]

### d = 21

- A_{21,3} = [1, 2, 4, 5, 8, 10, 11, 13, 16, 17, 19, 20]
- A_{21,7} = [1, 20]
- A_{21,21} = [1, 20]

### d = 24

- A_{24,2} = [1, 5, 7, 11, 13, 17, 19, 23]
- A_{24,3} = [1, 5, 7, 11, 13, 17, 19, 23]
- A_{24,4} = [1, 5, 7, 11, 13, 17, 19, 23]
- A_{24,6} = [1, 5, 11, 13, 19, 23]
- A_{24,8} = [1, 23]
- A_{24,12} = [1, 23]
- A_{24,24} = [1, 23]

### d = 30

- A_{30,2} = [1, 7, 11, 13, 17, 19, 23, 29]
- A_{30,3} = [1, 7, 11, 13, 17, 19, 23, 29]
- A_{30,5} = [1, 11, 19, 29]
- A_{30,6} = [1, 29]
- A_{30,10} = [1, 29]
- A_{30,15} = [1, 29]
- A_{30,30} = [1, 29]

### d = 35

- A_{35,5} = [1, 4, 6, 9, 11, 16, 19, 24, 26, 29, 31, 34]
- A_{35,7} = [1, 6, 29, 34]
- A_{35,35} = [1, 34]

### d = 36

- A_{36,2} = [1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35]
- A_{36,3} = [1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35]
- A_{36,4} = [1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35]
- A_{36,6} = [1, 5, 7, 29, 31, 35]
- A_{36,9} = [1, 17, 19, 35]
- A_{36,12} = [1, 35]
- A_{36,18} = [1, 35]
- A_{36,36} = [1, 35]

### d = 45

- A_{45,3} = [1, 2, 4, 7, 8, 11, 13, 14, 16, 17, 19, 22, 23, 26, 28, 29, 31, 32, 34, 37, 38, 41, 43, 44]
- A_{45,5} = [1, 4, 11, 14, 16, 19, 26, 29, 31, 34, 41, 44]
- A_{45,9} = [1, 44]
- A_{45,15} = [1, 44]
- A_{45,45} = [1, 44]

### d = 60

- A_{60,2} = [1, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59]
- A_{60,3} = [1, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59]
- A_{60,4} = [1, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59]
- A_{60,5} = [1, 11, 19, 29, 31, 41, 49, 59]
- A_{60,6} = [1, 11, 19, 41, 49, 59]
- A_{60,10} = [1, 59]
- A_{60,12} = [1, 59]
- A_{60,15} = [1, 29, 31, 59]
- A_{60,20} = [1, 59]
- A_{60,30} = [1, 59]
- A_{60,60} = [1, 59]

### d = 105

- A_{105,3} = [1, 2, 4, 8, 11, 13, 16, 17, 19, 22, 23, 26, 29, 31, 32, 34, 37, 38, 41, 43, 44, 46, 47, 52, 53, 58, 59, 61, 62, 64, 67, 68, 71, 73, 74, 76, 79, 82, 83, 86, 88, 89, 92, 94, 97, 101, 103, 104]
- A_{105,5} = [1, 4, 11, 16, 19, 26, 29, 31, 34, 41, 44, 46, 59, 61, 64, 71, 74, 76, 79, 86, 89, 94, 101, 104]
- A_{105,7} = [1, 8, 13, 92, 97, 104]
- A_{105,15} = [1, 104]
- A_{105,21} = [1, 104]
- A_{105,35} = [1, 104]
- A_{105,105} = [1, 104]

## Non-cyclotomic counts per d (only reported where > 0, for the full d list)

- d=5: 2 non-cyclotomic a values
- d=7: 4 non-cyclotomic a values
- d=9: 4 non-cyclotomic a values
- d=10: 2 non-cyclotomic a values
- d=11: 8 non-cyclotomic a values
- d=13: 10 non-cyclotomic a values
- d=14: 4 non-cyclotomic a values
- d=15: 4 non-cyclotomic a values
- d=16: 4 non-cyclotomic a values
- d=17: 14 non-cyclotomic a values
- d=18: 4 non-cyclotomic a values
- d=19: 16 non-cyclotomic a values
- d=20: 4 non-cyclotomic a values
- d=21: 10 non-cyclotomic a values
- d=22: 8 non-cyclotomic a values
- d=23: 20 non-cyclotomic a values
- d=25: 18 non-cyclotomic a values
- d=26: 10 non-cyclotomic a values
- d=27: 16 non-cyclotomic a values
- d=28: 8 non-cyclotomic a values
- d=29: 26 non-cyclotomic a values
- d=30: 4 non-cyclotomic a values
- d=31: 28 non-cyclotomic a values
- d=32: 12 non-cyclotomic a values
- d=33: 18 non-cyclotomic a values
- d=34: 14 non-cyclotomic a values
- d=35: 20 non-cyclotomic a values
- d=36: 8 non-cyclotomic a values
- d=37: 34 non-cyclotomic a values
- d=38: 16 non-cyclotomic a values
- d=39: 22 non-cyclotomic a values
- d=40: 8 non-cyclotomic a values
- d=41: 38 non-cyclotomic a values
- d=42: 10 non-cyclotomic a values
- d=43: 40 non-cyclotomic a values
- d=44: 16 non-cyclotomic a values
- d=45: 20 non-cyclotomic a values
- d=46: 20 non-cyclotomic a values
- d=47: 44 non-cyclotomic a values
- d=48: 8 non-cyclotomic a values
- d=49: 40 non-cyclotomic a values
- d=50: 18 non-cyclotomic a values
- d=51: 30 non-cyclotomic a values
- d=52: 20 non-cyclotomic a values
- d=53: 50 non-cyclotomic a values
- d=54: 16 non-cyclotomic a values
- d=55: 38 non-cyclotomic a values
- d=56: 20 non-cyclotomic a values
- d=57: 34 non-cyclotomic a values
- d=58: 26 non-cyclotomic a values
- d=59: 56 non-cyclotomic a values
- d=60: 8 non-cyclotomic a values
- d=61: 58 non-cyclotomic a values
- d=62: 28 non-cyclotomic a values
- d=63: 32 non-cyclotomic a values
- d=64: 28 non-cyclotomic a values
- d=65: 46 non-cyclotomic a values
- d=66: 18 non-cyclotomic a values
- d=67: 64 non-cyclotomic a values
- d=68: 28 non-cyclotomic a values
- d=69: 42 non-cyclotomic a values
- d=70: 22 non-cyclotomic a values
- d=71: 68 non-cyclotomic a values
- d=72: 18 non-cyclotomic a values
- d=73: 70 non-cyclotomic a values
- d=74: 34 non-cyclotomic a values
- d=75: 38 non-cyclotomic a values
- d=76: 32 non-cyclotomic a values
- d=77: 58 non-cyclotomic a values
- d=78: 22 non-cyclotomic a values
- d=79: 76 non-cyclotomic a values
- d=80: 24 non-cyclotomic a values
- d=81: 52 non-cyclotomic a values
- d=82: 38 non-cyclotomic a values
- d=83: 80 non-cyclotomic a values
- d=84: 18 non-cyclotomic a values
- d=85: 62 non-cyclotomic a values
- d=86: 40 non-cyclotomic a values
- d=87: 54 non-cyclotomic a values
- d=88: 36 non-cyclotomic a values
- d=89: 86 non-cyclotomic a values
- d=90: 20 non-cyclotomic a values
- d=91: 70 non-cyclotomic a values
- d=92: 40 non-cyclotomic a values
- d=93: 58 non-cyclotomic a values
- d=94: 44 non-cyclotomic a values
- d=95: 70 non-cyclotomic a values
- d=96: 26 non-cyclotomic a values
- d=97: 94 non-cyclotomic a values
- d=98: 40 non-cyclotomic a values
- d=99: 56 non-cyclotomic a values
- d=100: 36 non-cyclotomic a values
- d=101: 98 non-cyclotomic a values
- d=102: 30 non-cyclotomic a values
- d=103: 100 non-cyclotomic a values
- d=104: 44 non-cyclotomic a values
- d=105: 46 non-cyclotomic a values
- d=106: 50 non-cyclotomic a values
- d=107: 104 non-cyclotomic a values
- d=108: 32 non-cyclotomic a values
- d=109: 106 non-cyclotomic a values
- d=110: 38 non-cyclotomic a values
- d=111: 70 non-cyclotomic a values
- d=112: 42 non-cyclotomic a values
- d=113: 110 non-cyclotomic a values
- d=114: 34 non-cyclotomic a values
- d=115: 86 non-cyclotomic a values
- d=116: 52 non-cyclotomic a values
- d=117: 70 non-cyclotomic a values
- d=118: 56 non-cyclotomic a values
- d=119: 94 non-cyclotomic a values
- d=120: 18 non-cyclotomic a values
- d=121: 108 non-cyclotomic a values
- d=122: 58 non-cyclotomic a values
- d=123: 78 non-cyclotomic a values
- d=124: 56 non-cyclotomic a values
- d=125: 98 non-cyclotomic a values
- d=126: 34 non-cyclotomic a values
- d=127: 124 non-cyclotomic a values
- d=128: 60 non-cyclotomic a values
- d=129: 82 non-cyclotomic a values
- d=130: 46 non-cyclotomic a values
- d=131: 128 non-cyclotomic a values
- d=132: 36 non-cyclotomic a values
- d=133: 106 non-cyclotomic a values
- d=134: 64 non-cyclotomic a values
- d=135: 70 non-cyclotomic a values
- d=136: 60 non-cyclotomic a values
- d=137: 134 non-cyclotomic a values
- d=138: 42 non-cyclotomic a values
- d=139: 136 non-cyclotomic a values
- d=140: 42 non-cyclotomic a values
- d=141: 90 non-cyclotomic a values
- d=142: 68 non-cyclotomic a values
- d=143: 116 non-cyclotomic a values
- d=144: 42 non-cyclotomic a values
- d=145: 110 non-cyclotomic a values
- d=146: 70 non-cyclotomic a values
- d=147: 82 non-cyclotomic a values
- d=148: 68 non-cyclotomic a values
- d=149: 146 non-cyclotomic a values
- d=150: 38 non-cyclotomic a values
- d=151: 148 non-cyclotomic a values
- d=152: 68 non-cyclotomic a values
- d=153: 94 non-cyclotomic a values
- d=154: 58 non-cyclotomic a values
- d=155: 118 non-cyclotomic a values
- d=156: 44 non-cyclotomic a values
- d=157: 154 non-cyclotomic a values
- d=158: 76 non-cyclotomic a values
- d=159: 102 non-cyclotomic a values
- d=160: 58 non-cyclotomic a values
- d=161: 130 non-cyclotomic a values
- d=162: 52 non-cyclotomic a values
- d=163: 160 non-cyclotomic a values
- d=164: 76 non-cyclotomic a values
- d=165: 78 non-cyclotomic a values
- d=166: 80 non-cyclotomic a values
- d=167: 164 non-cyclotomic a values
- d=168: 40 non-cyclotomic a values
- d=169: 154 non-cyclotomic a values
- d=170: 62 non-cyclotomic a values
- d=171: 106 non-cyclotomic a values
- d=172: 80 non-cyclotomic a values
- d=173: 170 non-cyclotomic a values
- d=174: 54 non-cyclotomic a values
- d=175: 118 non-cyclotomic a values
- d=176: 76 non-cyclotomic a values
- d=177: 114 non-cyclotomic a values
- d=178: 86 non-cyclotomic a values
- d=179: 176 non-cyclotomic a values
- d=180: 42 non-cyclotomic a values
- d=181: 178 non-cyclotomic a values
- d=182: 70 non-cyclotomic a values
- d=183: 118 non-cyclotomic a values
- d=184: 84 non-cyclotomic a values
- d=185: 142 non-cyclotomic a values
- d=186: 58 non-cyclotomic a values
- d=187: 158 non-cyclotomic a values
- d=188: 88 non-cyclotomic a values
- d=189: 106 non-cyclotomic a values
- d=190: 70 non-cyclotomic a values
- d=191: 188 non-cyclotomic a values
- d=192: 60 non-cyclotomic a values
- d=193: 190 non-cyclotomic a values
- d=194: 94 non-cyclotomic a values
- d=195: 92 non-cyclotomic a values
- d=196: 80 non-cyclotomic a values
- d=197: 194 non-cyclotomic a values
- d=198: 58 non-cyclotomic a values
- d=199: 196 non-cyclotomic a values
- d=200: 76 non-cyclotomic a values
- d=201: 130 non-cyclotomic a values
- d=202: 98 non-cyclotomic a values
- d=203: 166 non-cyclotomic a values
- d=204: 60 non-cyclotomic a values
- d=205: 158 non-cyclotomic a values
- d=206: 100 non-cyclotomic a values
- d=207: 130 non-cyclotomic a values
- d=208: 92 non-cyclotomic a values
- d=209: 178 non-cyclotomic a values
- d=210: 42 non-cyclotomic a values
- d=211: 208 non-cyclotomic a values
- d=212: 100 non-cyclotomic a values
- d=213: 138 non-cyclotomic a values
- d=214: 104 non-cyclotomic a values
- d=215: 166 non-cyclotomic a values
- d=216: 68 non-cyclotomic a values
- d=217: 178 non-cyclotomic a values
- d=218: 106 non-cyclotomic a values
- d=219: 142 non-cyclotomic a values
- d=220: 74 non-cyclotomic a values
- d=221: 190 non-cyclotomic a values
- d=222: 70 non-cyclotomic a values
- d=223: 220 non-cyclotomic a values
- d=224: 90 non-cyclotomic a values
- d=225: 118 non-cyclotomic a values
- d=226: 110 non-cyclotomic a values
- d=227: 224 non-cyclotomic a values
- d=228: 68 non-cyclotomic a values
- d=229: 226 non-cyclotomic a values
- d=230: 86 non-cyclotomic a values
- d=231: 118 non-cyclotomic a values
- d=232: 108 non-cyclotomic a values
- d=233: 230 non-cyclotomic a values
- d=234: 70 non-cyclotomic a values
- d=235: 182 non-cyclotomic a values
- d=236: 112 non-cyclotomic a values
- d=237: 154 non-cyclotomic a values
- d=238: 94 non-cyclotomic a values
- d=239: 236 non-cyclotomic a values
- d=240: 50 non-cyclotomic a values
- d=252: 68 non-cyclotomic a values
- d=260: 92 non-cyclotomic a values
- d=264: 74 non-cyclotomic a values
- d=270: 70 non-cyclotomic a values
- d=280: 88 non-cyclotomic a values
- d=288: 88 non-cyclotomic a values
- d=300: 76 non-cyclotomic a values
- d=312: 90 non-cyclotomic a values
- d=315: 140 non-cyclotomic a values
- d=330: 78 non-cyclotomic a values
- d=336: 86 non-cyclotomic a values
- d=360: 90 non-cyclotomic a values
- d=420: 88 non-cyclotomic a values
- d=462: 118 non-cyclotomic a values
- d=480: 118 non-cyclotomic a values
- d=504: 136 non-cyclotomic a values
- d=510: 126 non-cyclotomic a values
- d=540: 138 non-cyclotomic a values
- d=546: 142 non-cyclotomic a values
- d=570: 142 non-cyclotomic a values
- d=600: 154 non-cyclotomic a values

