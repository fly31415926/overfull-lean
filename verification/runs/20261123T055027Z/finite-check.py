"""Finite exact-arithmetic sanity check, not Lean verification."""
from itertools import combinations
from fractions import Fraction

cases = 0
subpools = 0
for k in range(1, 9):
    edges = range(k)
    weights = [Fraction(1, k) for _ in edges]
    scaled = [k*w for w in weights]
    assert sum(weights) == 1
    assert all(scaled[e] == 1 for e in edges)
    for a in range(k + 1):
        for tup in combinations(edges, a):
            pool = set(tup)
            capacity = sum(scaled[i] * len({i} & pool) for i in edges)
            assert capacity == len(pool)
            subpools += 1
    assert sum(scaled) == k
    cases += 1
print(f"PASS: {cases} parallel-copy models (k=1..8), {subpools} exact pool equalities")
print("For k>1 the common endpoint-pair pattern weight equals k, not one.")
print("This is finite rational arithmetic, not Lean checking.")
