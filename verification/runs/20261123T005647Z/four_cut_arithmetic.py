#!/usr/bin/env python3
"""Finite arithmetic check only; NOT a Lean proof or graph realization."""
from itertools import product
cases = 0
for a,b,d,s in product(range(9), range(18), (0,2,4), (0,1)):
    if not (2*a <= b and b%2==0 and s <= a and s <= d and d <= b):
        continue
    cases += 1
    safe = (2*a+d <= b+2*s)
    tight = b == 2*a
    slack2 = b == 2*a+2
    criterion = (not tight or ((d != 2 or s >= 1) and d != 4)) and (not slack2 or d != 4 or s >= 1)
    if safe != criterion:
        raise SystemExit(f"COUNTEREXAMPLE: {(a,b,d,s)} safe={safe} criterion={criterion}")
print('PASS arithmetic-equivalence on',cases,'admissible local integer tuples with 0<=a<=8, 0<=b<=17, d in {0,2,4}, s in {0,1}; not kernel verification')
