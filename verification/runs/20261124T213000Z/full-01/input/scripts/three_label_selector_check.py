from collections import Counter
from itertools import combinations, product, permutations
import random


def graph(counts):
    return [p for p, m in zip(((0, 1), (0, 2), (1, 2)), counts) for _ in range(m)]


def incidence(E, v):
    return [i for i, p in enumerate(E) if v in p]


def admissible(E, cls, selected=None):
    if selected is None:
        selected = set(range(len(E)))
    for w in range(3):
        cut = [i for i in selected if w in E[i]]
        for v in range(3):
            counter = Counter(cls[v][i] for i in cut if v in E[i])
            if any(2 * s > len(cut) for s in counter.values()):
                return False
    return True


def coarse_classes(E, cls):
    result = []
    for v in range(3):
        inc = incidence(E, v)
        sizes = Counter(cls[v][i] for i in inc)
        tight = [c for c, n in sizes.items() if 2 * n == len(inc)]
        if tight:
            result.append({i: int(cls[v][i] == tight[0]) for i in inc})
        else:
            result.append(cls[v])
    return result


def compatible(E, cls, D):
    return all(len({cls[v][i] for i in D if v in E[i]}) ==
               sum(v in E[i] for i in D) for v in range(3))


def choose(E, cls):
    bundle = lambda a, b: [i for i, p in enumerate(E) if set(p) == {a, b}]
    coarse = coarse_classes(E, cls)
    order = next((a, b, c) for a, b, c in permutations(range(3))
                 if len(bundle(a, b)) >= len(bundle(a, c)) >= len(bundle(b, c)))
    a, b, c = order
    AB, AC, BC = bundle(a, b), bundle(a, c), bundle(b, c)
    x, y, z = len(AB), len(AC), len(BC)
    if x > z:
        counts = Counter(cls[a][i] for i in AB)
        tight = [k for k, s in counts.items() if 2 * s == x + z]
        class_a = (lambda i: cls[a][i] == tight[0]) if tight else coarse[a].__getitem__
        D = next((set((e, f)) for e, f in combinations(AB, 2)
                  if class_a(e) != class_a(f) and coarse[b][e] != coarse[b][f]), None)
        assert D is not None, ('unequal pair failure', E, cls, order, tight, coarse)
        return D, 'unequal_special' if tight else 'unequal_local'
    assert x > 0
    nonlocal_tight = []
    for v in range(3):
        for w in range(3):
            if v == w:
                continue
            counts = Counter(cls[v][i] for i in bundle(v, w))
            nonlocal_tight.extend((v, w, k) for k, s in counts.items() if 2 * s == 2 * x)
    if not nonlocal_tight:
        D = next((set((e, f)) for e, f in combinations(AB, 2)
                  if compatible(E, coarse, (e, f))), None)
        if D is not None:
            return D, 'equal_pair'
    D = next((set((e, f, g)) for e, f, g in product(AB, AC, BC)
              if compatible(E, coarse, (e, f, g))), None)
    assert D is not None, ('equal triangle failure', E, cls, coarse, nonlocal_tight)
    return D, 'equal_triangle_tight' if nonlocal_tight else 'equal_triangle_plain'


def random_classes(E, rng):
    result = []
    for v in range(3):
        inc = incidence(E, v)
        if rng.randrange(3) == 0 and len(inc) > 0:
            seq = [0] * (len(inc) // 2) + [1] * (len(inc) - len(inc) // 2)
            rng.shuffle(seq)
        else:
            colors = rng.choice([2, 3, 4, 5, max(1, len(inc))])
            seq = [rng.randrange(colors) for _ in inc]
        result.append(dict(zip(inc, seq)))
    return result


def partitions(n):
    if n == 0:
        yield ()
        return
    for p in partitions(n - 1):
        for c in range(2 + max(p, default=-1)):
            yield p + (c,)


def test(E, cls, stats):
    if not admissible(E, cls):
        return
    D, kind = choose(E, cls)
    assert compatible(E, cls, D), ('incompatible', E, cls, D)
    assert admissible(E, cls, set(range(len(E))) - D), ('unsafe', E, cls, D)
    stats[kind] += 1


def main():
    stats = Counter()
    graph_cases = 0
    for counts in product(range(4), repeat=3):
        if not sum(counts) or len({x % 2 for x in counts}) != 1:
            continue
        if max(counts) > 2:
            continue
        E = graph(counts)
        labels = []
        for v in range(3):
            inc = incidence(E, v)
            labels.append([dict(zip(inc, p)) for p in partitions(len(inc))
                           if all(2 * s <= len(inc) for s in Counter(p).values())])
        for cls in product(*labels):
            test(E, cls, stats)
        graph_cases += 1
    print('exhaustive_graph_cases', graph_cases)
    print('exhaustive_admissible_assignments', sum(stats.values()), dict(stats))
    random_stats = Counter()
    rng = random.Random(21645)
    for _ in range(300000):
        parity = rng.randrange(2)
        counts = tuple(2 * rng.randrange(6) + parity for _ in range(3))
        if not sum(counts):
            continue
        E = graph(counts)
        test(E, random_classes(E, rng), random_stats)
    print('random_admissible_assignments', sum(random_stats.values()), dict(random_stats))


if __name__ == '__main__':
    main()
