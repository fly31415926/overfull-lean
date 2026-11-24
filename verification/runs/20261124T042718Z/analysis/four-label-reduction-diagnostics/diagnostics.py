#!/usr/bin/env python3
"""Finite diagnostic checks for five proposed four-label reductions.

This is exploratory executable evidence, not a Lean proof, a kernel check,
or a numbered-assertion closure. It does not invoke Lean or modify any files.
All edges are distinct actual copies. All 16 vertex shores are enumerated.
Only classes containing an incidence at the tested vertex need enumeration:
every other class has class-cut cardinality zero and satisfies the inequality.
"""

from itertools import combinations
import json
import sys


VERTICES = (0, 1, 2, 3)


def require(condition, explanation):
    if not condition:
        raise AssertionError(explanation)


def instance(edges, classes=None):
    edges = dict(edges)
    incidence_keys = {(v, e) for e, ends in edges.items() for v in ends}
    require(all(len(ends) == 2 and ends[0] != ends[1]
                and set(ends) <= set(VERTICES) for ends in edges.values()),
            "Every actual copy must have two distinct endpoints in Fin 4")
    if classes is None:
        classes = {(v, e): f"singleton:{v}:{e}" for v, e in incidence_keys}
    require(set(classes) == incidence_keys,
            "Exactly the incident class assignments must be supplied")
    return {"edges": edges, "classes": dict(classes)}


def bundled(specification):
    return instance({f"{a}{b}_{i}": (a, b)
                     for a, b, count in specification for i in range(count)})


def restrict(G, selected):
    selected = set(selected)
    require(selected <= set(G["edges"]), "Restriction uses original actual copies")
    return instance({e: p for e, p in G["edges"].items() if e in selected},
                    {(v, e): k for (v, e), k in G["classes"].items()
                     if e in selected})


def degrees(G, selected=None):
    selected = set(G["edges"]) if selected is None else set(selected)
    return [sum(v in G["edges"][e] for e in selected) for v in VERTICES]


def shores():
    return [frozenset(v for v in VERTICES if mask & (1 << v))
            for mask in range(16)]


def local_classes(G, v):
    return sorted({G["classes"][v, e] for e, ends in G["edges"].items()
                   if v in ends})


def cut(G, shore):
    return sorted(e for e, (a, b) in G["edges"].items()
                  if (a in shore) != (b in shore))


def cut_record(G, shore, v, k):
    crossing = cut(G, shore)
    class_crossing = [e for e in crossing if v in G["edges"][e]
                      and G["classes"][v, e] == k]
    return {"shore": sorted(shore), "vertex": v, "class": k,
            "cut_copies": crossing, "cut_size": len(crossing),
            "class_cut_copies": class_crossing,
            "class_cut_size": len(class_crossing),
            "twice_class_cut_size": 2 * len(class_crossing),
            "slack": len(crossing) - 2 * len(class_crossing),
            "inequality_holds": 2 * len(class_crossing) <= len(crossing)}


def admissibility(G):
    checks = [cut_record(G, X, v, k) for X in shores() for v in VERTICES
              for k in local_classes(G, v)]
    bad = [row for row in checks if not row["inequality_holds"]]
    nontrivial = [row for row in checks if 0 < len(row["shore"]) < 4]
    return {"admissible": not bad, "shores_enumerated": 16,
            "inequalities_checked": len(checks), "violations": bad,
            "minimum_slack_on_nontrivial_shores":
                min((row["slack"] for row in nontrivial), default=None)}


def local_bounds(G):
    ds = degrees(G)
    rows = []
    for v in VERTICES:
        for k in local_classes(G, v):
            copies = sorted(e for e, ends in G["edges"].items()
                            if v in ends and G["classes"][v, e] == k)
            rows.append({"vertex": v, "class": k, "copies": copies,
                         "class_size": len(copies), "degree": ds[v],
                         "bound_holds": 2 * len(copies) <= ds[v]})
    return {"all_local_half_degree_bounds_hold": all(r["bound_holds"] for r in rows),
            "checks": rows}


def graph_report(G):
    ds = degrees(G)
    return {"vertices": list(VERTICES), "edge_copy_count": len(G["edges"]),
            "actual_copies": [{"copy": e, "endpoints": list(G["edges"][e])}
                              for e in sorted(G["edges"])],
            "degrees": ds, "all_degrees_even": all(d % 2 == 0 for d in ds),
            "admissibility": admissibility(G), "local_bounds": local_bounds(G)}


def compatibility(G, selected):
    selected = set(selected)
    bad = []
    for v in VERTICES:
        for k in local_classes(G, v):
            copies = sorted(e for e in selected if v in G["edges"][e]
                            and G["classes"][v, e] == k)
            if len(copies) > 1:
                bad.append({"vertex": v, "class": k, "copies": copies})
    return {"compatible": not bad, "violations": bad}


def is_circuit(G, selected):
    selected = set(selected)
    if not selected:
        return False
    support = set().union(*(set(G["edges"][e]) for e in selected))
    ds = degrees(G, selected)
    if any(ds[v] != 2 for v in support):
        return False
    # This directly checks Basic.IsCircuit's nonempty proper support cuts.
    for X in shores():
        if X and X < support:
            if not any((G["edges"][e][0] in X) != (G["edges"][e][1] in X)
                       for e in selected):
                return False
    return True


def partition_report(G, parts, selected=None):
    selected = set(G["edges"]) if selected is None else set(selected)
    parts = [set(part) for part in parts]
    rows = [{"copies": sorted(part), "is_circuit": is_circuit(G, part),
             "compatibility": compatibility(G, part)} for part in parts]
    disjoint = all(not (a & b) for a, b in combinations(parts, 2))
    covers = (set().union(*parts) if parts else set()) == selected
    valid = (disjoint and covers and all(r["is_circuit"]
             and r["compatibility"]["compatible"] for r in rows))
    return {"parts": rows, "pairwise_disjoint": disjoint,
            "covers_selected_copies": covers, "compatible_circuit_partition": valid}


def subsets(items):
    items = tuple(sorted(items))
    for size in range(len(items) + 1):
        yield from combinations(items, size)


def set_partitions(items):
    items = tuple(sorted(items))
    if not items:
        yield ()
        return
    first, rest = items[0], items[1:]
    for others in subsets(rest):
        part = (first,) + others
        remaining = tuple(e for e in rest if e not in others)
        for tail in set_partitions(remaining):
            yield (part,) + tail


def split(G, v, e, f, new_copy):
    require(e != f and v in G["edges"][e] and v in G["edges"][f],
            "The split selects two distinct copies incident with its center")
    a = next(w for w in G["edges"][e] if w != v)
    b = next(w for w in G["edges"][f] if w != v)
    require(a != b and new_copy not in G["edges"],
            "The split must be loopless and have a fresh copy identifier")
    H = restrict(G, set(G["edges"]) - {e, f})
    H["edges"][new_copy] = (a, b)
    H["classes"][a, new_copy] = G["classes"][a, e]
    H["classes"][b, new_copy] = G["classes"][b, f]
    H = instance(H["edges"], H["classes"])
    return H, {"center": v, "removed_copies": [e, f], "new_copy": new_copy,
               "new_endpoints": [a, b],
               "removed_classes_at_center": [G["classes"][v, e], G["classes"][v, f]],
               "removed_pair_has_distinct_classes_at_center":
                   G["classes"][v, e] != G["classes"][v, f],
               "endpoint_classes_inherited": True}


def example_a():
    G = bundled([(0, 1, 2), (0, 2, 2), (1, 3, 2), (2, 3, 2), (0, 3, 4)])
    for e, endpoints in G["edges"].items():
        if endpoints in [(1, 3), (2, 3)]:
            G["classes"][3, e] = "A"
    H, operation = split(G, 0, "01_0", "02_0", "12_split")
    before, after = graph_report(G), graph_report(H)
    old_cut = cut_record(G, {0, 3}, 3, "A")
    new_cut = cut_record(H, {0, 3}, 3, "A")
    require(before["admissibility"]["admissible"], "A: original must be admissible")
    require(operation["removed_pair_has_distinct_classes_at_center"], "A: compatible split pair")
    require(after["local_bounds"]["all_local_half_degree_bounds_hold"], "A: all local bounds survive")
    require(not after["admissibility"]["admissible"], "A: split must violate admissibility")
    require((old_cut["cut_size"], old_cut["class_cut_size"], old_cut["slack"]) == (8, 4, 0),
            "A: original specified cut is tight")
    require((new_cut["cut_size"], new_cut["class_cut_size"], new_cut["slack"]) == (6, 4, -2),
            "A: specified split cut must fail")
    return {"claim_tested": "A compatible split preserving every local bound need not preserve admissibility",
            "original": before, "split": operation, "split_graph": after,
            "specified_cut_before": old_cut, "specified_cut_after": new_cut}


def example_b():
    G = instance({"e": (0, 1), "g": (0, 1), "f": (0, 2), "h": (0, 2),
                  "p": (1, 2), "q": (1, 2), "r": (0, 3), "s": (0, 3)})
    for e in ["e", "g"]:
        G["classes"][0, e] = "A"
    for e in ["f", "h"]:
        G["classes"][0, e] = "B"
    H, operation = split(G, 0, "e", "f", "t")
    P = partition_report(H, [{"g", "h", "t"}, {"p", "q"}, {"r", "s"}])
    expanded = {"e", "f", "g", "h"}
    all_partitions = list(set_partitions(expanded))
    circuit_partitions = [partition_report(G, parts, expanded) for parts in all_partitions
                          if all(is_circuit(G, part) for part in parts)]
    original_witness = partition_report(G, [{"e", "f", "p"}, {"g", "h", "q"}, {"r", "s"}])
    require(admissibility(G)["admissible"] and admissibility(H)["admissible"],
            "B: both original and split graph must be admissible")
    require(P["compatible_circuit_partition"], "B: displayed split partition must be valid")
    require(not is_circuit(G, expanded), "B: expanded first part must not be a circuit")
    require(len(all_partitions) == 15 and len(circuit_partitions) == 1,
            "B: all set partitions must have exactly one circuit partition")
    require(not any(P["compatible_circuit_partition"] for P in circuit_partitions),
            "B: expanded first part must have no compatible circuit partition")
    require(original_witness["compatible_circuit_partition"],
            "B: the obstruction concerns partwise lifting, not original partition existence")
    return {"claim_tested": "Admissibility of a split does not guarantee partwise lifting of a supplied compatible partition",
            "original": graph_report(G), "split": operation, "split_graph": graph_report(H),
            "split_partition": P,
            "expanded_first_part": {"copies": sorted(expanded), "degrees": degrees(G, expanded),
                                    "is_circuit": is_circuit(G, expanded),
                                    "set_partitions_enumerated": len(all_partitions),
                                    "circuit_partitions": circuit_partitions,
                                    "compatible_circuit_partition_count": 0},
            "original_compatible_partition_rearranging_parts": original_witness}


def mixed_degree_graph():
    return bundled([(0, 1, 2), (0, 2, 2), (0, 3, 2), (1, 2, 1), (1, 3, 1), (2, 3, 1)])


def example_c():
    G = mixed_degree_graph()
    all_sets = list(subsets(G["edges"]))
    layers = [list(S) for S in all_sets if degrees(G, S) == [4, 4, 4, 4]]
    require(admissibility(G)["admissible"], "C: original singleton-class graph must be admissible")
    require(degrees(G) == [6, 4, 4, 4] and len(all_sets) == 512 and not layers,
            "C: no spanning four-regular actual-copy subgraph may exist")
    return {"claim_tested": "A mixed-degree admissible graph need not contain any spanning four-regular layer",
            "original": graph_report(G), "actual_copy_subsets_enumerated": len(all_sets),
            "spanning_four_regular_subgraphs": layers,
            "forced_residual_degrees_if_layer_existed": [2, 0, 0, 0],
            "explanation": "A loopless residual graph cannot have exactly one positive-degree vertex"}


def example_d():
    G = instance({"01a": (0, 1), "01b": (0, 1), "02": (0, 2), "03": (0, 3),
                  "12": (1, 2), "13": (1, 3), "23a": (2, 3), "23b": (2, 3)})
    groups = {0: [["01a", "01b"], ["02", "03"]],
              1: [["01a", "01b"], ["12", "13"]],
              2: [["02", "23a"], ["12", "23b"]],
              3: [["03", "23a"], ["13", "23b"]]}
    G = instance(G["edges"], {(v, e): f"class_{i}" for v, gs in groups.items()
                              for i, es in enumerate(gs) for e in es})
    all_sets = list(subsets(G["edges"]))
    factors = [{"copies": list(S), "compatibility": compatibility(G, S)}
               for S in all_sets if degrees(G, S) == [2, 2, 2, 2]]
    count_compatible = sum(F["compatibility"]["compatible"] for F in factors)
    witness = partition_report(G, [{"01a", "02", "12"}, {"01b", "03", "13"}, {"23a", "23b"}])
    require(admissibility(G)["admissible"] and degrees(G) == [4, 4, 4, 4],
            "D: original graph must be admissible and four-regular")
    require(len(factors) == 10 and count_compatible == 0,
            "D: exactly ten total and zero compatible spanning two-factors are required")
    require(witness["compatible_circuit_partition"], "D: displayed compatible circuit partition must exist")
    return {"claim_tested": "An admissible four-regular graph need not have a compatible spanning two-factor",
            "original": graph_report(G), "actual_copy_subsets_enumerated": len(all_sets),
            "spanning_two_factor_count": len(factors), "compatible_spanning_two_factor_count": count_compatible,
            "spanning_two_factors": factors, "compatible_circuit_partition": witness}


def example_e():
    G = mixed_degree_graph()
    G["classes"][0, "01_0"] = "A"
    G["classes"][0, "03_0"] = "A"
    D = {"01_1", "12_0", "23_0", "03_1"}
    R = restrict(G, set(G["edges"]) - D)
    original = graph_report(G)
    old_cut = cut_record(G, {0, 2}, 0, "A")
    deleted_cut = cut_record(restrict(G, D), {0, 2}, 0, "A")
    residual_cut = cut_record(R, {0, 2}, 0, "A")
    lhs = 2 * old_cut["class_cut_size"] + deleted_cut["cut_size"]
    rhs = old_cut["cut_size"] + 2 * deleted_cut["class_cut_size"]
    require(original["admissibility"]["admissible"], "E: original graph must be admissible")
    require(original["admissibility"]["minimum_slack_on_nontrivial_shores"] == 2,
            "E: no original nontrivial class-cut inequality is tight")
    require(is_circuit(G, D) and compatibility(G, D)["compatible"],
            "E: removed set must be a compatible four-cycle")
    require((old_cut["cut_size"], old_cut["class_cut_size"], old_cut["slack"]) == (6, 2, 2),
            "E: original specified inequality must have slack two")
    require((deleted_cut["cut_size"], deleted_cut["class_cut_size"]) == (4, 0),
            "E: cycle must cross four times while missing class A")
    require((residual_cut["cut_size"], residual_cut["class_cut_size"], residual_cut["slack"]) == (2, 2, -2),
            "E: residual specified inequality must fail")
    require(lhs > rhs and not admissibility(R)["admissible"],
            "E: exact deletion correction and residual admissibility must fail")
    return {"claim_tested": "Safe circuit deletion must track slack-two inequalities as well as tight ones",
            "original": original, "deleted_circuit": {"copies": sorted(D),
            "is_circuit": is_circuit(G, D), "compatibility": compatibility(G, D)},
            "residual": graph_report(R), "specified_cut_before": old_cut,
            "specified_cut_deleted": deleted_cut, "specified_cut_after": residual_cut,
            "exact_deletion_correction": {"left_2a_plus_d": lhs, "right_delta_plus_2b": rhs,
                                          "inequality_holds": lhs <= rhs}}


def main():
    result = {"evidence_kind": "finite exploratory Python diagnostic; not a Lean proof",
              "numbered_assertions_closed": 0, "lean_builds_performed": 0,
              "definitions_checked": {"degreeOn": "Number of selected incident actual copies",
                  "cutOn": "Actual copies with exactly one endpoint in the shore",
                  "classCutOn": "Crossing copies incident to the tested vertex with its tested class",
                  "AdmissibleOn": "For every vertex, class and shore: twice class-cut size <= cut size",
                  "Compatible": "No class occurs on two selected copies incident to one vertex",
                  "IsCircuit": "Nonempty; degree two on support; every nonempty proper support cut is nonempty"},
              "enumeration_scope": "All sixteen Fin 4 shores and all incidence classes present at each vertex; absent classes have count zero",
              "examples": {"A": example_a(), "B": example_b(), "C": example_c(),
                           "D": example_d(), "E": example_e()},
              "status": "all expected diagnostic outcomes observed"}
    json.dump(result, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
