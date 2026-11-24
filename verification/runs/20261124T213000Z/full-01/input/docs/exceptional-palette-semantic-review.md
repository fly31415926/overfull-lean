# Semantic review: exceptional palette extensions

This continuation starts from the exact local verified checkpoint
`1b5663a8fb472e42e698f4e09fcfc55497393815`, whose tree is
`ab2dd45502da57ea7dfb1db046a9efc9ab0cf067`. Its publication remained blocked
by automatic approval review. The new work preserves that candidate's
proofs, statement records, declaration mappings, and historical evidence.
It advances specific construction steps within the two-core branch of
Corollary 4.6. It does not complete another numbered assertion.

## 1. Empty reserve colors in the all-even case

The prior all-even joining theorem constructed an `h`-color palette but
did not leave a requested set of labels empty. That omission matters:
crossing-free reserve boundaries have no joining copy whose singleton
could identify their intended colors.

For a prescribed set `Q` of palette labels, the new proof constructs the
joining palette on `h-|Q|` colors, then transports it through an equivalence
with `Fin h \ Q`. It assigns the empty set to every label in `Q`.
The hypotheses pay for exactly these unavailable labels:

`6D+|Q|<h` and `nD ≤ 2L(h-6D-|Q|)`.

Matching, pairwise copy disjointness, exact joining-copy coverage, every
fiber's even cut parity, whole-class size, and vertex load are proved for
the transported palette. The original-assignment wrapper constructs the
required circuit decomposition from regularity, no overfull set, and
the stated all-even assigned-fiber parity. It assumes no coloring.

The uniform wrapper chooses the actual natural capacity
`L=(nD/2)/(h-6D-|Q|)+1`. Under the previously proved protected-budget
hypotheses, including `|Q|≤h/2`, `δ≤α/720`, `δ≤εα/720`, and `n≥12/ε`,
every complete class has at most `εn` support vertices. The size of an
individual circuit is not substituted for this whole-class bound.

## 2. Internal copies of a two-vertex exceptional fiber

Let the actual fiber of a label be `{x,y}`, with `x≠y`, and let its required
cut parity be even. Every joining class covers either both vertices or
neither. Consequently the two vertices have exactly the same free colors.
This follows from matching and cut parity; equal free palettes are not
assumed.

Each used color contributes exactly one joining incidence at `x`.
The disjoint palette covers every joining copy, so the number of used
colors is exactly the joining degree at `x`. Every other incidence at `x`
is an actual internal copy with endpoints `{x,y}`. Regularity
`d_H(x)=h` therefore implies that the number of these parallel copies is
exactly the number of free colors.

An injective prescribed assignment on a subset of the actual pair copies
extends to a bijection with the common free-color set. The seed hypotheses
require actual copy membership, distinct prescribed colors, and membership
in the common free palette. They describe the prescriptions that are to
be retained; they do not assume a coloring of the remaining pair copies.
An empty seed gives an unconditional extension from the preceding palette
and pair-fiber hypotheses.

One pair copy is inserted in each free color. This keeps every class a
matching, keeps different classes edge-disjoint, and covers exactly all
joining copies and all internal pair copies. Both exceptional vertices
are covered in every color. Each class gains at most one edge and two
support vertices. The support at every other vertex and every assigned
fiber cut are unchanged. The construction retains the identity of each
parallel copy and every valid prescribed assignment.

## 3. Whole reserved boundaries in protected colors

A singleton reserved crossing is only the joining portion of a compressed
boundary. The new insertion construction takes injectively indexed,
pairwise disjoint boundary matchings whose joining portions agree exactly
with the designated joining color classes. Replacing each designated class
by its boundary inserts only internal copies. It preserves the exact
joining portion of every class, every cut of a union of label fibers,
matching, and pairwise edge-copy disjointness.

The union after insertion is exactly the original joining-copy set union
the selected boundaries. The difference from the original joining set
is exactly the internal part of those boundaries. Classes retain the
bound `max(3L,b)` when each selected boundary has at most `b` copies;
their supports have at most `2 max(3L,b)` vertices.

The native application must establish the hypotheses in the actual
residual copy type. Original reserve membership alone does not identify
the parent boundary, and an original matching need not survive a deletion.
The residual transport and native construction retain the original
boundary index, injectivity, avoidance of deleted copies, and the exact
joining portion. Protected odd colors use their surviving crossing;
protected even colors have an empty joining portion.

## Scope and remaining work

The results above concern actual finite edge-copy sets. They do not use
an assumed residual edge-coloring, final factorization, or a new logical
axiom. The global count remains **47 complete assertions out of 69**.
Corollary 4.6 and the main theorem remain unproved.

The pair-fiber step concerns the optional two-vertex pair component.
Exceptional vertices assigned to the old cores still require a separate
coloring construction. Small joining-class support and small vertex load
alone do not establish the needed assignment of all parallel star copies
to free colors: multiplying the support bound by the maximum parallel
multiplicity can exceed the available palette. The next step must derive
appropriate weighted compatibility or provide a valid recoloring argument.

Likewise, even uncovered order on an assigned fiber does not imply even
uncovered order on the old core until its assigned exceptions are covered
in that color. Native protected boundaries have their own old-core parity
certificate; extending the remaining colors is a separate obligation.
The full robust matching completions, final residual factorization, and
restoration of the previously removed perfect matchings remain to be
composed under their actual hypotheses.

## Verification standard

Strict compilation of an individual module is a development check.
Verified checkpoint status requires the complete `scripts/verify.py` run,
the unchanged `Audit.lean`, every prior declaration and axiom mapping,
source and input hashes, and the supplementary preservation checker.
The run report records actual exit codes and keeps failed attempts.
Publication status is recorded separately from local proof verification.
