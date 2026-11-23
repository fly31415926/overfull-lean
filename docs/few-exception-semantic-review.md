# Semantic review of the recovered continuation

Historical record for the reconstructed checkpoint `b5afb03`. The subsequent
[three-vertex compatible-circuit proof](three-label-circuit-verification.md)
completes the selector and exact partition that were still open in this record.

All six continuation modules are recovered original bytes. Their fixed
source hashes and all 27 public proof names are recorded in
[`few-exception-source.json`](few-exception-source.json). Their current
imports are checked against the recreated ordinary-factorization closure
by the fresh strict build and the unchanged transitive axiom audit.

## One core and at most three exceptional vertices

`FewExceptions/Complement.lean` constructs the complement coloring from
the original degree, non-overfullness and exterior-cardinality hypotheses.
It does not take the desired coloring as an assumption. The sparse
coloring arguments account for all parallel copies and the actual
restrictions outside the distinguished core.

`OrdinaryFactorization/Parity.lean` handles either core parity by moving
one core vertex when needed and controlling the resulting error,
robustness and complement coloring. `FewExceptions/Factorization.lean`
combines these results with full ordinary-core factorization. Its public
host-normalized wrapper fixes the positive error and order threshold
before the finite host, regular degree and actual robust core. The final
wrapper partitions all original copies into perfect matchings.

This is the complete one-core branch of Corollary 4.6. The distinct
two-core branch remains incomplete, so no additional complete numbered
assertion is counted.

## Terminal one-core pieces

`TerminalComplement/Coloring.lean` proves complement colorability for the
recorded bounded exterior incidence situation, allowing one distinguished
apex exempt from the sparse exterior-incidence bound. `TerminalComplement/Factorization.lean`
combines that constructed input with the parity-normalized ordinary-core
result. The incidence conditions are genuine inputs of this terminal
stage. Their preceding construction in full Lemma 4.4 is not supplied by
these modules and is not claimed as complete.

## Safe three-label circuit deletion

`CompatibleCircuits/ThreeVertexDeletion.lean` proves that a circuit has
zero or two copies on each cut on at most three labels. It derives exact
equivalences between safe deletion and meeting the relevant tight
incidence classes. This is a deletion criterion. The general existence
and partition theorem for compatible circuits remains a separate proof
obligation.

The accompanying mathematical argument in
[`three-label-circuit-construction.md`](three-label-circuit-construction.md)
and finite Python checker are retained as supporting work. They are
explicitly separate from Lean verification and add no completed numbered
assertion.
