# Continuation after full ordinary-core factorization

Historical record for the reconstructed checkpoint `b5afb03`. The subsequent
[three-vertex compatible-circuit proof](three-label-circuit-verification.md)
completes the selector and exact partition that were still open in this record.

The six recovered modules extend the completed ordinary-core theorem in
three directions. They construct the complete one-core branch of
Corollary 4.6 for at most three exterior vertices, factor terminal
one-core pieces under the recorded incidence hypotheses, and characterize
safe circuit deletion on at most three labels.

| Result | Public interface | Remaining wider obligation |
| --- | --- | --- |
| Core parity normalization | `Overfull.OrdinaryFactorization.exists_uniform_factorization_any_core_parity` | Requires the complement-coloring input specified by that theorem. |
| One-core bounded input | `Overfull.one_core_three_exception_one_factorization` | The distinct two-core branch of full Corollary 4.6. |
| Terminal one-core factorization | `Overfull.TerminalComplement.exists_uniform_terminal_one_factorization` | The preceding incidence construction and the other branches of full Lemma 4.4. |
| Three-label safe deletion | `Overfull.Multigraph.threeLabel_admissibleOn_sdiff_iff_tight_classes` | Existence and full decomposition into compatible circuits. |

The continuation adds no complete numbered assertion beyond full Lemma
4.2. The overall inventory is 47 of 69, with the main theorem and 21 other
numbered assertions still incomplete. The pinned statement hashes and
source scopes for 4.4 and 4.6 remain unchanged.

See the [source mapping](few-exception-source.json),
[semantic review](few-exception-semantic-review.md),
[declaration mapping](../verification/few-exception-declarations.json), and
[verification report](../verification/results.json).
