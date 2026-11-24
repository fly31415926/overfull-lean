# Independent review of the exactly-two-odd four-core continuation

## Boundary and verdict

This review covers the final ten `Overfull/TerminalFourTwoOdd` source modules listed below. The reviewer did not author these modules; the reviewer authored the shared grouping and all-even continuation, and inspected this separate two-odd construction and the stock cut-safety, shore-factorization, and bounded-input interfaces it invokes. This is a semantic and evidence review, not a replacement for the complete project kernel audit.

**No mathematical scope gap was found.** The public `Overfull.four_two_odd_terminal_one_factorization` constructs a partition of the original simple host's actual edge-copy type into exactly its degree number of disjoint perfect matchings. Its hypotheses specify four disjoint covering robust cores with exactly two odd orders, original regularity and absence of overfull sets, positive density, nonnegative core error, and the linear bound `a + 1 ≤ ε*n`. All choices of tolerance and order threshold precede host data. There is no supplied residual coloring, assumed terminal conclusion, or forest-supply hypothesis in this branch.

## Mathematical chain checked

1. **Original joining pieces and uniform prefix.** The unrestricted four-label joining decomposition produces original primary/surplus matching pieces. The shared four-copy palette construction completes selected primary seeds together with every surplus piece, leaving exactly `h - rounds` original primary matchings. `FourTwoOddPrefix` records their exact surviving joining union, singleton cut at each odd core, and matching-cut parity at every core. The output robustness is chosen before the requested final tolerance and order threshold; the numerical bounds and original simple-host degree bound provide the eventual local error controls.
2. **Complete residual profile.** `RemainingProfile` indexes the actual surviving pieces and transports them injectively to the actual residual edge type. The union is the complete residual joining set. In particular, it is not reduced to the union of only the two odd cuts; even-to-even joining copies remain present. The retained odd cut counts and all four cut parities are transported using the proof that these original copies survive the prefix.
3. **Central geometry and matching cover.** The central graph retains the union of both even cores as distinct original vertices and contracts only the two odd shores to two apices. Injective core edge maps preserve both robust simple cores, their degrees, and their robustness. Original even-to-even edges remain retained central copies. `centralMatching_two_core_cover` covers every central copy outside the two retained core interiors. Each central matching covers both apices, remains a matching, and leaves even uncovered order in each retained even core.
4. **Central no-overfull certificate.** Whole-shore cuts are partitioned by the actual retained matching family. An odd whole shore has an odd cut in every matching, giving total cut size at least `k`. For an even whole shore, each matching contributes at most one incident crossing at a fixed vertex and an even total number of crossings, hence `2 * cutIncidence ≤ cutSize`. The regular cut-toggle identity gives cut size at least `k` after every one-vertex toggle. The existing robust small-cut classification then rules out every overfull set. This establishes the central no-overfull hypothesis before bounded-input factorization is invoked.
5. **Quantitative prerequisites.** The central proof explicitly supplies `τ ≤ α/10`, `a ≤ α*n/10`, the large-order robust threshold, and `k ≤ 2*n`; the last follows from the embedded simple core degree bound and small error. Its threshold also ensures `1 ≤ η*n/2`, so `a ≤ η*n/2` yields the required `a + 1 ≤ η*n`. The actual central order is no larger than the original order because both odd shores have positive order, so density and even-core size inequalities transport in the correct direction.
6. **Coloring and original-copy restoration.** Exact odd-cut size `k` follows from the disjoint complete matching cover and the singleton crossing of each odd cut. Existing shore factorization constructs both odd leaf colorings. The central and leaf colorings are aligned on their common original boundary copies and glued by the established original-copy theorem. `Completed` chooses the other two core indices exhaustively, factors the actual residual, and restores every completed prefix matching. The final coloring-to-factorization step constructs the requested perfect-matching family.

## Final compiler evidence

The genuine focused command was `lake build --wfail Overfull.TerminalFourTwoOdd.Theorem`, recorded in `development/twoodd-full-08`. Its child and wrapper exit codes are both zero, it completed 3,593 build jobs, and its recorded changed-input list is empty. All ten live source hashes below match the snapshots identified by that successful receipt. The command and terminal receipts are byte-identical, and the output hash was checked against the actual saved log. No additional Lean command was run for this review.

The reviewed fixes following the preliminary read were explicit casts, proof-irrelevant instance transports, dependent `Fin.cases` construction, unused-section-instance omissions, and heartbeat allowance. They preserve the mathematical statements and the construction described above.

The complete project audit and final preservation gate remain separate requirements; this focused pass does not certify the entire manuscript or publication.

Reviewed at UTC: 2026-11-24T21:50:52.870334+00:00

Successful command/terminal receipt SHA-256: `4bf022bfa12df31e1a4f35951bf65cddc8222ecf05218d167326a74681f1ef60`

Successful raw output SHA-256: `6b203dd4f29f2b195d480796b1fcc56611895f0cfeb75cfe83a4733adce1c929`

## Final source identities

| Source | SHA-256 |
|---|---|
| `Overfull/TerminalFourTwoOdd/CentralFactorization.lean` | `84bcb0a935a1ea655d849ec0df89b4f8953d761a1f68316bc22916b874b1458c` |
| `Overfull/TerminalFourTwoOdd/CentralGeometry.lean` | `dc136f6225c4b4a851a1754f47775735725acfaa670c7c42f9b7d2295513dbf6` |
| `Overfull/TerminalFourTwoOdd/CentralMatchings.lean` | `31d6b0d516c90f9d4a7f5849ab753d38bb810996713c479237fc009602d35ab1` |
| `Overfull/TerminalFourTwoOdd/Completed.lean` | `89ea5138e75e68acb660e25ae744c6777b240fa96c038385db3d107c58d97620` |
| `Overfull/TerminalFourTwoOdd/CutCertificates.lean` | `a0f0de1e95434f7b794380fde23d87b6a398d61288f15b3d0e347b55f7f07a1e` |
| `Overfull/TerminalFourTwoOdd/Prefix.lean` | `e320afc068fbd3072224a1e9167b3759b6a8dc0cb50a867724bfb93e50b7693c` |
| `Overfull/TerminalFourTwoOdd/PrefixResult.lean` | `250708b0e6a9331ea07c4e22a65a335adc4a44b7beef658b586444ff8f9af164` |
| `Overfull/TerminalFourTwoOdd/RemainingProfile.lean` | `f27fc2968bf5e8419a89507fb497bd17da380770c8a4824f4187e7d0643251fd` |
| `Overfull/TerminalFourTwoOdd/ResidualColoring.lean` | `a4d860e7aceebc916f6ce598a2bf95b6375f76b98737a8c0f882c19fb5051e0f` |
| `Overfull/TerminalFourTwoOdd/Theorem.lean` | `fb7f38593791c69eac49ccf44b02859d0f67a96501eed113f73986d92eb8a30b` |
