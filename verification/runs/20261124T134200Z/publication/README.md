# Publication of the verified four-label checkpoint

The approved checkpoint's exact contents were published to both `main` and
`verified-bipartite-continuation-2026-11-21` in the public repository
`fly31415926/overfull-lean`.

| Identity | Value |
| --- | --- |
| Approved local checkpoint | `2188bd1233aa66e32195e743ac8b32f97a2bbec2` |
| Public proof commit | `c8e1796c4315596e8f161a1b20216ed983be382e` |
| Exact approved and public tree | `46dda25b581f227718eb3c32a6ee4e6d88d3116d` |
| Direct baseline parent | `3991bb7eee091a329046073e0366daa84a603e5d` |

The connected GitHub API creates its own commit metadata, so the public
commit identifier differs from the approved local identifier. Their complete
trees are identical: all 12,807 tracked paths, modes, and blob identities
are preserved. The raw approved local commit object and its verified Git
hash are retained under `authorized-resumption/approved-commit-object.txt`
and `approved-commit-identity.json` in that directory.

## Verification and independent readback

The complete strict build passed 3,874 jobs. The unchanged kernel audit
checked 14,627 declarations, including 367 new proofs across 28 modules.
All 14,260 previous declaration names, owners, and axiom sets, 2,609 previous
completed-result mappings, and 19 previous declaration maps are preserved.
The allowed axioms remain `propext`, `Classical.choice`, and `Quot.sound`.
Numbered coverage remains 49/69; the main theorem remains unverified.

Every one of the 87 content batches, nine large blobs, and 23 sequential
final-tree batches has a genuine successful response with its expected
hash. The final returned tree equals the approved tree above. The created
commit's tree and parent were read back before either branch was advanced.
Both branch updates used the inspected baseline head and `force: false`.

GitHub branch readbacks and a separate native Git fetch confirmed both
branches at the public proof commit. The fetched-object integrity check
verified all 826 frozen inputs, 17 controls, 25 archived outputs, and all
2,149 nonpublication run files. It performed 1,736 explicit digest checks;
all published and frozen bytes match. The exact receipts are under
`authorized-resumption/`, especially `published-proof-integrity.json`,
`native-proof-readback.json`, and `proof-publication-status.json`.

## Authorization and retained execution history

The user explicitly authorized checkpoint `2188bd1233aa66e32195e743ac8b32f97a2bbec2`
and its publication receipts, all project sources and documentation,
public/private/generated declaration maps, paths and hashes, frozen inputs
and outputs, development artifacts, genuine successful and failed logs,
and environment metadata, and both named branch updates.

The earlier automatic-review rejections and partial-upload responses are
preserved as historical evidence. The old `blocked-status.json` describes
that earlier state; the successful authorized resumption is recorded
separately and does not rewrite those events. An interrupted blob worker
returned no confirmed API result, so its state remains recorded as unknown.
Separate completed root uploads provide actual matching responses for all
nine required large objects. No denied action was bypassed; publication
resumed after the user's explicit authorization.

## Receipt archive

The publication-only follow-up archives the authorization, actual upload
responses, exact intermediate tree hashes, commit and branch responses,
GitHub and native-Git readbacks, and independent reviews. It changes only
files beneath this publication directory and preserves every mathematical
input and all frozen verification evidence.

This archive records the completed proof publication. Its own final commit
and branch readbacks are checked after the archive is published and reported
separately; no receipt claims to contain its own future publication response.
