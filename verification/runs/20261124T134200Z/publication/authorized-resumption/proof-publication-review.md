# Independent proof-publication review

**Passed. The approved proof snapshot is public on both requested branches,
with no content discrepancy or publication blocker found.**

Fresh independent GitHub reads at `2026-11-24T14:57:53.243Z` returned:

| Item | Verified identity |
| --- | --- |
| `main` | `c8e1796c4315596e8f161a1b20216ed983be382e` |
| `verified-bipartite-continuation-2026-11-21` | `c8e1796c4315596e8f161a1b20216ed983be382e` |
| Public commit tree | `46dda25b581f227718eb3c32a6ee4e6d88d3116d` |
| Public commit parent | `3991bb7eee091a329046073e0366daa84a603e5d` |
| Approved local checkpoint | `2188bd1233aa66e32195e743ac8b32f97a2bbec2` |

The connector-created public commit has different author/committer metadata
and a different message from the approved local commit. Therefore its
commit hash is different. **The two commits have exactly the same tree and
parent.** Independent native Git comparison confirms that all **12,807 leaf
paths, file modes, and Git object identities** are identical. The preserved
raw local commit body also recomputes to the original approved hash.

## Raw receipt and hash-chain checks

The companion `proof-publication-review.json` contains the three fresh remote
responses and 146 successful independent checks. They establish that:

- All **87 content-upload** receipts and **9 large-blob** receipts report
  successful responses with their planned object hashes. The upload summary's
  96 receipt hashes match the actual receipt files.
- All **23 final-tree batches** form a continuous chain from baseline tree
  `6424bf81123aa75b2254aea7eceff6260611f397` to the exact approved tree. Their
  2,220 entries, request hashes, expected trees, and returned trees agree.
- Commit creation returned the stated public commit. Its subsequent raw
  readback agrees on tree, parent, and publication message.
- Both branch updates recorded the preceding verified baseline, targeted
  the public commit, used `force: false`, and returned success. Both stored
  branch readbacks and both fresh independent readbacks agree.
- The native fetch, `ls-remote`, and published-snapshot verification receipts
  all record exit 0. The integrity report matches its actual command output.

The interrupted blob worker is accurately recorded as having an unknown
remote execution outcome and no confirmed response. Its absence of a
response is not counted as success; separate confirmed upload receipts
supply the required blob identities.

## Published verification evidence

Independent recomputation of all **1,736 published digest checks** matches
the fetched Git blobs. The snapshot preserves all **826 frozen inputs**, **17
controls**, **25 archived outputs**, and **2,149 nonpublication run files**.
Exact tree equality also binds the complete snapshot to the preceding
independent approved-commit review.

The published receipts and logs retain the successful **3,874-job build**
and **14,627-declaration kernel audit**. The prior preservation result remains
unchanged: all 14,260 previous declaration owners and axiom sets, all 2,609
previous result mappings, and all 19 previous declaration maps are retained.
Numbered coverage remains **49/69**; the main theorem remains unverified.

No Lean build or audit was rerun. This review made no Git-ref, source,
frozen-control, or existing-evidence changes. Only this review and its JSON
companion were written.

This result concerns the published proof snapshot above. The later
authorization, upload, and review receipts are to be included in a separate
receipt-only follow-up, whose final branch readbacks remain a subsequent
step. This document does not represent that future commit as already public.
