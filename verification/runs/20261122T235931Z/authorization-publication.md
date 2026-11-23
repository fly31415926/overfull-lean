# Authorized publication of the two reviewed documents

The user explicitly approved public release of these two documents by
answering **Yes** to the question recorded in
[authorization-publication.json](authorization-publication.json).

- [Recovered manuscript statements and relevant proof excerpts](authorized-manuscript-recovery.md)
- [Extended next-target assessment](authorized-next-target-assessment.md)

Both files are published byte-for-byte as reviewed. The release record
contains their exact byte counts and SHA-256 hashes. Their historical
references to withholding describe the earlier approval-review decision;
this later authorization permits their public release. The earlier
restriction, verification report, run record, and public pointer files
remain unchanged as historical evidence.

## Scope and verification

This is a document release. It adds no Lean source or theorem and claims
no new Lean build or axiom audit. Every existing repository file is retained.
The preceding source checkpoint remains the fully verified
`51c17b4936cf450fa86aa40e646328c8f01771f8`: its strict build passed 3,665 jobs
and its unchanged complete audit checked 11,727 declarations. All 494
recorded source hashes and 67 verification-input hashes remain applicable.
Numbered coverage remains 47 of 69; the main theorem remains incomplete.

The recovered statement blocks for 4.4, 4.5 and 4.6 were checked again
against the current pinned statement hashes and all matched. Identity of
the complete newer manuscript or its proof text is not asserted. The
recovered manuscript explains the source-specific continuation route;
mathematical arguments in these documents are distinguished from checked
Lean proofs. Continue with the repository's current handoff and these
released source documents.

## Corrected reproduction command

The byte-identical reviewed manuscript document contains an older command
naming `manuscript-recovery.md`, which remains the historical public stub.
Use the released filename below to check the actual recovered statements.
Run this from the repository root:

```sh
python3 - <<'PY_CHECK'
import hashlib, json, re
from pathlib import Path
p = Path('verification/runs/20261122T235931Z/authorized-manuscript-recovery.md')
expected = {a['number']: a['statement_sha256']
            for a in json.loads(Path('docs/coverage.json').read_text())['numbered_assertions']}
blocks = re.findall(r'## Exact statement (4\.[456])\n.*?```tex\n(.*?)\n```', p.read_text(), re.S)
assert len(blocks) == 3 and {n for n, _ in blocks} == {'4.4', '4.5', '4.6'}
for number, block in blocks:
    actual = hashlib.sha256(block.encode()).hexdigest()
    assert actual == expected[number], (number, actual)
    print(number, len(block.encode()), actual, 'MATCH')
PY_CHECK
```
