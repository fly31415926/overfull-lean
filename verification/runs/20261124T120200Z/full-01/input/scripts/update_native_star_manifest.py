#!/usr/bin/env python3
"""Map exact native-star sources, without claiming verification."""
import hashlib
import json
from pathlib import Path
import re
from update_native_reserve_manifest import erase_comments

ROOT = Path(__file__).resolve().parents[1]


def main():
    modules = []
    for path in sorted((ROOT / 'Overfull/NativeStar').glob('*.lean')):
        namespaces, scopes, declarations = [], [], []
        for number, line in enumerate(erase_comments(path.read_text()).splitlines(), 1):
            if match := re.match(r'^namespace\s+(\S+)\s*$', line):
                namespaces.append(match[1])
                scopes.append(('namespace', match[1]))
            elif match := re.match(r'^section(?:\s+(\S+))?\s*$', line):
                scopes.append(('section', match[1]))
            elif match := re.match(r'^end(?:\s+(\S+))?\s*$', line):
                if not scopes or scopes[-1][1] != match[1]:
                    raise ValueError(f'Unmatched scope at {path}:{number}')
                kind, _ = scopes.pop()
                if kind == 'namespace':
                    namespaces.pop()
            elif match := re.match(r'^(?:@\[[^]]+\]\s+)?(?:theorem|lemma)\s+([^\s(:{]+)', line):
                declarations.append({'name': '.'.join([*namespaces, match[1]]),
                                     'source_line': number})
        if namespaces or scopes:
            raise ValueError(f'Unclosed scope in {path}')
        modules.append({'module': '.'.join(path.relative_to(ROOT).with_suffix('').parts),
                        'path': path.relative_to(ROOT).as_posix(),
                        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'public_theorem_count': len(declarations),
                        'public_proof_declarations': declarations})
    names = sorted(item['name'] for module in modules for item in module['public_proof_declarations'])
    if len(names) != len(set(names)):
        raise ValueError('Duplicate public proof in native-star source map')
    record = {
        'schema_version': 1, 'kind': 'supporting_continuation',
        'baseline_commit': 'af8dca22ef67d66d0de3f6d89954d31f06a4d2fa',
        'baseline_tree': '5ddefa9b77dfaf2d1cf09df1d7e2d4b541346a85',
        'baseline_publication_status': 'verified_local_publication_blocked_by_automatic_review_at_input_freeze',
        'numbered_assertions_completed': 0, 'main_theorem_verified': False,
        'scope': 'Actual reserved-copy injection into unpaired assigned stars, a disjoint joining/star/internal-exception incidence partition, native combined degree bounds, common internal-bundle coloring, exact remaining star copy/color balance, and endpoint-conflict Hall choice with sequential star accounting. These supporting results do not yet assemble the complete native weighted odd/even palette, all protected prescriptions and parity conditions into the full two-core Corollary 4.6, final robust factorization, or main theorem.',
        'review': 'docs/native-star-semantic-review.md',
        'proof_map': 'docs/native-star-verification.md',
        'module_count': len(modules), 'public_theorem_count': len(names),
        'modules': modules, 'required_proof_declarations': names,
    }
    (ROOT / 'docs/native-star-source.json').write_text(json.dumps(record, indent=2)+'\n')
    print(f'Mapped {len(modules)} modules and {len(names)} public theorem proofs; full verification remains required.')


if __name__ == '__main__':
    main()
