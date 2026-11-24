#!/usr/bin/env python3
"""Map exact weighted-palette sources, without claiming verification."""
import hashlib
import json
from pathlib import Path
import re
from update_native_reserve_manifest import erase_comments

ROOT = Path(__file__).resolve().parents[1]


def main():
    modules = []
    for path in sorted((ROOT / 'Overfull/WeightedPalette').glob('*.lean')):
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
        raise ValueError('Duplicate public proof in weighted-palette source map')
    record = {
        'schema_version': 1, 'kind': 'supporting_continuation',
        'baseline_commit': 'c28cec49522e1537452ee9fdc3b2baf3ca1cc3b2',
        'baseline_tree': '6a9e73eee4e944b104ff98630b04655e8bfb959d',
        'baseline_publication_status': 'published',
        'numbered_assertions_completed': 0, 'main_theorem_verified': False,
        'scope': 'Weighted palette extension preserving prescribed seeds and protected colors, resource-load and actual blocked-star-copy estimates, and finite Hall choice with asymmetric conflict bounds. These supporting constructions do not establish the exact remaining-star copy/free-color balance, complete actual exceptional-star assembly, native weighted wrappers, final robust factorization, full Corollary 4.6 or the main theorem.',
        'review': 'docs/weighted-palette-semantic-review.md',
        'proof_map': 'docs/weighted-palette-verification.md',
        'module_count': len(modules), 'public_theorem_count': len(names),
        'modules': modules, 'required_proof_declarations': names,
    }
    (ROOT / 'docs/weighted-palette-source.json').write_text(json.dumps(record, indent=2)+'\n')
    print(f'Mapped {len(modules)} modules and {len(names)} public theorem proofs; full verification remains required.')


if __name__ == '__main__':
    main()
