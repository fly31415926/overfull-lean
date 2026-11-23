#!/usr/bin/env python3
"""Map exact exceptional-palette sources, without claiming verification."""
import hashlib
import json
from pathlib import Path
import re
from update_native_reserve_manifest import erase_comments

ROOT = Path(__file__).resolve().parents[1]


def main():
    modules = []
    for path in sorted((ROOT / 'Overfull/ExceptionalPalette').glob('*.lean')):
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
        raise ValueError('Duplicate public proof in exceptional-palette source map')
    record = {
        'schema_version': 1, 'kind': 'supporting_continuation',
        'baseline_commit': '1b5663a8fb472e42e698f4e09fcfc55497393815',
        'baseline_tree': 'ab2dd45502da57ea7dfb1db046a9efc9ab0cf067',
        'baseline_publication_status': 'blocked_by_automatic_approval_review',
        'numbered_assertions_completed': 0, 'main_theorem_verified': False,
        'scope': 'Internal exceptional-pair coloring with exact free palettes and prescribed actual copies; all-even joining palettes with prescribed empty reserve colors and uniform footprint bounds; extension of protected joining classes to surviving original reserve boundaries. These supporting constructions do not complete arbitrary exceptional-to-core incidences, final robust completion, full residual factorization, Corollary 4.6 or the main theorem.',
        'review': 'docs/exceptional-palette-semantic-review.md',
        'proof_map': 'docs/exceptional-palette-verification.md',
        'module_count': len(modules), 'public_theorem_count': len(names),
        'modules': modules, 'required_proof_declarations': names,
    }
    (ROOT / 'docs/exceptional-palette-source.json').write_text(json.dumps(record, indent=2)+'\n')
    print(f'Mapped {len(modules)} modules and {len(names)} public theorem proofs; full verification remains required.')


if __name__ == '__main__':
    main()
