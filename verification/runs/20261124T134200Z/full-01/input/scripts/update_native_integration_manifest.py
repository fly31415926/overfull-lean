#!/usr/bin/env python3
"""Map exact native-integration sources, without claiming verification."""
import hashlib
import json
from pathlib import Path
import re
from update_native_reserve_manifest import erase_comments

ROOT = Path(__file__).resolve().parents[1]


def main():
    modules = []
    for path in sorted(p for folder in ('NativeWeighted', 'NativeAssembly', 'NativeCore')
                       for p in (ROOT / 'Overfull' / folder).glob('*.lean')):
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
        raise ValueError('Duplicate public proof in native-integration source map')
    record = {
        'schema_version': 1, 'kind': 'supporting_continuation',
        'baseline_commit': 'd2e7b1274d280ef6567cb2b562ec6e94eec2dda0',
        'baseline_tree': '9850008a20bfd828d8ab9da4c5e8d1bf50240570',
        'baseline_publication_status': 'verified_local_publication_blocked_by_automatic_review_at_input_freeze',
        'numbered_assertions_completed': 0, 'main_theorem_verified': False,
        'scope': 'Native weighted odd/even joining palettes derived from actual residual cores; complete paired and unpaired exceptional-copy assembly with exact selected reserve classes; original-core parity and whole-family load bounds; uniform completion of every nonprotected color, leaving a robust r/2-regular residual whose external copies are exactly the selected native reserve; and independent-exterior one-core factorization. These are supporting constructions; final protected-residual factorization and reassembly, full two-core Corollary 4.6, and the main theorem remain unproved.',
        'review': 'docs/native-integration-semantic-review.md',
        'proof_map': 'docs/native-integration-verification.md',
        'module_count': len(modules), 'public_theorem_count': len(names),
        'modules': modules, 'required_proof_declarations': names,
    }
    (ROOT / 'docs/native-integration-source.json').write_text(json.dumps(record, indent=2)+'\n')
    print(f'Mapped {len(modules)} modules and {len(names)} public theorem proofs; full verification remains required.')


if __name__ == '__main__':
    main()
