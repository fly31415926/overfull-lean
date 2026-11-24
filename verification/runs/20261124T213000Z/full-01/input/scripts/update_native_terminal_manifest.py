#!/usr/bin/env python3
"""Map exact native-terminal sources, without claiming verification."""
import hashlib
import json
from pathlib import Path
import re
from update_native_reserve_manifest import erase_comments

ROOT = Path(__file__).resolve().parents[1]


def main():
    modules = []
    for path in sorted(p for folder in ('NativeTerminal',)
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
        raise ValueError('Duplicate public proof in native-terminal source map')
    record = {
        'schema_version': 1, 'kind': 'complete_assertion_source_mapping',
        'baseline_commit': 'f557ae03355f14a0441b37283f35186a95aca2d7',
        'baseline_tree': 'efe81e946e1ab2d97ac30c6f8103a4a773f3aa6d',
        'baseline_publication_status': 'verified_local_predecessor_publication_separately_recorded',
        'numbered_assertions_completed': 1, 'main_theorem_verified': False,
        'manuscript_number': '4.6',
        'manuscript_label': 'three:lem:bounded-input',
        'statement_sha256': '86700ed56e6cd9be513339e7c06b5af19d1d8cbe074fed3985ef21e5c9ad6e26',
        'public_theorems': ['Overfull.bounded_input_factorization', 'Overfull.bounded_input_one_factorization'],
        'scope': 'Complete Corollary 4.6 for even regular multigraphs with no overfull set and either one robust core with at most three exceptional vertices or two robust cores with at most two exceptional vertices. Fixed positive degree and core-order densities and robust parameters precede one common positive core-error tolerance and order threshold. The conclusion constructs a coloring and an exact partition of all original edge copies into k perfect matchings. No representative matching, reserve, complementary coloring or residual factorization is assumed. Full fixed-pattern Lemma 4.4, five-exception Corollary 4.5, terminal Proposition 4.16 and the main theorem remain unproved.',
        'review': 'docs/native-terminal-semantic-review.md',
        'proof_map': 'docs/native-terminal-verification.md',
        'module_count': len(modules), 'public_theorem_count': len(names),
        'modules': modules, 'required_proof_declarations': names,
    }
    (ROOT / 'docs/native-terminal-source.json').write_text(json.dumps(record, indent=2)+'\n')
    print(f'Mapped {len(modules)} modules and {len(names)} public theorem proofs; full verification remains required.')


if __name__ == '__main__':
    main()
