#!/usr/bin/env python3
"""Map exact three-core-terminal sources, without claiming verification."""
import hashlib
import json
from pathlib import Path
import re
from update_native_reserve_manifest import erase_comments

ROOT = Path(__file__).resolve().parents[1]


def main():
    modules = []
    for path in sorted(p for folder in ('Terminal',)
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
        raise ValueError('Duplicate public proof in three-core-terminal source map')
    record = {
        'schema_version': 1, 'kind': 'supporting_continuation',
        'baseline_commit': '0cf1c68c4daaeec9b879a03f1871eb64a0fa9640',
        'baseline_tree': '5d031253d02d0d0878422f8fbc367f04b812450c',
        'baseline_publication_status': 'published_exact_tree_and_both_refs_verified',
        'numbered_assertions_completed': 0, 'main_theorem_verified': False,
        'manuscript_number': '4.16',
        'verified_subcase': 'exactly_three_core_parts',
        'manuscript_label': 'three:prop:terminal',
        'statement_sha256': '1ba102e379594ab72de4ba73cf41c88d9fbdadf1c132e2943b48da04e8c2cc1c',
        'public_theorems': ['Overfull.three_core_terminal_factorization', 'Overfull.three_core_terminal_one_factorization'],
        'scope': 'Uniform terminal factorization for a simple regular graph of even order with no overfull set and exactly three disjoint covering robust core parts. Fixed positive ambient degree and part-order densities and robust parameters precede a common positive core-error tolerance and order threshold. Joining palettes, completed perfect-matching prefixes, residual cores, the simultaneous contraction of the two odd parts, and compatible leaf colorings are constructed from the original host hypotheses. The conclusion is a coloring and an exact partition of all original edge copies into the degree number of perfect matchings. This proves only the three-core subcase of Proposition 4.16; the four-core cases, full Proposition 4.16, and the main theorem remain unproved. Numbered coverage stays 48 of 69.',
        'review': 'docs/three-core-terminal-semantic-review.md',
        'proof_map': 'docs/three-core-terminal-verification.md',
        'module_count': len(modules), 'public_theorem_count': len(names),
        'modules': modules, 'required_proof_declarations': names,
    }
    (ROOT / 'docs/three-core-terminal-source.json').write_text(json.dumps(record, indent=2)+'\n')
    print(f'Mapped {len(modules)} modules and {len(names)} public theorem proofs; full verification remains required.')


if __name__ == '__main__':
    main()
