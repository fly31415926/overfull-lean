#!/usr/bin/env python3
"""Map exact palette-continuation sources, without claiming verification."""
import hashlib
import json
from pathlib import Path
import re
from update_native_reserve_manifest import erase_comments

ROOT = Path(__file__).resolve().parents[1]


def main():
    modules = []
    for path in sorted((ROOT / 'Overfull/ResidualPalette').glob('*.lean')):
        namespaces, declarations = [], []
        for number, line in enumerate(erase_comments(path.read_text()).splitlines(), 1):
            if match := re.match(r'^namespace\s+(\S+)\s*$', line):
                namespaces.append(match[1])
            elif match := re.match(r'^end\s+(\S+)\s*$', line):
                if not namespaces or namespaces[-1] != match[1]:
                    raise ValueError(f'Unmatched namespace at {path}:{number}')
                namespaces.pop()
            elif match := re.match(r'^(?:@\[[^]]+\]\s+)?(?:theorem|lemma)\s+([^\s(:{]+)', line):
                declarations.append({'name': '.'.join([*namespaces, match[1]]),
                                     'source_line': number})
        if namespaces:
            raise ValueError(f'Unclosed namespace in {path}')
        modules.append({'module': '.'.join(path.relative_to(ROOT).with_suffix('').parts),
                        'path': path.relative_to(ROOT).as_posix(),
                        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'public_theorem_count': len(declarations),
                        'public_proof_declarations': declarations})
    names = sorted(item['name'] for module in modules for item in module['public_proof_declarations'])
    if len(names) != len(set(names)):
        raise ValueError('Duplicate public proof in residual-palette source map')
    record = {
        'schema_version': 1, 'kind': 'supporting_continuation',
        'baseline_commit': '98c6b228a997fead863d05041f12799c93fac18b',
        'native_reserve_source_checkpoint': '964027f1a74cd68149033dc74f87846cabdf2eae',
        'numbered_assertions_completed': 0, 'main_theorem_verified': False,
        'scope': 'Actual native residual joining-degree bounds; retained robustness chosen before requested surplus error; bounded matching palettes with exact original-copy coverage, per-class cut parity, whole-class footprint and vertex-load bounds; prescribed singleton primary joining copies and protected grouping. Supporting progress toward Corollary 4.6. Internal exceptional completion, final robust completion, full residual factorization and the main theorem remain incomplete.',
        'review': 'docs/residual-palette-semantic-review.md',
        'proof_map': 'docs/residual-palette-verification.md',
        'module_count': len(modules), 'public_theorem_count': len(names),
        'modules': modules, 'required_proof_declarations': names,
    }
    (ROOT / 'docs/residual-palette-source.json').write_text(json.dumps(record, indent=2)+'\n')
    print(f'Mapped {len(modules)} modules and {len(names)} public theorem proofs; full verification remains required.')


if __name__ == '__main__':
    main()
