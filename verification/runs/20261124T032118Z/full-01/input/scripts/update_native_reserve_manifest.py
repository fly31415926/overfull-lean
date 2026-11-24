#!/usr/bin/env python3
"""Map native reserve sources; only the full Lean verifier verifies proofs.

Comments are erased while preserving line numbers, including nested Lean
block comments, so explanatory prose cannot become a theorem inventory.
"""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def erase_comments(source: str) -> str:
    out, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1
                out.extend('  ')
                i += 2
            elif source.startswith('-/', i):
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' ')
                i += 1
        elif quoted:
            char = source[i]
            out.append(char)
            i += 1
            if char == '\\' and i < len(source):
                out.append(source[i])
                i += 1
            elif char == '"':
                quoted = False
        elif source.startswith('/-', i):
            depth = 1
            out.extend('  ')
            i += 2
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n':
                out.append(' ')
                i += 1
        else:
            char = source[i]
            out.append(char)
            i += 1
            if char == '"':
                quoted = True
    if depth:
        raise ValueError('Unclosed Lean block comment')
    return ''.join(out)


def main() -> None:
    modules = []
    for path in sorted((ROOT / 'Overfull/NativeReserve').glob('*.lean')):
        namespaces, declarations = [], []
        for number, line in enumerate(erase_comments(path.read_text()).splitlines(), 1):
            if match := re.match(r'^namespace\s+(\S+)\s*$', line):
                namespaces.append(match[1])
            elif match := re.match(r'^end\s+(\S+)\s*$', line):
                if not namespaces or namespaces[-1] != match[1]:
                    raise ValueError(f'Unmatched named namespace at {path}:{number}')
                namespaces.pop()
            elif match := re.match(r'^(?:@\[[^]]+\]\s+)?(?:theorem|lemma)\s+([^\s(:{]+)', line):
                declarations.append({'name': '.'.join([*namespaces, match[1]]),
                                     'source_line': number})
        if namespaces:
            raise ValueError(f'Unclosed namespace in {path}')
        modules.append({
            'module': '.'.join(path.relative_to(ROOT).with_suffix('').parts),
            'path': path.relative_to(ROOT).as_posix(),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'public_theorem_count': len(declarations),
            'public_proof_declarations': declarations,
        })
    names = sorted(d['name'] for m in modules for d in m['public_proof_declarations'])
    if len(names) != len(set(names)):
        raise ValueError('Duplicate public proof name in the native reserve map')
    source = {
        'schema_version': 1,
        'kind': 'supporting_continuation',
        'baseline_commit': '98c6b228a997fead863d05041f12799c93fac18b',
        'numbered_assertions_completed': 0,
        'main_theorem_verified': False,
        'scope': 'Uniform original-host native two-core reserve completion: actual disjoint compressed reserves, rounded and protected native multiplicities, original-copy boundary realization, robust core completions, and an actual regular non-overfull residual retaining robust embedded cores. The surviving linear reserve and h-r margin are derived from original-host assumptions. Supporting progress toward Corollary 4.6; palette grouping, the full two-core factorization, and the main theorem remain incomplete.',
        'review': 'docs/native-reserve-semantic-review.md',
        'proof_map': 'docs/native-reserve-verification.md',
        'recovery_provenance': 'verification/runs/20261123T201422Z/recovery-provenance.md',
        'authorized_manuscript_excerpts': 'verification/runs/20261122T235931Z/authorized-manuscript-recovery.md',
        'module_count': len(modules),
        'public_theorem_count': len(names),
        'modules': modules,
        'required_proof_declarations': names,
    }
    (ROOT / 'docs/native-reserve-source.json').write_text(json.dumps(source, indent=2)+'\n')
    print(f'Mapped {len(modules)} modules and {len(names)} public theorem proofs; full verification remains required.')


if __name__ == '__main__':
    main()
