#!/usr/bin/env python3
"""Index completed focused commands and their exact unchanged recorded files."""
import hashlib
import json
from pathlib import Path

RUN = Path(__file__).resolve().parent
files = {}
for path in sorted((RUN / 'development').rglob('*')):
    if path.is_file():
        data = path.read_bytes()
        files[path.relative_to(RUN).as_posix()] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
attempts = []
for path in sorted((RUN / 'development').glob('*/command.json')):
    command = json.loads(path.read_text())
    interrupted = command['exit_code'] is None and command['status'] == 'running'
    if interrupted:
        interruption = json.loads((path.parent / 'interruption.json').read_text())
        if not (interruption['status'] == 'interrupted' and interruption['child_exit_code'] is None
                and interruption['observed_tool_exit_code'] == interruption['observed_tool_result']['exit_code'] == 130
                and interruption['original_command_receipt_preserved'] is True):
            raise SystemExit('Unverified interruption: ' + path.parent.name)
    elif type(command['exit_code']) is not int or command['status'] not in {'passed', 'failed'}:
        raise SystemExit('Cannot freeze unfinished attempt: ' + path.parent.name)
    entry = {'attempt': path.parent.name, 'command': command['command'], 'exit_code': command['exit_code'],
             'status': 'interrupted' if interrupted else command['status'],
             'changed_inputs': command.get('inputs_changed_during_command')}
    if interrupted:
        entry['observed_tool_exit_code'] = interruption['observed_tool_exit_code']
    attempts.append(entry)
result = {'schema_version': 1, 'file_count': len(files), 'files': files, 'attempt_count': len(attempts),
          'attempts': attempts,
          'status_counts': {status: sum(a['status'] == status for a in attempts) for status in ['passed', 'failed', 'interrupted']}}
(RUN / 'development-index.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ['files', 'attempts']}, indent=2))
