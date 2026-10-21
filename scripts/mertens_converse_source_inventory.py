#!/usr/bin/env python3
"""Bundle exact pinned mathematical sources for offline API inspection.

Read-only: no environment, credentials, .git objects or compiled binaries are
included. The archive is a development aid, not proof evidence.
"""
from pathlib import Path
import json
import re
import subprocess
import zipfile

root = Path(__file__).resolve().parents[1]
out = root / 'mertens-converse-sources.zip'
roots = [
    ('project', root, ['RHLean', 'research', 'scripts', '.github', 'docs']),
    ('mathlib', root / '.lake/packages/mathlib', ['Mathlib']),
    ('PrimeNumberTheoremAnd', root / '.lake/packages/PrimeNumberTheoremAnd', ['PrimeNumberTheoremAnd']),
]
count = 0
with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED, compresslevel=6) as archive:
    archive.writestr('source_manifest.json', json.dumps({
        'checkout_sha': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
        'dependencies': json.loads((root / 'lake-manifest.json').read_text()),
        'note': 'Pinned upstream sources; no repository compatibility patches are applied.'
    }, indent=2))
    for label, base, directories in roots:
        for directory in directories:
            for p in sorted((base / directory).rglob('*')):
                if p.is_file() and p.suffix in {'.lean', '.py', '.md', '.yml', '.toml'}:
                    archive.write(p, str(Path(label) / p.relative_to(base)))
                    count += 1
print(f'Bundled {count} mathematical source files ({out.stat().st_size} bytes).')
pattern = re.compile(r'^(?:private\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+(\S+)')
keywords = re.compile(r'Borel|caratheodory|log_deriv|LogDeriv|exists.*log|has.*log|Smooth1|MellinOfSmooth|Pull|rectangle|shift', re.I)
for label, base, directories in roots[2:]:
    for directory in directories:
        for p in sorted((base / directory).rglob('*.lean')):
            for i, line in enumerate(p.read_text().splitlines(), 1):
                match = pattern.match(line)
                if match and keywords.search(match.group(1)):
                    print(f'{label}/{p.relative_to(base)}:{i}: {line}')
