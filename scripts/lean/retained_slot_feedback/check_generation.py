#!/usr/bin/env python3
"""Check generated-source integrity, not mathematical truth (Lean does that)."""
from pathlib import Path
import hashlib,json,re
root=Path.cwd();manifest=json.loads((root/'retained-slot-generation.json').read_text())
if manifest['original_pin']!='1581d4cbdd69a0faf34b2089614fe2a814316a6a':
    raise SystemExit('Unexpected original source pin')
for record in manifest['generated']:
    source=root/(record['module'].replace('.','/')+'.lean')
    actual=hashlib.sha256(source.read_bytes()).hexdigest()
    if actual!=record['generated_sha256']:raise SystemExit('Generated source changed: '+str(source))
    text=source.read_text()
    for bad in [r'\bsorry\b',r'\badmit\b',r'^\s*axiom\s',r'\bnative_decide\b',r'\bunsafe\s',r'set_option\s+warningAsError\s+false']:
        if re.search(bad,text,re.M):raise SystemExit('Forbidden proof construct in '+str(source)+': '+bad)
base=root/'research/oai_434/Feedback'
terminal=(base/'Terminal.lean').read_text()
start=terminal.index('theorem terminal_certificate_half');end=terminal.index(':= by',start);sig=terminal[start:end]
if 'CertifiedBand' not in sig or '(1/2:' not in sig:raise SystemExit('Wrong analytic terminal signature')
if '3/4' in sig:raise SystemExit('Old floor leaked into terminal signature')
source=(base/'SourceFeedback.lean').read_text();start=source.index('theorem source_batch_plain_marked_fine_half')
end=source.index(':= by',start);sig=source[start:end]
if 'henergy' in sig or 'PositiveFineSourceInput' in sig:raise SystemExit('Source terminal assumes its energy supplier')
if '1+D.t/2' not in sig or 'F.physicalProduct selected u' not in sig:raise SystemExit('Changed actual source or lost retained width')
print('PASS generated-source integrity and declared target interfaces; mathematical validation remains Lean kernel checking.')
