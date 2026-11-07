#!/usr/bin/env python3
"""Compile all independent branches, fail unless the entire proof graph passes."""
from pathlib import Path
import json, os, re, subprocess

if os.environ.get('GITHUB_ACTIONS')!='true':
    raise SystemExit('This proof is compiled only in pinned GitHub Actions.')
root=Path.cwd();out=root/'.lake/build/lib/lean'
manifest=json.loads((root/'retained-slot-generation.json').read_text())
modules=['research.oai_434.RetainedSlotFeedback']+[
    'research.oai_434.Feedback.'+name for name in manifest['compile_order']]
failed=set();compiled=[];skipped=[]
with (root/'retained-slot-analytic.log').open('w') as log:
    def say(text):
        print(text,flush=True);log.write(text+'\n');log.flush()
    for module in modules:
        source=root/(module.replace('.','/')+'.lean')
        text=source.read_text()
        bad_imports=set(re.findall(r'^import (research\.oai_434\.\S+)',text,re.M)) & failed
        if bad_imports:
            failed.add(module);skipped.append(module)
            say('BLOCKED '+module+' by '+','.join(sorted(bad_imports)));continue
        if re.search(r'^[ \t]*(sorry|admit|axiom)\b',text,re.M):
            failed.add(module);say('REJECTED forbidden declaration '+module);continue
        dest=out/(module.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        say('Checking '+module)
        proc=subprocess.Popen(['lean','-DwarningAsError=true','-DmaxHeartbeats=4000000',
            '-o',str(dest),str(source.relative_to(root))],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        assert proc.stdout is not None
        for line in proc.stdout:say(line.rstrip('\n'))
        if proc.wait()!=0:
            failed.add(module);dest.unlink(missing_ok=True);say('FAILED '+module)
        else:compiled.append(module);say('COMPILED '+module)
    say(json.dumps({'compiled':compiled,'failed_or_blocked':sorted(failed),'blocked':skipped},indent=2))
if failed:raise SystemExit('Incomplete proof graph: '+str(len(failed))+' failed or blocked modules')
text=(root/'retained-slot-analytic.log').read_text()
checks=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
allowed={'propext','Classical.choice','Quot.sound'}
for target in [
    'OAI.SevenEighths.RetainedSlotFeedback.terminal_certificate_half',
    'OAI.SevenEighths.RetainedSlotDetector.source_batch_plain_marked_fine_half',
    'OAI.SevenEighths.RetainedSlotMoments.source_moments_half',
    'OAI.SevenEighths.RetainedSlotFiberCount.plain_marked_count_half',
    'OAI.SevenEighths.RetainedSlotApplications.original_source_fineness_preserved']:
    found=[a for n,a in checks if n==target]
    if len(found)!=1:raise SystemExit('Missing exact terminal axiom report: '+target)
    actual={a.strip() for a in found[0].split(',') if a.strip()}
    if not actual<=allowed:raise SystemExit('Disallowed terminal axioms: '+str(actual-allowed))
if 'sorryAx' in text or 'admitAx' in text:raise SystemExit('Admitted dependency')
print('PASS: generalized analytic band, all four source moments, literal marked count, and mesh reuse; permitted axioms only.')
print('No new global Mertens exponent is asserted by this audit.')
