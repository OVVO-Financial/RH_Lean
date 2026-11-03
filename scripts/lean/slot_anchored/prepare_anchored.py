#!/usr/bin/env python3
"""Generate additive fixed-reference HIGH lemmas from pinned, unchanged sources.

The true Hecke supremum is never redefined. Only the contour/reference exponent
in fresh theorem copies is specialized to 7/8; external zero-free premises are
supplied by native_beta_le_seven_eighths. Generated sources must pass Lean and
the exact endpoint/live-dependency audits. No original proof file is changed.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

RH_PIN = '9cbfce5295343bcb411e6d2cb159b59995cd985b'
OAI_PIN = '1581d4cbdd69a0faf34b2089614fe2a814316a6a'
R, LE, BETA = chr(8477), chr(8804), chr(946)
AB, AC, LA, RA = chr(10216), chr(10217), chr(171), chr(187)
UPPER = 'OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_seven_eighths'
SPECS = [
 ('oai-upstream/lean/OAI/NumberTheory/DirichletL/PrimeRows/SmallTail.lean', 'VF919AnchoredSmallTail'),
 ('research/oai_434/VF919FiniteSlotReflectedGain.lean', 'VF919AnchoredPrincipalRemainder'),
 ('research/oai_434/VF919TiltedHighPrincipal.lean', 'VF919AnchoredHighPrincipal'),
 ('research/oai_434/VF919TiltedHighTails.lean', 'VF919AnchoredHighTails'),
 ('research/oai_434/VF919TiltedHighTransport.lean', 'VF919AnchoredHighTransport'),
 ('research/oai_434/VF919TiltedHighAssembly.lean', 'VF919AnchoredHighAssembly'),
]
DECL = re.compile(r'^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z_0-9\.]*)', re.M)

def blob_sha(b: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

def replace_once(s: str, old: str, new: str, label: str) -> str:
    n = s.count(old)
    if n != 1:
        raise ValueError(f'{label}: expected one occurrence, found {n}')
    return s.replace(old, new)

def imp(*names: str) -> str:
    return ''.join(f'import {LA}research.oai_434.{n}{RA}\n' for n in names)

def extract(s: str, start: str, end: str) -> str:
    if s.count(start) != 1 or s.count(end) != 1:
        raise ValueError('Namespace extraction markers were not unique')
    a = s.index(start)
    return s[a:s.index(end, a)+len(end)]

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repository', type=Path)
    root = ap.parse_args().repository.resolve()
    loaded = []
    for rel, name in SPECS:
        b = (root/rel).read_bytes()
        if rel.startswith('oai-upstream/'):
            git_root, pin, path = root/'oai-upstream', OAI_PIN, rel[len('oai-upstream/'):]
        else:
            git_root, pin, path = root, RH_PIN, rel
        expected = subprocess.check_output(['git', '-C', str(git_root), 'show', f'{pin}:{path}'])
        if b != expected:
            raise ValueError(f'Source drift: {rel}: {blob_sha(b)} != {blob_sha(expected)}')
        sha, s = blob_sha(b), b.decode('utf-8')
        if name == 'VF919AnchoredPrincipalRemainder':
            s = imp('VF919FiniteSlotReflectedGain')+'\nnamespace OAI\nnoncomputable section\nopen scoped Classical BigOperators\n'+extract(s,
                'namespace SevenEighths.ProbePrincipalRemainderBounds',
                'end SevenEighths.ProbePrincipalPhysical')+'\nend\nend OAI\n'
        elif name == 'VF919AnchoredHighPrincipal':
            s = imp('VF919TiltedHighPrincipal')+'\nnamespace OAI\nnoncomputable section\nopen scoped Classical BigOperators Topology ContDiff\n'+extract(s,
                'namespace SevenEighths.ProbePrincipalNormalized',
                'end SevenEighths.ProbePrincipalNormalized')+'\nend\nend OAI\n'
        loaded.append((rel, sha, name, s))
    mapping = {n: n+'_anchored' for _, _, _, s in loaded for n in DECL.findall(s)}
    if len(mapping) < 15:
        raise ValueError('Unexpected declaration inventory')
    pat = re.compile(r'(?<!\w)('+'|'.join(re.escape(n) for n in sorted(mapping, key=len, reverse=True))+r')(?!\w)')
    generated, provenance = [], []
    for rel, sha, name, s in loaded:
        if name == 'VF919AnchoredHighAssembly':
            old = (f'theorem fixed_tilted_high_bound (h{BETA} : (7/8:{R}){LE}HeckeZeroSupremum.beta)\n'
                   f'    (D : HighData (1/1000000:{R}))')
            new = (f'theorem fixed_tilted_high_bound (D : HighData (1/1000000:{R}))\n'
                   f'    (tilt : {R}) (htilt : 0{LE}tilt) (htiltCut : 24*tilt<D.t)')
            s = replace_once(s, old, new, 'generic fixed physical tilt')
            s = replace_once(s,
                f'obtain {AB}htilt,hcharge,htilt1,htiltCut,_{AC} := source_gain_budgets D',
                f'have h{BETA} : (7/8:{R}){LE}(7/8:{R}) := le_rfl', 'fixed reference comparison')
            if '(D.e/48)' not in s:
                raise ValueError('Old physical tilt not found')
            s = s.replace('(D.e/48)', 'tilt').replace('htilt.le', 'htilt')
        s = re.sub(r'\bHeckeZeroSupremum\.beta\b', f'(7/8:{R})', s)
        if name == 'VF919AnchoredSmallTail':
            s = replace_once(s, '(by linarith) le_rfl le_rfl S hS hmax hfirst',
                f'(by linarith) (by linarith only [he, {UPPER}]) le_rfl S hS hmax hfirst',
                'actual reciprocal bound on anchored small contour')
        elif name == 'VF919AnchoredHighTails':
            s = replace_once(s, "he he' (by linarith) le_rfl\n",
                f"he he' (by linarith) (by linarith only [he, {UPPER}])\n",
                'actual physical rows on anchored small contour')
        elif name == 'VF919AnchoredPrincipalRemainder':
            s = replace_once(s, '(by linarith only [he]) he (by linarith only [hehi])',
                f'(by linarith only [he, {UPPER}]) he (by linarith only [hehi])',
                'principal contour above actual supremum')
            s = replace_once(s, 'have heq := principal_physical_pool_ordered',
                f'have hbetaUpper := {UPPER}\n  have heq := principal_physical_pool_ordered',
                'physical residue decomposition above actual zeros')
        elif name == 'VF919AnchoredHighPrincipal':
            s = replace_once(s, 'obtain '+AB+'D,hD,hres'+AC+' := normalized_actual_window_residue_tilted',
                f'have hbetaUpper := {UPPER}\n  obtain '+AB+'D,hD,hres'+AC+' := normalized_actual_window_residue_tilted',
                'actual zero-free premise for normalized residue')
        s = pat.sub(lambda m: mapping[m[0]], s)
        imports = {
            'VF919AnchoredSmallTail': imp('VF919NativeSevenEighthsReplay'),
            'VF919AnchoredPrincipalRemainder': imp('VF919NativeSevenEighthsReplay'),
            'VF919AnchoredHighPrincipal': imp('VF919AnchoredPrincipalRemainder'),
            'VF919AnchoredHighTails': imp('VF919AnchoredSmallTail'),
            'VF919AnchoredHighTransport': imp('VF919AnchoredHighTails', 'VF919AnchoredHighPrincipal'),
            'VF919AnchoredHighAssembly': imp('VF919AnchoredHighTransport'),
        }[name]
        s = imports+f'/-! Generated from pinned {rel}; blob {sha}.\nThe true supremum remains unchanged; exact-head CI establishes proof status. -/\n'+s
        if re.search(r'\b(?:sorry|admit|axiom)\b', re.sub(r'/-.*?-/', '', s, flags=re.S)):
            raise ValueError('Proof placeholder in output')
        generated.append((name+'.lean', s))
        provenance.append({'source': rel, 'git_blob_sha': sha, 'output': name+'.lean'})
    dest = root/'research/oai_434'
    for name, s in generated:
        p = dest/name
        if p.exists() and p.read_text(encoding='utf-8') != s:
            raise FileExistsError(f'Refusing to overwrite different file: {p}')
    for name, s in generated:
        (dest/name).write_text(s, encoding='utf-8')
    result = {'status': 'GENERATED_NOT_VERIFIED', 'reference_ceiling': '7/8',
        'true_supremum_unchanged': True, 'source_pins': [RH_PIN, OAI_PIN],
        'sources': provenance, 'renamed_declarations': mapping,
        'outputs': [str(dest/name) for name, _ in generated]}
    (root/'anchored-tilt-generation.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
