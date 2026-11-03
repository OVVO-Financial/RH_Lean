#!/usr/bin/env python3
"""Generate additive anchored HIGH modules from immutable source commits.

The actual HeckeZeroSupremum.beta declaration is never changed. The generated
lemmas use the already proved non-strict bound to choose fixed HIGH contours.
Generation is not proof acceptance: warning-fatal Lean and terminal audits
must separately succeed. Existing theorem files are not overwritten.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

SOURCE_PIN = '9cbfce5295343bcb411e6d2cb159b59995cd985b'
UPSTREAM_PIN = '1581d4cbdd69a0faf34b2089614fe2a814316a6a'
R = chr(8477)
LE = chr(8804)
BETA = chr(946)
AB = chr(10216)
AC = chr(10217)
LA = chr(171)
RA = chr(187)
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


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise ValueError(f'{label}: expected one occurrence, found {count}')
    return text.replace(old, new)


def imp(*names: str) -> str:
    return ''.join(f'import {LA}research.oai_434.{name}{RA}\n' for name in names)


def extract(text: str, start: str, end: str) -> str:
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError('Namespace extraction markers were not unique')
    first = text.index(start)
    last = text.index(end, first) + len(end)
    return text[first:last]


def read_pinned(root: Path, relative: str) -> tuple[str, str]:
    data = (root / relative).read_bytes()
    if relative.startswith('oai-upstream/'):
        gitroot, pin = root / 'oai-upstream', UPSTREAM_PIN
        gitpath = relative.removeprefix('oai-upstream/')
    else:
        gitroot, pin, gitpath = root, SOURCE_PIN, relative
    original = subprocess.check_output(['git', '-C', str(gitroot), 'show', f'{pin}:{gitpath}'])
    if data != original:
        raise ValueError(f'Source drift from {pin}: {relative}')
    return data.decode('utf-8'), blob_sha(original)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path)
    root = parser.parse_args().repository.resolve()
    loaded = []
    for relative, name in SPECS:
        text, sha = read_pinned(root, relative)
        if name == 'VF919AnchoredPrincipalRemainder':
            text = (imp('VF919FiniteSlotReflectedGain') +
                    '\nnamespace OAI\nnoncomputable section\nopen scoped Classical BigOperators\n' +
                    extract(text, 'namespace SevenEighths.ProbePrincipalRemainderBounds',
                            'end SevenEighths.ProbePrincipalPhysical') + '\nend\nend OAI\n')
        elif name == 'VF919AnchoredHighPrincipal':
            text = (imp('VF919TiltedHighPrincipal') +
                    '\nnamespace OAI\nnoncomputable section\nopen scoped Classical BigOperators Topology ContDiff\nopen Complex Filter MeasureTheory\n' +
                    extract(text, 'namespace SevenEighths.ProbePrincipalNormalized',
                            'end SevenEighths.ProbePrincipalNormalized') + '\nend\nend OAI\n')
        loaded.append((relative, sha, name, text))
    mapping = {name: name + '_anchored' for _, _, _, text in loaded for name in DECL.findall(text)}
    if len(mapping) < 15:
        raise ValueError('Unexpected declaration inventory')
    pattern = re.compile(r'(?<!\w)(' + '|'.join(re.escape(name) for name in sorted(mapping, key=len, reverse=True)) + r')(?!\w)')
    generated, provenance = [], []
    for relative, sha, name, text in loaded:
        if name == 'VF919AnchoredHighAssembly':
            old = (f'theorem fixed_tilted_high_bound (h{BETA} : (7/8:{R}){LE}HeckeZeroSupremum.beta)\n'
                   f'    (D : HighData (1/1000000:{R}))')
            new = (f'theorem fixed_tilted_high_bound (D : HighData (1/1000000:{R}))\n'
                   f'    (tilt : {R}) (htilt : 0{LE}tilt) (htiltCut : 24*tilt<D.t)')
            text = replace_once(text, old, new, 'generic fixed physical tilt')
            text = replace_once(text,
                f'obtain {AB}htilt,hcharge,htilt1,htiltCut,_{AC} := source_gain_budgets D',
                f'have h{BETA} : (7/8:{R}){LE}(7/8:{R}) := le_rfl',
                'fixed reference comparison')
            if '(D.e/48)' not in text:
                raise ValueError('Old physical tilt not found')
            text = text.replace('(D.e/48)', 'tilt').replace('htilt.le', 'htilt')
        # Only the exact real-coordinate reference changes in NEW lemmas.
        # The actual supremum declaration and beta_le_one remain untouched.
        text = re.sub(r'\bHeckeZeroSupremum\.beta\b', f'(7/8:{R})', text)
        if name == 'VF919AnchoredSmallTail':
            text = replace_once(text, 'Fin K→Finset PrimeIdeal',
                'Fin K→Finset HeckeInverseAmplification.PrimeIdeal',
                'pinned small-tail prime-ideal type')
            text = replace_once(text, '(by linarith) le_rfl le_rfl S hS hmax hfirst',
                f'(by linarith) (by linarith only [he, {UPPER}]) le_rfl S hS hmax hfirst',
                'actual reciprocal bound on anchored small contour')
            # This former lower-bound premise is now only reflexivity.
            text = text.replace(f'(h{BETA} :', f'(_h{BETA} :')
        elif name == 'VF919AnchoredHighTails':
            text = replace_once(text, 'open HeckeFamily HeckeInverseAmplification',
                'open Complex\nopen HeckeFamily HeckeInverseAmplification',
                'complex projection namespace for anchored HIGH tails')
            if text.count('∃j s,LFunction') != 2:
                raise ValueError('Unexpected complex zero-witness inventory')
            text = text.replace('∃j s,LFunction', '∃j, ∃s : ℂ,LFunction')
            if text.count('a≤s.re ∧ s.re<a+e ∧ |s.im|') != 2:
                raise ValueError('Unexpected complex projection inventory')
            text = text.replace('a≤s.re ∧ s.re<a+e ∧ |s.im|',
                'a≤Complex.re s ∧ Complex.re s<a+e ∧ |Complex.im s|')
            text = replace_once(text, "he he' (by linarith) le_rfl\n",
                f"he he' (by linarith) (by linarith only [he, {UPPER}])\n",
                'actual physical rows on anchored small contour')
        elif name == 'VF919AnchoredPrincipalRemainder':
            text = replace_once(text, '(by linarith only [he]) he (by linarith only [hehi])',
                f'(by linarith only [he, {UPPER}]) he (by linarith only [hehi])',
                'principal remainder contour above the true supremum')
            text = replace_once(text, 'have heq := principal_physical_pool_ordered',
                f'have hbetaUpper := {UPPER}\n  have heq := principal_physical_pool_ordered',
                'physical residue decomposition above actual zeros')
        elif name == 'VF919AnchoredHighPrincipal':
            text = replace_once(text,
                'obtain ' + AB + 'D,hD,hres' + AC + ' := normalized_actual_window_residue_tilted',
                f'have hbetaUpper := {UPPER}\n  obtain ' + AB + 'D,hD,hres' + AC + ' := normalized_actual_window_residue_tilted',
                'generic principal residue, true zero-free premise')
        elif name == 'VF919AnchoredHighTransport':
            text = text.replace('have hbetal :=', 'have _hbetal :=')
        # The imported native packages also expose mathlib's graph `≤s`
        # notation, which otherwise absorbs `a≤s.re` as a graph comparison.
        # Spacing must be fixed in EVERY generated theorem and its consumers.
        expected_zero_comparisons = {
            'VF919AnchoredHighTails': 0,
            'VF919AnchoredHighTransport': 3,
            'VF919AnchoredHighAssembly': 1,
        }.get(name, 0)
        if text.count('a≤s.re ∧') != expected_zero_comparisons:
            raise ValueError(f'{name}: unexpected real-zero comparison inventory')
        text = text.replace('a≤s.re ∧', 'a ≤ s.re ∧')
        # The token `≤saving` is parsed as mathlib's graph `≤s`
        # operator followed by "aving", not a real inequality.
        required_saving_comparisons = {
            'VF919AnchoredHighTransport': 2,
            'VF919AnchoredHighAssembly': 1,
        }.get(name, 0)
        if text.count('≤saving') != required_saving_comparisons:
            raise ValueError(f'{name}: unexpected saving comparison inventory')
        text = text.replace('≤saving', ' ≤ saving')
        # Native imports expose several letter-suffixed relation notations.
        # Separate ordinary comparisons from following identifier tokens.
        text = re.sub(r'([≤<≥>])(?=[^\\W\\d_])', r'\\1 ', text)
        text = pattern.sub(lambda match: mapping[match[0]], text)
        imports = {
            'VF919AnchoredSmallTail': imp('VF919NativeSevenEighthsReplay'),
            'VF919AnchoredPrincipalRemainder': imp('VF919NativeSevenEighthsReplay'),
            'VF919AnchoredHighPrincipal': imp('VF919AnchoredPrincipalRemainder'),
            'VF919AnchoredHighTails': imp('VF919AnchoredSmallTail'),
            'VF919AnchoredHighTransport': imp('VF919AnchoredHighTails', 'VF919AnchoredHighPrincipal'),
            'VF919AnchoredHighAssembly': imp('VF919AnchoredHighTransport'),
        }[name]
        # A module doc comment is a Lean command and would end the import
        # header before the original imports. This must be an ordinary comment.
        text = imports + f'/- Generated from {relative}; original blob {sha}.\nAcceptance requires warning-fatal Lean and the terminal audit. -/\n' + text
        if re.search(r'\b(?:sorry|admit|axiom)\b', re.sub(r'/-.*?-/', '', text, flags=re.S)):
            raise ValueError('Proof placeholder in output')
        generated.append((name + '.lean', text))
        provenance.append({'source': relative, 'git_blob_sha': sha, 'output': name + '.lean'})
    destination = root / 'research/oai_434'
    for name, text in generated:
        path = destination / name
        if path.exists() and path.read_text(encoding='utf-8') != text:
            raise FileExistsError(f'Refusing to overwrite different file: {path}')
    for name, text in generated:
        (destination / name).write_text(text, encoding='utf-8')
    result = {'status': 'GENERATED_NOT_VERIFIED', 'source_pin': SOURCE_PIN,
              'upstream_pin': UPSTREAM_PIN, 'reference_ceiling': '7/8',
              'true_supremum_unchanged': True, 'sources': provenance,
              'renamed_declarations': mapping,
              'outputs': [str(destination / name) for name, _ in generated]}
    (root / 'anchored-tilt-generation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
