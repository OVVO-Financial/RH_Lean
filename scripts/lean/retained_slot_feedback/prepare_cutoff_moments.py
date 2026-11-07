#!/usr/bin/env python3
"""Materialize the reviewed cutoff interface and record its source provenance."""

import argparse
import hashlib
import json
from pathlib import Path


def generate(root, upstream):
    base = upstream / 'OAI/NumberTheory/DirichletL'
    source_paths = [
        'Hecke/DetectorRawFiber.lean',
        'Hecke/DetectorRawBranches.lean',
        'PrimeRows/NonfloorMoments.lean',
        'Detector/FinalAssemblyCertifiedBands.lean',
    ]
    sources = {path: hashlib.sha256((base / path).read_bytes()).hexdigest()
               for path in source_paths}
    template = root / 'scripts/lean/retained_slot_feedback/CutoffMoments.lean'
    output = root / 'research/oai_434/Feedback/CutoffMoments.lean'
    output.write_bytes(template.read_bytes())
    manifest_path = root / 'retained-slot-generation.json'
    manifest = json.loads(manifest_path.read_text())
    if 'CutoffMoments' not in manifest['compile_order']:
        manifest['compile_order'].append('CutoffMoments')
    module = 'research.oai_434.Feedback.CutoffMoments'
    manifest['generated'] = [record for record in manifest['generated']
                             if record['module'] != module]
    manifest['generated'].append({
        'module': module,
        'original_module': 'OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands',
        'original_sha256': sources['Detector/FinalAssemblyCertifiedBands.lean'],
        'reviewed_source_sha256': sources,
        'generated_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
    })
    manifest_path.write_text(json.dumps(manifest, indent=2))
    print('Generated arbitrary-cutoff two-error source moments and three literal count consumers.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--upstream', type=Path)
    args = parser.parse_args()
    generate(args.root, args.upstream or args.root / 'oai-upstream/lean')
