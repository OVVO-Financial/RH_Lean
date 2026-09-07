#!/usr/bin/env python3
"""Rewrite tracker references out of a module before it is published.

The published package names the layer a statement refers to rather than the
number of the change that introduced it.  Wording already committed in the
export wins, so a resync does not churn lines that did not otherwise move.
"""
import json, pathlib, re

MEMORY = json.load(
    open(pathlib.Path(__file__).resolve().parent / 'scrub_memory.json', encoding='utf-8'))

# Lines where the tracker number was the only thing naming the layer, so the
# replacement has to supply a description rather than delete a qualifier.
MEMORY.update({
    '/-- Euler product of a chronological prime list, using the same factor as #540. -/':
        '/-- Euler product of a chronological prime list, using the canonical rough Euler factor. -/',
    '/-- Unit-atom support capacity left after #532 and after exposing the selected':
        '/-- Unit-atom support capacity left after the middle/top opposition and after exposing the selected',
})

N = r'#[0-9]{1,5}'

RULES = [
    # Heading and parenthetical tracker tags.
    (rf'\s*\((?:Issue|issue|PR|pr) {N}\)', ''),
    (rf'\((?:Issue|issue|PR|pr) {N}, ', '('),
    (rf'\s+in (?:Issue|issue) {N} and ', ' in '),
    (rf' (?:in|from) (?:Issue|issue) {N}\b', ''),
    # A determiner already introduces the noun; the tag adds nothing.
    (rf'\b(the|The|that|That|its|our|existing|same) (?:PR|Issue|issue) {N} ', r'\1 '),
    # Sentence-initial provenance.
    (rf'^(\s*(?:/-[-!]?\s*)?)(?:PR|Pull request) {N} ', r'\1An earlier layer '),
    (rf'(?<=[.:] )(?:PR|Pull request) {N} ', 'An earlier layer '),
    # "the #NNN thing" -> "the thing"; the number qualified a noun phrase.
    (rf'\b(the|The|a|A|an|An|one|One|every|Every|its|our|existing|canonical|Canonical|actual|strict|exact|factorized|complete|Complete|full|full|occupied|scaled) {N} ', r'\1 '),
    (rf'\*\*([A-Za-z][A-Za-z -]*?) {N} ', r'**\1 '),
    (rf'\*\*Terminal {N} ', '**Terminal '),
    # Multi-reference lists.
    (rf'{N} and {N}\b', 'earlier layers'),
    (rf'(?:by|in|from|of|needed by|used by|used in) {N} and {N}\b', 'by earlier layers'),
    (rf"{N}'s\b", 'its'),
    # Residual prepositional references.
    (rf'\b(by|in|from|of|to|with) {N}\b', r'\1 an earlier layer'),
    (rf'\bPR {N}\b', 'an earlier layer'),
    (rf'\b(?:Issue|issue) {N}\b', 'an earlier layer'),
    # Bare leading reference at the head of a continuation line.
    (rf'^(\s*)({N}) ', r'\1'),
    (rf' {N} ', ' '),
    (rf' {N}\b', ''),
    # Workspace name.
    (r'`RH_Lean`', 'this package'),
    (r'\bRH[_-]Lean\b', 'this package'),
]
# Pointers to files that only exist alongside the library are retargeted at the
# published package's own equivalents, so a reader is never sent to a path this
# repository does not ship.
RETARGET = [
    ('`scripts/CumulativeOthelloBoundary/frontier_capacity.py`',
     '`EMPIRICAL_DIAGNOSTICS.md`'),
    ('`RESEARCH_ROUTE_REGISTRY.md`', '`boundary/dead_lanes.json`'),
]

COMPILED = [(re.compile(p), r) for p, r in RULES]
REF = re.compile(r'(?:^|[^A-Za-z0-9_])#[0-9]{1,5}(?:[^0-9]|$)|RH[_-]Lean')


def scrub_line(line: str) -> str:
    for target, replacement in RETARGET:
        if target in line:
            line = line.replace(target, replacement)
    if not REF.search(line):
        return line
    if line in MEMORY:
        return MEMORY[line]
    out = line
    for pattern, repl in COMPILED:
        if not REF.search(out):
            break
        out = pattern.sub(repl, out)
    return out


def scrub(text: str) -> str:
    return '\n'.join(scrub_line(l) for l in text.split('\n'))
