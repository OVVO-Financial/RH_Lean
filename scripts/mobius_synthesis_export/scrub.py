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
    # A capitalized 'Post-' tag opens the phrase, so deleting it has to hand the
    # capital to the next word.
    '/-- **Post-#688 boundary normal form.**  The old cancelled packet is exactly the':
        '/-- **Boundary normal form.**  The old cancelled packet is exactly the',
    '/-! ## Post-#673 exact splice onto whole q^2 Mertens daughters -/':
        '/-! ## Exact splice onto whole q^2 Mertens daughters -/',
    # A reference used as the subject of its own clause has to leave a noun
    # behind, not a gap.
    '/-- #643/#645 combined with the multiplicity-free deep pushforward.  The old':
        '/-- An earlier layer combined with the multiplicity-free deep pushforward.  The old',
    'The universal three-vector inequality costs a factor `3`.  Because #665/#666':
        'The universal three-vector inequality costs a factor `3`.  Because earlier layers',
    # A span between two tags names the chain they bound, not two layers.
    'Every reduction from #596 to #602 runs in one direction: the terminal Mertens':
        'Every reduction in this chain runs in one direction: the terminal Mertens',
    # The reference is the object of the previous line's sentence, so the line
    # has to keep a noun where the number was.
    '#638.  A fixed least-owner physical channel transports the selected-prime field':
        'an earlier layer.  A fixed least-owner physical channel transports the selected-prime field',
})

N = r'#[0-9]{1,5}'

RULES = [
    # A pair or range of references still names one earlier layer collectively,
    # so collapse it before anything else and let the rules below read it as a
    # single tag.  Left whole, the first rule to fire would strip one number and
    # leave the other stranded behind its separator.
    (rf'{N}(?:/|--|-)({N})', r'\1'),
    # Heading and parenthetical tracker tags.
    (rf'\s*\((?:Issue|issue|PR|pr)? ?{N}\)', ''),
    (rf'\((?:Issue|issue|PR|pr) {N}, ', '('),
    (rf'\s+in (?:Issue|issue) {N} and ', ' in '),
    (rf' (?:in|from) (?:Issue|issue) {N}\b', ''),
    # 'post-' and 'pre-' mark where a statement sits relative to a layer.  The
    # pointer goes; 'pre-' keeps its sense as 'original'.
    (rf'\bpre-{N} ', 'original '),
    (rf'\bpost-{N} ?', ''),
    (rf'^(\s*/--\s+){N} ', r'\1'),
    # A determiner already introduces the noun; the tag adds nothing.
    (rf'\b(the|The|that|That|its|our|existing|same) (?:PR|Issue|issue) {N} ', r'\1 '),
    # Sentence-initial provenance.
    (rf'^(\s*(?:/-[-!]?\s*)?)(?:PR|Pull request) {N} ', r'\1An earlier layer '),
    # After sentence-ending punctuation, including a closing bold marker, the
    # tag really is the subject and has to be named.
    (rf'([.:]|\*\*)(\s+)(?:PR|Pull request)? ?{N} ', r'\1\2An earlier layer '),
    # "the #NNN thing" -> "the thing"; the number qualified a noun phrase.
    (rf'\b(the|The|a|A|an|An|one|One|every|Every|its|our|existing|canonical|Canonical|actual|strict|exact|factorized|complete|Complete|full|full|occupied|scaled) {N} ', r'\1 '),
    (rf'\*\*([A-Za-z][A-Za-z -]*?) {N} ', r'**\1 '),
    (rf'\*\*Terminal {N} ', '**Terminal '),
    # Multi-reference lists.
    (rf'{N} and {N}\b', 'earlier layers'),
    (rf'(?:by|in|from|of|needed by|used by|used in) {N} and {N}\b', 'by earlier layers'),
    (rf"{N}'s\b", 'its'),
    # Residual prepositional references.
    (rf'\b(by|in|from|of|to|with|after|After|before|Before|than|versus'
     rf'|through|via|against|beyond|under|onto|into) {N}\b',
     r'\1 an earlier layer'),
    (rf'\bmerged PR {N}\b', 'an earlier merged layer'),
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
    # Numerical diagnostics: the package records the measurement rather than
    # shipping the script that produced it.
    ('`scripts/CumulativeOthelloBoundary/frontier_capacity.py`',
     '`EMPIRICAL_DIAGNOSTICS.md`'),
    ('`scripts/FrozenSecondContactReassembly/second_contact_window_scale.py`',
     '`EMPIRICAL_DIAGNOSTICS.md`'),
    ('`scripts/far_four_diagnostic.py --q2-support`',
     '`EMPIRICAL_DIAGNOSTICS.md`'),
    ('`research/TWO_ANCHOR_SLACK_COVERAGE.md`', '`EMPIRICAL_DIAGNOSTICS.md`'),
    ('`research/OMEGA_PARITY_ORIENTATION.md`', '`EMPIRICAL_DIAGNOSTICS.md`'),
    ('`research/COMPRESSION_ESCAPE_DEFECT_NOGO.md`', '`EMPIRICAL_DIAGNOSTICS.md`'),
    # Closed routes live in the ledger that records why each one is closed.
    ('`RESEARCH_ROUTE_REGISTRY.md`', '`boundary/dead_lanes.json`'),
    # A pointer at a classical write-up becomes a description of the argument,
    # since the package carries the interface but not the prose.
    ('The mathematical proof in `research/K2_CENTERED_CLASSICAL_PROOF_COMPLETE.md` proves:',
     'The classical argument behind this interface proves:'),
]

COMPILED = [(re.compile(p), r) for p, r in RULES]
REF = re.compile(r'(?:^|[^A-Za-z0-9_])#[0-9]{1,5}(?:[^0-9]|$)|RH[_-]Lean')

# A tag that opens a line is ambiguous on its own: it can continue a noun phrase
# from the line above ("inside the / #643 reduced carrier"), where it is a
# qualifier to drop, or stand as a noun in its own right ("any completion of /
# #646 must identify"), where deleting it leaves a fragment. Only the previous
# line tells them apart.
LEADING_REF = re.compile(rf'^(\s*)({N}) ')
DANGLING = re.compile(
    r'\b(of|by|in|from|to|with|for|after|before|through|via|than|required by)$')


def scrub_line(line: str, prev: str = '') -> str:
    for target, replacement in RETARGET:
        if target in line:
            line = line.replace(target, replacement)
    if not REF.search(line):
        return line
    if line in MEMORY:
        return MEMORY[line]
    out = line
    lead = LEADING_REF.match(out)
    if lead:
        before = prev.rstrip()
        if not before:
            out = LEADING_REF.sub(r'\1An earlier layer ', out, count=1)
        elif DANGLING.search(before):
            out = LEADING_REF.sub(r'\1an earlier layer ', out, count=1)
    for pattern, repl in COMPILED:
        if not REF.search(out):
            break
        out = pattern.sub(repl, out)
    # A tag deleted at the end of a line would otherwise leave trailing space.
    return out.rstrip() if out != line else out


def scrub(text: str) -> str:
    lines = text.split('\n')
    return '\n'.join(
        scrub_line(line, lines[i - 1] if i else '') for i, line in enumerate(lines))
