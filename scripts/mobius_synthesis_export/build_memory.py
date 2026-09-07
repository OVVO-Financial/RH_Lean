#!/usr/bin/env python3
"""Harvest the scrub wording already committed in the export.

Each published module rewrites tracker references into prose naming the layer
they refer to.  Recording those rewrites keeps a resync byte-stable on lines
that did not otherwise change.
"""
import difflib, json, os, pathlib, re

REF = re.compile(r'(?:^|[^A-Za-z0-9_])#[0-9]{1,5}(?:[^0-9]|$)|RH[_-]Lean')
memory = {}
for dirpath, dirnames, filenames in os.walk('RHLean'):
    dirnames[:] = [d for d in dirnames if d not in ('.lake', '.git')]
    for name in filenames:
        if not name.endswith('.lean'):
            continue
        src = os.path.join(dirpath, name)
        dst = os.path.join('export_mobius_synthesis', src)
        if not os.path.exists(dst):
            continue
        a = open(src, encoding='utf-8').read().splitlines()
        b = open(dst, encoding='utf-8').read().splitlines()
        sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag != 'replace' or (i2 - i1) != (j2 - j1):
                continue
            for k in range(i2 - i1):
                oa, ob = a[i1 + k], b[j1 + k]
                if REF.search(oa) and not REF.search(ob):
                    memory[oa] = ob
here = pathlib.Path(__file__).resolve().parent
json.dump(memory, open(here / 'scrub_memory.json', 'w', encoding='utf-8'), indent=1,
          ensure_ascii=False)
print(f'{len(memory)} memorized scrub lines')
