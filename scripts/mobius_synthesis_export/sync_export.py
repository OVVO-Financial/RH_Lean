#!/usr/bin/env python3
"""Republish the Lean library into export_mobius_synthesis.

Every module is copied with tracker references rewritten, and the export root
is rebuilt so it imports exactly what the package ships.  Running this twice is
a no-op: wording already committed in the export is reused verbatim.
"""
import os, pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from scrub import scrub

SRC_ROOT = 'RHLean'
DST_PKG = 'export_mobius_synthesis'

added = changed = same = 0
for dirpath, dirnames, filenames in os.walk(SRC_ROOT):
    dirnames[:] = sorted(d for d in dirnames if d not in ('.lake', '.git'))
    for name in sorted(filenames):
        if not name.endswith('.lean'):
            continue
        src = os.path.join(dirpath, name)
        dst = os.path.join(DST_PKG, src)
        text = scrub(open(src, encoding='utf-8').read())
        if os.path.exists(dst):
            if open(dst, encoding='utf-8').read() == text:
                same += 1
                continue
            changed += 1
        else:
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            added += 1
        open(dst, 'w', encoding='utf-8').write(text)

# The root imports every shipped module, in the same order the library uses.
root = scrub(open('RHLean.lean', encoding='utf-8').read())
root_dst = os.path.join(DST_PKG, 'RHLean.lean')
root_changed = not (os.path.exists(root_dst)
                    and open(root_dst, encoding='utf-8').read() == root)
if root_changed:
    open(root_dst, 'w', encoding='utf-8').write(root)

# A module dropped upstream must not linger in the published tree.
shipped = set()
for dirpath, dirnames, filenames in os.walk(SRC_ROOT):
    dirnames[:] = [d for d in dirnames if d not in ('.lake', '.git')]
    shipped.update(os.path.join(dirpath, n) for n in filenames if n.endswith('.lean'))
stale = []
for dirpath, dirnames, filenames in os.walk(os.path.join(DST_PKG, SRC_ROOT)):
    dirnames[:] = [d for d in dirnames if d not in ('.lake', '.git')]
    for name in filenames:
        if not name.endswith('.lean'):
            continue
        path = os.path.join(dirpath, name)
        if os.path.relpath(path, DST_PKG) not in shipped:
            stale.append(path)
for path in stale:
    os.remove(path)

print(f'added {added}, updated {changed}, unchanged {same}, removed {len(stale)}')
print(f'root import list {"rewritten" if root_changed else "unchanged"}')
