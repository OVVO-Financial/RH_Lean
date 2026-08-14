#!/usr/bin/env python3
"""Verify that every published export tree is a buildable standalone Lake project.

Two structural failure modes are checked for every export:

  * an export root imports a module it does not ship, so ``lake build RHLean
    --wfail`` would fail on a missing file rather than on mathematics;
  * an export ships a module unreachable from its own root, which is dead weight
    in a published repository.

Each export is checked on its own terms. Exported source files are not required
to remain byte-identical to files elsewhere in this repository: a standalone
package owns its own documentation, comments, source map, and publication
history once exported.

Run from the repository root::

    python3 scripts/check_export_sync.py
"""
from __future__ import annotations

import os
import re
import sys

IMPORT_RE = re.compile(r'^\s*import\s+([A-Za-z0-9_.]+)', re.M)
ROOT_MODULE = 'RHLean'

# (label, package directory, repo-local modules)
#
# Repo-local modules are shipped in a published repository and reached by that
# repository's own tooling rather than necessarily by its root module, so they
# are exempt from the unreachable-module check.
EXPORTS = [
    ('export_mobius_synthesis', 'export_mobius_synthesis',
     {'RHLean.Analysis.MobiusSynthesisBoundary'}),
    ('export_square_block', 'export_square_block/lean', set()),
    ('export_prime_wheel', 'export_prime_wheel/formalization', set()),
]


def module_map(package_dir: str) -> dict[str, str]:
    """Map ``RHLean.Foo.Bar`` to its file path within a Lake package."""
    found = {}
    for dirpath, dirnames, filenames in os.walk(package_dir):
        dirnames[:] = [d for d in dirnames if d not in ('.lake', '.git')]
        for name in filenames:
            if not name.endswith('.lean'):
                continue
            path = os.path.join(dirpath, name)
            rel = os.path.relpath(path, package_dir)
            module = rel[: -len('.lean')].replace(os.sep, '.')
            found[module] = path
    return found


def imports_of(path: str) -> list[str]:
    with open(path, encoding='utf-8', errors='replace') as handle:
        return IMPORT_RE.findall(handle.read())


def check_closure(label: str, package_dir: str, local_modules: set[str]) -> list[str]:
    """Every RHLean module reachable from the root must exist on disk."""
    modules = module_map(package_dir)
    if ROOT_MODULE not in modules:
        return [f'{label}: no root {ROOT_MODULE}.lean in {package_dir}']

    problems = []
    seen: set[str] = set()
    queue = [ROOT_MODULE]
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        seen.add(module)
        path = modules.get(module)
        if path is None:
            continue
        for imported in imports_of(path):
            if not imported.startswith(ROOT_MODULE):
                continue
            if imported in modules:
                queue.append(imported)
            else:
                problems.append(
                    f'{label}: {module} imports {imported}, which is not exported'
                )

    orphans = sorted(set(modules) - seen - {'lakefile'} - local_modules)
    for orphan in orphans:
        problems.append(f'{label}: {orphan} is exported but not reachable from {ROOT_MODULE}')
    return problems


def main() -> int:
    if not os.path.isdir(ROOT_MODULE):
        print(f'run from the repository root: no {ROOT_MODULE}/ here', file=sys.stderr)
        return 2

    problems = []
    for label, package_dir, local_modules in EXPORTS:
        if not os.path.isdir(package_dir):
            problems.append(f'{label}: {package_dir} is missing')
            continue
        problems.extend(check_closure(label, package_dir, local_modules))

    if problems:
        for problem in problems:
            print(problem, file=sys.stderr)
        print(f'\n{len(problems)} export problem(s) found.', file=sys.stderr)
        return 1

    print('Export closure audit passed.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
