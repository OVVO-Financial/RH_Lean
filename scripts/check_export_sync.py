#!/usr/bin/env python3
"""Verify the published export trees against the development tree.

Two failure modes have actually bitten this repository, and this script exists
to catch both before an export is published:

  * an export copies ``RHLean.lean`` verbatim but omits modules it imports, so
    ``lake build RHLean --wfail`` dies on a missing file rather than on any
    mathematics;
  * an export carries a module snapshot older than the development tree, so the
    published statement is not the one that was verified upstream.

Run from the repository root::

    python3 scripts/check_export_sync.py
"""
from __future__ import annotations

import os
import re
import sys

IMPORT_RE = re.compile(r'^\s*import\s+([A-Za-z0-9_.]+)', re.M)
ROOT_MODULE = 'RHLean'

# (label, package directory, match development tree, repo-local modules)
#
# The prime-wheel export deliberately renames its public modules, so its file
# contents are not expected to match the development tree; only its closure is
# checked.
#
# Repo-local modules live in the published repository but not upstream, and are
# reached by that repository's own tooling rather than by the root module.
# MobiusSynthesisBoundary is the synthesis PR gate contract driven by
# scripts/check_boundary_advance.py.
EXPORTS = [
    ('export_mobius_synthesis', 'export_mobius_synthesis', True,
     {'RHLean.Analysis.MobiusSynthesisBoundary'}),
    ('export_square_block', 'export_square_block/lean', True, set()),
    ('export_prime_wheel', 'export_prime_wheel/formalization', False, set()),
]


def module_map(package_dir: str) -> dict[str, str]:
    """Map ``RHLean.Foo.Bar`` to its file path within a lake package."""
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
                continue  # Mathlib and core are resolved by lake
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


def check_against_development(label: str, package_dir: str,
                              local_modules: set[str]) -> list[str]:
    """Exported modules must be byte-identical to the development tree."""
    problems = []
    for module, path in sorted(module_map(package_dir).items()):
        if not module.startswith(ROOT_MODULE + '.') or module in local_modules:
            continue
        upstream = module.replace('.', os.sep) + '.lean'
        if not os.path.exists(upstream):
            problems.append(f'{label}: {module} has no counterpart in the development tree')
            continue
        with open(path, 'rb') as exported_file, open(upstream, 'rb') as upstream_file:
            if exported_file.read() != upstream_file.read():
                problems.append(f'{label}: {module} differs from the development tree')
    return problems


def main() -> int:
    if not os.path.isdir(ROOT_MODULE):
        print(f'run from the repository root: no {ROOT_MODULE}/ here', file=sys.stderr)
        return 2

    problems = []
    for label, package_dir, match_development, local_modules in EXPORTS:
        if not os.path.isdir(package_dir):
            problems.append(f'{label}: {package_dir} is missing')
            continue
        problems.extend(check_closure(label, package_dir, local_modules))
        if match_development:
            problems.extend(check_against_development(label, package_dir, local_modules))

    if problems:
        for problem in problems:
            print(problem, file=sys.stderr)
        print(f'\n{len(problems)} export problem(s) found.', file=sys.stderr)
        return 1

    print('Export sync audit passed.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
