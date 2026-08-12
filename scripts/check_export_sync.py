#!/usr/bin/env python3
"""Verify that every published export tree is a buildable Lake project.

Two structural failure modes are checked for every export:

  * an export copies ``RHLean.lean`` but omits a module it imports, so
    ``lake build RHLean --wfail`` dies on a missing file rather than on any
    mathematics;
  * an export ships a module unreachable from its own root, which is dead
    weight in a published repository.

``export_mobius_synthesis`` has one additional invariant: every exported
``RHLean.*`` module must be byte-identical to the development tree.  That export
is the handoff directory used to promote the verified native-PNT and Möbius
synthesis layers into the standalone ``mobius-synthesis`` repository.  A stale
pre-existing dependency is therefore just as dangerous as an omitted file: the
export can be structurally closed while still failing after it is copied out.

The other published repositories remain standalone Lake projects.  They compile
their own subsets with ``--wfail``, run their own assumption audits, and may
diverge intentionally from this development tree.  Their export directories are
therefore closure-checked without requiring byte identity.

Run from the repository root::

    python3 scripts/check_export_sync.py
"""
from __future__ import annotations

import os
import re
import sys

IMPORT_RE = re.compile(r'^\s*import\s+([A-Za-z0-9_.]+)', re.M)
ROOT_MODULE = 'RHLean'

# (label, package directory, match development tree, repo-local modules,
#  mirror the development root manifest)
#
# The mobius-synthesis export is intentionally pinned at the module-content
# level because it is used as a manual promotion source.  Its root manifest is
# still allowed to be a curated subset, so mirror_root remains False.
#
# The prime-wheel and square-block exports remain closure-only because their
# published repositories are standalone and may diverge intentionally.
#
# Repo-local modules are shipped in a published repository and reached by that
# repository's own tooling rather than by its root module, so they are exempt
# from the unreachable-module check. MobiusSynthesisBoundary is listed because
# it is the synthesis PR gate contract driven by mobius-synthesis's
# scripts/check_boundary_advance.py, and whether its root manifest imports it is
# now that repository's decision rather than this one's: it is imported there
# today, and the entry costs nothing while that holds but prevents a false
# failure if the export tracks a state where it is not.
EXPORTS = [
    ('export_mobius_synthesis', 'export_mobius_synthesis', True,
     {'RHLean.Analysis.MobiusSynthesisBoundary'}, False),
    ('export_square_block', 'export_square_block/lean', False, set(), False),
    ('export_prime_wheel', 'export_prime_wheel/formalization', False, set(), False),
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


def check_mirrors_root(label: str, package_dir: str) -> list[str]:
    """A mirroring export must carry the development root manifest verbatim.

    The closure check walks the export's own RHLean.lean, so an export whose
    root is simply out of date still closes cleanly against its own stale
    manifest. Only comparing against the development root catches that.
    """
    exported = os.path.join(package_dir, ROOT_MODULE + '.lean')
    upstream = ROOT_MODULE + '.lean'
    with open(exported, 'rb') as a, open(upstream, 'rb') as b:
        if a.read() != b.read():
            return [f'{label}: {ROOT_MODULE}.lean differs from the development root manifest']
    return []


def main() -> int:
    if not os.path.isdir(ROOT_MODULE):
        print(f'run from the repository root: no {ROOT_MODULE}/ here', file=sys.stderr)
        return 2

    problems = []
    for label, package_dir, match_development, local_modules, mirror_root in EXPORTS:
        if not os.path.isdir(package_dir):
            problems.append(f'{label}: {package_dir} is missing')
            continue
        problems.extend(check_closure(label, package_dir, local_modules))
        if match_development:
            problems.extend(check_against_development(label, package_dir, local_modules))
        if mirror_root:
            problems.extend(check_mirrors_root(label, package_dir))

    if problems:
        for problem in problems:
            print(problem, file=sys.stderr)
        print(f'\n{len(problems)} export problem(s) found.', file=sys.stderr)
        return 1

    print('Export sync audit passed.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
