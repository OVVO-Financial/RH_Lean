#!/usr/bin/env python3
"""Repair multiline raw-string markers in the revision helper, then execute it."""
from pathlib import Path

script = Path(__file__).with_name("apply_equivalence_revision.py")
source = script.read_text(encoding="utf-8")
repairs = {
    'r"Then\n\\begin{equation}\n \\sum_{n\\le N}|S_n|^2",':
        'r"""Then\n\\begin{equation}\n \\sum_{n\\le N}|S_n|^2""",',
    'r"%======================================================================\n\\section{The unresolved high-height problem}",':
        'r"""%======================================================================\n\\section{The unresolved high-height problem}""",',
    'r"%======================================================================\n\\section{Fixed packets, small-prime channels, and uniform control}",':
        'r"""%======================================================================\n\\section{Fixed packets, small-prime channels, and uniform control}""",',
    'r"%======================================================================\n\\appendix",':
        'r"""%======================================================================\n\\appendix""",',
}
for old, new in repairs.items():
    count = source.count(old)
    if count != 1:
        raise RuntimeError(f"repair marker expected once, found {count}: {old[:50]!r}")
    source = source.replace(old, new, 1)

code = compile(source, str(script), "exec")
exec(code, {"__name__": "__main__", "__file__": str(script)})
