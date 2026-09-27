#!/usr/bin/env python3
"""Check relative file targets in tracked Markdown (including new local files).

Checks inline links and link-reference definitions outside fenced code blocks.
External URLs and in-document anchors are deliberately outside this file audit.
This is not a mathematical-status or rendered-layout checker.
"""

from pathlib import Path
import re
import subprocess
from urllib.parse import unquote, urlsplit


def main():
    root = Path(__file__).resolve().parents[1]
    paths = sorted(set(subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "*.md"],
        cwd=root,
    ).decode().rstrip("\0").split("\0")))
    errors = []
    count = 0
    for name in paths:
        if not name or not (root / name).is_file():
            continue
        count += 1
        text = (root / name).read_text(encoding="utf-8")
        text = re.sub(r"(?ms)^\s*(`{3,}|~{3,})[^\n]*\n.*?^\s*\1\s*$", "", text)
        targets = re.findall(r"\[[^\]\n]*\]\((<[^>]+>|[^\s)]+)(?:\s+[^)]*)?\)", text)
        targets += re.findall(r"(?m)^\s{0,3}\[[^\]]+\]:\s*(<[^>]+>|\S+)", text)
        for raw in targets:
            target = raw.strip("<>")
            parts = urlsplit(target)
            if parts.scheme or parts.netloc or not parts.path:
                continue
            destination = root / name
            destination = destination.parent / unquote(parts.path)
            if not destination.exists():
                errors.append(f"{name}: missing relative target {target}")
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"Relative Markdown file links passed across {count} documents.")


if __name__ == "__main__":
    main()
