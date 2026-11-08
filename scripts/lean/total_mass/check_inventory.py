#!/usr/bin/env python3
"""Check the committed public surface of the total-mass LOW proof.

This read-only check never invokes Lean and never updates its expectations.
The manifest and ExactTypes.lean must be reviewed and committed explicitly.
Source hashes pin comment-free, whitespace-normalized binders and result types;
the separate Lean file checks those concrete types against the compiled terms.

The parser deliberately accepts only the small command grammar used by these
three files. An unfamiliar declaration or scope command fails closed instead
of silently disappearing from the inventory. It is not a general Lean parser.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


SOURCES = (
    "research/oai_434/VF919TotalMassLowEnergy.lean",
    "research/oai_434/VF919TotalMassLowPhysical.lean",
    "research/oai_434/VF919TotalMassEndpoint.lean",
)
AUDIT_DIR = Path("scripts/lean/total_mass")
MANIFEST = AUDIT_DIR / "expected_inventory.json"
EXACT_TYPES = AUDIT_DIR / "ExactTypes.lean"
SCHEMA = 1
HASH_FORMAT = "sha256 of comment-free source binders, colon, and result type; whitespace collapsed"
FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|native_decide)\b")
DECLARATION = re.compile(r"^(theorem|lemma|def)\s+([\w'.]+)\b", re.UNICODE)
ANY_DECLARATION = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|example|axiom|opaque)\b"
)


def normalized(text: str) -> str:
    return " ".join(text.split())


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def uncomment(text: str) -> str:
    """Blank nested comments, preserving offsets and literal strings."""
    chars = list(text)
    i, depth = 0, 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                chars[i:i + 2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                chars[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    chars[i] = " "
                i += 1
        elif in_string:
            if text[i] == "\\":
                i += 2
            else:
                if text[i] == '"':
                    in_string = False
                i += 1
        elif text.startswith("/-", i):
            chars[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                chars[i] = " "
                i += 1
        else:
            if text[i] == '"':
                in_string = True
            i += 1
    if depth or in_string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(chars)


def top_level_positions(text: str):
    """Yield character offsets outside binder brackets and quoted strings."""
    stack: list[str] = []
    closing = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            if i == len(text):
                raise ValueError("unterminated string in declaration")
        elif ch == "«":
            end = text.find("»", i + 1)
            if end < 0:
                raise ValueError("unterminated quoted identifier")
            i = end
        elif ch in closing:
            stack.append(closing[ch])
        elif ch in closing.values():
            if not stack or stack.pop() != ch:
                raise ValueError("unbalanced declaration brackets")
        elif not stack:
            yield i
        i += 1


@dataclass(frozen=True)
class Declaration:
    kind: str
    name: str
    binders: str
    result: str

    def inventory(self) -> dict[str, str]:
        return {
            "kind": self.kind,
            "name": self.name,
            "type_sha256": digest(normalized(self.binders + " : " + self.result)),
        }


@dataclass
class Source:
    path: str
    imports: list[str]
    contexts: list[str]
    declarations: list[Declaration]
    events: list[tuple[str, object]]

    def inventory(self) -> dict[str, object]:
        return {
            "path": self.path,
            "imports": self.imports,
            "scope_sha256": digest("\n".join(normalized(x) for x in self.contexts)),
            "declarations": [d.inventory() for d in self.declarations],
        }


def parse_type(rest: str, kind: str) -> tuple[str, str]:
    separator = None
    for pos in top_level_positions(rest):
        if separator is None and rest[pos] == ":" and not rest.startswith(":=", pos):
            separator = pos
        if rest.startswith(":=", pos) and re.match(r":=\s+by\b", rest[pos:]):
            end = pos
            break
        if kind == "def" and re.match(r"where\b", rest[pos:]):
            end = pos
            break
    else:
        raise ValueError("expected an explicitly typed theorem ':= by' or definition 'where'")
    if separator is None or separator >= end:
        raise ValueError("declaration has no explicit result type")
    binders, result = rest[:separator].strip(), rest[separator + 1:end].strip()
    if not result:
        raise ValueError("empty declaration type")
    return binders, result


def read_source(root: Path, relative: str) -> Source:
    code = uncomment((root / relative).read_text(encoding="utf-8"))
    # Literal contents are inert; comments were already blanked above.
    executable = re.sub(r'"(?:\\.|[^"\\])*"', '""', code)
    banned = FORBIDDEN.search(executable)
    if banned:
        raise ValueError(f"{relative}: prohibited token {banned.group(0)!r}")
    source = Source(relative, [], [], [], [])
    scopes: list[tuple[str, str]] = []
    offset = 0
    for line in code.splitlines(keepends=True):
        statement = line.strip()
        location = offset
        offset += len(line)
        if not statement:
            continue
        if line[0].isspace():
            if ANY_DECLARATION.match(statement):
                raise ValueError(f"{relative}: indented declaration is outside the audited grammar")
            continue
        if statement.startswith("import "):
            module = statement.removeprefix("import ").strip()
            if not re.fullmatch(r"(?:«[\w.]+»|[\w.]+)", module):
                raise ValueError(f"{relative}: unsupported import command {statement!r}")
            source.imports.append(module.removeprefix("«").removesuffix("»"))
            continue
        match = DECLARATION.match(statement)
        if match:
            kind, local_name = match.groups()
            names = [name for command, name in scopes if command == "namespace"]
            name = ".".join([*names, local_name])
            binders, result = parse_type(code[location + match.end():], kind)
            declaration = Declaration(kind, name, binders, result)
            source.declarations.append(declaration)
            source.events.append(("declaration", declaration))
            continue
        if statement.startswith("namespace "):
            scopes.append(("namespace", statement.removeprefix("namespace ")))
        elif statement == "noncomputable section" or statement.startswith("section"):
            scopes.append(("section", statement.removeprefix("noncomputable ").removeprefix("section").strip()))
        elif statement == "end" or statement.startswith("end "):
            if not scopes:
                raise ValueError(f"{relative}: unmatched end command")
            _, scope_name = scopes.pop()
            end_name = statement.removeprefix("end").strip()
            if end_name and end_name != scope_name:
                raise ValueError(f"{relative}: mismatched end {end_name!r}, expected {scope_name!r}")
        elif statement.startswith(("open ", "local notation ", "local instance :")):
            pass
        elif statement.startswith("#print axioms "):
            continue
        else:
            raise ValueError(f"{relative}: unsupported top-level command {statement!r}")
        source.contexts.append(statement)
        source.events.append(("context", statement))
    if scopes:
        raise ValueError(f"{relative}: unclosed namespace or section")
    return source


def expected_binders(declaration: Declaration) -> str:
    """Alpha-rename only outer binders with no later identifier occurrence.

    Source proof arguments can be unused in their quantified type even though
    the original proof uses them. Prefixing their names avoids the unused-name
    linter in an explicit forall assertion. Referenced binders and every result
    type character stay unchanged; source declaration hashes use the originals.
    """
    text = declaration.binders
    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    replacements: list[tuple[int, int, str]] = []
    cursor = 0
    while cursor < len(text):
        if text[cursor].isspace():
            cursor += 1
            continue
        if text[cursor] not in pairs:
            raise ValueError(f"{declaration.name}: unsupported expected-type binder")
        start = cursor
        stack = [pairs[text[cursor]]]
        cursor += 1
        while stack and cursor < len(text):
            char = text[cursor]
            if char in pairs:
                stack.append(pairs[char])
            elif char in pairs.values():
                if char != stack.pop():
                    raise ValueError(f"{declaration.name}: unbalanced expected-type binder")
            cursor += 1
        if stack:
            raise ValueError(f"{declaration.name}: unclosed expected-type binder")
        inside = text[start + 1:cursor - 1]
        colon = next((i for i in top_level_positions(inside)
                      if inside[i] == ":" and not inside.startswith(":=", i)), None)
        if colon is None:
            if text[start] == "[":  # Anonymous instance binder.
                continue
            raise ValueError(f"{declaration.name}: expected an explicitly typed binder")
        names = inside[:colon]
        if not re.fullmatch(r"[\w'\s]+", names):
            raise ValueError(f"{declaration.name}: unsupported binder name syntax")
        later = text[cursor:] + "\n" + declaration.result
        for match in re.finditer(r"[\w']+", names):
            name = match.group(0)
            if name.startswith("_"):
                continue
            occurrence = rf"(?<![\w']){re.escape(name)}(?![\w'])"
            if not re.search(occurrence, later):
                new_name = "_" + name
                if re.search(rf"(?<![\w']){re.escape(new_name)}(?![\w'])", text + declaration.result):
                    raise ValueError(f"{declaration.name}: alpha-renaming would collide")
                replacements.append((start + 1 + match.start(),
                                     start + 1 + match.end(), new_name))
    for start, end, new_name in reversed(replacements):
        text = text[:start] + new_name + text[end:]
    return text


def render_exact_types(sources: list[Source]) -> str:
    """Deterministic expected text; comparison only, never written by this check."""
    lines = [
        "import «research.oai_434.VF919TotalMassEndpoint»",
        "",
        "/-!",
        "# Exact public types for the total-mass LOW endpoint",
        "",
        "Every assertion below spells out the expected quantified type. The terms",
        "are the compiled public declarations; no expected conclusion is introduced",
        "as a premise. This file and its source-type manifest are committed review",
        "artifacts. CI compares them and elaborates this file; it never rewrites them.",
        "",
        "The four unconditional endpoints construct one positive-minimum source.",
        "The growth and signed-pair endpoints save m/4, while the fixed-power",
        "endpoint saves m/8. The signed-pair type retains the actual diagonal.",
        "-/",
        "",
        "set_option autoImplicit false",
        "",
    ]
    for source in sources:
        section = Path(source.path).stem + "ExactTypes"
        lines.extend([f"-- Source: {source.path}", f"section {section}", ""])
        for event, value in source.events:
            if event == "context":
                command = str(value)
                if command.startswith("local instance :"):
                    command = command.replace("local instance :", "local instance exactTypesUnitsFintype :", 1)
                lines.append(command)
                continue
            assert isinstance(value, Declaration)
            lines.extend(["", f"-- Expected public type: {value.name}"])
            binders = expected_binders(value)
            prefix = f"example : ∀ {binders},\n    " if binders else "example :\n    "
            lines.extend([prefix + value.result + " :=", f"  @_root_.{value.name}", ""])
        lines.extend(["", f"end {section}", ""])
    return "\n".join(lines)


def expected_manifest(sources: list[Source], exact_types: str) -> dict[str, object]:
    return {
        "schema": SCHEMA,
        "hash_format": HASH_FORMAT,
        "public_theorems": sum(d.kind in ("theorem", "lemma") for s in sources for d in s.declarations),
        "public_definitions": sum(d.kind == "def" for s in sources for d in s.declarations),
        "files": [source.inventory() for source in sources],
        "exact_types_sha256": digest(exact_types),
    }


def main() -> int:
    if len(sys.argv) > 2:
        raise ValueError("usage: check_inventory.py [repository-root]")
    root = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else Path(__file__).resolve().parents[3]
    expected = json.loads((root / MANIFEST).read_text(encoding="utf-8"))
    sources = [read_source(root, path) for path in SOURCES]
    exact_types = render_exact_types(sources)
    actual = expected_manifest(sources, exact_types)
    if actual != expected:
        raise ValueError(
            "public declaration names, imports, scopes, or exact source types differ from "
            "expected_inventory.json; review the changed statements explicitly"
        )
    committed_types = (root / EXACT_TYPES).read_text(encoding="utf-8")
    if committed_types != exact_types:
        raise ValueError("ExactTypes.lean differs from the committed public-type assertions")
    if actual["public_theorems"] != 23 or actual["public_definitions"] != 1:
        raise ValueError("expected exactly 23 public theorems and one public definition")
    names = [d.name for source in sources for d in source.declarations]
    if len(names) != len(set(names)):
        raise ValueError("duplicate public declaration name")
    print("PASS total-mass inventory: 3 files, 23 public theorems, 1 definition; exact types and imports pinned")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as error:
        print(f"FAIL total-mass inventory: {error}", file=sys.stderr)
        sys.exit(1)
