#!/usr/bin/env python3
"""Shared library for the RHLean mathematical knowledge graph.

`scripts/proof_inventory.py` answers "which file knows about which file?".  This
module answers the finer question "which declaration references which
declaration?", and attaches an auditable semantic facet layer on top of it.

Three things live here:

* a Lean source scanner that recovers top-level declarations together with the
  namespace stack and `open` directives in scope at each one;
* a name resolver that maps a referenced identifier to a repository declaration
  the way Lean itself would search (current namespace prefixes, then opens,
  then the root namespace);
* graph algorithms used by `scripts/proofq.py` (reachability, shortest path,
  dominators, normalized statement signatures).

## Epistemic status

The graph built from this module is **syntactic**.  It records that the text of
one declaration mentions the name of another.  It is a search index, not a
kernel-certified dependency record, and it is deliberately conservative in one
direction and lossy in the other:

* it cannot see dependencies introduced by elaboration -- instance resolution,
  notation and macro expansion, `simp` lemmas invoked by a bare `simp`, or
  anything reached through dot-notation on a hypothesis;
* it can in principle over-report, when a local hypothesis or bound variable
  happens to share a name with a global declaration.

`scripts/lean/DeclGraph.lean` produces the exact elaborated graph from the
compiled environment in the same JSON schema.  Where the two disagree, the
elaborated graph is authoritative, per `AGENTS.md`.
"""

from __future__ import annotations

import hashlib
import re
from collections import defaultdict, deque
from dataclasses import dataclass, field
from pathlib import Path

SOURCE_ROOT = Path("RHLean")
ROOT_MANIFEST = Path("RHLean.lean")

DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "class",
    "inductive",
    "instance",
    "example",
    "axiom",
    "opaque",
)
PROOF_KINDS = ("theorem", "lemma")

_MODIFIERS = r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
_ATTR_PREFIX = r"(?:@\[[^\n]*?\]\s*)*"
DECL_START_RE = re.compile(
    r"^" + _ATTR_PREFIX + _MODIFIERS + r"(" + "|".join(DECL_KEYWORDS) + r")\b"
)
DECL_NAME_RE = re.compile(
    r"^" + _ATTR_PREFIX + _MODIFIERS + r"(" + "|".join(DECL_KEYWORDS) + r")\s+([^\s(:{\[⦃]+)"
)
NAMESPACE_RE = re.compile(r"^namespace\s+([\w.'!?]+)")
SECTION_RE = re.compile(r"^section\b\s*([\w.'!?]*)")
END_RE = re.compile(r"^end\b\s*([\w.'!?]*)")
OPEN_RE = re.compile(r"^open\b(.*)$")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$")
ATTR_RE = re.compile(r"^@\[")

# Lean identifiers admit unicode letters (Greek is used heavily here) plus the
# usual `_`, `'`, `!`, `?` and subscripts.
_IDENT_CHAR = r"[^\W\d]|[_]"
IDENT_RE = re.compile(
    r"(?<![\w.'])((?:[^\W\d]|_)[\w'!?₀-₉ₐ-ₜ]*(?:\.(?:[^\W\d]|_)[\w'!?₀-₉ₐ-ₜ]*)*)",
    re.UNICODE,
)

# Structural tokens kept in a normalized statement signature.  Local names,
# numerals and binder identifiers are dropped; only the logical skeleton and the
# resolved global constants survive, which is what makes two independently
# proved but equivalent propositions collide.
SHAPE_TOKENS = (
    "↔", "→", "∀", "∃", "¬", "∧", "∨", "=", "≠", "≤", "<", "≥", ">",
    "∑", "∏", "∫", "|", "‖", "∈", "⊆", "∪", "∩", "\\", "+", "-", "*", "/", "^",
)


def strip_lean_comments(text: str) -> tuple[str, list[tuple[int, int, str]]]:
    """Blank Lean comments while preserving newlines, and return doc comments.

    The returned text has the same number of newlines as the input so line
    numbers stay valid.  The second element lists `(start_line, end_line, body)`
    for each `/-- ... -/` documentation comment, which the declaration parser
    attaches to whatever declaration follows it.
    """

    out: list[str] = []
    docs: list[tuple[int, int, str]] = []
    i = 0
    n = len(text)
    line = 1
    block_depth = 0
    in_string = False
    escaped = False
    doc_start = 0
    doc_chars: list[str] = []
    collecting_doc = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                if collecting_doc:
                    doc_chars.append("/-")
                out.extend("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                if collecting_doc and block_depth == 0:
                    docs.append((doc_start, line, "".join(doc_chars).strip()))
                    collecting_doc = False
                    doc_chars = []
                elif collecting_doc:
                    doc_chars.append("-/")
                out.extend("  ")
                i += 2
                continue
            if collecting_doc:
                doc_chars.append(ch)
            if ch == "\n":
                out.append("\n")
                line += 1
            else:
                out.append(" ")
            i += 1
            continue

        if in_string:
            out.append(ch)
            if ch == "\n":
                line += 1
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            # `/--` opens a doc comment; `/-!` a module doc; `/-` a plain one.
            after = text[i + 2] if i + 2 < n else ""
            if after == "-" and text[i + 3 : i + 4] != "]":
                collecting_doc = True
                doc_start = line
                doc_chars = []
                out.extend("   ")
                i += 3
                continue
            out.extend("  ")
            i += 2
            continue

        if ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue

        out.append(ch)
        if ch == "\n":
            line += 1
        i += 1

    return "".join(out), docs


def module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def _split_top_level(text: str, marker: str) -> int:
    """Index of the first occurrence of `marker` at bracket depth zero, or -1."""

    depth = 0
    i = 0
    n = len(text)
    mlen = len(marker)
    while i < n:
        ch = text[i]
        if ch in "([{⟨⦃":
            depth += 1
        elif ch in ")]}⟩⦄":
            depth -= 1
        elif depth == 0 and text.startswith(marker, i):
            # `:=` inside `⟨_, _⟩` anonymous constructors is already excluded by
            # depth; guard against `:=` appearing as part of a longer token.
            return i
        i += 1
    return -1


def _statement_value_split(body: str) -> tuple[str, str]:
    """Split a declaration into its statement text and its proof/value text."""

    idx = _split_top_level(body, ":=")
    if idx >= 0:
        return body[:idx], body[idx + 2 :]
    # Pattern-matching definitions have no top-level `:=`; the alternatives
    # start at a `|` opening a line.
    m = re.search(r"^\s{0,4}\|", body, re.MULTILINE)
    if m:
        return body[: m.start()], body[m.start() :]
    return body, ""


@dataclass
class Declaration:
    name: str
    short_name: str
    kind: str
    is_private: bool = False
    module: str = ""
    path: str = ""
    line: int = 0
    end_line: int = 0
    namespace: str = ""
    opens: tuple[str, ...] = ()
    statement: str = ""
    value: str = ""
    doc: str = ""
    statement_refs: list[str] = field(default_factory=list)
    conclusion_refs: list[str] = field(default_factory=list)
    proof_refs: list[str] = field(default_factory=list)
    external_refs: list[str] = field(default_factory=list)

    @property
    def is_proof(self) -> bool:
        return self.kind in PROOF_KINDS

    @property
    def decl_id(self) -> str:
        """Graph identity.

        Lean mangles `private` declarations per module (`_private.<mod>.0.<name>`),
        so the same source-level name may legitimately occur in several modules
        without clashing.  Private declarations therefore get a module-qualified
        id.  `scripts/lean/DeclGraph.lean` normalizes Lean's mangling to exactly
        this form so both producers agree.
        """

        return f"{self.name}#{self.module}" if self.is_private else self.name


def parse_module(path: Path, text: str) -> list[Declaration]:
    """Recover top-level declarations from one Lean module.

    Namespaces, sections and `open` directives are tracked so that each
    declaration carries the scope Lean would have resolved its identifiers in.
    """

    clean, docs = strip_lean_comments(text)
    lines = clean.splitlines()
    raw_lines = text.splitlines()
    mod = module_name(path)

    doc_by_end: dict[int, str] = {}
    for _start, end, bodytext in docs:
        doc_by_end[end] = bodytext

    # Scope stack entries are ("namespace" | "section", name, opens_added).
    scope: list[tuple[str, str, int]] = []
    opens: list[str] = []
    ns_parts: list[str] = []

    decls: list[Declaration] = []
    pending: dict[str, object] | None = None
    pending_doc = ""
    last_doc_end = -10

    def current_ns() -> str:
        return ".".join(ns_parts)

    def flush(end_line: int) -> None:
        nonlocal pending
        if pending is None:
            return
        start = int(pending["line"])
        body = "\n".join(lines[start - 1 : end_line])
        statement, value = _statement_value_split(body)
        ns = str(pending["namespace"])
        short = str(pending["short"])
        full = f"{ns}.{short}" if ns else short
        decls.append(
            Declaration(
                name=full,
                short_name=short,
                kind=str(pending["kind"]),
                is_private=bool(pending["private"]),
                module=mod,
                path=str(path),
                line=start,
                end_line=end_line,
                namespace=ns,
                opens=tuple(pending["opens"]),  # type: ignore[arg-type]
                statement=statement,
                value=value,
                doc=str(pending["doc"]),
            )
        )
        pending = None

    for idx, line in enumerate(lines, 1):
        if idx in doc_by_end:
            pending_doc = doc_by_end[idx]
            last_doc_end = idx
            continue

        if not line.strip():
            continue
        if line[0].isspace():
            continue  # continuation of the current declaration

        stripped = line.rstrip()

        if IMPORT_RE.match(stripped):
            flush(idx - 1)
            continue

        m = NAMESPACE_RE.match(stripped)
        if m:
            flush(idx - 1)
            name = m.group(1)
            scope.append(("namespace", name, len(opens)))
            ns_parts.extend(name.split("."))
            pending_doc = ""
            continue

        m = SECTION_RE.match(stripped)
        if m:
            flush(idx - 1)
            scope.append(("section", m.group(1), len(opens)))
            pending_doc = ""
            continue

        m = END_RE.match(stripped)
        if m:
            flush(idx - 1)
            if scope:
                kind, name, opens_mark = scope.pop()
                del opens[opens_mark:]
                if kind == "namespace":
                    drop = len(name.split("."))
                    del ns_parts[len(ns_parts) - drop :]
            pending_doc = ""
            continue

        m = OPEN_RE.match(stripped)
        if m:
            flush(idx - 1)
            rest = m.group(1)
            # `open scoped X`, `open X in`, `open A B C`
            rest = re.sub(r"\bscoped\b", " ", rest)
            rest = re.sub(r"\bin\b.*$", " ", rest)
            for tok in re.findall(r"[\w.'!?]+", rest):
                if tok not in opens:
                    opens.append(tok)
            pending_doc = ""
            continue

        if ATTR_RE.match(stripped) and not DECL_START_RE.match(stripped):
            # Attribute-only command.  A same-line `@[simp] theorem ...` must
            # fall through to the declaration parser below.
            flush(idx - 1)
            continue

        m = DECL_NAME_RE.match(stripped)
        if m:
            flush(idx - 1)
            doc = pending_doc if idx - last_doc_end <= 2 else ""
            modifiers = stripped[: m.start(1)]
            pending = {
                "line": idx,
                "kind": m.group(1),
                "short": m.group(2),
                "private": "private" in modifiers.split(),
                "namespace": current_ns(),
                "opens": list(opens),
                "doc": doc,
            }
            pending_doc = ""
            continue

        if DECL_START_RE.match(stripped):
            # A declaration keyword whose name we could not parse (e.g. `example`).
            flush(idx - 1)
            pending_doc = ""
            continue

        # Any other column-0 command (`variable`, `set_option`, `#print`, ...)
        # terminates the previous declaration.
        flush(idx - 1)
        pending_doc = ""

    flush(len(lines))
    return decls


class NameTable:
    """Resolve referenced identifiers to repository declarations."""

    def __init__(self, decls: list[Declaration]) -> None:
        self.by_name: dict[str, Declaration] = {}
        self.private_by_module: dict[str, dict[str, Declaration]] = {}
        for decl in decls:
            if decl.is_private:
                self.private_by_module.setdefault(decl.module, {})[decl.name] = decl
            else:
                self.by_name[decl.name] = decl
        self.by_id: dict[str, Declaration] = {d.decl_id: d for d in decls}
        self.namespaces: set[str] = set()
        for name in self.by_name:
            parts = name.split(".")
            for i in range(1, len(parts)):
                self.namespaces.add(".".join(parts[:i]))

    def candidates(self, token: str, decl: Declaration) -> list[str]:
        """Candidate full names for `token`, in Lean's resolution order."""

        out: list[str] = []
        ns_parts = decl.namespace.split(".") if decl.namespace else []
        for i in range(len(ns_parts), 0, -1):
            out.append(".".join(ns_parts[:i]) + "." + token)
        for op in decl.opens:
            out.append(op + "." + token)
            # An `open Foo` inside `namespace RHLean.Proof` names
            # `RHLean.Proof.Foo`, so try the open relative to the namespace too.
            for i in range(len(ns_parts), 0, -1):
                out.append(".".join(ns_parts[:i]) + "." + op + "." + token)
        out.append(token)
        return out

    def resolve(self, token: str, decl: Declaration) -> str | None:
        """Resolve `token` as seen from `decl`, returning a graph id or None.

        A `private` declaration is in scope only within the module that declares
        it, so the private table for `decl.module` is consulted first and the
        private tables of other modules never are.
        """

        private = self.private_by_module.get(decl.module, {})
        for cand in self.candidates(token, decl):
            hit = private.get(cand)
            if hit is not None:
                return hit.decl_id
            hit = self.by_name.get(cand)
            if hit is not None:
                return hit.decl_id
        return None


def _tokens(text: str) -> list[str]:
    return IDENT_RE.findall(text)


def resolve_references(decls: list[Declaration], table: NameTable) -> None:
    """Fill in `statement_refs` / `proof_refs` for every declaration."""

    for decl in decls:
        for attr, source in (("statement_refs", decl.statement), ("proof_refs", decl.value)):
            seen: list[str] = []
            unresolved: set[str] = set()
            for tok in _tokens(source):
                full = table.resolve(tok, decl)
                if full is None:
                    if "." in tok:
                        unresolved.add(tok)
                    continue
                if full == decl.decl_id:
                    continue  # self-reference / recursion
                if full not in seen:
                    seen.append(full)
            setattr(decl, attr, seen)
            if attr == "statement_refs":
                decl.external_refs = sorted(unresolved)

        # The conclusion is resolved separately: a reference appearing only in
        # a hypothesis means the theorem *assumes* that proposition, while one
        # in the conclusion means it *establishes* it. That distinction is what
        # separates a proved result from a conditional reduction.
        conclusion: list[str] = []
        for tok in _tokens(statement_conclusion(decl.statement)):
            full = table.resolve(tok, decl)
            if full is None or full == decl.decl_id:
                continue
            if full not in conclusion:
                conclusion.append(full)
        decl.conclusion_refs = conclusion


def normalized_signature(decl: Declaration, table: NameTable) -> str:
    return normalized_signature_parts(decl, table)[0]


def normalized_signature_parts(decl: Declaration, table: NameTable) -> tuple[str, int]:
    """Hash of a statement's logical skeleton plus its resolved constants.

    Binder names, local hypothesis names, numerals and whitespace are discarded.
    Two declarations with the same signature state propositions of the same
    shape over the same repository constants -- a *candidate* equivalence to be
    checked by hand, never an equality claim.
    """

    text = decl.statement
    # Drop the declaration header up to the first binder or `:`.
    text = re.sub(r"^" + _ATTR_PREFIX + _MODIFIERS + r"\w+\s+\S+", "", text)
    parts: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        m = IDENT_RE.match(text, i)
        if m and m.start() == i:
            tok = m.group(1)
            full = table.resolve(tok, decl)
            if full is not None:
                parts.append(full)
            i = m.end()
            continue
        if ch in SHAPE_TOKENS:
            parts.append(ch)
        i += 1
    payload = " ".join(parts)
    constants = sum(1 for p in parts if p not in SHAPE_TOKENS)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16], constants


# --------------------------------------------------------------------------
# Graph algorithms
# --------------------------------------------------------------------------


def reachable(graph: dict[str, list[str]], roots: list[str]) -> set[str]:
    seen: set[str] = set()
    q = deque(roots)
    while q:
        node = q.popleft()
        if node in seen:
            continue
        seen.add(node)
        q.extend(graph.get(node, ()))
    return seen


def shortest_path(graph: dict[str, list[str]], src: str, dst: str) -> list[str] | None:
    if src == dst:
        return [src]
    prev: dict[str, str] = {src: src}
    q = deque([src])
    while q:
        node = q.popleft()
        for nxt in graph.get(node, ()):
            if nxt in prev:
                continue
            prev[nxt] = node
            if nxt == dst:
                path = [dst]
                while path[-1] != src:
                    path.append(prev[path[-1]])
                return list(reversed(path))
            q.append(nxt)
    return None


def invert(graph: dict[str, list[str]]) -> dict[str, list[str]]:
    rev: dict[str, list[str]] = {n: [] for n in graph}
    for src, deps in graph.items():
        for dep in deps:
            rev.setdefault(dep, []).append(src)
    for key in rev:
        rev[key].sort()
    return rev


def strongly_connected_components(
    graph: dict[str, list[str]], nodes: set[str] | None = None
) -> list[list[str]]:
    """Kosaraju SCCs, implemented iteratively so a 10k-node graph is safe."""

    keep = set(graph) if nodes is None else set(nodes)
    for deps in graph.values():
        keep.update(d for d in deps if nodes is None or d in nodes)

    seen: set[str] = set()
    finish: list[str] = []
    for root in sorted(keep):
        if root in seen:
            continue
        seen.add(root)
        stack: list[tuple[str, object]] = [
            (root, iter(d for d in graph.get(root, ()) if d in keep))
        ]
        while stack:
            node, raw_it = stack[-1]
            it = raw_it  # iterator, kept opaque only to satisfy the type checker
            try:
                nxt = next(it)  # type: ignore[arg-type]
            except StopIteration:
                stack.pop()
                finish.append(node)
                continue
            if nxt in seen:
                continue
            seen.add(nxt)
            stack.append((nxt, iter(d for d in graph.get(nxt, ()) if d in keep)))

    rev = invert({n: [d for d in graph.get(n, ()) if d in keep] for n in keep})
    seen.clear()
    out: list[list[str]] = []
    for root in reversed(finish):
        if root in seen:
            continue
        comp: list[str] = []
        seen.add(root)
        stack = [root]
        while stack:
            node = stack.pop()
            comp.append(node)
            for nxt in rev.get(node, ()):
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        out.append(sorted(comp))
    return out


def topological_order(graph: dict[str, list[str]], nodes: set[str]) -> list[str]:
    """Reverse-postorder DFS; tolerates cycles by ignoring back edges."""

    order: list[str] = []
    state: dict[str, int] = {}
    for root in sorted(nodes):
        if state.get(root):
            continue
        stack = [(root, iter(sorted(graph.get(root, ()))))]
        state[root] = 1
        while stack:
            node, it = stack[-1]
            advanced = False
            for nxt in it:
                if nxt not in nodes or state.get(nxt):
                    continue
                state[nxt] = 1
                stack.append((nxt, iter(sorted(graph.get(nxt, ())))))
                advanced = True
                break
            if not advanced:
                stack.pop()
                state[node] = 2
                order.append(node)
    order.reverse()
    return order


def dominators(graph: dict[str, list[str]], root: str) -> dict[str, str]:
    """Immediate dominators of every node reachable from `root`.

    Cooper--Harvey--Kennedy iteration.  On the dependency graph (edges point
    from a theorem to what it uses) a dominator of `n` is a declaration that
    every route from `root` down to `n` must pass through: a genuine
    mathematical choke point rather than a merely popular lemma.
    """

    nodes = reachable(graph, [root])
    order = [n for n in topological_order(graph, nodes)]
    if root in order:
        order.remove(root)
    order.insert(0, root)
    index = {n: i for i, n in enumerate(order)}
    rev = invert({n: [d for d in graph.get(n, ()) if d in nodes] for n in nodes})

    idom: dict[str, str] = {root: root}

    def intersect(a: str, b: str) -> str:
        while a != b:
            while index[a] > index[b]:
                a = idom[a]
            while index[b] > index[a]:
                b = idom[b]
        return a

    changed = True
    while changed:
        changed = False
        for node in order[1:]:
            preds = [p for p in rev.get(node, ()) if p in idom]
            if not preds:
                continue
            new = preds[0]
            for pred in preds[1:]:
                new = intersect(pred, new)
            if idom.get(node) != new:
                idom[node] = new
                changed = True
    return idom


def load_sources() -> list[tuple[Path, str]]:
    if not SOURCE_ROOT.is_dir():
        raise SystemExit(f"ERROR: {SOURCE_ROOT}/ not found; run from repository root")
    out = []
    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        out.append((path, path.read_text(encoding="utf-8")))
    return out


def build_declarations() -> tuple[list[Declaration], NameTable]:
    decls: list[Declaration] = []
    for path, text in load_sources():
        decls.extend(parse_module(path, text))
    table = NameTable(decls)
    resolve_references(decls, table)
    return decls, table


# --------------------------------------------------------------------------
# Semantic facet layer
# --------------------------------------------------------------------------

# Logical connectives whose presence in a statement classifies its role.  This
# is read off the whole statement, not a truncated preview, because "is this an
# equivalence or a one-directional bound?" is the single most load-bearing
# distinction the role layer makes.
ROLE_GLYPHS = ("↔", "≤", "≥", "<", ">", "=", "∃", "∀", "→", "¬")


def statement_conclusion(statement: str) -> str:
    """The conclusion of a declaration, with binders and hypotheses removed.

    A theorem's role is decided by what it concludes, not by what it assumes:
    `3 ≤ a → x = y` is an equality, not a bound.  Binders are bracketed, so the
    first bracket-depth-zero `:` ends the binder list, and the last depth-zero
    `→` after it ends the hypotheses.
    """

    idx = _split_top_level(statement, ":")
    body = statement[idx + 1 :] if idx >= 0 else statement

    # Split on depth-zero arrows and keep the final consequent.
    depth = 0
    last = 0
    for i, ch in enumerate(body):
        if ch in "([{⟨⦃":
            depth += 1
        elif ch in ")]}⟩⦄":
            depth -= 1
        elif depth == 0 and ch == "→":
            last = i + 1
    return body[last:]


def statement_shape(statement: str, conclusion_only: bool = True) -> list[str]:
    """The logical connectives occurring in a statement, deduplicated."""

    text = statement_conclusion(statement) if conclusion_only else statement
    return [g for g in ROLE_GLYPHS if g in text]

FACETS_PATH = Path(__file__).with_name("semantic_facets.json")

_CAMEL_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")


def name_tokens(name: str) -> set[str]:
    """Lowercased camelCase/snake_case tokens of a declaration's short name."""

    short = name.split("#", 1)[0].rsplit(".", 1)[-1]
    spaced = _CAMEL_RE.sub("_", short)
    return {t.lower() for t in re.split(r"[_'.]+", spaced) if t and not t.isdigit()}


def load_facets(path: Path | None = None) -> dict:
    import json

    return json.loads((path or FACETS_PATH).read_text(encoding="utf-8"))


def _matches(rule: dict, tokens: set[str], module: str, kind: str) -> str | None:
    for group in rule.get("tokens", ()):
        if all(tok in tokens for tok in group):
            return "name tokens " + "+".join(group)
    for frag in rule.get("modules", ()):
        if frag in module:
            return f"module contains {frag!r}"
    if kind in rule.get("kinds", ()):
        return f"declaration kind {kind}"
    return None


def tag_declaration(
    node_id: str,
    entry: dict,
    facets: dict,
) -> dict[str, object]:
    """Attach facet and role tags to one declaration, recording the evidence.

    Every tag is a search heuristic.  A shared carrier tag means the two names
    use the same vocabulary, nothing more; see the disclaimer in
    `scripts/semantic_facets.json`.
    """

    tokens = name_tokens(node_id)
    module = str(entry.get("module", ""))
    kind = str(entry.get("kind", ""))
    # Prefer the precomputed full-statement shape; fall back to the preview,
    # which is truncated and can hide a trailing connective.
    shape = entry.get("shape")
    if isinstance(shape, list):
        statement_glyphs = set(shape)
    else:
        statement_glyphs = set(statement_shape(str(entry.get("statement_preview", ""))))

    tags: dict[str, list[str]] = {}
    evidence: dict[str, str] = {}

    for facet, values in facets["facets"].items():
        hits: list[str] = []
        for value, rule in values.items():
            if value == "_doc":
                continue
            why = _matches(rule, tokens, module, kind)
            if why:
                hits.append(value)
                evidence[f"{facet}:{value}"] = why
        if hits:
            tags[facet] = sorted(hits)

    roles: list[str] = []
    for role, rule in facets["roles"].items():
        if role == "_doc":
            continue
        why: str | None = None
        for glyph in rule.get("shape", ()):
            if glyph in statement_glyphs:
                why = f"statement contains {glyph}"
                break
        if why is None and rule.get("shape_eq_only"):
            if "=" in statement_glyphs and not (
                statement_glyphs & {"≤", "≥", "<", ">", "↔"}
            ):
                why = "statement is an equation with no inequality or iff"
        if why is None:
            why = _matches(rule, tokens, module, kind)
        if why:
            roles.append(role)
            evidence[f"role:{role}"] = why

    return {"facets": tags, "roles": sorted(roles), "evidence": evidence}


def tag_all(nodes: dict[str, dict], facets: dict) -> dict[str, dict]:
    return {name: tag_declaration(name, entry, facets) for name, entry in nodes.items()}


# --------------------------------------------------------------------------
# Proof status layer
# --------------------------------------------------------------------------

STATUS_PROVED = "proved"
STATUS_REDUCED = "reduced"
STATUS_OPEN = "open"
STATUS_NOGO = "no-go"
STATUS_REFUTED = "refuted"
STATUS_DEFINITION = "definition"

_CLOSED_PROP_RE = re.compile(
    r"^\s*" + _ATTR_PREFIX + _MODIFIERS
    + r"(?:def|abbrev)\s+(\S+)(.*?):\s*Prop\s*$"
)


# Glyphs that mark a hypothesis stated inline rather than through a named
# project proposition -- `(hR : 1 ≤ R)`, `∀ᶠ R in atTop, ...`, and so on.
_RAW_HYPOTHESIS_GLYPHS = (
    "≤", "<", "≥", ">", "=", "∈", "∣", "≠", "∀", "∃", "¬", "↔", "∧", "∨"
)


def statement_hypotheses(statement: str) -> str:
    """The binder and antecedent text of a declaration, excluding its conclusion.

    Binders sit before the first bracket-depth-zero `:`; antecedents sit between
    that `:` and the last depth-zero `→`.  Everything else is the conclusion.
    """

    idx = _split_top_level(statement, ":")
    if idx < 0:
        return statement
    binders = statement[:idx]
    body = statement[idx + 1 :]

    depth = 0
    last = 0
    for i, ch in enumerate(body):
        if ch in "([{⟨⦃":
            depth += 1
        elif ch in ")]}⟩⦄":
            depth -= 1
        elif depth == 0 and ch == "→":
            last = i + 1
    return binders + " " + body[:last]


def has_raw_hypothesis(statement: str) -> bool:
    """Does this declaration assume something not named by a project proposition?

    A theorem whose conclusion is a closed proposition but which assumes
    `1 ≤ R`, or an eventually-quantified condition, does not establish that
    proposition outright -- it establishes it for whoever can supply the
    hypothesis.
    """

    hyp = statement_hypotheses(statement)
    return any(g in hyp for g in _RAW_HYPOTHESIS_GLYPHS)


def prop_valued_defs(nodes: dict[str, dict]) -> set[str]:
    """Every `Prop`-valued definition, whether or not it takes binders.

    Parameterised ones (`CenteredDistinguishedPrimeGlobalGramBounded x`) are
    just as much an assumption as closed ones when they appear as a hypothesis,
    so the assumption side must see both.
    """

    out: set[str] = set()
    for name, entry in nodes.items():
        if entry.get("kind") not in ("def", "abbrev"):
            continue
        if _CLOSED_PROP_RE.match(str(entry.get("statement_preview", ""))):
            out.add(name)
    return out


def closed_propositions(nodes: dict[str, dict]) -> set[str]:
    """Named `def X : Prop` statements that take no binders.

    A binder-free Prop is a closed statement -- something someone is trying to
    prove.  `def IsFoo (n : ℕ) : Prop` is a predicate applied throughout the
    library and is not an obligation, so binders are the discriminator.
    """

    out: set[str] = set()
    for name, entry in nodes.items():
        if entry.get("kind") not in ("def", "abbrev"):
            continue
        m = _CLOSED_PROP_RE.match(str(entry.get("statement_preview", "")))
        if m and not m.group(2).strip():
            out.add(name)
    return out


def compute_status(
    nodes: dict[str, dict],
    tags: dict[str, dict] | None = None,
) -> tuple[dict[str, str], dict[str, list[str]]]:
    """Classify declarations and derive proposition-level proof rules.

    Closed `def X : Prop` declarations are the research propositions.  A theorem
    can close one only when every *hard* hypothesis is absent and every named
    closed proposition it assumes has already been closed.  Parameterised Prop
    hypotheses and structure/class/inductive binders are hard blockers: they are
    data the theorem requires, not globally discharged propositions.

    Exact unconditional `A ↔ B` theorems contribute both implication rules.  The
    least fixpoint therefore propagates proved status across compiled coordinate
    equivalences instead of leaving an equivalent proposition artificially open.
    """

    closed = closed_propositions(nodes)
    all_props = prop_valued_defs(nodes)
    carriers = {
        n for n, e in nodes.items()
        if e.get("kind") in ("structure", "class", "inductive")
    }
    parameterised_props = all_props - closed

    assumed_all: dict[str, list[str]] = {}
    rules: dict[str, list[tuple[set[str], str]]] = defaultdict(list)
    refutes: dict[str, list[str]] = defaultdict(list)

    for name, entry in nodes.items():
        if entry.get("kind") not in PROOF_KINDS:
            continue

        stmt = set(entry.get("statement_refs", ()))
        concl = list(entry.get("conclusion_refs", ()))
        hypothesis_refs = stmt - set(concl)
        prop_assumptions = sorted(hypothesis_refs & all_props)
        closed_assumptions = sorted(hypothesis_refs & closed)

        hard_blocked = bool(entry.get("has_raw_hypothesis")) or bool(
            hypothesis_refs & (parameterised_props | carriers)
        )
        assumed_all[name] = prop_assumptions
        entry["closed_assumes"] = closed_assumptions
        entry["hard_blocked"] = hard_blocked

        conclusion_props = [r for r in concl if r in closed]
        shape = set(entry.get("shape") or ())

        if "¬" in shape and len(concl) == 1 and len(conclusion_props) == 1:
            target = conclusion_props[0]
            entry["refutes_prop"] = target
            refutes[target].append(name)
            continue

        # B from A (or from several named closed propositions).  Raw/data
        # hypotheses block a global proposition rule, but named closed premises
        # are allowed to discharge later in the fixpoint.
        if not hard_blocked and len(concl) == 1 and len(conclusion_props) == 1:
            target = conclusion_props[0]
            entry["establishes_prop"] = target
            rules[target].append((set(closed_assumptions), name))
            continue

        # An exact unconditional A ↔ B is two proposition implications.  Do not
        # manufacture this from a theorem that itself assumes another Prop.
        if (
            not hard_blocked
            and "↔" in shape
            and len(concl) == 2
            and len(conclusion_props) == 2
            and not prop_assumptions
        ):
            a, b = conclusion_props
            entry["iff_props"] = [a, b]
            rules[a].append(({b}, name))
            rules[b].append(({a}, name))

    proved_props: set[str] = set()
    changed = True
    while changed:
        changed = False
        for prop in closed - proved_props:
            for premises, _thm in rules.get(prop, ()):
                if premises <= proved_props:
                    proved_props.add(prop)
                    changed = True
                    break

    status: dict[str, str] = {}
    for name, entry in nodes.items():
        kind = entry.get("kind")
        if kind in PROOF_KINDS:
            if tags is not None and "no-go" in tags[name]["roles"]:
                status[name] = STATUS_NOGO
            elif any(a not in proved_props for a in assumed_all.get(name, ())):
                status[name] = STATUS_REDUCED
            else:
                status[name] = STATUS_PROVED
        elif name in closed:
            if name in proved_props:
                status[name] = STATUS_PROVED
            elif refutes.get(name):
                status[name] = STATUS_REFUTED
            else:
                status[name] = STATUS_OPEN
        else:
            status[name] = STATUS_DEFINITION
    return status, assumed_all
