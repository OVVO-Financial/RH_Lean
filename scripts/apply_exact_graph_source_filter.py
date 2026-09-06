#!/usr/bin/env python3
"""One-shot patch: induce exact olean edges on written source declarations."""

from pathlib import Path

p = Path('scripts/decl_graph.py')
s = p.read_text(encoding='utf-8')

old = '''    Edges come from the compiled environment.  Source locations, doc comments,
    statement previews and normalized signatures are not in the environment
    dump, so they are merged in from the source parse where the declaration can
    be matched by name; declarations that only exist after elaboration simply
    lack them.
    """

    records: list[dict] = []
    module_by_name: dict[str, str] = {}
    with jsonl.open(encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            if is_internal_lean_name(rec["name"]):
                continue
            records.append(rec)
            module_by_name[rec["name"]] = rec["module"]

    def to_id(raw: str) -> str:
        mod = module_by_name.get(raw)
        if mod is None:
            return raw
        return demangle_private(raw, mod)[0]

    # References may point at elaborator-generated constants that were filtered
    # out above.  Drop those edges before statistics/reachability are computed.
    kept_ids = {demangle_private(r["name"], r["module"])[0] for r in records}

    # Source-side metadata, keyed by the same ids.
    src_decls, table = kg.build_declarations()
    meta = {d.decl_id: (d, kg.normalized_signature_parts(d, table)) for d in src_decls}
'''

new = '''    Edges come from the compiled environment, but the graph nodes are the
    declarations actually written in `RHLean/**/*.lean`. Lean elaboration also
    creates thousands of recursors, projections, equation lemmas and auxiliary
    constants; those are real environment entries but are machinery, not research
    declarations. We therefore take the exact kernel-recorded edges induced on
    the source declaration set. Source locations, docs, statement previews and
    normalized signatures are merged from the source parse.
    """

    # Source-side metadata defines the node universe. This is stricter and more
    # auditable than trying to maintain an ever-growing regex of elaborator name
    # patterns.
    src_decls, table = kg.build_declarations()
    meta = {d.decl_id: (d, kg.normalized_signature_parts(d, table)) for d in src_decls}

    raw_records: list[dict] = []
    module_by_name: dict[str, str] = {}
    with jsonl.open(encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            raw_records.append(rec)
            module_by_name[rec["name"]] = rec["module"]

    def to_id(raw: str) -> str:
        mod = module_by_name.get(raw)
        if mod is None:
            return raw
        return demangle_private(raw, mod)[0]

    # Keep exactly the written declarations. Generated constants may still occur
    # in raw proof terms, but they are not nodes in the mathematical graph.
    records: list[dict] = []
    seen_source: set[str] = set()
    for rec in raw_records:
        node_id = demangle_private(rec["name"], rec["module"])[0]
        if node_id in meta:
            records.append(rec)
            seen_source.add(node_id)

    missing_source = sorted(set(meta) - seen_source)
    if missing_source:
        preview = ", ".join(missing_source[:10])
        more = f" (+{len(missing_source) - 10} more)" if len(missing_source) > 10 else ""
        raise ValueError(
            f"elaborated environment is missing {len(missing_source)} source declarations: "
            f"{preview}{more}"
        )

    # References to generated environment constants are deliberately omitted;
    # references to written declarations retain their exact elaborated edges.
    kept_ids = seen_source
'''

if s.count(old) != 1:
    raise SystemExit(f'expected one ingestion block, found {s.count(old)}')
s = s.replace(old, new, 1)

old2 = '''        found = meta.get(node_id)
        if found is not None:
            decl, (signature, sig_constants) = found
            entry["path"] = decl.path
            entry["line"] = decl.line
            entry["namespace"] = decl.namespace
            entry["signature"] = signature
            entry["signature_constants"] = sig_constants
            entry["shape"] = kg.statement_shape(decl.statement)
            entry["shape_full"] = kg.statement_shape(decl.statement, conclusion_only=False)
            # The environment dump does not distinguish hypothesis from
            # conclusion, so the conclusion split comes from the source parse
            # and is intersected with the exact statement references.
            entry["conclusion_refs"] = [
                r for r in decl.conclusion_refs if r in stmt_refs_set
            ]
            entry["has_raw_hypothesis"] = kg.has_raw_hypothesis(decl.statement)
            entry["statement_preview"] = _preview(decl.statement, STATEMENT_PREVIEW)
            if include_docs and decl.doc:
                entry["doc"] = _preview(decl.doc, DOC_PREVIEW)
'''
new2 = '''        decl, (signature, sig_constants) = meta[node_id]
        entry["path"] = decl.path
        entry["line"] = decl.line
        entry["namespace"] = decl.namespace
        entry["signature"] = signature
        entry["signature_constants"] = sig_constants
        entry["shape"] = kg.statement_shape(decl.statement)
        entry["shape_full"] = kg.statement_shape(decl.statement, conclusion_only=False)
        # The environment dump does not distinguish hypothesis from conclusion,
        # so the conclusion split comes from source and is intersected with the
        # exact statement references.
        entry["conclusion_refs"] = [
            r for r in decl.conclusion_refs if r in stmt_refs_set
        ]
        entry["has_raw_hypothesis"] = kg.has_raw_hypothesis(decl.statement)
        entry["statement_preview"] = _preview(decl.statement, STATEMENT_PREVIEW)
        if include_docs and decl.doc:
            entry["doc"] = _preview(decl.doc, DOC_PREVIEW)
'''
if s.count(old2) != 1:
    raise SystemExit(f'expected one metadata block, found {s.count(old2)}')
s = s.replace(old2, new2, 1)

old3 = '''            "Exact declaration dependency graph read from the compiled environment. "
            "Edges are the constants the kernel records in each declaration's type "
            "and proof term. This is authoritative per AGENTS.md."
'''
new3 = '''            "Exact declaration dependency graph induced on written RHLean source "
            "declarations. Edges are the written project constants the elaborated "
            "environment records in each declaration's type and proof term. Generated "
            "recursors/projections/auxiliaries are intentionally not graph nodes. "
            "This is authoritative per AGENTS.md."
'''
if s.count(old3) != 1:
    raise SystemExit(f'expected one authority block, found {s.count(old3)}')
s = s.replace(old3, new3, 1)

p.write_text(s, encoding='utf-8')
Path('scripts/apply_exact_graph_source_filter.py').unlink()
print('Applied exact graph source-declaration filter.')
