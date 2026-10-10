# Repository search and import DAG

The library declaration graph is still the audited `RHLean/` graph. The
repository source index adds navigation across `research/`, documents, scripts,
and the independent export projects. It can also search fetched PR refs without
checking them out. A source hit carries its path, line, scope, view, and commit;
it does not certify compilation or discharge any theorem hypothesis.

## Search the entire current checkout

Run these commands from the repository root. No Lean build or Python packages
are required:

```bash
python3 scripts/repo_index.py build --dot repo-imports.dot --report repo-map.md --require-acyclic
python3 scripts/proofq.py repo-search 'SectorSix' --scope research
python3 scripts/proofq.py repo-search 'owner two' --scope research --kind declaration
python3 scripts/proofq.py repo-search 'compensated' --carrier compensated-four-corner
python3 scripts/proofq.py repo-search 'floor li' --scope docs
python3 scripts/proofq.py repo-search 'Mertens' --scope scripts
python3 scripts/proofq.py repo-search 'FirstBad.*Budget' --regex --json
```

Plain queries require every whitespace-separated term, case insensitively.
`--regex` opts into regular expressions. Searches cover declaration names,
complete source statements and proof bodies, attached documentation, filenames,
and text files. Long statements are not cut to the old graph preview length.
`--kind declaration` excludes file-level hits; `--kind file` searches files only.
`--scope` accepts `library`, `research`, `docs`, `scripts`, `exports`, `config`, or
`other`. `--carrier` and `--role` filter declaration heuristics, not proof facts.

Named declaration occurrences retain file and line identity. The same theorem
name in research, the library, an export, or a different ref remains a separate
hit. Anonymous examples remain searchable in their file text. Attached doc
matches anchor their line at the declaration and label that evidence in JSON.

## Navigate the complete module DAG

```bash
python3 scripts/repo_index.py module research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean
python3 scripts/repo_index.py module research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean --transitive --dot first-bad-imports.dot
python3 scripts/repo_index.py module RHLean.Analysis.SquarePrefixMertensBridge
python3 scripts/repo_index.py module RHLean.Analysis.SquarePrefixMertensBridge --project export_mobius_synthesis
```

Edges point from importer to dependency. The parser reads the Lean import
preamble, strips nested comments, and supports quoted module names and multiple
imports per line. Export projects resolve imports within their own Lake project;
an export's `RHLean.*` copy never becomes a dependency on the development copy.
External package imports and unresolved repository-local imports are reported
separately. The generated report includes coverage, omitted non-text inputs,
and import cycles. The DOT output contains the full import graph or the selected
module's dependency/importer subgraph.

Use the existing [knowledge graph](KNOWLEDGE_GRAPH.md) commands for declaration
dependencies, reduction rules, and proof-status analysis. The source import DAG
does not replace the kernel's elaborated dependency graph.

## Include active PR work

PRs #915, #918, and #919 were unmerged on 2026-10-10. Fetch their current heads
explicitly, then index them as separate views:

```bash
git fetch origin refs/pull/915/head:refs/remotes/origin/pr-915 refs/pull/918/head:refs/remotes/origin/pr-918 refs/pull/919/head:refs/remotes/origin/pr-919
python3 scripts/repo_index.py build --ref origin/pr-915 --ref origin/pr-918 --ref origin/pr-919 --dot repo-imports.dot --report repo-map.md --require-acyclic
python3 scripts/proofq.py repo-search 'owner two' --view origin/pr-919 --scope research
python3 scripts/repo_index.py module research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean --view origin/pr-915
```

Every view records its resolved commit. A modified checkout is marked as such
and JSON results include the file's content hash; its commit is the checkout's
base, not a claim that uncommitted edits belong to that commit.
Indexing reads Git blobs in a batch and
does not switch branches, merge PR contents, or count PR results as landed on
`main`. Ref queries also work with an explicit commit SHA. The tool never
fetches remote refs itself; repeat `git fetch` to refresh them.

## Freshness and CI

Generated JSON, DOT, and reports are ignored by Git. The default index is
`repo-index.json`; queries build in memory when it is absent. The fingerprint
covers source contents, filenames, ref commits, and the index/parser code.
A stale default cache is rebuilt; an explicit stale `--index` is rejected with
a rebuild instruction. Modification times alone cannot validate a cache.

The [proof-inventory workflow](../.github/workflows/proof-inventory.yml) runs
the regression tests, generates the source index and import DAG, cross-checks
library proof counts and research coverage against the independent inventory,
and uploads the index, graph, coverage report, and current research search.
Research, documentation, export, and tooling changes trigger regeneration.
The normal Lean audit still generates and checks the exact library declaration
graph independently. A workflow reference or a navigation hit is not a green
Lean build for that file.
