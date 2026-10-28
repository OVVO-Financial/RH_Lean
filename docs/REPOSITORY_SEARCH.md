# Repository search and import DAG

## Coordinate-aware search (start here)

The same object often appears under several names: `C_R`, `squareRootCanonicalRoughCorrelation` and "rough correlation" are one quantity, while `D_R` names at least five different ones. Plain search finds only the spelling you typed. Use the [coordinate atlas](COORDINATE_ATLAS.md) to translate first:

```bash
python3 scripts/coordinate_atlas.py lookup D_R                       # every reading of a symbol, alias or Lean name
python3 scripts/coordinate_atlas.py path "rough correlation" ANCHOR-PRIME-DISCREPANCY   # strongest-evidence crosswalk chain
python3 scripts/coordinate_atlas.py path COORD-EULER-SELF-DUAL COORD-CORR4-PARENT --lean-only
python3 scripts/proofq.py repo-search 'q2 daughter' --expand --scope research    # search every alias of the coordinate
git grep -n -E "$(python3 scripts/coordinate_atlas.py expand 'floor-Li' --grep)"
```

`--expand` matches any one exact alias or Lean name of the coordinates the query names (it cannot be combined with `--regex`) and labels each hit with the alias that matched. Agents without Python should use the committed [static search index](search/INDEX.md): one page per coordinate (definition, crosswalks, every proved `<def>_eq_…` rewrite, top files) and per route, plus JSONL shards for code search ([guide](search/README.md)). Regenerate with `python3 scripts/search_catalog.py --write` and `python3 scripts/coordinate_atlas.py write`.

## Full-text search and the module DAG

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

## Current frontier and PR history

The [current research frontier DAG](RESEARCH_FRONTIER_DAG.md) and
[registry](research-frontier.json) replace the obsolete October 10 list of
unmerged #915/#918/#919 branches. The #918/#919 work is already on main;
#915 and #922/#923/#925–#929 are preserved as distinct cleanup tracks.
The registry records sources and open inputs rather than a live PR-state claim.

```bash
python3 scripts/research_frontier_dag.py
python3 scripts/proofq.py repo-search 'FirstBadSourcePayment' --scope research
python3 scripts/proofq.py repo-search 'lowVariation' --scope research
```

To compare a specific current or historical PR, fetch that PR explicitly,
then index its ref as a separate view. For example:

```bash
git fetch origin refs/pull/915/head:refs/remotes/origin/pr/915
python3 scripts/repo_index.py build --ref origin/pr/915 --dot repo-imports.dot --report repo-map.md --require-acyclic
python3 scripts/proofq.py repo-search 'FirstBadSourcePayment' --view origin/pr/915 --scope research
python3 scripts/repo_index.py module research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean --view origin/pr/915
```

Every view records its resolved commit. A modified checkout is marked as such
and JSON results include the file's content hash; its commit is the checkout's
base, not a claim that uncommitted edits belong to that commit.
Indexing reads Git blobs in a batch and does not switch branches, merge PR
contents, or count PR results as landed on main. Ref queries also work with an
explicit commit SHA. The tool never fetches remote refs itself; repeat
`git fetch` to refresh them. PR heads and check status must be inspected at
GitHub before making compilation or merge-readiness claims.

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
