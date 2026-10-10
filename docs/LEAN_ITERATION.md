# Fast Lean iteration

Use **Targeted Lean iteration** in GitHub Actions, choose your proof branch,
and enter one or more `research/*.lean` files. It builds their imported native
targets and warning-fatal research import closure. The standing full-library,
declaration-graph, source, export and terminal-axiom gates still decide PR acceptance;
this targeted check is compiler feedback, not a replacement for those audits.

Locally, after installing the pinned toolchain, restoring Mathlib and applying
the repository's StrongPNT patches, run:

```bash
python3 scripts/compile_research_import_closure.py --build-library \
  research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean
```

Multiple entry files share one traversal. `--plan /tmp/closure.json` lists the
ordered source closure and native targets without installing Lean.
`--force` recompiles every research prerequisite.

| Change | Research compilation |
| --- | --- |
| Fresh checkout or changed timestamps | Reuse verified artifacts |
| Leaf proof edit | Recompile the leaf and its dependent consumers |
| Imported research edit | Recompile that module and its descendants |
| Unrelated research edit | Reuse the selected closure |
| Native sources, dependency pins, patch layer or compiler flags | Invalidate research reuse |
| Missing, unverified or corrupt artifact | Recompile it |
| Failed new proof | Keep completed prerequisites; discard its invalid output |

The shared dependency setup saves a completed pinned Mathlib cache before
proof compilation. An exact hit with its completion marker skips a second
Mathlib download. Cold setup and the one-time migration from an old cache
still run `lake exe cache get`. Dependency restores never cross toolchain or
manifest pins. Native build fallbacks use a compatibility hash; research
artifacts additionally carry content records and output digests.

The five first-bad/recursive workflows classify changed files against their
actual transitive import DAG before installing Lean. Unrelated research edits
skip expensive setup; new imports enter the closure automatically. A missing
base commit conservatively runs the check. Keep theorem signatures
and axiom checks after compilation; cached oleans alone do not establish
acceptance. New research workflows can use `./.github/actions/lean-setup`
followed by `./.github/actions/research-compile` with a `targets` input.
