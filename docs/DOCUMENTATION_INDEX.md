# Documentation index

Updated 2026-09-26. The repository is a formal reduction and obstruction map;
the required uniform correlation estimate remains open. Start with the
[current proof contract](../CURRENT_PROOF_CONTRACT.md).

## Reading order and authority

| Document | Purpose |
| --- | --- |
| [README](../README.md) | Public project status and entry points. |
| [Current proof contract](../CURRENT_PROOF_CONTRACT.md) | Exact current target, quantifiers, sufficient constants, and theorem interfaces. |
| [Agent instructions](../AGENTS.md) | Research and repository rules. |
| [Formalization checklist](../FORMALIZATION_CHECKLIST.md) | Execution gates and historical PR closeouts. |
| [Formalization sequence](../FORMALIZATION_SEQUENCE.md) | Dependency catalog and append-only research record. |
| [Research route registry](../RESEARCH_ROUTE_REGISTRY.md) | Route dispositions and the scope of the current freeze. |
| [Research handoff](../CURRENT_RESEARCH_HANDOFF.md) | Latest handoff followed by historical checkpoints. |
| [Knowledge graph](KNOWLEDGE_GRAPH.md) | Navigation, inventory, and exact dependency audit tooling. |

Lean source and the applicable successful kernel checks take precedence over
prose. A theorem's ordinary hypotheses matter even when its axiom list is
clean. The import root covers the library; it does not cover every `research/`
module automatically.

## Historical and diagnostic material

The root architecture maps, multi-route plan, earlier `docs/` research notes,
and dated entries in the handoff/sequence preserve the state at their original
checkpoint. Their "current", "open", and "next" labels are local to that
checkpoint. They do not override the current contract or authorize repeating a
closed route. Exact identities and counterexamples remain useful and are kept.

The [research index](../research/README.md) identifies the latest closeout
modules. Scripts and experiments reproduce finite evidence unless accompanied
by an explicit Lean-certified checker. A script passing on a finite range
does not prove a uniform estimate.

The `export_mobius_synthesis`, `export_prime_wheel`, and `export_square_block`
directories are separately buildable snapshots. Their module lists and
documentation describe what each package ships. Development-only research
results are not silently part of an export. This cleanup changes export status
headers, not their Lean sources, manifests, or provenance pins.

## Verification map

| Scope | Command or hosted gate |
| --- | --- |
| Markdown relative file links | `python3 scripts/check_documentation.py` / `Documentation checks` |
| Unfinished proofs / axioms | `bash scripts/audit_assumptions.sh` |
| Generated library import root | `python3 scripts/check_root_manifest.py` |
| Paper / Analysis boundary | `bash scripts/check_paper_analysis_boundary.sh` |
| Export closure and synchronization | `python3 scripts/check_export_sync.py` / `Public export verification` |
| Library compilation and exact declaration graph | `Lean source audits`, including `Hosted Lean build` and the owned-warning gate |
| Local development validation | `bash scripts/local_ci.sh` (requires Lean and dependency-cache access) |
| Local independent export builds | `bash scripts/verify_exports_local.sh` |
| #796–#798 Stokes / CORR research chain | [Signed cell Stokes bridge check](../.github/workflows/signed-cell-stokes-bridge.yml) |
| #799 Möbius inversion | [Mobius inversion global cancellation](../.github/workflows/mobius-inversion-global-cancellation.yml) |
| #800 K₂ finite diagnostic | [K2 coherent-mode diagnostic](../.github/workflows/k2-coherent-mode.yml) |

Workflows use path filters. A documentation-only head need not trigger a Lean
build; absence of a run is not a successful build. Check the actual final head,
and distinguish a successful source audit from successful Lean compilation.

`scripts/check_rh_conditionality.py` reports the specific historical
`ClassicalMertensRHCriterion` parameter. It is a targeted source scan, not a
complete proof that a declaration has no other open mathematical hypothesis.

## Maintenance rule

Update the contract when a theorem changes the frontier, then reconcile the
README, instructions, and route registry. Append historical results with their
scope and evidence grade. Prepopulate the closeout before final CI; do not add
a commit afterward solely to claim that the preceding commit was green.
