# Pinned geometric suppliers and native all-place descent

Upstream source: `CocoSgt/riemann-hypothesis-lean` at
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
Native baseline: `OVVO-Financial/RH_Lean` at
`608b5702a20ab34a9efcd38b5d59e09f9f565f61`.

## What is constructed

`AlpogeGeometryInputClosure.lean` gives closed source proofs of the six global
packages consumed by the original short integral cusp-section constructor.
`AlpogeShortConstructorClosure.lean` applies those proofs to the original
constructor. Its explicit conclusion constructs an integral section with a
regular level determinant and the original all-embedding multiplication bound
`exp (C * (f * r * Lb)^9)`. All hypotheses on the actual datum, core, good deep
cover, flat line, weight, and level remain in its statement.

These files are **original-source audit targets**. They do not supply a native
theta datum or claim that the entire geometric closure has been ported to the
native Mathlib version. The independently extracted native all-place descent
library is a separate deliverable.

## Six packages are supplied by closed proofs

In this table, `D` denotes
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/`.
Every supplying expression is expanded in `AlpogeGeometryInputClosure.lean`;
the manifest and import-closure report pin its transitive source files.

| Required package | Actual closed supplier | Source root |
| --- | --- | --- |
| `GlobalTheory.CovTop.PublishedHodgeBundleTheorems` | `RHLean.UpstreamGeometryAudit.hodgeBundleTheorems`; all 28 stored fields assembled directly | `AlpogeGeometryInputClosure.lean`; definitions in `.../HodgeBundleWeights/ToKnownTheoremsOf.lean` |
| `GlobalTheory.Published.GrothendieckDeformation` | `grothendieckDeformation_of_lifting` applied to `PositivityTheory.DualRT.abelianDeRham` and `GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers` | `D/GrothendieckDeformationOfLifting.lean`, `D/AbelianSchemeHomLiftingNilpotentDividedPowers.lean`, and `.../AbelianDeRhamDuality/AbelianDeRhamDuality.lean` |
| `GlobalTheory.HSCore.Quoted` | Eight fields assembled from closed vanishing, nef, GAGA, Chow, and intersection-length suppliers | `AlpogeGeometryInputClosure.lean` |
| `GlobalTheory.Published.SiegelToroidalIntegral` | `GlobalTheory.siegelToroidalIntegral_holds` | `D/SiegelToroidalIntegralHolds.lean` |
| `GlobalTheory.Published.ToroidalForFanKS` | `GlobalTheory.TorKSField.toroidalForFanKS` | `D/ToroidalCompactificationFanLogKodairaSpencerIso.lean` |
| `GlobalTheory.Published.SemiAbelianLieSeminegative` | `GlobalTheory.Nef.semiAbelianLieSeminegative` | `D/SemiAbelianLieSeminegativeBis.lean` |

The Grothendieck lifting adapter by itself is conditional; both actual inputs
are supplied here. Similarly, the split-torus special case is not substituted
for general semiabelian Lie seminegativity. No `OpenLiteratureStatements`
parameter is introduced. The terminal every-character assembly is not imported.

## Source identity and independent verification

The original release archive is 239,275,554 bytes, SHA256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
The local comparison checked **all 175,187 Lean source files** and the
`lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` files against their
pinned Git blob hashes. There were no missing files and no byte differences.
The receipt is `upstream_archive_git_receipt.json`; the comparison is reproducible
with `verify_alpoge_archive_identity.py` and does not execute Lean.

The [MIT verification page](https://math.mit.edu/~drew/grh/), inspected at its
2026-11-22 16:20 UTC update, reports successful source compilation of the same
original archive and independent kernel checks. Its
[axiom log](https://math.mit.edu/~drew/grh/audit.log) records only
`propext`, `Classical.choice`, and `Quot.sound` for its five headline targets.
The archive identity comparison is what connects that evidence to this exact
Git pin. Those reported checks are external evidence; they are not described
as a new native RH_Lean build or as a fresh build of our new wrappers.

Original toolchain: Lean `v4.33.1`; Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.
Native toolchain: Lean `v4.34.1`; Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Executable source and axiom gate

The selected original-source closure contains **52,223 upstream modules** plus
three local audit modules, **356,643,395 bytes** and **6,265,197 lines** in total.
The source/import/escape scan passed with no findings; external module roots
were Mathlib only. No metaprogram/environment mutation escape was found by the
configured lexical inventory. This is a module-level closure of the universal
packages; it is not a claim that every declaration is mathematically necessary.

Closure digest:
`080e4c70ee452e1b945dfdfc949dd00ce521cdc2ac4774758064159b9b070be4`.
The compact result is `closed_source_audit_receipt.json`. The 43 MB detailed
report is a generated audit artifact, not a required source-control file.

The closure excludes `Main`, `Statements`, `Supplements.*`, and the terminal
every-character assembly. Its broad import environment does contain the three
conditional RH-from-growth transfer modules listed in the compact receipt.
They are not a closed terminal RH theorem. The seven selected axiom targets
are the six closed geometric packages and the actual short-section wrapper.

`run_alpoge_geometric_audit.sh` refuses to execute outside GitHub Actions. It:

1. Verifies the exact source/config hashes, the complete selected import graph,
   and the configured proof-escape exclusions.
2. Exports only the selected `.lean` sources and pinned build configuration to
   a fresh directory; no original project `.olean` files are copied.
3. Retrieves the Mathlib dependency cache, verifies all dependency Git
   revisions and the unchanged manifest, and rejects any prebuilt project
   `.olean` before the source build.
4. Builds the explicit `AlpogeGeometryAudit` target rather than default targets.
5. Runs the seven declaration/axiom checks and requires a real axiom receipt for
   every target with no axiom outside the three standard kernel axioms.

**Status:** static source audit passed; the new original-source wrappers' fresh
hosted build and seven-target axiom audit are pending. No local Lean, Lake, or
elan execution was used for this work.

## Native all-place descent is a much smaller closed slice

The raw `HtMapLeOfPoints` import closure contains 480 source modules / 85,810
lines. The actual supplying proof can be extracted as **77 supplier modules**
plus three narrowly pruned files and one explicit entry theorem: **81 native
modules / 15,894 lines** before compiler repair.

The entry point is `RHLean.Geometry.nativeAllPlaceDescent` in
`RHLean/Geometry/NativeAllPlaceDescent.lean`. The entire supplier namespace and
module paths are renamed under `RHLean.Geometry.AlpogeAllPlace`, including the
two auxiliary `Bl` namespaces. The import graph is closed over Mathlib.

The proof retains genuine finitely generated `O_K` submodules, a jointly
injective family of integral maps into the Hilbert direct sum, the all-place
joint norm bound, short generators for the target, and the actual near-rank
saturation inequality. Its conclusion retains the original normalized slope
loss `t - ε * (|t| + 2 * Λ)`. No real-lattice replacement, artificial map count,
or assumed cancellation estimate is inserted.

The supplying roots are `descent_slope`, `span_min_slope`, and the actual
`power_slope_mu` proof in `BranchIsometryProofs/OrthSum.lean`. The later theta
section material in `IsProbabilityMeasureMuPart` is removed after
`slope_sq_eq`. The dense complex-place pointwise operator norm proof is retained
with only its real definition dependencies. Reexport aliases are replaced by
their proven suppliers, and the original block-inverse and positive-rank
proofs discharge the two small helper calls.

`extract_native_all_place_descent.py` and
`descent-extraction/native_all_place_descent_manifest.json` record the extraction
and original source hashes. One known Mathlib 4.34 product-inequality API change
is recorded explicitly. **Status:** staged native source; hosted compilation
and the native entry axiom check are pending. This status must be updated only
from the exact-head CI result.

## Smaller actual theta constructor entry

For `GlobalTheory.ShortSpanComp.short_span_comp_mem`, two suppliers ignore their
universal hodge-package argument: `minimal_level_cover_is_good` and
`log_sum_bad_primes_le_sq`. The third supplier follows
`unramified_points_at_deep_level` → `unramified_points_of_CMDatum` →
`exists_unramified_curve_over_field`, which uses only field `p8`,
`RayClassFieldSt`. Its closed source supplier is
`PositivityTheory.Stage1.PM.rayClassFieldSt` in
`Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean`.

Thus a specialized ShortSpan port can follow these actual proofs without
assembling all 28 universal fields. The orbit-separation construction is a
different obligation: its actual quotient-fibre section separation uses
`q15` (Nadel vanishing), nefness, and `q16` (principalisation), together with the
geometric bigness and toroidal suppliers. The finite determinant selector does
not itself prove those geometric inputs.
