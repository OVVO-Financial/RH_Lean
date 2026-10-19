# Lean v4.34.1 upgrade for Quasi-Riemann Tracker

**Draft migration, not yet a completed upgrade.** PR #983 is a compatibility program toward the tracker-pinned Lean v4.34.1. No RH proof or new zero-free region follows merely from changing compiler versions.

## Why the migration is staged

The first revision directly changed RHLean's checked-in `lean-toolchain` and Mathlib/PNT+ pins. That triggered the old v4.24 StrongPNT patch in more than a dozen legacy CI jobs, causing a wave of **pre-compilation failures**, plus one inconsistent Mathlib dependency-cache failure. One specialized compilation job also reported unresolved typeclass elaboration in `ActualForcingEstimates.lean`. These failures must be distinguished, not treated as failures of established theorems.

The migration now stores **candidate-only** toolchain and dependency files under `.github/lean434/`:

- `lean-toolchain`: exact tracker compiler `leanprover/lean4:v4.34.1`
- `lakefile.lean`: original StrongPNT source, then tracker PNT+, then tracker Mathlib **last** to override old transitive versions
- `lake-manifest.json`: initially staged tracker lock plus StrongPNT, **not yet proven to match a freshly generated Lake lock**

The checked-in root project remains at Lean v4.24.0 while the port is incomplete. `.github/workflows/lean-434-upgrade.yml` overlays the candidate files **inside the temporary CI checkout only**. Existing root proof checks remain fully enabled and unweakened; only the new candidate build uses 4.34.1. Once all dependencies and repository modules compile, the final step of this **same draft PR** will promote the validated candidate files to the root.

## Exact source pins

| Package | Required revision |
| --- | --- |
| Lean | `v4.34.1` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| PrimeNumberTheoremAnd | `c39a751132c88b6e8080b74c74023fd95b3d8be0` |
| StrongPNT (preserved historical source) | `2f5835c322314f55f1026ec2f139d704b7c45c69` |

The first three target pins match the Quasi-Riemann Tracker; StrongPNT is RHLean's additional dependency.

## Mandatory validation gates

1. In the isolated 4.34.1 CI runner, regenerate `lake-manifest.json` and check every Mathlib transitive dependency. Commit the **generated** candidate lock when differences are observed.
2. Confirm an actual Mathlib smoke test passes under Lean v4.34.1.
3. Compile the tracker PNT+ interface without changing its mathematical statement.
4. Port historical StrongPNT into a **new** source-exact `scripts/strongpnt_434` layer. Do not reuse the v4.24 patch as-is, remove hypotheses, or add axioms. Revalidate `Strong_PNT`.
5. Compile all RHLean modules and research imports; repair Lean 4.34 API/elaborator changes with theorem statements and premises invariant.
6. Recheck the Mertens/rightmost-zero correspondence, canonical VF statements, #915 source and returned-boundary consumers.
7. Check `#print axioms` and forbidden-admission audit. Require CI green at the exact commit.
8. **Only then** move the candidate compiler/Lake configuration into the root project, run the full legacy and new CI suite, and obtain human review before merging.

A red **isolated migration gate** accurately signals incomplete compatibility. It does not require turning dozens of existing proof checks red just to produce that diagnostic.

## What this does not prove

The ordinary Mertens exponent right-wall equivalence is already formalized in `research/MERTENS_CONVERSE_IDENTIFICATION.lean`. The tracker additionally quantifies over **all Dirichlet characters** and independently checks proof artifacts with Comparator, Lean, NanoDa and con-ron. A qualifying tracker proof requires independent Dirichlet-character estimates; the compiler migration alone is infrastructure work.

Sources: [tracker pins](https://github.com/GTimG/QuasiRiemannTracker/blob/main/verifier/pins.json) and [tracker lock](https://github.com/GTimG/QuasiRiemannTracker/blob/main/verifier/standard/lake-manifest.json).
