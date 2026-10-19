# Lean v4.34.1 / Quasi-Riemann Tracker compatibility migration

**State: WORK IN PROGRESS — isolated migration branch; do not merge or report a passed full Lean build.**

- Branch: `chore/lean-4.34.1-tracker-compat`.
- Base `main` commit when branched: `28a270195167530615c2b182f8c9ffd86855b1f6`.
- Tracker source: [QuasiRiemannTracker verifier pins](https://github.com/GTimG/QuasiRiemannTracker/blob/main/verifier/pins.json) and its [verified Lake manifest](https://github.com/GTimG/QuasiRiemannTracker/blob/main/verifier/standard/lake-manifest.json).
- Scope: **toolchain/dependency migration only**. No change to RHLean's arithmetic definitions, proof statements, canonical VF, Mertens-zero correspondence, or original physical source.

## Target pins and what has been staged

| Component | Previous `main` | Staged on this branch | Status |
| --- | --- | --- | --- |
| Lean | `v4.24.0` | `v4.34.1` | `lean-toolchain` updated; build not certified |
| Mathlib | `v4.24.0` | `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`) | `lakefile.lean` and lock staged |
| PrimeNumberTheoremAnd | `7f3cd7c3e1c85d60478ed8934be42a06b07de374` | `c39a751132c88b6e8080b74c74023fd95b3d8be0` (tracker source) | dependency update staged; API port pending |
| StrongPNT | `2f5835c322314f55f1026ec2f139d704b7c45c69` | same historical source | **new Mathlib port required** |

The staged `lake-manifest.json` contains the tracker's exact dependency revisions plus RHLean's additional pinned StrongPNT package. **This manifest was assembled from authenticated committed manifests; it is not yet a Lake-regenerated or build-tested lock.** Regenerate it with `lake update` on the new compiler, inspect the dependency diff, and commit the verified generated lock before declaring this step complete. Do not silently accept a downgrade of Mathlib or PNT+.

The tracker's Lean compiler pin is v4.34.1, but matching the compiler alone does **not** guarantee a proof is accepted there. Its submission must use the canonical all-Dirichlet-character theorem and pass Comparator, Lean, NanoDa, and con-ron against their pinned inputs.

## Known compatibility boundary

The current [StrongPNT 4.24 port scripts](../scripts/strongpnt_424/) perform exact source replacements for the old external files. They were explicitly written for Mathlib v4.24 and **must not be regarded as a 4.34.1 port**. The new PrimeNumberTheoremAnd revision also has changed imports and transitive dependencies. The historical StrongPNT file remains pinned to preserve theorem provenance until a source-exact port is proved. This is the anticipated first substantive migration gate.

No proof in this branch is upgraded merely because its toolchain file changed.

## Acceptance sequence (all required before merging)

1. On the migration branch, install the pinned compiler and run `lake update`. Review `git diff -- lake-manifest.json` against the tracker pins and commit the Lake-generated dependency graph.
2. Restore Mathlib caches with `lake exe cache get`; compile a small Mathlib-only module to prove the new toolchain actually runs.
3. Compile the pinned PrimeNumberTheoremAnd source with v4.34.1. Repair exact API changes in separate, reviewed patches, without modifying mathematical premises.
4. Port StrongPNT separately to v4.34.1. Do not blindly run `scripts/strongpnt_424`; create and test a new version-specific compatibility patch with a source hash/expected-text guard. Verify `StrongPNT.PNT5_Strong` and `#print axioms Strong_PNT`.
5. Build `RHLean` and its research import closure with the new dependency graph, preserve warning-as-error for repository-owned sources, and audit forbidden axioms and placeholder proofs. Keep existing CI intact.
6. Compile and compare public declarations including `research/MERTENS_CONVERSE_IDENTIFICATION.lean`, the canonical `VFCanonicalSquareVonKochStatement`, and the original #915 physical source/consumers. Check theorem **statements and assumptions**, not just names or successfully generated `.olean` files.
7. Run old and new toolchain regression comparisons. Require every relevant full build and source audit green at the **same exact commit**, before making a PR ready for human review or merging.

Minimal local commands to start the dependency-port diagnosis (not assertions that these currently succeed):

```sh
lake update
git diff -- lake-manifest.json
lake exe cache get
lake build PrimeNumberTheoremAnd.SmoothExistence
lake build StrongPNT.PNT5_Strong
lake build RHLean
bash scripts/audit_assumptions.sh
```

## Distinct follow-on: tracker admission

RH_Lean already formalizes the ordinary Möbius-exponent/zeta-right-wall equivalence in [MERTENS_CONVERSE_IDENTIFICATION.lean](../research/MERTENS_CONVERSE_IDENTIFICATION.lean). The Quasi-Riemann Tracker demands nonvanishing of **all** Dirichlet L-functions for the common bound `theta`. Upgrading Lean is necessary for convenient proof transport, but it does not supply a new unconditional exponent or generalize the analytic estimate to twisted Möbius sums `sum_(n<=x) mu(n) chi(n)`.

Only after an independently established qualifying theorem should a separate tracker submission implement `Candidate.bound`, match the exact challenge, and undergo independent multi-kernel verification. Keep arithmetic research and build-system compatibility as separate proof-status categories.
