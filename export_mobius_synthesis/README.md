# Möbius Synthesis

This directory is the staging export for a future **Möbius Synthesis** repository combining the two complementary formal tracks:

- **Square-Block Möbius** — square endpoints, canonical factor geometry, lifetime flow, death removal, and square-prefix Mertens criteria.
- **Prime-Wheel Möbius** — finite prime-wheel reconstruction, torus Fourier analysis, conductor decomposition, Ramanujan identification, and divisor-boundary reduction.

Unlike the narrower publication exports, this synthesis export is intentionally broad. Its Lean snapshot mirrors the complete import-audited `RHLean` source tree from the parent repository so that both tracks, their transitive formal scaffolding, and the modules where they meet are present together.

## Formal seam

The synthesis-facing endpoint is represented particularly by the modules around:

- `RHLean.Analysis.SquarePrefixMertensBridge`
- `RHLean.Analysis.SquareWheelNesting`
- `RHLean.Analysis.SquareWheelQuadraticSampling`
- `RHLean.Analysis.SquareWheelZeroModeElimination`
- `RHLean.Analysis.PrimeWheelRamanujanIdentification`
- `RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction`
- `RHLean.Analysis.RamanujanDivisorBoundary`
- `RHLean.Proof.TerminalMertensReduction`
- `RHLean.Proof.MutablePNTClosure`
- `RHLean.Proof.TerminalAxiomAudit`

These sit on top of the complete arithmetic, geometry, lifetime, Fourier, conductor, and Gram infrastructure copied alongside them.

## Layout

- `RHLean.lean` — complete import manifest for the copied Lean source.
- `RHLean/` — exact source snapshot, copied by Git blob identity from the verified parent development.
- `lakefile.lean`, `lean-toolchain`, `lake-manifest.json` — pinned project metadata matching the parent development.
- `MODULES.md` — guide to the two tracks and their synthesis seam.

## Verification

From this directory after extraction as a standalone project:

```bash
lake build RHLean --wfail
```

The source files in this export are not rewritten variants: they are the same Git blobs as the corresponding files in the parent `RH_Lean` tree at export time. The parent repository remains the authoritative development and CI source.

The project does **not** claim an unconditional proof of the Riemann Hypothesis. Open analytic obligations remain explicit ordinary propositions; the purpose of this export is to publish the complete machine-checked reduction architecture in one place.
