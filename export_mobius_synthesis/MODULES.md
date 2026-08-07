# Möbius Synthesis — Lean source map

This export intentionally contains the full import-audited `RHLean` source snapshot rather than a minimal transitive closure. `RHLean.lean` is the authoritative file-by-file inventory.

## Square-block track

The square-block side is centered on:

- square-prefix Mertens endpoints and interpolation;
- canonical largest-prime/cofactor decomposition;
- low/high height partition and low occupancy;
- squared-complex Fermat/cofactor geometry;
- square-root transport and dyadic compression;
- lifetime active sets, death shells, and survivor reduction;
- canonical gap/ancestry, signed Gram, and terminal quadratic closure.

Representative entry modules include `SquarePrefixMertensBridge`, `CanonicalHighSectorCore`, `CanonicalLowOccupancy`, `SquareBlockSurvivorBridge`, `LifetimeEndpointDecomposition`, and `CanonicalGapAncestryQuadraticClosure`.

## Prime-wheel track

The prime-wheel side is centered on:

- deterministic Möbius reconstruction and primorial-wheel arithmetic;
- finite torus Fourier pairing;
- arithmetic and complete spectra;
- reduced additive conductors and conductor Gram decomposition;
- periodic raw response and coconductor subtraction;
- classical Ramanujan identification;
- divisor-residue boundary fluctuations and Mertens transfer.

Representative entry modules include `PrimeWheelFiniteSystem`, `PrimeWheelMobiusRecovery`, `PrimeWheelFourierReduction`, `PrimeWheelConductorGram`, `PrimeWheelPeriodicRawBridge`, `PrimeWheelRamanujanIdentification`, and `PrimeWheelRamanujanBoundaryReduction`.

## Synthesis seam

The modules most directly joining the two descriptions and the final arithmetic targets include:

- `RHLean.Analysis.SquareWheelNesting`
- `RHLean.Analysis.SquareWheelQuadraticSampling`
- `RHLean.Analysis.SquareWheelZeroModeElimination`
- `RHLean.Analysis.PrimeWheelRamanujanIdentification`
- `RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction`
- `RHLean.Analysis.RamanujanDivisorBoundary`
- `RHLean.Analysis.PrimorialWheelMertensTransfer`
- `RHLean.Proof.TerminalMertensReduction`
- `RHLean.Proof.MutablePNTClosure`
- `RHLean.Proof.RiemannHypothesisBridge`
- `RHLean.Proof.TerminalAxiomAudit`

## Scope policy

For synthesis, dependency completeness is more important than keeping the publication tree small. Modules that look auxiliary, experimental, geometric, or intermediate are therefore retained when they are part of the current audited Lean source tree. This avoids creating a third repository whose formal statements silently depend on files left behind in `RH_Lean`.
