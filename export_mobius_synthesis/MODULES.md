# Möbius Synthesis — Lean source map

This export intentionally contains the full import-audited `RHLean` source snapshot rather than a minimal transitive closure. `RHLean.lean` is the authoritative file-by-file inventory. The synchronized manifest currently imports **246 Lean modules**, and every imported `RHLean.*` module is mirrored under the corresponding path in `RHLean/` using the same Git blob as the parent development.

## Elementary prime-sieve seam

The synthesis now records an elementary seam beneath the later square-wheel Fourier bridge.

`RHLean.Proof.PrimeSievePostSqrtGap` defines the all-plus prime-comb state by reversing the seed orientation of the existing `seededPrimeComb`. After all primes through a cutoff `y` strictly above `sqrt x` have acted, it proves the exact identity

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q)).
```

The proof is finite bookkeeping only. Under square-root coverage, every unresolved squarefree source has one remaining prime factor `q > y`; applying that fresh prime changes its sign once. The module reindexes the unresolved sources by their unique canonical `(c,q)` pair and identifies the cofactor-first batch with the lower-scale Mertens prime tail.

`RHLean.Proof.PrimeSieveSquareRootTransport` specializes this theorem to the complete square endpoint `x = R^2 - 1`, `y = R`, and identifies the two prime-sieve states with the original square-block smooth and transport variables:

```text
before remaining large-prime flips = smooth + transport
after all prime flips              = smooth - transport = M(R^2-1)
```

In particular it proves

```text
before - M(R^2-1) = 2 * transport
before + M(R^2-1) = 2 * smooth.
```

This is a foundational representation theorem, not a quantitative estimate. It does not alter the synthesis endpoint or claim progress on the open nonzero-response bound.

## Square-block track

The square-block side is centered on:

- square-prefix Mertens endpoints and interpolation;
- canonical largest-prime and cofactor decomposition;
- low and high height partition and low occupancy;
- squared-complex Fermat and cofactor geometry;
- square-root transport and dyadic compression;
- lifetime active sets, death shells, and survivor reduction;
- canonical gap and ancestry, signed Gram, and terminal quadratic closure;
- zero-cutoff ancestry and the square-root ancestry root and successor constructions.

Representative entry modules include `SquarePrefixMertensBridge`, `CanonicalHighSectorCore`, `CanonicalLowOccupancy`, `SquareBlockSurvivorBridge`, `LifetimeEndpointDecomposition`, `CanonicalGapAncestryQuadraticClosure`, `CanonicalGapAncestryZeroCutoff`, `SquareRootAncestryRoot`, and `SquareRootAncestrySuccessor`.

## Prime-wheel track

The prime-wheel side is centered on:

- deterministic Möbius reconstruction and primorial-wheel arithmetic;
- finite torus Fourier pairing;
- arithmetic and complete spectra;
- reduced additive conductors and conductor Gram decomposition;
- periodic raw response and coconductor subtraction;
- Möbius reindexing of raw and smooth conductor families;
- raw boundary pairing and expansion collapse;
- full-conductor uniform packets and the reindexed residual;
- classical Ramanujan identification;
- boundary and bulk divisor-residue reductions;
- Mertens transfer.

Representative entry modules include `PrimeWheelFiniteSystem`, `PrimeWheelMobiusRecovery`, `PrimeWheelFourierReduction`, `PrimeWheelConductorGram`, `PrimeWheelPeriodicRawBridge`, `PrimeWheelRawConductorMobiusReindex`, `PrimeWheelRawBoundaryMobiusPairing`, `PrimeWheelRawBoundaryExpansionCollapse`, `PrimeWheelFullConductorMobiusReindexedResidual`, `PrimeWheelRamanujanIdentification`, `PrimeWheelRamanujanBoundaryBulkReduction`, and `RamanujanDivisorBoundaryBulk`.

## Synthesis seam

The modules most directly joining the two descriptions include:

- `RHLean.Proof.PrimeSievePostSqrtGap`
- `RHLean.Proof.PrimeSieveSquareRootTransport`
- `RHLean.Arithmetic.PrimorialWheelMinimalTorus`
- `RHLean.Arithmetic.PrimeProductLowerBound`
- `RHLean.Analysis.SquareWheelNesting`
- `RHLean.Analysis.SquareWheelQuadraticSampling`
- `RHLean.Analysis.SquareWheelZeroModeElimination`
- `RHLean.Analysis.SquareWheelQuantitativeBridge`
- `RHLean.Analysis.PrimeWheelRawConductorMobiusReindex`
- `RHLean.Analysis.PrimeWheelRawBoundaryMobiusPairing`
- `RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse`
- `RHLean.Analysis.PrimeWheelFullConductorMobiusReindexedResidual`
- `RHLean.Analysis.PrimeWheelSmoothConductorMobiusReindex`
- `RHLean.Analysis.PrimeWheelRamanujanIdentification`
- `RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction`
- `RHLean.Analysis.PrimeWheelRamanujanBoundaryBulkReduction`
- `RHLean.Analysis.RamanujanDivisorBoundary`
- `RHLean.Analysis.RamanujanDivisorBoundaryBulk`
- `RHLean.Analysis.PrimorialWheelMertensTransfer`

The prime-sieve modules give the elementary seam: fresh-prime parity produces the square-root transport variable exactly. `SquareWheelQuantitativeBridge` remains the synthesis-facing quantitative endpoint of the later spectral bridge: it proves the factor-six modulus separation, the uniform square-sample ratio bound below `1/6`, defines `primorialExpansionReindexedNumerator`, and identifies `squareWheelNonzeroSampleResponse` with the expansion-reindexed numerator after the zero mode is removed.

## Mertens and zeta bridge

The current parent development also contains the forward analytic chain needed around the terminal Mertens and zeta statements:

- `RHLean.Analysis.DivisorUpperMobius`
- `RHLean.Analysis.MertensStepFunction`
- `RHLean.Analysis.MertensStepGrowth`
- `RHLean.Analysis.MertensPowerGrowth`
- `RHLean.Analysis.MertensEnergyRHForward`
- `RHLean.Analysis.MertensMellinLSeriesBridge`
- `RHLean.Analysis.MertensMellinContinuation`
- `RHLean.Analysis.MertensZetaIdentityContinuation`
- `RHLean.Proof.TerminalMertensForward`
- `RHLean.Proof.TerminalMertensReduction`
- `RHLean.Proof.MutablePNTClosure`
- `RHLean.Proof.RiemannHypothesisBridge`
- `RHLean.Proof.TerminalAxiomAudit`

## Modules added since the original 214-module synthesis snapshot

The current synchronized parent manifest contains **32** modules beyond the original 214-module synthesis snapshot. The previous synthesis export had already synchronized 21 of them. This synchronization catches up the nine survivor modules that were subsequently imported by the parent root and adds the two new elementary prime-sieve seam modules.

Previously synchronized 21-module delta:

```text
RHLean.Analysis.DivisorUpperMobius
RHLean.Analysis.MertensEnergyRHForward
RHLean.Analysis.MertensMellinContinuation
RHLean.Analysis.MertensMellinLSeriesBridge
RHLean.Analysis.MertensPowerGrowth
RHLean.Analysis.MertensStepFunction
RHLean.Analysis.MertensStepGrowth
RHLean.Analysis.MertensZetaIdentityContinuation
RHLean.Analysis.PrimeWheelFullConductorMobiusReindexedResidual
RHLean.Analysis.PrimeWheelFullConductorUniformPacket
RHLean.Analysis.PrimeWheelRamanujanBoundaryBulkReduction
RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse
RHLean.Analysis.PrimeWheelRawBoundaryMobiusPairing
RHLean.Analysis.PrimeWheelRawConductorMobiusReindex
RHLean.Analysis.PrimeWheelSmoothConductorMobiusReindex
RHLean.Analysis.RamanujanDivisorBoundaryBulk
RHLean.Analysis.SquareWheelQuantitativeBridge
RHLean.Proof.CanonicalGapAncestryZeroCutoff
RHLean.Proof.SquareRootAncestryRoot
RHLean.Proof.SquareRootAncestrySuccessor
RHLean.Proof.TerminalMertensForward
```

Additional 11-module synchronization in this change:

```text
RHLean.Proof.SurvivorDyadicStaticCancellation
RHLean.Proof.SurvivorLargePrimeRootBoundary
RHLean.Proof.SurvivorPairEffectiveModulus
RHLean.Proof.SurvivorPrimeFaceFrontier
RHLean.Proof.SurvivorPrimeFaceRealization
RHLean.Proof.SurvivorResidueCollisionReindex
RHLean.Proof.SurvivorResidueCovariance
RHLean.Proof.SurvivorResidueCovarianceCriterion
RHLean.Proof.SurvivorResiduePrimeToggle
RHLean.Proof.PrimeSievePostSqrtGap
RHLean.Proof.PrimeSieveSquareRootTransport
```

## Scope and synchronization policy

For synthesis, dependency completeness is more important than keeping the publication tree small. Modules that look auxiliary, experimental, geometric, or intermediate are therefore retained whenever they are part of the current audited root import manifest.

The synchronization invariant is simple: `export_mobius_synthesis/RHLean.lean` must match the parent `RHLean.lean`, and every internal import in that manifest must resolve to a corresponding file under `export_mobius_synthesis/RHLean/`. When the parent adds an imported module, the export should copy the parent blob and update the manifest in the same synchronization commit. This avoids a publication export whose formal statements silently depend on files left behind in `RH_Lean`.
