# Möbius Synthesis — Lean source map

This export intentionally contains the full import-audited `RHLean` source snapshot rather than a minimal transitive closure. `RHLean.lean` is the authoritative file-by-file inventory. The synchronized manifest currently imports **247 Lean modules**, and every imported `RHLean.*` module is mirrored under the corresponding path in `RHLean/` using the same Git blob as the parent development.

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

`RHLean.Analysis.PrimeSievePNTCentering` then separates the explicit prime tail into a deterministic logarithmic-integral density bulk and the exact prime-indicator discrepancy. Its singleton density uses the same Li convention as the existing exact-activity prime-density route:

```text
density(q) = Li(q) - Li(q-1).
```

The module proves the exact split

```text
prime tail = PNT bulk + prime-distribution error
```

and pushes it through the **actual** square-wheel zero-mode centering coefficient `(X_n-L_k)/Q_k`. Thus the canonical nonzero response has the exact forms

```text
H_{k,n} = centered PNT-corrected comb - 2 * centered prime error
```

and

```text
H_{k,n}
  = centered all-plus comb
    - 2 * centered PNT bulk
    - 2 * centered prime error.
```

It also proves the corresponding norm-transfer inequality. These are exact interfaces, not prime-distribution estimates: no PNT error bound, Bombieri–Vinogradov estimate, large-sieve estimate, or RH-scale power saving is asserted.

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
- `RHLean.Analysis.PrimeSievePNTCentering`
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

The prime-sieve modules give the elementary seam: fresh-prime parity produces the square-root transport variable exactly, then Li-density centering exposes its deterministic prime bulk and exact prime-count discrepancy. `SquareWheelQuantitativeBridge` remains the synthesis-facing quantitative endpoint of the later spectral bridge: it proves the factor-six modulus separation, the uniform square-sample ratio bound below `1/6`, defines `primorialExpansionReindexedNumerator`, and identifies `squareWheelNonzeroSampleResponse` with the expansion-reindexed numerator after the zero mode is removed. `PrimeSievePNTCentering` proves that the same `H_{k,n}` can simultaneously be read as the actual wheel centering of the PNT-corrected prime-sieve process plus its residual prime-distribution error.

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

The current synchronized parent manifest contains **33** modules beyond the original 214-module synthesis snapshot. The previous synchronization reached 246 modules; this change adds the one new PNT-centering seam module while retaining the two elementary prime-sieve bridge modules and the earlier survivor synchronization.

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

Subsequent 11-module synchronization:

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

Current one-module synchronization:

```text
RHLean.Analysis.PrimeSievePNTCentering
```

## Scope and synchronization policy

For synthesis, dependency completeness is more important than keeping the publication tree small. Modules that look auxiliary, experimental, geometric, or intermediate are therefore retained whenever they are part of the current audited root import manifest.

The synchronization invariant is simple: `export_mobius_synthesis/RHLean.lean` must match the parent `RHLean.lean`, and every internal import in that manifest must resolve to a corresponding file under `export_mobius_synthesis/RHLean/`. When the parent adds an imported module, the export should copy the parent blob and update the manifest in the same synchronization commit. This avoids a publication export whose formal statements silently depend on files left behind in `RH_Lean`.
