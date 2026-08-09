# Square-Block Möbius — Lean module manifest

This manifest lists the Lean sources published under `lean/` in **Square-Block Möbius**.

The **paper-facing inventory** below is selected by mathematical paper scope: these are the modules that state the results of the standalone square-block manuscript. Alongside them this repository also ships the **transitive import closure** of that inventory, so the library builds and is machine-checked here. The closure modules are listed under [Supporting closure modules](#supporting-closure-modules); they carry no paper-facing statements and are present so that `lake build RHLean --wfail` succeeds in this repository.

The `Baseline coupling audit` workflow builds the library, prints the paper-facing survivor endpoint together with its axiom dependencies, and fails if that endpoint rests on `sorryAx`.

## Square-prefix criterion and canonical decomposition

- `RHLean/Analysis/SquarePrefixMertensBridge.lean` — Mertens summatory function, exact square endpoint, square-prefix sequence, interpolation bridge.
- `RHLean/Analysis/ConcreteSquarePrefixGeometry.lean` — local-energy criterion, low/high geometric partition interface, total/high equivalences.
- `RHLean/Analysis/CanonicalHighSectorCore.lean` — canonical largest-prime factor, cofactor, doubled height, square blocks, low/high increments and prefixes.
- `RHLean/Analysis/CanonicalLowOccupancy.lean` — unconditional low-height clustering and low-increment control.
- `RHLean/Analysis/CanonicalHighSectorBridge.lean` — canonical high-sector criterion and conditional RH composition.
- `RHLean/Analysis/CanonicalExtremePrimeSupport.lean` — extreme-largest-prime theorem: composite sources below `x` have largest prime at most `floor(x/2)`; canonical cofactors are also at most `floor(x/2)`.
- `RHLean/Analysis/MertensEnergyCriterion.lean` — protected Mertens energy criterion interface used by the square-prefix bridge.
- `RHLean/Analysis/SquarePrefixHeightPartition.lean` — exact concrete square-prefix height partition.

## Squared-complex geometry

- `RHLean/Geometry/FermatCoordinates.lean` — midpoint and half-gap factor coordinates.
- `RHLean/Geometry/ComplexSquareRecovery.lean` — exact recovery of factor data from squared-complex coordinates.
- `RHLean/Geometry/ComplexSquareFiber.lean` — fibre and injectivity statements for the square map.
- `RHLean/Geometry/CofactorParabolas.lean` — fixed-cofactor parabola geometry.
- `RHLean/Geometry/SquareMapConformality.lean` — conformal differential and Jacobian scale.
- `RHLean/Geometry/TwoABDisplacement.lean` — exact `2ab` displacement laws.

## Intrinsic arithmetic and phase identities appearing in the manuscript

- `RHLean/Arithmetic/MoebiusDoubling.lean` — Möbius doubling identity.
- `RHLean/Arithmetic/FourSlotCell.lean` — exact four-slot dyadic cell compression.
- `RHLean/Arithmetic/PrimeSquareMod24.lean` — prime-square congruence modulo 24.
- `RHLean/Arithmetic/PrimeSquareMod40.lean` — prime-square classes modulo 40 used by the diagnostic section.
- `RHLean/Analysis/ComplexQuadraticPhase.lean` — complex quadratic phase definitions.
- `RHLean/Analysis/ReducedQuadraticGauss.lean` — reduced quadratic Gauss factors on the correct modulus.
- `RHLean/Analysis/SmallModulusResonance.lean` — exact small-modulus resonance statements.

## Intrinsic square-root transport identities

- `RHLean/Analysis/TwoABScaleTransfer.lean` — source-resolved entry, transition, lifetime, and exact scale transfer.
- `RHLean/Analysis/TwoABPrimeDilation.lean` — prime-first transport and reciprocal prime-dilation formulas.
- `RHLean/Analysis/DyadicTransportCompression.lean` — dyadic parent-child transport compression.
- `RHLean/Analysis/DyadicTransportCanonicalForm.lean` — canonical-source form of the dyadic compression.
- `RHLean/Analysis/SquareRootMatchedTransport.lean` — matched born-smooth and transport cancellation object.
- `RHLean/Analysis/SquareRootTransportRealization.lean` — exact realization of the original square-root transport term.

## Lifetime and death-process refinement

- `RHLean/Proof/LifetimeActiveSet.lean` — exact active-survivor set and mass.
- `RHLean/Proof/LifetimeLocalEnergyCriterion.lean` — lifetime active and absorbed local-energy criterion.
- `RHLean/Proof/LifetimeEndpointDecomposition.lean` — exact births = survivors + deaths endpoint decomposition.
- `RHLean/Proof/DeathProcessShellIdentity.lean` — exact death-shell identity.
- `RHLean/Proof/DeathShellDivisorFibers.lean` — divisor-fibre majorant for the death shell.
- `RHLean/Proof/DeathShellSubpolynomial.lean` — subpolynomial divisor-window estimate and unconditional RH-scale death-process local bound.
- `RHLean/Analysis/SquareBlockDeathProcess.lean` — paper-facing Analysis wrapper for the divisor-window and accumulated-death estimates.
- `RHLean/Analysis/SquareBlockSurvivorBridge.lean` — paper-facing active-survivor kernel and endpoint reduction after death removal.

## Scope boundary

The paper-facing inventory intentionally covers only the mathematics represented in the standalone square-block manuscript. Modules belonging to other block architectures, or to a synthesis between architectures, are outside its scope and are not claimed here. The supporting closure modules listed below are shipped solely to make that inventory buildable, and are not part of the manuscript's claims.


## Supporting closure modules

These modules are imported, directly or transitively, by the paper-facing inventory above. They are present so that this repository builds on its own; the manuscript makes no claim about them beyond their use as dependencies.

### `RHLean/Analysis`

- `RHLean/Analysis/FiniteTorusFourierPairing.lean`
- `RHLean/Analysis/QuadraticExponentCongruence.lean`
- `RHLean/Analysis/QuadraticPhasePeriod.lean`

### `RHLean/Arithmetic`

- `RHLean/Arithmetic/FullPrimeFactorizationState.lean`

### `RHLean/Kernel`

- `RHLean/Kernel/FixedPackets.lean`

### `RHLean/Proof`

- `RHLean/Proof/ActualForcingEstimates.lean`
- `RHLean/Proof/ActualResidualDecomposition.lean`
- `RHLean/Proof/ActualStartLocalSignedFrame.lean`
- `RHLean/Proof/ActualStartSignedFrame.lean`
- `RHLean/Proof/BalancedCanonicalGap.lean`
- `RHLean/Proof/BirthMovingAbsorption.lean`
- `RHLean/Proof/BlockLyapunovClosure.lean`
- `RHLean/Proof/CanonicalGapAncestryBridge.lean`
- `RHLean/Proof/CanonicalGapAncestryFlow.lean`
- `RHLean/Proof/CanonicalGapPrefixGram.lean`
- `RHLean/Proof/CanonicalSignedParent.lean`
- `RHLean/Proof/ConcreteSquarePrefixCofactorRealization.lean`
- `RHLean/Proof/CumulativeHeightFlow.lean`
- `RHLean/Proof/DeathProcessArithmetic.lean`
- `RHLean/Proof/DeathShellCardinalityAndCentering.lean`
- `RHLean/Proof/DeathShellCofactorParity.lean`
- `RHLean/Proof/FullFactorizationBridge.lean`
- `RHLean/Proof/GeometricRHReduction.lean`
- `RHLean/Proof/HeightShellGram.lean`
- `RHLean/Proof/HeightShellReconstruction.lean`
- `RHLean/Proof/JointGramControl.lean`
- `RHLean/Proof/LifetimeOverlapKernel.lean`
- `RHLean/Proof/NormalizedCofactorExpansion.lean`
- `RHLean/Proof/ResonantLeakage.lean`
- `RHLean/Proof/ResonantProjection.lean`
- `RHLean/Proof/RiemannHypothesisBridge.lean`
- `RHLean/Proof/SignedCanonicalHeight.lean`
- `RHLean/Proof/SurvivorResidueCovariance.lean`
- `RHLean/Proof/SurvivorZeroMode.lean`
- `RHLean/Proof/UniformResidualBound.lean`

### `RHLean/Verification`

- `RHLean/Verification/FiniteRangeCertificates.lean`
