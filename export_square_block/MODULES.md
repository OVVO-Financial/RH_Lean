# Square-Block Möbius — Lean module manifest

This manifest lists the curated Lean source snapshots published under `lean/` in **Square-Block Möbius**. The inventory is selected by **mathematical paper scope**, not by transitive import closure. The modules were verified in the full Lean development before publication export; supporting implementation modules outside the square-block paper remain outside this standalone snapshot.

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

This export intentionally contains only the mathematics represented in the standalone square-block manuscript. Modules belonging to other block architectures, or to a future synthesis between architectures, are outside scope and are not copied here.
