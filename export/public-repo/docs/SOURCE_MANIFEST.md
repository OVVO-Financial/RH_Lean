# Source provenance

This export was assembled from `OVVO-Financial/RH_Lean` at merged commit:

`f6110ca00b27a0a329a0f74db8b7747ad4bae234`

The arithmetic and Fourier theorem files are copied byte-for-byte from the merged repository by reusing their Git blob objects.

## Exact merged source modules

### Arithmetic

- `RHLean/Arithmetic/BooleanCubeCancellation.lean`
- `RHLean/Arithmetic/TruncatedBooleanCube.lean`
- `RHLean/Arithmetic/PrimeProductCubeFrontier.lean`
- `RHLean/Arithmetic/PrimeFaceMoebius.lean`
- `RHLean/Arithmetic/PrimesUpToFrontier.lean`
- `RHLean/Arithmetic/PrimeWheelFiniteSystem.lean`
- `RHLean/Arithmetic/PrimorialWheelScale.lean`
- `RHLean/Arithmetic/PrimeWheelMobiusRecovery.lean`
- `RHLean/Arithmetic/PrimorialWheelPrefixIdentity.lean`
- `RHLean/Arithmetic/PrimorialWheelScaleGrowth.lean`

### Analysis

- `RHLean/Analysis/FiniteTorusFourierPairing.lean`
- `RHLean/Analysis/PrimeWheelFourierReduction.lean`
- `RHLean/Analysis/PrimeWheelTorusRealization.lean`
- `RHLean/Analysis/PrimeWheelJointSpectrum.lean`
- `RHLean/Analysis/PrimeWheelArithmeticSpectrum.lean`
- `RHLean/Analysis/PrimeWheelCompleteSpectrum.lean`
- `RHLean/Analysis/PrimeWheelHarmonicCriterion.lean`
- `RHLean/Analysis/PrimeWheelConductorGram.lean`
- `RHLean/Analysis/PrimeWheelDirichletResponse.lean`
- `RHLean/Analysis/PrimeWheelExplicitCriterion.lean`
- `RHLean/Analysis/PrimorialWheelMertensTransfer.lean`

## Public adapters

The export replaces two sandbox-coupled bridge modules with minimal public adapters at the same module paths:

- `RHLean/Analysis/SquarePrefixMertensBridge.lean` — defines only the Mertens summatory function and squared growth criterion required by the exact reduction.
- `RHLean/Analysis/PrimeWheelRHBridge.lean` — names Mathlib's `RiemannHypothesis` proposition and keeps the classical Mertens/RH theorem as an explicit argument.

`RHLean/Analysis/PublicPrimeWheelReduction.lean` exposes the final public theorem without a caller-supplied primorial bridge.

## Dependency pin

- Lean: `v4.24.0`
- Mathlib: `v4.24.0`
