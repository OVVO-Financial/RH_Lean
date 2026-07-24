# Formalization inventory and sequence

This document is the canonical implementation order for `RH_Lean`.

It records only what is actually compiled, distinguishes exact algebraic layers from unproved analytic obligations, and preserves corrections explicitly rather than rewriting the PR history.

The governing invariants are:

- no `sorry`, `admit`, new axioms, opaque theorem substitutes, weakened statements, changed indexing, or circular RH assumptions;
- modulus `2r`, not `r`, is the canonical quadratic-phase modulus;
- the prime-3 cell-mask energy and prime-3 quadratic phase remain type-separated;
- the high-sector target is the full signed Gram recombination, not separate shellwise positivity;
- theorem-predicted subtraction remains distinct from true orthogonal projection;
- numerical finite-range claims enter only through a proved certificate checker;
- a prefix estimate from zero must never be presented as a uniform local-window estimate;
- the RH bridge must use the manuscript's uniform local criterion
  `V_loc(N,H) ≪_ε H N^(2+ε)` for `1 ≤ H ≤ N`, not merely a global
  `O(N^(3+ε))` average.

## 1. Compiled inventory

The root library imports thirty-five theorem modules.

### Arithmetic and cell structure

1. `RHLean.Arithmetic.MoebiusDoubling`
2. `RHLean.Arithmetic.FourSlotCell`
3. `RHLean.Arithmetic.PrimeThreeActivation`
4. `RHLean.Arithmetic.PrimeSquareMod24`
5. `RHLean.Arithmetic.PrimeSquareMod40`
6. `RHLean.CellMask.PrimeThreeMeanEnergy`

These modules compile the exact Möbius doubling and four-slot identities, prime-3 activation and mean energy, and the required prime-square congruence classes.

### Corrected modulus-`2r` phase architecture

7. `RHLean.Analysis.QuadraticPhasePeriod`
8. `RHLean.Analysis.QuadraticExponentCongruence`
9. `RHLean.Analysis.QuadraticShiftDichotomy`
10. `RHLean.Analysis.ComplexQuadraticPhase`
11. `RHLean.Analysis.QuadraticPhaseShiftSign`
12. `RHLean.Analysis.ReducedQuadraticGauss`
13. `RHLean.Analysis.SmallModulusResonance`
14. `RHLean.Analysis.ReducedSquareClassMod40`

These modules retain the canonical modulus `2r`, exact shift signs, reduced Gauss normalization, small-modulus resonance, and the two exact square-class modes modulo `40`.

### Factor geometry

15. `RHLean.Geometry.FermatCoordinates`
16. `RHLean.Geometry.ComplexSquareRecovery`
17. `RHLean.Geometry.CofactorParabolas`
18. `RHLean.Geometry.TwoABDisplacement`
19. `RHLean.Geometry.SquareMapConformality`
20. `RHLean.Geometry.ComplexSquareFiber`

These modules compile the midpoint/half-gap coordinates, squared complex recovery, cofactor parabolas, `2ab` displacement, conformality, and positive-branch injectivity.

### Kernel and exact signed Hilbert/Gram machinery

21. `RHLean.Kernel.FixedPackets`
22. `RHLean.Analysis.HeightShellGram`
23. `RHLean.Analysis.OrthogonalResidual`
24. `RHLean.Analysis.ResonantProjection`
25. `RHLean.Analysis.ResonantLeakage`
26. `RHLean.Analysis.BlockLyapunovClosure`
27. `RHLean.Analysis.ActualResidualDecomposition`
28. `RHLean.Analysis.ResonantCofactorCancellation`
29. `RHLean.Analysis.ActualForcingEstimates`
30. `RHLean.Analysis.JointGramControl`

These modules keep the full shell/cofactor/mode/row recombination inside the norm, retain every signed off-diagonal Gram term, separate true orthogonal projection from theorem-predicted subtraction, and expose the full block recurrence and Lyapunov closure hypotheses.

### Certified verification, residual closure, and actual-start frame

31. `RHLean.Verification.FiniteRangeCertificates`
32. `RHLean.Analysis.UniformResidualBound`
33. `RHLean.Analysis.ActualStartSignedFrame`

The certificate checker is sound but does not manufacture a numerical run or a mathematical realization. The uniform residual theorem retains the finite realization and asymptotic full-joint control explicitly. The actual-start theorem proves the exact prefix identity

```text
actualFrameEnergy(N)
  = 4 * predictionFrameEnergy(N)
    + residualFrameEnergy(N)
    + signedPredictionResidualInteraction(N)
```

and derives the sharp prefix inequality only from explicit signed absorption.

### Corrected uniform-local layer and RH bridge

34. `RHLean.Analysis.ActualStartLocalSignedFrame`
    - defines actual, prediction, residual, and signed-interaction energies on `[N,N+H)`;
    - proves the exact local signed energy identity;
    - proves the residual contribution is at most `H * bound` from the pointwise residual bound;
    - introduces `ActualStartLocalSignedFrameControl`, separate from prefix control;
    - proves the sharp constant-`4` frame inequality on every finite window;
    - proves the local theorem specializes to the old prefix theorem at `N = 0`.

35. `RHLean.Analysis.RiemannHypothesisBridge`
    - exposes mathlib's `RiemannHypothesis` as `RiemannHypothesisStatement`;
    - defines `ActualStartLocalSignedFrameStatement`;
    - defines the manuscript's uniform local criterion

      ```text
      V_loc(N,H) ≪_ε H N^(2+ε),  1 ≤ H ≤ N;
      ```

    - defines the pointwise square-prefix statement;
    - proves the elementary manuscript step `uniform local → pointwise` by taking `H = 1`;
    - separates the remaining prediction transport, RH-to-local direction, and pointwise/Mertens-to-RH direction as ordinary fields of `ActualStartRHBridge`;
    - composes the compiled local frame theorem with that explicit bridge;
    - introduces no project axiom and makes no unconditional RH claim.

## 2. Correction of the PR #42 target

PR #42 compiled an axiom-free conditional theorem, but its asymptotic target was the global prefix average

```text
actualStartFrameEnergy(N) = O(N^(3+ε)).
```

That statement is a natural cubic benchmark, but it is not the manuscript's pointwise RH criterion. A global prefix inequality does not imply a translated local-window inequality by subtraction.

The manuscript's actual criterion is

```text
∀ ε > 0, ∃ C ≥ 0, ∀ N H,
  1 ≤ H → H ≤ N →
  V_loc(N,H) ≤ C * H * N^(2+ε).
```

Taking `H = 1` gives the pointwise square-prefix estimate used in the Mertens interpolation argument. The corrective local layer is therefore a genuine missing dependency, not a cosmetic restatement.

PR #43 corrects the formal target while preserving the historical fact that PR #42 was formally valid as a conditional composition theorem.

## 3. Current checkpoint

The compiled algebraic and signed-Gram chain now reaches the exact local statement

```text
actualStartLocalFrameEnergy(start,N,H)
  ≤ 4 * actualStartLocalPredictionFrameEnergy(start,N,H)
```

under explicit finite-range realization, asymptotic full-joint control, exact starting configuration, and uniform local signed-interaction absorption.

The corrected bridge then uses:

```text
local signed-frame
  → uniform local square-prefix bound
  → pointwise square-prefix bound          [proved by H = 1]
  → RiemannHypothesis.
```

The reverse RH-to-uniform-local direction is retained separately so that the final criterion can be stated as an equivalence once its concrete classical/realization proof is supplied.

The following remain unproved and explicit:

- the concrete prediction estimate transporting the local signed-frame inequality to `H N^(2+ε)`;
- the identification of `start.actual N` with the manuscript's square-prefix Mertens quantity;
- the RH-to-uniform-local Mertens direction;
- the pointwise square-prefix/Mertens interpolation implication to RH;
- the concrete finite-range realization, asymptotic contraction, exact start, and local signed-interaction-control instances.

## 4. Formalization sequence

### Phase I — corrected complex quadratic-phase layer

- [x] **1. Complex quadratic phase API** — PR #21.
- [x] **2. Exact shift-by-`r` sign law** — PR #22.
- [x] **3. Corrected reduced quadratic Gauss factor** — PR #23.
- [x] **4. Exact small-modulus resonance** — PR #24.

### Phase II — exact combinatorial and geometry layers

- [x] **5. Prime-3 cell-mask mean energy** — PR #27.
- [x] **6. `2ab` displacement and lifetime geometry** — PR #28.
- [x] **7. Reduced square-class phase support modulo `40`** — PR #29.

### Phase III — exact signed Hilbert/Gram machinery

- [x] **8. Height-shell Gram identity** — PR #30.
- [x] **9. Orthogonal residual** — PR #31.
- [x] **10. Scale-dependent resonant projection skeleton** — PR #32.
- [x] **11. Explicit resonant/nonresonant leakage operator** — PR #33.
- [x] **12. Abstract weighted affine Lyapunov closure** — PR #34.

### Phase IV — number-theoretic closure

- [x] **13. Actual residual decomposition** — PR #35.
- [x] **14. Resonant Möbius cofactor cancellation** — PR #36.
- [x] **15. Low-height, endpoint, and boundary estimates** — PR #37.
- [x] **16. Full joint signed Gram control** — PR #38.
- [x] **17. Certified finite-range checker** — PR #39.
- [x] **18. Uniform full residual bound** — PR #40.
- [x] **19. Actual-start prefix signed-frame theorem** — PR #41.
- [x] **20. Explicit global conditional bridge** — PR #42; formally valid but insufficient as the manuscript's RH criterion.

### Phase V — corrected localization

- [x] **21. Uniform local signed-frame and corrected RH criterion** — anticipated PR #43.
  - proves the exact `[N,N+H)` energy identity;
  - adds local signed absorption as a separate hypothesis;
  - proves the sharp local frame inequality;
  - replaces the global cubic bridge target with the manuscript's uniform local bound;
  - proves the `H = 1` extraction to a pointwise square-prefix bound;
  - keeps the remaining classical Mertens/RH directions and concrete realization obligations explicit.

## 5. Dependency spine

```text
exact arithmetic, factor geometry, and modulus-2r phase structure
        ↓
full signed shell/cofactor/mode/row Gram identity
        ↓
finite certificate checker + explicit realization
        ↓
weighted affine full-joint residual closure
        ↓
actual-start prefix signed frame
        ↓
separate uniform local signed-interaction control
        ↓
uniform local actual-start signed frame
        ↓
prediction transport to H N^(2+ε)
        ↓
H = 1 pointwise square-prefix bound
        ↓
Mertens interpolation / classical RH criterion
```

## 6. Maintenance rule

Whenever a theorem layer is merged, the same PR must:

- record the completing PR number;
- update the compiled inventory and current checkpoint;
- preserve corrections explicitly rather than silently changing historical claims;
- identify every remaining unproved realization or analytic implication;
- update `FORMALIZATION_CHECKLIST.md` on the same branch;
- pass `bash scripts/audit_assumptions.sh` and `lake build RHLean --wfail` with no warnings.