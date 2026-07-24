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
  `O(N^(3+ε))` average;
- an exact low/high signal decomposition does not give an energy subtraction identity;
  total/high criterion equivalence must use the two norm inequalities and the
  separately proved local low-sector bound.

## 1. Compiled inventory

The root library imports thirty-six theorem modules.

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

### Exact geometric low/high reduction

36. `RHLean.Analysis.GeometricRHReduction`
    - defines `ActualStartGeometricPartition` with exact signal-level recombination
      `actual = low + high`;
    - carries the proved pointwise squared low-sector estimate as explicit geometric data;
    - defines translated-window low and high energies;
    - proves the elementary uniform local low-sector bound `V_low(N,H) ≤ 4 K H N^2`;
    - proves both energy inequalities

      ```text
      V_total ≤ 2 V_low + 2 V_high,
      V_high  ≤ 2 V_total + 2 V_low;
      ```

    - proves the total and high-sector `H N^(2+ε)` criteria are equivalent without estimating a cross term;
    - composes that result with `ActualStartRHBridge` to state the pure architectural equivalence between the geometric high-sector criterion and RH.

## 2. Correction history

PR #42 compiled an axiom-free conditional theorem, but its asymptotic target was the global prefix average

```text
actualStartFrameEnergy(N) = O(N^(3+ε)).
```

That statement is a natural cubic benchmark, but it is not the manuscript's pointwise RH criterion. A global prefix inequality does not imply a translated local-window inequality by subtraction.

PR #43 corrected the target to

```text
∀ ε > 0, ∃ C ≥ 0, ∀ N H,
  1 ≤ H → H ≤ N →
  V_loc(N,H) ≤ C * H * N^(2+ε).
```

Taking `H = 1` gives the pointwise square-prefix estimate used in the Mertens interpolation argument.

PR #44 resolves the next architectural issue. The exact signal identity

```text
S = S_low + S_high
```

does not imply an energy subtraction identity because the low/high cross term remains. However, the two elementary norm inequalities and the proved local low-sector bound show that the total and high-sector local growth criteria are exactly equivalent. The cross term never needs a separate estimate.

## 3. Current checkpoint

The compiled chain now distinguishes two statements:

1. the analytic theorem to be proved inside the signed-Gram architecture;
2. the unconditional equivalence showing that theorem is exactly the geometric form of the RH criterion.

For an exact geometric partition with pointwise low-sector bound,

```text
ActualStartHighUniformLocalBoundedStatement(partition)
  ↔ ActualStartUniformLocalBoundedStatement(start)
  ↔ RiemannHypothesisStatement
```

where the final equivalence uses the explicit classical/realization fields of `ActualStartRHBridge`.

The first equivalence is fully proved by the new geometric reduction module. It requires no high-sector estimate and no control of the low/high cross term.

The following remain unproved and explicit:

- the concrete construction identifying `start.actual N` with the manuscript's square-prefix Mertens quantity;
- the concrete construction of the manuscript's low/high geometric partition and its pointwise low-sector constant;
- the RH-to-uniform-local Mertens direction inside Lean;
- the pointwise square-prefix/Mertens interpolation implication to RH inside Lean;
- the local prediction estimate transporting the signed-frame inequality to `H N^(2+ε)`;
- the concrete finite-range realization, asymptotic contraction, exact start, and local signed-interaction-control instances.

The geometric reduction itself is no longer an open analytic obligation.

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

- [x] **21. Uniform local signed-frame and corrected RH criterion** — PR #43.

### Phase VI — geometric criterion equivalence

- [x] **22. Exact low/high geometric reduction** — PR #44.
  - proves the translated-window low-sector bound from the pointwise linear geometric bound;
  - proves total↔high local-criterion equivalence by norm inequalities;
  - proves high-sector criterion↔RH through the explicit square-prefix bridge;
  - does not assume or prove the high-sector estimate itself.

## 5. Dependency spine

```text
exact arithmetic, factor geometry, and modulus-2r phase structure
        ↓
exact signal-level low/high geometric partition
        ↓
elementary translated-window low-sector bound
        ↓
total local criterion ↔ high-sector local criterion
        ↓
classical square-prefix Mertens bridge ↔ RH
```

The separate analytic proof program remains:

```text
full signed shell/cofactor/mode/row Gram identity
        ↓
finite certificate checker + explicit realization
        ↓
weighted affine full-joint residual closure
        ↓
uniform local actual-start signed frame
        ↓
prediction transport to H N^(2+ε)
        ↓
high-sector local criterion
```

## 6. Maintenance rule

Whenever a theorem layer is merged, the same PR must:

- record the completing PR number;
- update the compiled inventory and current checkpoint;
- preserve corrections explicitly rather than silently changing historical claims;
- identify every remaining unproved realization or analytic implication;
- update `FORMALIZATION_CHECKLIST.md` on the same branch;
- pass `bash scripts/audit_assumptions.sh` and `lake build RHLean --wfail` with no warnings.
