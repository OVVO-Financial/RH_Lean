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
  separately proved local low-sector bound;
- the canonical square-prefix endpoint is exactly `X_n = (n+1)^2 - 1`;
- the final mathlib integration theorem must accept the classical Mertens↔RH
  equivalence directly, without an abstract start-sequence bridge.

## 1. Compiled inventory

The root library imports forty-nine theorem modules.

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
    - defines the manuscript's uniform local criterion and pointwise criterion;
    - proves `uniform local → pointwise` by taking `H = 1`;
    - retains the older abstract `ActualStartRHBridge` for compatibility.

### Exact geometric low/high reduction

36. `RHLean.Analysis.GeometricRHReduction`
    - defines `ActualStartGeometricPartition` with exact signal-level recombination;
    - proves the translated-window low-sector bound;
    - proves

      ```text
      V_total ≤ 2 V_low + 2 V_high,
      V_high  ≤ 2 V_total + 2 V_low;
      ```

    - proves total and high-sector local criteria are equivalent without estimating a cross term.

### Concrete square-prefix Mertens and direct geometry bridge

37. `RHLean.Analysis.SquarePrefixMertensBridge`
    - defines

      ```text
      M(x) = ∑_{m≤x} μ(m),
      X_n = (n+1)^2 - 1,
      S_n = M(X_n);
      ```

    - proves `M` changes by at most the length of an integer interval;
    - proves the full Mertens energy criterion is equivalent to the exact square-prefix energy criterion;
    - proves the exact shifted square-prefix criterion is equivalent to the project's current pointwise criterion;
    - exposes `ClassicalMertensRHCriterion`, whose only field is
      `MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement`.

38. `RHLean.Analysis.ConcreteSquarePrefixGeometry`
    - defines a low/high geometric partition directly on the concrete sequence `squarePrefixMertens`;
    - proves the concrete translated-window low bound;
    - proves concrete total↔high local-criterion equivalence;
    - proves concrete uniform-local↔pointwise↔square-prefix↔Mertens equivalence;
    - proves the concrete high-sector criterion↔RH theorem from the classical criterion.

39. `RHLean.Analysis.MathlibMertensHook`
    - exposes the zero-friction future integration theorem

      ```text
      squarePrefix_highUniformLocalBounded_iff_riemannHypothesis_of_classical_iff
      ```

    - accepts directly

      ```text
      criterion : MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement
      ```

      with no project-specific bridge constructor or realization argument.

No abstract start-sequence realization, indexing adapter, exponent adapter, localization adapter, or project-specific RH bridge remains in this final theorem.

### Normalized ordered cofactor arithmetic and concrete channel realization

40. `RHLean.Proof.NormalizedCofactorExpansion`
    - defines `alphaWeightRat n = 2^(-ω(n))`;
    - proves the exact normalized ordered coprime-factor fiber identity;
    - proves the rational fiber expansion and its exact complex Mertens cast bridge;
    - proves multiplication by a new factor `3` increases the distinct-prime count by one.

41. `RHLean.Proof.NormalizedCofactorTripling`
    - proves the Möbius sign flip and dyadic weight halving under tripling;
    - proves `a(3c,q) = -(1/2) a(c,q)` when `3 ∤ cq`;
    - proves the exact child-plus-twice-parent cancellation identity over `ℚ` and `ℂ`.

42. `RHLean.Proof.ConcreteSquarePrefixCofactorRealization`
    - maps ordered factor pairs into `ActualCofactorChannel`;
    - separates the lower Möbius factor from the remaining normalized channel amplitude;
    - proves exact coefficient compatibility with `actualResidualEntry`'s convention;
    - proves the normalized channel expansion at `X_n=(n+1)^2-1` equals `squarePrefixMertens n`.

43. `RHLean.Proof.SquarePrefixHeightPartition`
    - defines the manuscript cutoff `|Y| ≤ Λ n` using the exact squared-complex ordinate;
    - constructs complete, low-height, and high-height ordered-pair and channel supports;
    - proves exact cover and disjointness of the low/high supports;
    - proves exact rational and complex low/high recombination without changing the normalized product-fiber indexing.

44. `RHLean.Proof.FareyModesAndTransportWindows`
    - defines the finite reduced Farey support `0 ≤ a < r ≤ R`, with `Nat.Coprime a r`;
    - provides exact natural-number labels and a total `ResonantModeIndex` map with exact decoding on retained labels;
    - proves exact squared-complex phase transport under `(c,q) ↦ (3c,q)`, with unchanged denominator and explicit phase defect;
    - defines the entry shell `⌊√(cq)⌋`, transition index `q-1`, and exact contiguous packet window `[⌊√(cq)⌋,q-1)`;
    - proves every retained square-prefix channel has an entry shell in `0,…,n`.

45. `RHLean.Proof.ConcreteSquarePrefixHighResidual`
    - proves product fibers are pairwise disjoint and flattens the high expansion without changing ordered-pair indexing;
    - reindexes the exact high sum through the injective `ActualCofactorChannel` map;
    - chooses the source-entry block `⌊√(cq)⌋` as the concrete finite shell assignment;
    - retains the complete reduced Farey label support and isolates the exact zero label `(0,1)`;
    - defines singleton source-entry packets so both ordered orientations remain represented even when a transport interval is empty;
    - constructs concrete `ActualResidualData` and proves its `actualResidual` is exactly `squarePrefixHighHeightExpansion`.

46. `RHLean.Proof.TriplingPacketTransport`
    - defines normalized arithmetic/Farey/packet-index transport entries and concrete contiguous transport data;
    - proves the transport data agrees exactly with the existing `actualResidualEntry` and packet interfaces at each channel's source shell;
    - proves tripling moves the entry shell weakly upward while retaining the transition index;
    - splits the base packet exactly into a finite boundary prefix and the window shared with the tripled channel;
    - proves phase-aligned child-plus-twice-parent cancellation on the common window from the `-1/2` coefficient law and exact phase transport;
    - proves the unaligned phase-defect identity and the complete boundary-plus-phase signed defect formula;
    - retains all Farey modes in one signed sum and takes energy only after that recombination.

47. `RHLean.Proof.CompleteHighFamilyDecomposition`
    - defines retained new-prime bases, their injective tripled-child image, and every remaining high channel as an explicit unpaired channel;
    - proves the exact disjoint support decomposition `high = bases ⊔ children ⊔ unpaired`;
    - proves the corresponding generic finite-sum decomposition without collapsing ordered orientations;
    - defines complete all-mode transport contributions for channels, retained raw pairs, retained signed defects, child multiplicity correction, and unpaired channels;
    - proves that the raw once-per-channel retained pair sum is the weighted signed-defect sum minus one child copy;
    - proves the complete high-family identity with every retained defect, child correction, and unmatched contribution visible before any norm or Gram estimate.

48. `RHLean.Proof.ConcreteHighFamilyJointGram`
    - proves every concrete transport packet vanishes away from its assigned source shell;
    - proves the shell/channel Farey-mode sum is exactly the complete channel contribution at that source shell and zero elsewhere;
    - proves the concrete transport `actualResidual` is exactly the once-per-channel, all-mode complete high-family contribution;
    - instantiates the full shell/cofactor/mode/row signed joint Gram identity for the concrete family;
    - proves the PR #56 defect-minus-child-correction-plus-unpaired recombination has that same exact joint Gram energy;
    - exposes the remaining pointwise and uniform analytic control propositions without asserting that the estimate is proved.

### Native canonical high-sector bridge

49. `RHLean.Proof.CanonicalHighSectorBridge`
    - defines the unique largest-prime-factor canonical point `q_m=P⁺(m)`, `c_m=m/q_m` and signed doubled height `q_m^2-c_m^2`;
    - defines the exact square blocks, native canonical low/high increments, and cumulative square-prefix values;
    - proves exact blockwise and cumulative low/high recombination;
    - proves the complete canonical block prefix is exactly `squarePrefixMertens` at `X_n=(n+1)^2-1`;
    - packages the manuscript's elementary uniform low-increment estimate as the explicit typed input `CanonicalLowIncrementControl` and derives the required pointwise low-energy bound;
    - defines the native unresolved statement `CanonicalHighUniformLocalBoundedStatement Λ` at scale `H N^(2+ε)`;
    - proves the native canonical high criterion is equivalent to the total square-prefix local criterion and, from `ClassicalMertensRHCriterion`, to `RiemannHypothesisStatement`;
    - does not prove the low-block occupancy theorem, `(HS)`, or the classical Mertens↔RH theorem.

## 2. Correction history

PR #42 compiled an axiom-free conditional theorem with the global prefix target

```text
actualStartFrameEnergy(N) = O(N^(3+ε)).
```

That is a natural cubic benchmark but not the manuscript's uniform local RH criterion. A global prefix inequality does not imply translated-window control by subtraction.

PR #43 corrected the target to

```text
∀ ε > 0, ∃ C ≥ 0, ∀ N H,
  1 ≤ H → H ≤ N →
  V_loc(N,H) ≤ C * H * N^(2+ε).
```

Taking `H = 1` gives the pointwise square-prefix estimate.

PR #44 proved that exact signal recombination plus the elementary low-sector bound gives total↔high local-criterion equivalence by norm inequalities. No low/high cross-term estimate is needed.

PR #45 closes the project-specific Mertens adapter. It fixes the exact endpoint `X_n=(n+1)^2-1`, proves square interpolation and all exponent/localization conversions, states the final geometric equivalence directly for the concrete square-prefix Mertens sequence, and adds a theorem accepting the classical Mertens↔RH equivalence itself.

PR #49 corrects the factor-pair arithmetic by proving the exact normalized ordered cofactor expansion with weight `2^(-ω(cq))`, together with the exact `-1/2` tripling scale and child-plus-twice-parent cancellation law.

PR #51 supplies the first exact concrete realization bridge from those normalized ordered coefficients to the square-prefix Mertens sequence and the existing `ActualCofactorChannel` convention. It deliberately stops before shells, modes, Farey actions, and packet windows.

PR #52 defines the manuscript's exact height selector on the normalized ordered channels and proves the finite low/high support partition and exact signal recombination. It does not infer an energy subtraction identity and stops before shell, mode, and packet data.

PR #53 formalizes the exact reduced Farey support, encoded denominator-mode labels, the tripling phase action, and the contiguous ordered-channel packet window. It records that the manuscript does not specify a unique independent high-height shell formula; the source-entry shell is chosen by the concrete residual constructor.

PR #54 chooses the exact source-entry block as the finite high-height shell assignment and constructs concrete `ActualResidualData` whose residual is the exact high-height signal. It also corrects a hidden indexing obstruction: the transport interval can be empty for a reversed ordered channel, so exact signal realization uses a distinct singleton source-entry packet while preserving the transport window for the later dynamical layer.

PR #55 formalizes that dynamical layer. The tripled packet is the suffix beginning at `⌊√(3cq)⌋`; the omitted base prefix is retained as an explicit boundary packet. On the common window, exact coefficient scaling and phase transport give phase-aligned cancellation, while the unaligned identity leaves precisely `(1-D)` times the common base packet. No unmatched channel, mode, or boundary term is silently removed.

PR #56 completes the finite high-family bookkeeping. Retained new-prime bases and their injective tripled children form a disjoint paired support, every remaining high channel is retained explicitly, and the raw once-per-channel pair contribution is identified as the weighted PR #55 defect minus one child copy. Thus the full family is decomposed exactly without pretending that the factor-of-two transport identity is an ordinary set-pair cancellation.

PR #57 supplies the missing concrete Gram realization. The transport-data `actualResidual` is proved equal to the complete PR #56 family, so the existing joint Gram theorem now applies to the exact concrete shell/channel/Farey-mode/residual-row index. This corrects the dependency order: the concrete identity must precede, and is not itself, the still-open uniform analytic estimate.

PR #60 corrects the identification of the minimal bridge. The Phase VIII/IX construction is an exact normalized all-ordered-pair/Farey transport family and remains a possible sufficient proof strategy, but it is not definitionally the paper's unique largest-prime-factor decomposition. The new native module defines one canonical point per source, proves exact recombination with `squarePrefixMertens`, and isolates `CanonicalHighUniformLocalBoundedStatement Λ` as the single analytic bridge statement. The manuscript's elementary low-increment estimate remains an explicit typed input until separately transcribed into Lean.

## 3. Current checkpoint

For every exact concrete geometric partition satisfying the pointwise low-sector bound, the compiled chain is

```text
SquarePrefixHighUniformLocalBoundedStatement(partition)
  ↔ SquarePrefixUniformLocalBoundedStatement
  ↔ SquarePrefixCurrentPointwiseBoundedStatement
  ↔ SquarePrefixEnergyBoundedStatement
  ↔ MertensEnergyBoundedStatement
  ↔ RiemannHypothesisStatement.
```

The first four equivalences are project-proved. The final direct integration theorem accepts the last classical equivalence as an argument of exactly matching proposition type.

The paper's native largest-prime-factor sequence is now instantiated explicitly. For fixed `Λ`, `CanonicalHighSectorBridge` defines the canonical block increments and prefixes, proves

```text
squarePrefixMertens n
  = canonicalLowPrefix Λ n + canonicalHighPrefix Λ n,
```

and, from `CanonicalLowIncrementControl Λ`, constructs the exact concrete partition required by the existing bridge. Consequently the compiled native chain is

```text
CanonicalHighUniformLocalBoundedStatement Λ
  ↔ SquarePrefixUniformLocalBoundedStatement
  ↔ MertensEnergyBoundedStatement
  ↔ RiemannHypothesisStatement,
```

where the last equivalence is still supplied as the ordinary typed argument `ClassicalMertensRHCriterion`.

The normalized ordered-pair/Farey development remains compiled as a distinct, more structured proof program: complete supports, packet transport, exact tripling defects, unpaired channels, and the full signed shell/cofactor/mode/row Gram identity are all available. No theorem identifies that all-ordered-pair family with the native largest-prime-factor high sequence, so its uniform Gram estimate is a sufficient strategy only after an additional realization theorem.

The remaining obligations are now separated exactly:

- formalize the manuscript's elementary canonical low-block estimate as a concrete `CanonicalLowIncrementControl Λ` (manuscript bound `⌊Λ⌋` for nontrivial sources, with the isolated `m=1` term handled separately or absorbed by `⌊Λ⌋+1`);
- prove the native analytic statement `CanonicalHighUniformLocalBoundedStatement Λ`, i.e. `(HS)`;
- import or formalize `MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement`;
- optionally connect the normalized Farey/transport family to the native canonical sequence and use its full signed Gram estimate as a route to `(HS)`.

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

### Phase VII — concrete Mertens closure

- [x] **23. Concrete square-prefix Mertens and direct mathlib adapter** — PR #45.
  - proves the exact `M(x) ↔ S_n` interpolation at `X_n=(n+1)^2-1`;
  - proves all shifted/current/local criterion conversions;
  - removes `ActualStartSquarePrefixRealization` and `ActualStartRHBridge` from the final concrete theorem;
  - adds a direct theorem accepting the classical Mertens↔RH equivalence itself.

### Phase VIII — normalized cofactor realization

- [x] **24. Normalized ordered cofactor expansion and exact tripling scaling** — PR #49.
- [x] **25. Concrete square-prefix cofactor-channel realization** — PR #51.
- [x] **26. Exact high/low height partition and finite channel supports** — PR #52.
- [x] **27. Reduced Farey modes, exact phase action, entry shells, and contiguous packet windows** — PR #53.
- [x] **28. Concrete high-height shell choice, `ActualResidualData` constructor, amplitudes, and exact high-sector recombination** — PR #54.
- [x] **29. Tripling-compatible packet transport and full signed defect identity** — PR #55.

### Phase IX — complete high-family analytic interface

- [x] **30. Complete tripling-pair/unpaired-channel decomposition and exact multiplicity correction** — PR #56.
- [x] **31. Concrete complete-family joint Gram realization** — PR #57.
- [ ] **32. Uniform full-family signed Gram estimate with all cross interactions retained** — optional sufficient strategy, not the minimal bridge.

### Phase X — native canonical bridge

- [x] **33. Native largest-prime-factor low/high realization and exact conditional RH bridge** — PR #60.
- [ ] **34. Concrete canonical low-increment control with the manuscript nontrivial-source bound `⌊Λ⌋` and the isolated `m=1` endpoint handled explicitly**.
- [ ] **35. Native canonical uniform local high-sector estimate `(HS)`**.

## 5. Dependency spine

The minimal bridge is now:

```text
native largest-prime-factor canonical definitions
        ↓
exact block and square-prefix low/high recombination
        ↓
concrete canonical low-increment control
        ↓
CanonicalHighUniformLocalBoundedStatement Λ  [(HS)]
        ↓
SquarePrefixUniformLocalBoundedStatement
        ↓
MertensEnergyBoundedStatement
        ↓
classical Mertens criterion ↔ RH
```

The normalized Farey/transport program is a separate sufficient strategy that may feed into `(HS)` only after an exact native realization theorem:

```text
complete bases/children/unpaired family decomposition
        ↓
retained defect - child correction + unpaired recombination
        ↓
concrete full signed shell/cofactor/mode/row Gram identity
        ↓
uniform full-family signed Gram estimate
        ↓
exact realization as the native canonical high sequence
        ↓
CanonicalHighUniformLocalBoundedStatement Λ  [(HS)]
```
