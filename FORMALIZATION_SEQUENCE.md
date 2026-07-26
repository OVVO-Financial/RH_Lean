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
  equivalence directly, without an abstract start-sequence bridge;
- a death-shell divisor bound must sum divisor fibers over every integer height
  in the half-open shell window, not use the divisor count of one endpoint;
- a bound on the death process alone does not bound the endpoint survivor
  discrepancy `birth - death`;
- a cofactor-parity decomposition must be finite, include `ω(c)=0`, and use
  `μ(cq)=-μ(c)` only on nonzero Möbius support;
- exact `2ab` source transfer, square-root inversion, or prime-first Fubini
  reindexing is a realization theorem, not by itself a contraction estimate;
- raw Euclidean interval scaling does not model prime transport: any analytic
  low-to-high estimate must retain prime density and the complete signed
  scale-transfer discrepancy;
- finite correlations and baseline `R^2` values remain numerical diagnostics
  unless introduced through the repository's certificate architecture.

## 1. Compiled inventory

The root library imports seventy-five theorem modules.

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
14. `RHLean.Proof.ReducedSquareClassMod40`

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
22. `RHLean.Proof.HeightShellGram`
23. `RHLean.Proof.OrthogonalResidual`
24. `RHLean.Proof.ResonantProjection`
25. `RHLean.Proof.ResonantLeakage`
26. `RHLean.Proof.BlockLyapunovClosure`
27. `RHLean.Proof.ActualResidualDecomposition`
28. `RHLean.Proof.ResonantCofactorCancellation`
29. `RHLean.Proof.ActualForcingEstimates`
30. `RHLean.Proof.JointGramControl`

These modules keep the full shell/cofactor/mode/row recombination inside the norm, retain every signed off-diagonal Gram term, separate true orthogonal projection from theorem-predicted subtraction, and expose the full block recurrence and Lyapunov closure hypotheses.

### Certified verification, residual closure, and actual-start frame

31. `RHLean.Verification.FiniteRangeCertificates`
32. `RHLean.Proof.UniformResidualBound`
33. `RHLean.Proof.ActualStartSignedFrame`

The certificate checker is sound but does not manufacture a numerical run or a mathematical realization. The uniform residual theorem retains the finite realization and asymptotic full-joint control explicitly. The actual-start theorem proves the exact prefix identity

```text
actualFrameEnergy(N)
  = 4 * predictionFrameEnergy(N)
    + residualFrameEnergy(N)
    + signedPredictionResidualInteraction(N)
```

and derives the sharp prefix inequality only from explicit signed absorption.

### Corrected uniform-local layer and RH bridge

34. `RHLean.Proof.ActualStartLocalSignedFrame`
    - defines actual, prediction, residual, and signed-interaction energies on `[N,N+H)`;
    - proves the exact local signed energy identity;
    - proves the residual contribution is at most `H * bound` from the pointwise residual bound;
    - introduces `ActualStartLocalSignedFrameControl`, separate from prefix control;
    - proves the sharp constant-`4` frame inequality on every finite window;
    - proves the local theorem specializes to the old prefix theorem at `N = 0`.

35. `RHLean.Proof.RiemannHypothesisBridge`
    - exposes mathlib's `RiemannHypothesis` as `RiemannHypothesisStatement`;
    - defines the manuscript's uniform local criterion and pointwise criterion;
    - proves `uniform local → pointwise` by taking `H = 1`;
    - retains the older abstract `ActualStartRHBridge` for compatibility.

### Exact geometric low/high reduction

36. `RHLean.Proof.GeometricRHReduction`
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

43. `RHLean.Analysis.SquarePrefixHeightPartition`
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

### Native canonical high-sector analysis and bridge

49. `RHLean.Analysis.CanonicalHighSectorCore`
    - defines the unique largest-prime-factor canonical point `q_m=P⁺(m)`, `c_m=m/q_m` and signed doubled height `q_m^2-c_m^2`;
    - defines the exact square blocks, native canonical low/high increments, and cumulative square-prefix values;
    - proves exact blockwise and cumulative low/high recombination;
    - proves the complete canonical block prefix is exactly `squarePrefixMertens` at `X_n=(n+1)^2-1`;
    - defines `CanonicalLowIncrementControl` and derives the pointwise low-energy consequence of any uniform increment bound.

50. `RHLean.Analysis.CanonicalLowOccupancy`
    - proves the canonical largest-prime-factor/cofactor product identities and the exact absolute-gap height formula;
    - proves that a fixed positive absolute factor gap contributes at most one source to a square block;
    - proves low height forces `|q_m-c_m| ≤ Λ`;
    - proves the sharp nontrivial nonzero-Möbius occupancy bound `card ≤ floor Λ`;
    - isolates the single `m=1` endpoint and proves `‖canonicalLowIncrement Λ j‖ ≤ floor Λ + 1`;
    - constructs `canonicalLowIncrementControl Λ` unconditionally.

51. `RHLean.Analysis.CanonicalHighSectorBridge`
    - constructs the concrete geometric partition from the analysis-layer canonical sequence;
    - defines the unresolved native statement `CanonicalHighUniformLocalBoundedStatement Λ` at scale `H N^(2+ε)`;
    - proves the native canonical high criterion is equivalent to the protected square-prefix uniform-local criterion with the proved low control inserted;
    - proves the conditional equivalence to `RiemannHypothesisStatement` from `ClassicalMertensRHCriterion`;
    - leaves only `(HS)` and the external classical Mertens↔RH theorem unproved.

52. `RHLean.Proof.CanonicalHighSectorCovariance`
    - defines the finite-window sum, mean, coherent mean energy, and centered covariance energy;
    - proves the exact identity `local energy = coherent mean energy + centered covariance energy`;
    - proves the centered term vanishes at `H=1`, so one-point control is entirely coherent;
    - proves the canonical high-sector criterion is exactly the conjunction of coherent and centered control;
    - preserves both analytic estimates as explicit open propositions and derives the conditional RH bridge without introducing an operator realization.

53. `RHLean.Proof.SquareBlockSmoothTransportGram`
    - defines the exact canonical smooth contribution and sign-reversed large-prime transport contribution in each square block;
    - proves blockwise and cumulative `smooth - transport` recombination from the common origin;
    - proves the cumulative residual is exactly `squarePrefixMertens`;
    - defines both diagonal energies and the complete signed smooth/transport interaction before forming the joint Gram energy;
    - proves the joint Gram energy is exactly the cumulative residual local energy and hence the existing square-prefix local energy;
    - exposes `SquareBlockSmoothTransportGramBound` as an ordinary open premise equivalent to the existing local criterion and, conditionally, to RH.

54. `RHLean.Proof.SquareBlockIncrementEnergy`
    - defines the stronger global increment-energy premise at the corrected scale `K^(1+ε)`;
    - proves the cumulative residual is the finite sum of the exact smooth-minus-transport increments;
    - applies finite Cauchy–Schwarz to obtain the RH-scale cumulative pointwise estimate;
    - reuses the existing pointwise-to-uniform-local theorem to derive the repository's minimal cumulative criterion;
    - derives the smooth/transport Gram premise and the conditional RH implication;
    - does not prove the strong increment estimate or replace the weaker minimal cumulative criterion.

55. `RHLean.Proof.SquareBlockTransportBaseline`
    - defines a deterministic transport approximation for arbitrary `F : ℝ → ℂ`;
    - defines the exact error relative to the existing canonical transport increment;
    - proves `transport = approximation + error`;
    - proves `canonical increment = baseline main increment - baseline transport error`;
    - proves the corresponding common-origin cumulative identity and concrete square-prefix Mertens identity;
    - does not identify transport with a prime-count interval sum, choose a baseline, or prove an analytic estimate.

### Finite signed moments, lifetime flow, and death-shell arithmetic

56. `RHLean.Proof.FinitePartialMoments`
57. `RHLean.Proof.RealSquareBlockIncrements`
58. `RHLean.Proof.SquareBlockPartialMomentBalance`
59. `RHLean.Proof.HeightShellReconstruction`
60. `RHLean.Proof.CumulativeHeightFlow`
61. `RHLean.Proof.BirthMovingAbsorption`
62. `RHLean.Proof.LifetimeOverlapKernel`
63. `RHLean.Proof.LifetimeActiveSet`
64. `RHLean.Proof.LifetimeLocalEnergyCriterion`
65. `RHLean.Proof.LifetimeEndpointDecomposition`
66. `RHLean.Proof.DeathProcessArithmetic`
67. `RHLean.Proof.DeathProcessShellIdentity`
68. `RHLean.Proof.DeathShellCardinalityAndCentering`
69. `RHLean.Proof.CompleteFermatSieve`
70. `RHLean.Proof.DeathShellDivisorFibers`
71. `RHLean.Proof.DeathShellCofactorParity`
72. `RHLean.Proof.TwoABScaleTransfer`
73. `RHLean.Proof.TwoABPrimeDilation`
74. `RHLean.Proof.DyadicTransportCompression`
75. `RHLean.Proof.DyadicTransportCanonicalForm`

These modules compile the exact finite partial-moment identities and their square-block specialization; reconstruct canonical height-shell energies; define the cumulative moving boundary and lifetime interval system; prove the active/birth/death endpoint identities; identify each death increment with a thin factorized shell sum; transfer shell cardinality to pointwise and cumulative death-process bounds; verify the complete mod-twenty Fermat sieve; inject each positive-cutoff shell into the divisor fibers over its full finite integer-height window; regroup each shell by finite cofactor-`ω` parity fibers; prove exact source-resolved `entered = smooth - transport`; formalize square-root inversion and `2ab` dilation; expose the complete finite weighted prime-dilation discrepancy and prime-first Fubini identity; compress every parent/doubled-child common transport suffix to an explicit dyadic boundary packet; and identify both the canonical high-source subset and the complete odd dyadic annulus.

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

PR #60 corrects the identification of the minimal bridge. The Phase VIII/IX construction is an exact normalized all-ordered-pair/Farey transport family and remains a possible sufficient proof strategy, but it is not definitionally the paper's unique largest-prime-factor decomposition. The native module defines one canonical point per source, proves exact recombination with `squarePrefixMertens`, and isolates `CanonicalHighUniformLocalBoundedStatement Λ` as the single analytic bridge statement. PR #72 subsequently moves the exact canonical arithmetic into the analysis layer and machine-checks the elementary low-height occupancy theorem, including the isolated `m=1` endpoint, so the low-increment control is no longer an uninstantiated premise.

PR #62 decomposes every finite local high-sector energy exactly into a coherent mean contribution and a centered covariance contribution. The `H=1` specialization proves that the centered term vanishes identically, so covariance control alone cannot discharge the pointwise burden. No source-level operator or analytic estimate is inferred from the algebraic decomposition.

PR #63 defines the exact canonical smooth-minus-transport square-block split and retains the complete signed interaction in the joint Gram energy. The cumulative residual is proved equal to `squarePrefixMertens`, so the new typed Gram premise is definitionally the existing cumulative local criterion rather than a separate diagonal estimate.

PR #64 corrects the proposed increment-energy exponent: a global second moment sufficient for RH must be `O(K^(1+ε))`, not `O(K^(2+ε))`. The new layer formalizes that stronger premise and proves by finite Cauchy–Schwarz that it implies the existing cumulative pointwise and uniform-local criteria, while leaving the strong arithmetic estimate explicit and unproved.

PR #65 adds an arbitrary deterministic baseline coordinate split of the existing transport. It proves exact blockwise and cumulative recombination but deliberately does not attach prime-count interval semantics or any analytic estimate.

PRs #67-#69 formalize finite partial moments, real square-block increments, total variation, and the degree-one balance sufficient route. The balance estimate remains an explicit premise; the finite identities do not themselves prove cancellation.

PR #72 proves the manuscript's canonical low-height occupancy theorem in the analysis layer. It establishes one product per positive absolute gap, the sharp `floor Λ` count on nonzero Möbius support away from `m=1`, the uniform `floor Λ + 1` increment bound, and an unconditional `CanonicalLowIncrementControl Λ`. The canonical high-sector bridge therefore has no remaining internal low-sector hypothesis.

PRs #73-#77 enforce the paper/Analysis boundary and relocate paper-facing and proof-technology modules without changing their theorem APIs. PR #78 then adds the exact canonical height-shell reconstruction.

PRs #79-#85 distinguish the cumulative moving boundary from the birth-block high prefix, build the lifetime-overlap kernel and active set, and prove the exact endpoint identity `active = birth - death`. They also record that death-process control alone is insufficient: the survivor discrepancy remains a separate local-energy obligation.

PRs #86-#89 define the exact death shell, prove `ΔD_t` equals its Möbius mass, and transfer shell-cardinality bounds to death-process bounds and centered decompositions. No asymptotic shell estimate is asserted there.

PR #92 verifies the complete Fermat sieve modulo twenty, including both mod-four parity lanes and the exceptional factor-five classes.

PR #93 corrects the proposed one-endpoint divisor estimate. A shell spans every integer height in a half-open interval, so the valid elementary theorem is

```text
#S_t ≤ ∑_{k in I_{Λ,t}} τ(k),
```

proved by the injective code `m ↦ (|q_m^2-c_m^2|, |q_m-c_m|)`. The unsupported statement `#S_t ≤ τ(2Λ(t+1))` is false in general and is not formalized.

PR #94 proves the exact finite cofactor-parity decomposition of each positive-cutoff death shell. On nonzero Möbius support it proves `μ(m)=(-1)^(ω(c_m)+1)`, retains the `ω(c)=0` class, and regroups the actual death increment as the complete finite alternating sum over represented cofactor-prime-count fibers. It proves no cancellation estimate.

PR #95 tests and formalizes the `2ab` scale-transfer route. It proves exact source and finite-family `entered = smooth - transport`, the canonical square-prefix smooth-minus-transport identity, square-root inversion and `λ^2=q/c`, a total baseline-scaled-low plus discrepancy identity, and finite cofactor-first/prime-first Fubini reindexing. The accompanying experiment verifies the exact lower-Mertens transform with zero integer error through `R=10000`, while random-sign controls show that the exceptional contraction is arithmetic rather than generic geometry. No finite correlation or baseline fit is promoted to an asymptotic theorem.

PR #96 adds exact dyadic transport compression. For an odd parent `(c,q)` and doubled child `(2c,q)`, it proves opposite Möbius weights, nested entry times, a common transition endpoint, and exact cancellation of the entire common suffix, leaving the boundary packet from `floor(sqrt(cq))` to the earlier of `floor(sqrt(2cq))`, `q-1`, and the finite horizon. It then proves, for `X=R^2-1`,

```text
T_R = sum over q prime, R<q<=X,
        sum over c odd, X<2cq<=2X of mu(c),
-T_R = sum over the same canonical sources of mu(cq),
M(B) = sum over m odd, B<2m<=2B of mu(m).
```

The high transport source sum is only the `P+(m)>R` part of the complete odd annulus. The complementary `P+(m)<=R` smooth population is not a negligible boundary, and a transport-only energy estimate is not silently identified with the protected full residual criterion.

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

The paper's native largest-prime-factor sequence is instantiated explicitly. For fixed `Λ`, `CanonicalHighSectorBridge` proves

```text
squarePrefixMertens n
  = canonicalLowPrefix Λ n + canonicalHighPrefix Λ n,
```

and `CanonicalLowOccupancy` constructs `canonicalLowIncrementControl Λ` unconditionally from the machine-checked occupancy theorem. Consequently the compiled native chain is

```text
CanonicalHighUniformLocalBoundedStatement Λ
  ↔ SquarePrefixUniformLocalBoundedStatement
  ↔ MertensEnergyBoundedStatement
  ↔ RiemannHypothesisStatement,
```

with no remaining internal low-sector premise. The last equivalence is supplied as the ordinary typed argument `ClassicalMertensRHCriterion`; the unresolved project mathematics is exactly the native high-sector estimate `(HS)`.

The smooth/transport and increment-energy layers add the compiled sufficient hierarchy

```text
SquareBlockIncrementEnergyBoundedStatement
  → SquarePrefixCurrentPointwiseBoundedStatement
  → SquarePrefixUniformLocalBoundedStatement
  ↔ SquareBlockSmoothTransportGramBound
  ↔ MertensEnergyBoundedStatement
  ↔ RiemannHypothesisStatement.
```

The baseline layer adds only the exact coordinate identity

```text
squarePrefixMertens
  = baseline main prefix - baseline transport error prefix.
```

It creates no independent criterion until later analytic hypotheses are explicitly stated and proved sufficient.

The lifetime/death route now contains the exact identities

```text
active_t = birth_t - death_t,
Δ death_t = deathHeightShellMass Λ t,
‖Δ death_t‖ ≤ #S_t
             ≤ ∑_{k in I_{Λ,t}} τ(k).
```

The last inequality is the exact finite divisor-fiber theorem for `0 < Λ`. A classical subpolynomial divisor estimate would convert it into the expected shell-cardinality growth bound for fixed `Λ`, but that analytic theorem is not yet in the repository. Even a complete death-process estimate would still leave the endpoint discrepancy `birth - death` to control.

The `2ab` scale-transfer route now contains the exact realization identities

```text
entered = smooth - transport,
squarePrefixMertens = squareRootSmoothMass - squareRootTransportMass,
iota_R(x) = R^2/x,
iota_sqrt(cq)(c) = q,
weighted high observable = baseline-scaled low observable + discrepancy,
cofactor-first transport pairs = prime-first lower-cofactor fibers.
```

For `X=R^2-1`, finite Fubini gives analytically

```text
T_R = ∑_{R<q≤X, q prime} M(floor(X/q))
    = ∑_{d<R} K_R(d) M(d).
```

Thus the high transport term is an exact lower-triangular prime-dilation operator on lower-scale Mertens data. The remaining theorem is not the realization but a cancellation-aware operator or discrepancy estimate, with the born-smooth remainder and full signed interaction retained.

The complete multi-route roadmap is recorded in `MULTIROUTE_FORMALIZATION_PLAN.md`, and the strategic invariants are summarized in `BIG_PICTURE_PROOF_MAP.md`.

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

### Phase X — native canonical bridge and cumulative smooth/transport hierarchy

- [x] **33. Native largest-prime-factor low/high realization and exact conditional RH bridge** — PR #60.
- [x] **34. Canonical coherent-mean and centered-covariance decomposition** — PR #62.
- [x] **35. Exact square-block smooth/transport joint Gram realization** — PR #63.
- [x] **36. Strong square-block increment-energy sufficient hierarchy** — PR #64.
- [x] **37. Generic deterministic baseline transport split** — PR #65.
- [x] **38. Concrete canonical low-increment control with the manuscript nontrivial-source bound `⌊Λ⌋` and the isolated `m=1` endpoint handled explicitly** — PR #72.
- [ ] **39. Native canonical uniform local high-sector estimate `(HS)`**.

### Phase XI — finite signed-moment routes

- [x] **40. Generic finite partial moments with the degree-one signed-sum identity and guarded ratio form** — PR #67.
- [x] **41. Sign-valued degree collapse for `{-1,0,1}` sequences** — PR #67.
- [x] **42. Real square-block increments and exact complex-cast bridge** — PR #68.
- [x] **43. Elementary square-block total-variation bound** — PR #68.
- [x] **44. Degree-one partial-moment balance sufficient criterion** — PR #69.
- [ ] **45. Common-normalized signed empirical discrepancy sufficient criterion**.

### Phase XII — baseline energy and descriptive block structure

- [ ] **46. Exact baseline main/error signed joint-energy identity**.
- [ ] **47. Strong diagonal baseline-main plus baseline-error sufficient criterion**.
- [ ] **48. Generic finite atomic block bridge**.
- [ ] **49. Generic implied logarithmic-base transform**.
- [ ] **50. Deterministic Viole function definitions and midpoint interpolation**.
- [ ] **51. Correct Viole asymptotic expansion and explicit third-order bias**.

### Phase XIII — prime-count transport realization

- [ ] **52. Exact canonical largest-prime-factor transport reindexing into prime/cofactor pairs**.
- [ ] **53. Restricted pulled-back prime-interval realization with exact endpoints**.
- [ ] **54. Two-index baseline interval discrepancy identity**.
- [ ] **55. Triangular Möbius transport operator and finite Cauchy–Schwarz bounds**.
- [ ] **56. Cancellation-aware transport large-sieve premise as a sufficient route**.

### Phase XIV — further energy and weighted-moment routes

- [ ] **57. Increment coherent-mean and centered-energy decomposition**.
- [ ] **58. Weighted signed Möbius power-moment identities**.
- [ ] **59. Finite certificate checkers for partial moments, baselines, prime blocks, and transport operators**.

### Phase XV — height-shell reconstruction and lifetime/death-shell route

- [x] **60. Exact canonical high-sector height-shell reconstruction** — PR #78.
- [x] **61. Cumulative moving-height flow** — PR #79.
- [x] **62. Birth-high absorption bridge** — PRs #80 and #81.
- [x] **63. Exact lifetime-overlap kernel** — PR #82.
- [x] **64. Lifetime active-set bridge** — PR #83.
- [x] **65. Honest lifetime local-energy criterion** — PR #84.
- [x] **66. Lifetime endpoint decomposition** — PR #85.
- [x] **67. Death-process arithmetic shell structure** — PR #86.
- [x] **68. Death increment equals death-shell Möbius mass** — PR #87.
- [x] **69. Shell-cardinality transfer and centering** — PR #89.
- [x] **70. Complete verified Fermat sieve** — PR #92.
- [x] **71. Exact death-shell divisor-fiber bound over the full integer window** — PR #93.
- [x] **72. Exact finite cofactor-`ω` parity decomposition, including `ω(c)=0`** — PR #94.
- [ ] **73. Classical divisor-window asymptotic or stronger signed shell cancellation estimate**.
- [ ] **74. Endpoint survivor-discrepancy local-energy control**.

### Phase XVI — exact `2ab` scale transfer and prime-dilation operator

- [x] **75. Exact source and finite-family `entered = smooth - transport` realization** — PR #95.
- [x] **76. Canonical square-prefix smooth-minus-transport realization and exact `2ab` dilation** — PR #95.
- [x] **77. Baseline-scaled low plus complete discrepancy identity** — PR #95.
- [x] **78. Finite cofactor-first/prime-first transport Fubini identity** — PR #95.
- [x] **79. Direct Lean identification of each prime-first fiber with the finite Mertens prefix** — PR #96.
- [ ] **80. Reciprocal-interval kernel `K_R(d)` realization**.
- [ ] **81. Cancellation-aware prime-dilation operator or signed discrepancy estimate sufficient for the protected criterion**.

### Phase XVII — exact dyadic transport compression

- [x] **82. Odd-parent/doubled-child pointwise and packet cancellation** — PR #96.
- [x] **83. Exact finite-horizon and born-smooth boundary classification** — PR #96.
- [x] **84. Complete transport reindexing to odd cofactor fibers `X<2cq<=2X`** — PR #96.
- [x] **85. Canonical source-sign form with `q=P+(cq)` and exact cofactor recovery** — PR #96.
- [x] **86. Complete odd dyadic-annulus identity `M(B)=sum_{B<2m<=2B, m odd} mu(m)`** — PR #96.
- [ ] **87. Dyadic smooth/high joint local-energy estimate with the full signed interaction retained**.

## 5. Dependency spine

The minimal bridge remains

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

The lifetime/death branch supplies a distinct sufficient route into the same protected local criterion:

```text
exact moving-boundary and endpoint identities
        ↓
ΔD_t = death-shell Möbius mass
        ↓
#S_t ≤ full-window divisor sum
        ↓
analytic death-process control
        +
endpoint survivor-discrepancy control
        ↓
SquarePrefixUniformLocalBoundedStatement.
```

The exact divisor-fiber theorem does not by itself provide the analytic divisor estimate, cofactor cancellation, or survivor-discrepancy bound.

The `2ab` scale-transfer branch is another compatible route:

```text
exact source entry/transition geometry
        ↓
square-root inversion and prime-first Fubini
        ↓
T_R = ∑_{d<R} K_R(d) M(d)
        ↓
cancellation-aware operator/discrepancy estimate
        +
born-smooth remainder and full signed interaction
        ↓
SquarePrefixCurrentPointwiseBoundedStatement
        ↓
SquarePrefixUniformLocalBoundedStatement.
```

Exact scale transfer does not by itself prove contraction. The dyadic compression now sharpens the operator support:

```text
parent lifetime + doubled-child lifetime
        = fixed-log-width boundary packet,
-T_R    = canonical high part of the odd top-half annulus,
M(X_R)  = complete odd top-half annulus
        = smooth complement + canonical high part.
```

Consequently the single dyadic inequality definitionally equal to the protected criterion is the local energy of the complete odd annulus. A bound for the high transport subset alone is a separate possible component and requires control of the smooth complement or their full signed interaction. The new multi-route branches may feed only into the existing pointwise, local, increment-energy, or native high-sector propositions. They do not replace the protected spine.

See `MULTIROUTE_FORMALIZATION_PLAN.md` for theorem classifications, nonclaims, and the mandatory PR order.
