# Formalization inventory and sequence

This document is the canonical implementation order for `RH_Lean`.

It records only what is actually compiled on the implementation branch, distinguishes completed algebraic layers from still-open analytic obligations, and orders future work by theorem dependency rather than by narrative order in the research notes.

The governing invariants remain unchanged:

- no `sorry`, `admit`, new axioms, opaque theorem substitutes, weakened statements, changed indexing, or circular RH assumptions;
- modulus `2r`, not `r`, is the canonical quadratic-phase modulus;
- the prime-3 cell-mask energy and the prime-3 quadratic phase factor remain type-separated;
- the high-sector target is the full signed Gram recombination, not independent positivity or smallness of every shell;
- numerical finite-range claims enter only through a proved certificate checker.

## 1. Compiled inventory

The root library currently imports thirty-one theorem modules.

### Arithmetic and cell structure

1. `RHLean.Arithmetic.MoebiusDoubling`
   - exact Möbius doubling for odd inputs;
   - core theorem: `μ (2 * a) = -μ a`.

2. `RHLean.Arithmetic.FourSlotCell`
   - exact four-slot compression;
   - deterministic `(+,-,+,0)` structure.

3. `RHLean.Arithmetic.PrimeThreeActivation`
   - universal prime-3 activation;
   - exact deterministic three-cycle.

4. `RHLean.Arithmetic.PrimeSquareMod24`
   - residue classification modulo `24`;
   - prime-square theorem `q^2 ≡ 1 (mod 24)` for primes other than `2` and `3`.

5. `RHLean.Arithmetic.PrimeSquareMod40`
   - the sixteen unit residue classes modulo `40`;
   - prime-square dichotomy `q^2 ≡ 1` or `9 (mod 40)` for primes other than `2` and `5`.

### Cell-mask exact energy

6. `RHLean.CellMask.PrimeThreeMeanEnergy`
   - rational divisibility indicators for the three active cell channels;
   - exact indicator sum equal to `1` in every complete cell;
   - exact rational mean `1/3` and squared mean-mode energy `1/9`.

### Corrected modulus-`2r` phase architecture

7. `RHLean.Analysis.QuadraticPhasePeriod`
   - exact difference-of-squares factorization;
   - preservation of quadratic numerators modulo `2r`;
   - explicit shift-by-`r` and shift-by-`2r` identities.

8. `RHLean.Analysis.QuadraticExponentCongruence`
   - exact quadratic exponent congruence relation modulo `2r`;
   - reflexivity, symmetry, transitivity, input-congruence compatibility, and `2r` periodicity.

9. `RHLean.Analysis.QuadraticShiftDichotomy`
   - if `a*r` is even, shifting by `r` preserves the exponent class;
   - if `a*r` is odd, shifting by `r` moves the exponent by exactly half the modulus.

10. `RHLean.Analysis.ComplexQuadraticPhase`
    - complex additive character with integer numerator and modulus;
    - corrected quadratic phase using modulus `2r`;
    - exact congruence invariance and `2r` periodicity.

11. `RHLean.Analysis.QuadraticPhaseShiftSign`
    - exact half-turn exponential identity;
    - exact sign law

    ```text
    phase(a,r,u+r) = (-1)^(a*r) * phase(a,r,u).
    ```

12. `RHLean.Analysis.ReducedQuadraticGauss`
    - unit-level phase over `(ZMod (2*r))ˣ`;
    - corrected reduced Gauss sum;
    - normalization by `Nat.totient (2*r)`.

13. `RHLean.Analysis.SmallModulusResonance`
    - exact unit-square identities modulo `6` and `24`;
    - coherent reduced sums at those moduli;
    - exact normalized value at `(a,r)=(1,3)`;
    - exact norm-one theorem.

14. `RHLean.Analysis.ReducedSquareClassMod40`
    - reusable reduced square-class predicate with exact classes `1` and `9`;
    - exact reduction of the modulus-`40` quadratic numerator to its square residue;
    - every eligible prime phase at `r = 20` lies in one of two complex square-class modes;
    - no coefficient, multiplicity, cancellation, or reinforcement claim.

### Factor geometry

15. `RHLean.Geometry.FermatCoordinates`
    - midpoint and signed half-gap coordinates;
    - exact recovery of both factors;
    - real and imaginary coordinates after squaring;
    - squared-radius identity.

16. `RHLean.Geometry.ComplexSquareRecovery`
    - exact complex Fermat point;
    - squared image equals product/imbalance coordinates;
    - exact recovery of both factor squares without sign choices.

17. `RHLean.Geometry.CofactorParabolas`
    - exact lower-factor and upper-factor parabolas;
    - simultaneous membership of each squared factor pair in both cofactor curves.

18. `RHLean.Geometry.TwoABDisplacement`
    - exact identification of the imaginary squared coordinate with `2ab`;
    - exact midpoint, half-gap, upper-factor, and lower-factor finite differences;
    - exact linear common-shift displacement and parity-preserving specialization;
    - explicit monotonicity and vertical-window lifetime criteria.

19. `RHLean.Geometry.SquareMapConformality`
    - exact Jacobian action of complex squaring;
    - common norm and inner-product scale `4 * (a^2 + b^2)`;
    - orthogonality preservation and determinant identity.

20. `RHLean.Geometry.ComplexSquareFiber`
    - exact fiber theorem `z^2 = w^2 ↔ z = w ∨ z = -w`;
    - injectivity on the positive-real branch;
    - injectivity of Fermat coordinates and positive-midpoint squared images.

### Kernel foundations

21. `RHLean.Kernel.FixedPackets`
    - fixed-packet definitions and exact packet identities used by later kernel and Gram layers.

### Exact signed Hilbert/Gram machinery

22. `RHLean.Analysis.HeightShellGram`
    - ordered finite height-shell sums over `0 ≤ i < n`;
    - exact diagonal shell energy;
    - explicit off-diagonal Gram enumeration `∑_{j<n} ∑_{i<j} re⟪S_i,S_j⟫`;
    - exact identity keeping the full signed shell sum inside the norm.

23. `RHLean.Analysis.OrthogonalResidual`
    - true projection coefficient onto a nonzero prediction vector under mathlib's inner-product convention;
    - exact orthogonal residual and two-sided inner-product orthogonality;
    - exact recombination and Pythagorean energy decomposition;
    - theorem-predicted subtraction and residual kept as separate definitions.

24. `RHLean.Analysis.ResonantProjection`
    - scale-dependent cutoff and positive resonant denominators `r ≤ R0(M)`;
    - exact quadratic modes with canonical period `2r`;
    - declared resonant span and scale-dependent linear extraction into that span;
    - exact algebraic resonant/nonresonant recombination with no orthogonality claim.

25. `RHLean.Analysis.ResonantLeakage`
    - separately typed resonant and nonresonant state spaces;
    - explicit scale-dependent block maps `A_M`, `B_M`, `C_M`, and `D_M`;
    - separate low-height, endpoint, and boundary forcing in both recurrence rows;
    - exact affine recurrence with no contraction or triangularity claim.

26. `RHLean.Analysis.BlockLyapunovClosure`
    - nonnegative resonant and nonresonant Lyapunov weights with abstract component sizes;
    - explicit invariant bound `max B0 (C / (1 - rho))` for descending affine recurrences;
    - full weighted block-contraction closure with all base, descent, contraction, and forcing hypotheses explicit;
    - decay-weighted forcing corollary with no number-theoretic instantiation.

27. `RHLean.Analysis.ActualResidualDecomposition`
    - explicitly indexed cofactor channels with exact squared-map geometry;
    - finite scale-`M` shell, cofactor, denominator-mode, packet-start, packet-length, and packet-index data;
    - exact Möbius-weighted complex quadratic packet entries using the canonical modulus `2r`;
    - full signed cofactor/mode shell sums and full shell recombination;
    - scale-dependent resonant extraction, exact algebraic remainder, span membership, and exact recombination;
    - direct packaging as `ResonantNonresonantState ℂ ℂ` for the leakage and Lyapunov layers.

28. `RHLean.Analysis.ResonantCofactorCancellation`
    - complex Möbius scalar and exact odd/doubled sign reversal;
    - explicit base/doubled cofactor-pair indices with the upper factor retained;
    - actual unweighted packet entries and fixed packets with the canonical quadratic phase unchanged;
    - exact factorization of actual entries and packets by their Möbius scalar;
    - explicit compatibility certificates recording channel membership and denominator-mode packet data;
    - exact cancellation after scale-dependent extraction for each retained denominator mode, each joint cofactor-mode contribution, and every finite certified pair family;
    - no assertion that all actual channels are paired or that unpaired, low-height, endpoint, or boundary terms vanish.

29. `RHLean.Analysis.ActualForcingEstimates`
    - positive separated low-height shell positions and a proved spacing-to-incidence bound;
    - explicit resonant and nonresonant low-height finite sums with cutoff-times-envelope estimates;
    - left and right endpoint sources retained separately with two-sided triangle bounds;
    - finite boundary sources with independent incidence caps and pointwise envelopes;
    - exact instantiation of all six forcing fields of `ResonantLeakageOperator ℂ ℂ ℂ` while preserving the four block maps;
    - combined rowwise and weighted forcing bounds for the compiled Lyapunov interface;
    - no decay rate, contraction, numerical constant, or joint Gram estimate asserted.

30. `RHLean.Analysis.JointGramControl`
    - complete finite index over height shell, actual cofactor channel, denominator mode, and resonant/nonresonant row;
    - exact rowwise packet recombination without orthogonality assumptions;
    - a finite ordinal enumeration that retains every complete joint index exactly once;
    - exact equality of the enumerated joint sum with the actual residual;
    - exact diagonal-plus-signed-off-diagonal Gram identity for the actual residual energy;
    - a single full joint-Gram control and recursive-control interface;
    - no independent shell, cofactor, row, or denominator-mode positivity or smallness claim.

### Certified verification boundary

31. `RHLean.Verification.FiniteRangeCertificates`
    - explicit code-version, source-commit, external data-checksum, and recomputed numeric payload-checksum metadata;
    - exact integer-numerator decomposition checkpoints with a common positive denominator;
    - prime totals and residue-class counts with positive modulus, distinct in-range classes, and exact count recombination;
    - complete signed joint-Gram checkpoint data retaining every diagonal and off-diagonal term;
    - exact reconstruction of the full signed joint energy and scaled recurrence inequality at every declared scale;
    - executable `checkFiniteRangeCertificate` with a proved soundness theorem and an accepted-certificate boundary;
    - no numerical run, numerical constant, uniform residual bound, or RH claim.

## 2. Current checkpoint

Phase I, Phase II, and Phase III are complete. Phase IV items 13 through 16 are completed by PRs #35 through #38. Phase IV item 17, the certified finite-range certificate checker, is completed on the implementation branch for anticipated PR #39.

Generated data are represented by a `FiniteRangeCertificate` carrying:

```text
code version, source commit, external data checksum,
recomputed numeric payload checksum,
range endpoints, common value denominator,
contraction numerator/denominator, and ordered rows.
```

Each row retains exact resonant/nonresonant decomposition checkpoints, prime totals and residue-class counts, and the complete signed joint-Gram payload. The checker verifies the declared joint cardinality

```text
shellCount * cofactorCount * denominatorModeCount * 2,
```

checks the diagonal and strict off-diagonal term counts, reconstructs

```text
claimedJointEnergy
  = sum(diagonalTerms) + 2 * sum(offDiagonalTerms),
```

and verifies the denominator-cleared recurrence inequality without independently bounding any shell, cofactor, residual row, or denominator mode.

The executable checker is defined by decision of a trusted proposition, and `checkFiniteRangeCertificate_sound` proves that a successful check implies the full proposition. Numerical data can cross the import boundary only through `AcceptedFiniteRangeCertificate`, which requires a proof that the checker returned `true`. This PR deliberately imports no numerical run.

No numerical finite-range conclusion, contraction constant, decay law, uniform residual bound, actual-start theorem, or RH statement is introduced.

The following remain open:

- the uniform full residual bound;
- the actual-start signed-frame theorem and final RH bridge.

## 3. Formalization sequence from the current checkpoint

Each item is a small, reviewable PR. The checkbox is authoritative: `[x]` means completed on the implementation branch and anticipated for the stated PR; `[ ]` means still open.

### Phase I — corrected complex quadratic-phase layer

- [x] **1. Complex quadratic phase API** — completed by PR #21.
- [x] **2. Exact shift-by-`r` sign law** — completed by PR #22.
- [x] **3. Corrected reduced quadratic Gauss factor** — completed by PR #23.
- [x] **4. Exact small-modulus resonance** — completed by PR #24.

### Phase II — remaining exact combinatorial and geometry layers

- [x] **5. Prime-3 cell-mask mean energy** — completed by PR #27.
- [x] **6. `2ab` displacement and lifetime geometry** — completed by PR #28.
- [x] **7. Reduced square-class phase support modulo `40`** — completed by PR #29.

### Phase III — exact signed Hilbert/Gram machinery

- [x] **8. Height-shell Gram identity** — completed by PR #30.
- [x] **9. Orthogonal residual** — completed by PR #31.
- [x] **10. Scale-dependent resonant projection skeleton** — completed by PR #32.
- [x] **11. Explicit resonant/nonresonant leakage operator** — completed by PR #33.
- [x] **12. Abstract weighted affine Lyapunov closure** — completed by PR #34.

### Phase IV — number-theoretic closure

- [x] **13. Resonant/nonresonant decomposition of the actual residual** — completed by PR #35.
  - defines explicit cofactor channels and their exact cofactor-parabola geometry;
  - retains the scale, shell, cofactor, denominator-mode, packet-start, packet-length, and packet-index arguments;
  - uses the exact Möbius weight, fixed packet, and canonical complex quadratic phase;
  - defines the resonant component by the scale-dependent extraction and the nonresonant component as the exact remainder;
  - proves only declared-span membership and exact algebraic recombination;
  - packages the result as the separately typed state used by later leakage and Lyapunov theorems.

- [x] **14. Explicit resonant cancellation across Möbius-weighted cofactor channels** — completed by PR #36.
  - defines explicit odd/base and doubled cofactor channels with the upper factor retained;
  - records channel membership and exact packet compatibility separately for every retained denominator mode;
  - factors the actual packet and its extracted component by the exact complex Möbius scalar;
  - proves exact per-mode, joint denominator-mode, and finite certified-pair-family cancellation;
  - makes no exhaustive-pairing, unpaired-term, low-height, endpoint, boundary, contraction, or smallness claim.

- [x] **15. Low-height spacing, incidence, endpoint, and boundary estimates** — completed by PR #37.
  - derives low-height incidence from positive spacing and a finite height cutoff;
  - proves separate resonant and nonresonant low-height finite-sum estimates;
  - retains left/right endpoint and finite boundary sources separately;
  - instantiates the six forcing fields of the compiled leakage operator without changing its four block maps;
  - proves rowwise and weighted forcing bounds, with no unproved decay or contraction claim.

- [x] **16. Joint Gram control** — completed by PR #38.
  - indexes simultaneously by height shell, actual cofactor channel, denominator mode, and residual row;
  - proves exact packet-row and full-index recombination to the actual residual;
  - retains every signed off-diagonal interaction in one complete Gram expression;
  - exposes direct and recursive full-joint-Gram control interfaces;
  - makes no numerical, finite-range, uniform-bound, or RH claim.

- [x] **17. Certified finite-range certificate checker** — anticipated PR #39.
  - defines explicit metadata expectations and recomputes a deterministic checksum from every numeric payload field;
  - verifies exact decomposition checkpoints, prime/residue counts, complete joint cardinality, and all diagonal/off-diagonal term counts;
  - reconstructs the full signed joint energy and checks the scaled recurrence inequality for every ordered range row;
  - proves executable-checker soundness and exposes an accepted-certificate import boundary;
  - imports no numerical run and proves no finite numerical conclusion.

- [ ] **18. Uniform full residual bound** — next dependency.
  - instantiate the weighted affine closure with all analytic obligations discharged.

- [ ] **19. Actual-start signed-frame theorem**.
  - derive the theorem from the unconditional residual bound and exact starting configuration.

- [ ] **20. RH bridge**.
  - add only after every unconditional obligation above has been formally proved;
  - no equivalent form of RH may enter earlier as a premise.

## 4. Dependency spine

```text
compiled Möbius/cell arithmetic
+
compiled factor geometry
+
compiled modulus-2r exponent and complex-phase arithmetic
        ↓
correct reduced Gauss factors and exact resonances
        ↓
exact cell-mask energy, remaining geometry, and reduced square-class support
        ↓
exact full signed height-shell Gram identity
        ↓
true orthogonal residual
+
scale-dependent resonant/nonresonant projection
+
actual residual with explicit shell/cofactor/denominator/packet indexing
+
explicit leakage operator and abstract Lyapunov closure
        ↓
exact resonant cancellation for certified Möbius cofactor pairs
        ↓
low-height, endpoint, and boundary forcing estimates
        ↓
full joint signed Gram control
        ↓
certified finite-range checker
        ↓
uniform full residual bound
        ↓
actual-start signed-frame theorem
        ↓
RH bridge only after unconditional closure
```

## 5. Maintenance rule

This file is the single source of truth for implementation order.

`README.md`, `ARCHITECTURE.md`, and `SIGNED_GRAM_ARCHITECTURE.md` may summarize or link to this sequence, but should not maintain independent numbered roadmaps.

Whenever a theorem layer is merged, the same PR must:

- change that item from `[ ]` to `[x]`;
- record the completing PR number;
- move the corresponding module into the compiled inventory;
- revise the current checkpoint;
- identify the next unchecked dependency;
- update `FORMALIZATION_CHECKLIST.md` with the same explicit status and successful PR ledger entry.
