# Formalization inventory and sequence

This document is the canonical implementation order for `RH_Lean`.

It records only what is actually compiled on `main`, distinguishes completed algebraic layers from still-open analytic obligations, and orders future work by theorem dependency rather than by narrative order in the research notes.

The governing invariants remain unchanged:

- no `sorry`, `admit`, new axioms, opaque theorem substitutes, weakened statements, changed indexing, or circular RH assumptions;
- modulus `2r`, not `r`, is the canonical quadratic-phase modulus;
- the prime-3 cell-mask energy and the prime-3 quadratic phase factor remain type-separated;
- the high-sector target is the full signed Gram recombination, not independent positivity or smallness of every shell;
- numerical finite-range claims enter only through a proved certificate checker.

## 1. Compiled inventory

The root library currently imports twenty-four theorem modules.

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
    - exact theorem that every eligible prime phase at `r = 20` lies in one of two complex square-class modes;
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
    - fixed-packet definitions and exact packet identities used by the later kernel and Gram layers.

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

## 2. Current checkpoint

Phase I and Phase II are complete. Phase III item 8, the exact height-shell Gram identity, is completed by PR #30. Phase III item 9, the orthogonal residual, is completed by PR #31. Phase III item 10, the scale-dependent resonant projection skeleton, is completed by PR #32.

The library now contains:

- integer exponent congruence modulo `2r`;
- the exact complex quadratic phase and full-period invariance;
- the exact shift-by-`r` sign law;
- the reduced unit-group Gauss sum over `(ZMod (2*r))ˣ`;
- exact modulus-6 and modulus-24 coherence;
- the normalized `(a,r)=(1,3)` factor and its norm-one theorem;
- a dedicated rational cell-mask module with exact mean `1/3` and squared mean-mode energy `1/9`;
- exact `2ab` finite-difference geometry, including the linear common-shift displacement `h(q-c)` and exact vertical-window lifetime criterion;
- exact reduced square-class phase support modulo `40`: every eligible prime phase at `r = 20` is one of the class-`1` or class-`9` modes;
- the exact height-shell energy expansion

  ```text
  ‖∑_{i<n} S_i‖²
  = ∑_{i<n} ‖S_i‖²
    + 2 * ∑_{j<n} ∑_{i<j} re⟪S_i,S_j⟫;
  ```

- for nonzero `P`, the exact orthogonal decomposition

  ```text
  beta_orth = ⟪P,B⟫ / ⟪P,P⟫,
  E_orth = B - beta_orth • P,
  ⟪P,E_orth⟫ = ⟪E_orth,P⟫ = 0,
  ‖B‖² = ‖E_orth‖² + ‖beta_orth • P‖²;
  ```

- a scale-dependent resonant skeleton with positive denominators `r ≤ R0(M)`, canonical phase period `2r`, a declared resonant span, and the exact algebraic decomposition

  ```text
  x_res(M) + x_non(M) = x,
  x_non(M) = x - x_res(M).
  ```

The shell sum remains inside the norm, and no off-diagonal real inner product is discarded or replaced by a shellwise positivity or independent-smallness estimate. The theorem-predicted coefficient remains separate from the true orthogonal coefficient. The scale-dependent extraction is not assumed idempotent, self-adjoint, or orthogonal, so no Pythagorean identity or norm splitting is inferred from its algebraic decomposition.

The following remain open:

- explicit resonant/nonresonant leakage and Lyapunov closure;
- explicit number-theoretic resonant cancellation and low-height control;
- certified finite-range verification;
- actual-start signed-frame theorem and the final RH bridge.

## 3. Formalization sequence from the current checkpoint

Each item is a small, reviewable PR. The checkbox is authoritative: `[x]` means merged and compiled on `main`; `[ ]` means still open.

### Phase I — corrected complex quadratic-phase layer

- [x] **1. Complex quadratic phase API** — completed by PR #21.
- [x] **2. Exact shift-by-`r` sign law** — completed by PR #22.
- [x] **3. Corrected reduced quadratic Gauss factor** — completed by PR #23.
- [x] **4. Exact small-modulus resonance** — completed by PR #24.

### Phase II — remaining exact combinatorial and geometry layers

- [x] **5. Prime-3 cell-mask mean energy** — completed by PR #27.
  - introduced the dedicated `RHLean.CellMask` namespace and module;
  - proved the exact rational-valued mean and squared mean-mode energy;
  - preserved strict separation from the complex quadratic prime-phase factor.

- [x] **6. `2ab` displacement and lifetime geometry** — completed by PR #28.
  - formalized exact finite differences of the imaginary squared coordinate;
  - proved common factor translation has exact linear displacement `h(q-c)`;
  - stated parity-preserving scan, monotonicity, and lifetime/window identities before asymptotic inequalities;
  - kept all order and positivity assumptions explicit.

- [x] **7. Reduced square-class phase support modulo `40`** — completed by PR #29.
  - factored the merged prime-square dichotomy into a reusable reduced-square-class API;
  - proved the canonical phase at `r = 20` has at most the exact class-`1` and class-`9` modes for eligible primes;
  - made no reinforcement or coefficient claim.

### Phase III — exact signed Hilbert/Gram machinery

- [x] **8. Height-shell Gram identity** — completed by PR #30.
  - defined the ordered full shell sum, diagonal energy, and exact unordered-pair Gram sum;
  - proved the exact energy expansion over real or complex inner-product spaces;
  - retained every off-diagonal real inner product and kept the full signed shell sum inside the norm;
  - introduced no shellwise positivity or independent-smallness substitute.

- [x] **9. Orthogonal residual** — completed by PR #31.
  - defined the true coefficient `⟪P,B⟫ / ⟪P,P⟫` for nonzero `P` using mathlib's second-argument linearity;
  - defined the corresponding residual and proved orthogonality in both inner-product orientations;
  - proved exact recombination and Pythagorean energy decomposition;
  - defined theorem-predicted subtraction and residual separately, with equality to the orthogonal residual requiring a separate coefficient-equality hypothesis.

- [x] **10. Scale-dependent resonant projection skeleton** — completed by PR #32.
  - defined scale-dependent resonant mode indices with positive denominator `r ≤ R0(M)`;
  - defined the exact quadratic mode and proved its canonical `2r` periodicity;
  - defined the resonant span and a scale-dependent linear extraction into that span;
  - proved only the algebraic resonant/nonresonant recombination, with no idempotence, orthogonality, or Pythagorean claim.

- [ ] **11. Explicit resonant/nonresonant leakage operator** — next dependency.
  - expose the four block maps `A_M`, `B_M`, `C_M`, and `D_M`;
  - include low-height and boundary forcing explicitly.

- [ ] **12. Abstract weighted affine Lyapunov closure**.
  - prove the generic contraction-with-forcing theorem independently of number theory;
  - support either a full weighted block contraction or a proved triangular alternative.

### Phase IV — number-theoretic closure

- [ ] **13. Resonant/nonresonant decomposition of the actual residual**.
  - connect the complex quadratic phase and cofactor channels to the scale-dependent projection.

- [ ] **14. Explicit resonant cancellation across Möbius-weighted cofactor channels**.
  - retain denominator-mode and cofactor interactions;
  - do not seek shellwise positivity.

- [ ] **15. Low-height spacing, incidence, endpoint, and boundary estimates**.
  - prove the analytic forcing bounds required by the block recurrence.

- [ ] **16. Joint Gram control**.
  - index simultaneously by height shell, cofactor block, and denominator mode;
  - retain cross-shell, cross-cofactor, resonant/nonresonant, and mode interactions.

- [ ] **17. Certified finite-range certificate checker**.
  - prove the checker correct in Lean;
  - import numerical runs only as checked data with checksums and code-version metadata.

- [ ] **18. Uniform full residual bound**.
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
scale-dependent resonant/nonresonant decomposition
+
full signed shell/cofactor/mode Gram identity
+
explicit leakage operator and forcing
        ↓
weighted affine block contraction
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
