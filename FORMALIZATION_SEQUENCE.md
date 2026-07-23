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

The root library currently imports fourteen theorem modules.

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

### Corrected modulus-`2r` exponent arithmetic

6. `RHLean.Analysis.QuadraticPhasePeriod`
   - exact difference-of-squares factorization;
   - preservation of quadratic numerators modulo `2r`;
   - explicit shift-by-`r` and shift-by-`2r` identities.

7. `RHLean.Analysis.QuadraticExponentCongruence`
   - exact quadratic exponent congruence relation modulo `2r`;
   - reflexivity, symmetry, transitivity, input-congruence compatibility, and `2r` periodicity.

8. `RHLean.Analysis.QuadraticShiftDichotomy`
   - if `a*r` is even, shifting by `r` preserves the exponent class;
   - if `a*r` is odd, shifting by `r` moves the exponent by exactly half the modulus;
   - exact arithmetic precursor of the eventual complex sign law.

### Factor geometry

9. `RHLean.Geometry.FermatCoordinates`
   - midpoint and signed half-gap coordinates;
   - exact recovery of both factors;
   - real and imaginary coordinates after squaring;
   - squared-radius identity.

10. `RHLean.Geometry.ComplexSquareRecovery`
    - exact complex Fermat point;
    - squared image equals product/imbalance coordinates;
    - exact recovery of both factor squares without sign choices.

11. `RHLean.Geometry.CofactorParabolas`
    - exact lower-factor and upper-factor parabolas;
    - simultaneous membership of each squared factor pair in both cofactor curves.

12. `RHLean.Geometry.SquareMapConformality`
    - exact Jacobian action of complex squaring;
    - common norm and inner-product scale `4 * (a^2 + b^2)`;
    - orthogonality preservation and determinant identity.

13. `RHLean.Geometry.ComplexSquareFiber`
    - exact fiber theorem `z^2 = w^2 ↔ z = w ∨ z = -w`;
    - injectivity on the positive-real branch;
    - injectivity of Fermat coordinates and positive-midpoint squared images.

### Kernel foundations

14. `RHLean.Kernel.FixedPackets`
    - fixed-packet definitions and exact packet identities used by the later kernel and Gram layers.

## 2. Current checkpoint

The exact arithmetic and factor-geometry foundations are now substantially developed.

The corrected quadratic-phase branch is complete only at the **integer exponent-congruence level**. The library does not yet define the complex additive character, the reduced quadratic Gauss factor, or the exact small-modulus normalized factors.

The following remain open:

- complex phase invariance and the shift-by-`r` sign law;
- reduced unit-group Gauss sums over `(ZMod (2*r))ˣ`;
- exact modulus-6 and modulus-24 resonance and norm-one coherence at `(a,r)=(1,3)`;
- type-separated prime-3 cell-mask mean energy;
- `2ab` displacement and lifetime geometry;
- exact signed shell Gram identities and orthogonal residuals;
- scale-dependent resonant projection, leakage, and Lyapunov closure;
- explicit number-theoretic resonant cancellation and low-height control;
- certified finite-range verification;
- actual-start signed-frame theorem and the final RH bridge.

## 3. Formalization sequence from current `main`

Each item below is intended to be a small reviewable PR. Generic algebraic or functional-analytic lemmas should be proved before their number-theoretic instantiations.

### Phase I — finish the corrected complex quadratic-phase layer

1. **Complex quadratic phase API**
   - add `RHLean.Analysis.ComplexQuadraticPhase`;
   - define the additive character and quadratic phase with an explicit nonzero-modulus contract;
   - prove invariance from `QuadraticExponentCongruent`;
   - prove `2r` periodicity.

2. **Exact shift-by-`r` sign law**
   - convert the merged arithmetic dichotomy into

   ```text
   phase(a,r,u+r) = (-1)^(a*r) * phase(a,r,u).
   ```

3. **Corrected reduced quadratic Gauss factor**
   - add `RHLean.Analysis.ReducedQuadraticGauss`;
   - sum over `(ZMod (2*r))ˣ` only;
   - define the normalized factor using `Nat.totient (2*r)`;
   - do not expose an old modulus-`r` public API.

4. **Exact small-modulus resonance**
   - add unit-square theorems for `ZMod 6` and `ZMod 24`;
   - compute the normalized factor at `(a,r)=(1,3)`;
   - prove its norm is exactly `1`;
   - keep this theorem in `RHLean.QuadraticPrimePhase`.

### Phase II — finish the remaining exact combinatorial and geometry layers

5. **Prime-3 cell-mask mean energy**
   - introduce `RHLean.CellMask`;
   - prove the exact rational-valued mean-energy statement;
   - ensure no coercion or theorem path treats `1/9` as a bound for the quadratic prime-phase factor.

6. **`2ab` displacement and lifetime geometry**
   - formalize exact finite differences of the imaginary squared coordinate;
   - state scanning/lifetime identities before asymptotic inequalities;
   - keep sign and positivity assumptions explicit.

7. **Reduced square-class phase support modulo `40`**
   - factor the merged prime-square dichotomy into a reusable reduced-square-class API;
   - prove the corresponding phase expression has at most two exact square-class modes;
   - do not infer reinforcement without a coefficient theorem.

### Phase III — build the exact signed Hilbert/Gram machinery

8. **Height-shell Gram identity**
   - prove the exact energy expansion with all off-diagonal real inner products retained;
   - the shell sum remains inside the norm.

9. **Orthogonal residual**
   - define the true orthogonal coefficient and residual;
   - prove orthogonality and Pythagorean energy decomposition;
   - keep theorem-predicted subtraction as a separate object.

10. **Scale-dependent resonant projection skeleton**
    - define the denominator cutoff and modulus-`2r` resonant modes;
    - prove only algebraic decomposition until orthogonality is established.

11. **Explicit resonant/nonresonant leakage operator**
    - expose the four block maps `A_M`, `B_M`, `C_M`, and `D_M`;
    - include low-height and boundary forcing explicitly.

12. **Abstract weighted affine Lyapunov closure**
    - prove the generic contraction-with-forcing theorem independently of number theory;
    - support either a full weighted block contraction or a proved triangular alternative.

### Phase IV — instantiate the number-theoretic closure

13. **Resonant/nonresonant decomposition of the actual residual**
    - connect the complex quadratic phase and cofactor channels to the scale-dependent projection.

14. **Explicit resonant cancellation across Möbius-weighted cofactor channels**
    - retain denominator-mode and cofactor interactions;
    - do not seek shellwise positivity.

15. **Low-height spacing, incidence, endpoint, and boundary estimates**
    - prove the analytic forcing bounds required by the block recurrence.

16. **Joint Gram control**
    - index simultaneously by height shell, cofactor block, and denominator mode;
    - retain cross-shell, cross-cofactor, resonant/nonresonant, and mode interactions.

17. **Certified finite-range certificate checker**
    - prove the checker correct in Lean;
    - import numerical runs only as checked data with checksums and code-version metadata.

18. **Uniform full residual bound**
    - instantiate the weighted affine closure with all analytic obligations discharged.

19. **Actual-start signed-frame theorem**
    - derive the theorem from the unconditional residual bound and exact starting configuration.

20. **RH bridge**
    - add only after every unconditional obligation above has been formally proved;
    - no equivalent form of RH may enter earlier as a premise.

## 4. Dependency spine

```text
compiled Möbius/cell arithmetic
+
compiled factor geometry
+
compiled modulus-2r exponent arithmetic
        ↓
complex quadratic phase and exact sign law
        ↓
correct reduced Gauss factors and exact resonances
        ↓
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

`README.md`, `ARCHITECTURE.md`, and `SIGNED_GRAM_ARCHITECTURE.md` may summarize or link to this sequence, but should not maintain independent numbered roadmaps. Whenever a theorem layer is merged, update this inventory by moving it from the open sequence into the compiled inventory and revising the checkpoint before beginning unrelated work.
