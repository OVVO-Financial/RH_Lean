# RH_Lean architecture

This repository formalizes the square-prefix Möbius program through small, reviewable theorem layers. The architecture is deliberately split into exact arithmetic, exact geometry, finite-modulus resonance, and analytic closure. No analytic estimate may be represented by an axiom, opaque constant, weakened theorem, or circular RH assumption.

## 1. Two independent structural branches

The project has two distinct prime-3 mechanisms. They must not be conflated.

### A. Möbius cell-mask branch

```text
Möbius doubling
  μ(2a) = -μ(a) for odd a
        ↓
Exact four-slot compression
  (+,-,+,0)
        ↓
Universal prime-3 cell activation
  one active slot in each three-channel cell
        ↓
Cell-mask Fourier decomposition
        ↓
Nonresonant frame contraction
```

This branch concerns the compressed cell index and its sign mask. Its ideal prime-3 mean-mode energy is `1/9`, but that number applies only after the relevant cell-mask projection and leakage control have been proved.

Planned namespace:

```lean
namespace RHLean.CellMask
```

### B. Quadratic prime-phase branch

```text
Prime square congruences
  q^2 ≡ 1 (mod 24) for primes q > 3
        ↓
Correct quadratic phase period
  modulus 2r, not r
        ↓
Reduced unit-group quadratic factor
  units of ZMod (2r)
        ↓
Exact small-modulus resonances
        ↓
Finite-rank resonant major-arc component
```

This branch concerns the prime variable in the quadratic phase

```text
q ↦ exp(2πi a q^2 / (2r)).
```

At `r = 3`, the normalized quadratic factor has norm `1`; this is exact coherence and is not the cell-mask energy `1/9`.

Planned namespace:

```lean
namespace RHLean.QuadraticPrimePhase
```

## 2. Correct modulus for the quadratic phase

For

```text
quadraticPhase(a,r,u) = exp(2πi a u^2 / (2r)),
```

the phase is naturally periodic modulo `2r`. A shift by `r` contributes the sign

```text
quadraticPhase(a,r,u+r)
  = (-1)^(a*r) * quadraticPhase(a,r,u).
```

Therefore a residue-class model modulo `r` is invalid whenever `a*r` is odd. The uniform reduced factor must be defined over the unit group of `ZMod (2*r)`.

Target definitions:

```lean
noncomputable def reducedQuadraticGauss
    (a r : ℕ) : ℂ :=
  ∑ u : (ZMod (2 * r))ˣ,
    quadraticAdditiveCharacter a r ((u : ZMod (2 * r)) ^ 2)

noncomputable def normalizedQuadraticFactor
    (a r : ℕ) : ℂ :=
  reducedQuadraticGauss a r / Nat.totient (2 * r)
```

A conductor-reduced formulation may be added later, but modulus `2r` is the canonical uniform API.

## 3. Exact arithmetic and finite-modulus modules

The next arithmetic modules should be introduced in this order.

```text
RHLean/
├── Arithmetic/
│   └── PrimeSquareMod24.lean
├── Analysis/
│   ├── QuadraticPhasePeriod.lean
│   ├── ReducedQuadraticGauss.lean
│   ├── ExactSmallModulusResonance.lean
│   └── ResonantNonresonantSplit.lean
└── Tests/
    └── MajorArcRegression.lean
```

### `Arithmetic/PrimeSquareMod24.lean`

Target theorem graph:

```lean
theorem odd_sq_modEq_one_8 ...

theorem sq_modEq_one_3_of_not_dvd ...

theorem sq_modEq_one_24_of_coprime_six
    {n : ℕ} (h : Nat.Coprime n 6) :
    Nat.ModEq 24 (n ^ 2) 1

theorem prime_sq_modEq_one_24
    {q : ℕ}
    (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) :
    Nat.ModEq 24 (q ^ 2) 1
```

### `Analysis/QuadraticPhasePeriod.lean`

First prove the integer congruence independently of complex exponentials:

```lean
theorem quadratic_numerator_modEq
    {a r u v : ℤ}
    (h : u ≡ v [ZMOD (2 * r)]) :
    a * u ^ 2 ≡ a * v ^ 2 [ZMOD (2 * r)]
```

Then prove phase invariance modulo `2r` and the exact shift law:

```lean
theorem quadraticPhase_eq_of_modEq_two_mul ...

theorem quadraticPhase_shift_r
    (a r u : ℤ) :
    quadraticPhase a r (u + r)
      = (-1 : ℂ) ^ (a * r) * quadraticPhase a r u
```

### `Analysis/ReducedQuadraticGauss.lean`

Define the corrected reduced-unit factor over `(ZMod (2*r))ˣ` and its normalized form. The old modulus-`r` construction must not appear in the public API.

### `Analysis/ExactSmallModulusResonance.lean`

Target exact theorems:

```lean
theorem unit_sq_eq_one_mod_six
    (u : (ZMod 6)ˣ) :
    ((u : ZMod 6) ^ 2) = 1

theorem unit_sq_eq_one_mod_twenty_four
    (u : (ZMod 24)ˣ) :
    ((u : ZMod 24) ^ 2) = 1

theorem normalizedQuadraticFactor_one_three :
    normalizedQuadraticFactor 1 3 = phaseAtSixth

theorem norm_normalizedQuadraticFactor_one_three :
    ‖normalizedQuadraticFactor 1 3‖ = 1
```

### `Analysis/ResonantNonresonantSplit.lean`

Introduce distinct resonant and nonresonant error objects. The contraction theorem must not apply the cell-mask factor directly to the coherent rational square-class component.

Target architecture:

```text
E(M) = E_res(M) + E_nonres(M)
```

with separate obligations:

```text
explicit cofactor-channel cancellation of E_res
+
frame/minor-arc contraction of E_nonres
→
uniform cubic residual bound.
```

## 4. Type separation of the two prime-3 objects

The library must make this confusion difficult or impossible:

```text
primeThreeCellMeanEnergy = 1/9
```

is a rational-valued cell-mask statement, while

```text
‖normalizedQuadraticFactor 1 3‖ = 1
```

is a norm statement about a complex reduced quadratic factor.

They belong in separate namespaces and modules. A later documentation theorem may state that both hold simultaneously, but no theorem may use the former as a bound for the latter.

## 5. Regression protection

`Tests/MajorArcRegression.lean` should eventually certify the corrected finite-modulus behavior. Required regression targets include:

```text
q^2 mod 24 = 1 for every tested prime q > 3
```

and the exact `r = 3` distinction:

```text
old modulus-r factor at (a,r)=(1,3): zero
correct modulus-2r normalized factor: norm one.
```

The regression layer must fail if the reduced quadratic factor is changed back from modulus `2r` to modulus `r`.

## 6. Geometry branch remains valid

The midpoint/half-gap coordinates, complex squaring map, factor-square recovery, cofactor parabolas, conformal Jacobian, and `2ab` lifetime geometry are unaffected by the phase-normalization correction. They remain an independent exact-geometry branch that later supplies the cofactor channels across which resonant cancellation must be proved.

## 7. Revised dependency graph

```text
Exact Möbius arithmetic ──→ cell-mask decomposition ──→ nonresonant contraction
                                                         │
Exact factor geometry ──→ Möbius-weighted cofactor channels│
                         │                               │
Prime-square arithmetic ─→ modulus-2r phase theory ─→ resonant component
                                                         │
                                                         ▼
                        explicit resonant cancellation
                                  +
                        nonresonant frame contraction
                                  ↓
                        uniform cubic residual bound
                                  ↓
                        actual-start signed-frame theorem
                                  ↓
                        RH bridge, only after closure
```

## 8. Pull-request sequence

Completed exact foundations:

1. scaffold, CI, Fermat coordinates, fixed packets;
2. Möbius doubling;
3. four-slot compression;
4. universal prime-3 activation.

Current and next focused PRs:

5. squared complex recovery;
6. prime squares modulo `24`;
7. quadratic phase period and the shift-by-`r` sign law;
8. corrected reduced quadratic Gauss factor over modulus `2r`;
9. exact modulus-`6` and modulus-`24` resonance theorems;
10. cofactor parabolas, conformal Jacobian, and `2ab` lifetime;
11. type-separated prime-3 cell-mask energy theorem;
12. resonant/nonresonant decomposition;
13. explicit cancellation across Möbius-weighted cofactor channels;
14. low-height spacing and incidence bounds;
15. prefix kernels, directional Gram identities, and uniform closure;
16. actual-start signed-frame theorem;
17. RH bridge only after all unconditional obligations are discharged.
