# Full signed Gram closure architecture

The high-sector theorem must control the signed recombination of all structural components. It must not attempt to prove that every height shell, cofactor block, or resonant mode is individually small.

## 1. Revised empirical lesson

The observed architecture is

```text
large coherent resonant component
+
large shell components
+
large negative cross-shell terms
=
small total residual.
```

Accordingly, the formal target is the full signed Gram form. A sum of separate positive shell-energy estimates is not an acceptable substitute unless an exact orthogonalizing transform has first been proved.

## 2. Shell recombination remains inside the norm

For shell components `S[ell]`, the relevant quantity is

```text
‖∑ ell, S[ell]‖²
```

and not merely

```text
∑ ell, ‖S[ell]‖².
```

The library should expose the exact identity

```text
‖∑ ell, S[ell]‖²
=
∑ ell, ‖S[ell]‖²
+
2 * ∑ ell < m, re ⟪S[ell], S[m]⟫.
```

The off-diagonal Gram terms are mathematically essential and may be negative.

Planned module:

```text
RHLean/Analysis/HeightShellGram.lean
```

Target theorem shape:

```lean
theorem energy_sum_shells
    (s : ι → E) :
    ‖∑ i, s i‖ ^ 2 =
      ∑ i, ‖s i‖ ^ 2 +
      2 * ∑ p : {p : ι × ι // p.1 < p.2},
        reInner (s p.1.1) (s p.1.2)
```

The exact implementation should use a finite linearly ordered shell index or a finite set with an explicit pair enumeration.

## 3. Orthogonal projection versus predicted subtraction

Two residual constructions must remain distinct.

### Theorem-predicted residual

```text
E_pred = B - beta_pred * P
```

where `beta_pred` is supplied by an asymptotic theorem or structural prediction.

### Orthogonal residual

```text
beta_orth = ⟪B,P⟫ / ⟪P,P⟫
E_orth = B - beta_orth * P.
```

Only the second construction supports the exact orthogonality and Pythagorean identities.

Planned module:

```text
RHLean/Analysis/OrthogonalResidual.lean
```

Target theorem shapes:

```lean
theorem projection_residual_orthogonal
    (P B : E) (hP : P ≠ 0) :
    ⟪B - ((⟪B, P⟫ / ⟪P, P⟫) • P), P⟫ = 0

theorem projection_energy_decomposition ...
```

Lean must not permit a Pythagorean conclusion from the theorem-predicted coefficient unless equality with the orthogonal coefficient is separately proved.

Notation should reserve `sigma` for the cofactor-scale exponent and `theta` for Fourier frequency.

## 4. Scale-dependent major-arc projection

There is no single permanent finite resonant subspace. At scale `M`, the major-arc component should capture denominators

```text
r ≤ R0(M)
```

with `R0(M) = M^(o(1))` or another explicitly chosen cutoff.

The corrected quadratic factors use modulus `2*r`.

Planned module:

```text
RHLean/Analysis/ResonantProjection.lean
```

The state decomposition is

```text
x_res(M) = P_maj(M) x
x_non(M) = (I - P_maj(M)) x.
```

If `P_maj(M)` is proved to be an orthogonal projection, the library may derive

```lean
P_maj M x + (1 - P_maj M) x = x
```

and orthogonality of the two components. If the extraction is not orthogonal, only the algebraic sum identity may be used; no Pythagorean decomposition may be asserted.

## 5. Resonant and nonresonant leakage

Scale descent must track feedback between resonant and nonresonant states. A scalar recurrence for the nonresonant component alone is insufficient unless triangularity or zero leakage has been proved.

Planned module:

```text
RHLean/Analysis/ResonantLeakage.lean
```

The structural recurrence is

```text
[R_M]   [A_M  B_M] [R_parent]   [f_R]
[N_M] = [C_M  D_M] [N_parent] + [f_N].
```

Here:

- `A_M` propagates resonant state;
- `D_M` propagates nonresonant state;
- `B_M` and `C_M` measure leakage;
- forcing contains low-height, endpoint, and boundary terms.

The formal API should make the four block maps explicit rather than hiding them in one opaque operator.

## 6. Affine block contraction and Lyapunov closure

The actual closure condition is contraction of the full block operator in a weighted Lyapunov norm, or a proved triangular structure with summable leakage.

Planned module:

```text
RHLean/Analysis/BlockLyapunovClosure.lean
```

Proposed state structure:

```lean
structure ScaleState (E : Type*) where
  resonant : E
  nonresonant : E
  lowHeight : E
  boundary : E
```

Target abstract closure theorem:

```lean
theorem uniform_bound_of_affine_block_contraction
    (ancestor : ℕ → ℕ)
    (state : ℕ → ScaleState E)
    (rho C : ℝ)
    (hrho : 0 ≤ rho ∧ rho < 1)
    (hdesc : ∀ n > N0, ancestor n < n)
    (hcontract :
      ∀ n > N0,
        lyapunovNorm (state n) ≤
          rho * lyapunovNorm (state (ancestor n)) + forcing n)
    (hforcing : ∀ n > N0, forcing n ≤ C * decay n) :
    ∃ B, ∀ n, lyapunovNorm (state n) ≤ B
```

The abstract theorem should be proved independently of the number-theoretic instantiation.

## 7. Exact mod-40 square classes

Secondary resonance means support on a small exact phase set; it does not necessarily mean constructive interference.

For primes `q > 5`, the exact arithmetic target is

```text
q^2 ≡ 1 or 9 (mod 40).
```

Planned modules:

```text
RHLean/Arithmetic/PrimeSquareMod40.lean
RHLean/Arithmetic/ReducedSquareClasses.lean
```

Target theorem:

```lean
theorem prime_sq_modEq_one_or_nine_40
    {q : ℕ}
    (hq : q.Prime)
    (hq2 : q ≠ 2)
    (hq5 : q ≠ 5) :
    Nat.ModEq 40 (q ^ 2) 1 ∨
    Nat.ModEq 40 (q ^ 2) 9
```

The resulting prime-phase expression has at most two exact square-class modes. Their coefficients may reinforce or cancel.

## 8. Joint Gram indexing

The final Gram object should be indexed simultaneously by

```text
(height shell, cofactor block, prime denominator mode).
```

The target energy is

```text
1* G_M 1
```

for the full joint Gram matrix, retaining:

- cross-shell terms;
- cross-cofactor terms;
- resonant/nonresonant cross terms;
- denominator-mode interactions.

The desired recursive inequality is

```text
1* G_M 1
≤ rho * 1* G_parent 1
  + C_epsilon * M^(3 - eta + epsilon),
```

with `rho < 1` and constants uniform in `M`.

## 9. Certified computation boundary

The exact finite-range values observed numerically must not be inserted as axioms or ordinary mathematical theorems.

Planned verification module:

```text
RHLean/Verification/FiniteRangeCertificates.lean
```

It should consume generated certificates containing:

- exact decomposition checkpoints;
- prime counts and residue-class counts;
- finite shell energies and cross terms;
- code version and data checksum.

The trusted mathematical library should prove the certificate checker correct. Individual numerical runs should then be imported as data checked by that verifier.

## 10. Revised closure chain

```text
exact Möbius and factor geometry
+
correct modulus-2r resonant phase model
+
scale-dependent major-arc projection
+
full signed shell/cofactor/mode Gram identity
+
explicit resonant/nonresonant leakage operator
+
weighted affine block contraction with forcing
→
uniform full residual bound
→
actual-start signed-frame theorem
→
RH bridge only after unconditional closure.
```

The high sector is not required to be small shell by shell. It is required to be small after the exact signed recombination represented by the full joint Gram form.
