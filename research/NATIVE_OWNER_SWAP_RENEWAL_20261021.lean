import Mathlib
import RHLean.Proof.RecursivePrimeReplacement
import RHLean.Analysis.SquareRootMatchedTransport
import RHLean.Analysis.SquareRootPostCrossingRenewal

/-!
# Original-owner swap and exact renewal correspondence

This file preserves the original square endpoint `R^2 - 1`, the actual
transport cutoff `p > R`, the original smooth mass, and the existing native
replacement row. It proves finite algebra only. It makes no cancellation,
operator-norm, Mertens exponent, or RH claim.

The cofactor swap preserves the product of the original Möbius weights.
Consequently an interior/wedge partition is not a sign-reversing involution.
The complete owner Gram is identified below with the native replacement-row
Gram after deleting exactly the actual high-owner diagonal.

Status at creation: proof source prepared for CI; no local Lean executable is
available in the scratch environment. There are no `sorry` declarations.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators ComplexConjugate

namespace RHLean.Proof.NativeOwnerSwapRenewal

open RHLean.Analysis

/-! ## The swap is sign preserving -/

/-- All four original multiplicative weights survive a complete cofactor swap.
For actual high owners, the four coprimality hypotheses follow from `p,q > R`
and `c,d < R`. No additional minus sign is introduced by the swap. -/
theorem mobius_swap_product
    (p q c d : ℕ)
    (hpc : Nat.Coprime p c) (hqd : Nat.Coprime q d)
    (hpd : Nat.Coprime p d) (hqc : Nat.Coprime q c) :
    (μ (p * c) : ℤ) * (μ (q * d) : ℤ) =
      (μ (p * d) : ℤ) * (μ (q * c) : ℤ) := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpc,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqd,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpd,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqc]
  ring

/-- Exact interior plus wedge split. When `u=N_R(c)` and `v=N_R(d)` with
`c<d`, `v*(v-1)` is the complete interior, not a canceled contribution. -/
theorem cofactor_kernel_interior_wedge (u v : ℤ) :
    u * v - v = v * (v - 1) + v * (u - v) := by
  ring

/-- The original signed cofactor factor multiplies BOTH pieces. -/
theorem signed_cofactor_kernel_interior_wedge (a b u v : ℤ) :
    a * b * (u * v - v) =
      a * b * (v * (v - 1)) + a * b * (v * (u - v)) := by
  ring

/-! ## Exact high-prime quotient multiplicities -/

/-- Actual `p>R` prime owners with reciprocal quotient exactly `y`, counted in
`ℂ` to use the repository's native Mertens values without changing currency. -/
def ownerQuotientMultiplicity (R y : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc R (squareRootEndpoint R),
    if p.Prime ∧ squareRootEndpoint R / p = y then 1 else 0

/-- Generic finite pushforward of the ACTUAL high-prime owner set. In
particular the terminal quotient layer is clipped at `p>R`. -/
theorem owner_quotient_pushforward
    (R : ℕ) (hR : 2 ≤ R) (f : ℕ → ℂ) :
    (∑ y ∈ Finset.range R, ownerQuotientMultiplicity R y * f y) =
      ∑ p ∈ Finset.Ioc R (squareRootEndpoint R),
        if p.Prime then f (squareRootEndpoint R / p) else 0 := by
  unfold ownerQuotientMultiplicity
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hpR : R ≤ p := (Finset.mem_Ioc.mp hp).1.le
  have hylt : squareRootEndpoint R / p < R :=
    squareRootEndpoint_div_lt_root_of_root_le hR hpR
  have hymem : squareRootEndpoint R / p ∈ Finset.range R :=
    Finset.mem_range.mpr hylt
  by_cases hprime : p.Prime
  · simp [hprime, hymem, ite_mul]
  · simp [hprime]

/-- The existing transport population, with its original coefficients and
cutoff, is exactly the quotient-multiplicity row. -/
theorem transport_eq_owner_quotient_row (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportPrimeFirst R =
      ∑ y ∈ Finset.range R,
        ownerQuotientMultiplicity R y * mertensSummatory y := by
  rw [owner_quotient_pushforward R hR]
  exact squareRootTransportPrimeFirst_eq_mertensTransform R (by omega)

/-! ## The genuine smooth row; no unspecified compensating prime count -/

/-- Original smooth minus original transport equals the native Mertens value.
The proof uses the repository's existing square-prefix factorization. -/
theorem smooth_sub_transport_eq_mertens (R : ℕ) (hR : 2 ≤ R) :
    squareRootSmoothMass (R - 1) - squareRootTransportPrimeFirst R =
      mertensSummatory (squareRootEndpoint R) := by
  have hprefix := squarePrefixMertens_eq_squareRootSmooth_sub_transport (R - 1)
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel (by omega)
  unfold squarePrefixMertens squarePrefixEndpoint at hprefix
  rw [hpred] at hprefix
  rw [squareRootTransportMass_pred_eq_cofactorFirst R (by omega),
    squareRootTransportCofactorFirst_eq_primeFirst] at hprefix
  simpa [squareRootEndpoint] using! hprefix.symm

/-- This is the actual complete smooth population expressed on the existing
native lower-scale Mertens states. Its coefficient is the proved replacement
coefficient PLUS the actual high-prime multiplicity. -/
theorem smooth_eq_native_replacement_plus_owner_row
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootSmoothMass (R - 1) =
      ∑ y ∈ Finset.range R,
        (squareRootReplacementCoefficient R y +
          ownerQuotientMultiplicity R y) * mertensSummatory y := by
  have hdecomp := smooth_sub_transport_eq_mertens R hR
  calc
    squareRootSmoothMass (R - 1) =
        mertensSummatory (squareRootEndpoint R) +
          squareRootTransportPrimeFirst R := by
            linear_combination hdecomp
    _ = (∑ y ∈ Finset.range R,
          squareRootReplacementCoefficient R y * mertensSummatory y) +
        ∑ y ∈ Finset.range R,
          ownerQuotientMultiplicity R y * mertensSummatory y := by
            rw [mertensEndpoint_eq_recombinedReplacementRow R (by omega),
              transport_eq_owner_quotient_row R (by omega)]
    _ = ∑ y ∈ Finset.range R,
        (squareRootReplacementCoefficient R y +
          ownerQuotientMultiplicity R y) * mertensSummatory y := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro y _hy
            ring

/-- The existing replacement coefficient has the full canonical rough-prime
diagonal and every strict descendant, with its native endpoint term. The
cofactor-one prime face is present inside both full rough masses. -/
theorem replacement_coefficient_eq_full_rough_row
    (R y : ℕ) (hR : 2 ≤ R) (hy : 1 ≤ y) (hyR : y < R) :
    squareRootReplacementCoefficient R y =
      (if y = R - 1 then 1 else 0) +
        replacementFibreCanonicalRoughFullMass R y +
          squareRootCanonicalRoughStrictDescendantTransform R y := by
  have h := squareRootPostCrossingReplacementCoefficient_eq_canonicalRough
    R 0 0 y hR hy hyR
  unfold squareRootPostCrossingReplacementCoefficient
    squareRootPostCrossingCanonicalRoughCoefficient at h
  linear_combination h

/-- Post-crossing packet admission changes that same coefficient row before
any norm. It does not delete the rough prime faces in strict descendants. -/
theorem post_crossing_eq_native_modified_row
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      ∑ y ∈ Finset.range R,
        (squareRootReplacementCoefficient R y +
          squareRootCrossingRemovalCoefficient R K j y) *
            mertensSummatory y := by
  simpa [squareRootPostCrossingReplacementCoefficient] using!
    squareRootPostCrossingCoupledTail_eq_replacementRow R K j hR hK hKR

/-! ## Complete original-owner Gram and the exact replacement kernel -/

def ownerDiagonalComplex (R : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc R (squareRootEndpoint R),
    if p.Prime then
      mertensSummatory (squareRootEndpoint R / p) *
        conj (mertensSummatory (squareRootEndpoint R / p))
    else 0

def ownerDiagonal (R : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ioc R (squareRootEndpoint R),
    if p.Prime then ‖mertensSummatory (squareRootEndpoint R / p)‖ ^ 2
    else 0

private theorem mul_conj_eq_cast_norm_sq (z : ℂ) :
    z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj']
  norm_cast

theorem cast_owner_diagonal (R : ℕ) :
    (ownerDiagonal R : ℂ) = ownerDiagonalComplex R := by
  unfold ownerDiagonal ownerDiagonalComplex
  push_cast
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hprime : p.Prime
  · simp only [hprime, ite_true]
    simpa using! (mul_conj_eq_cast_norm_sq
      (mertensSummatory (squareRootEndpoint R / p))).symm
  · simp [hprime]

theorem owner_diagonal_eq_quotient_row (R : ℕ) (hR : 2 ≤ R) :
    ownerDiagonalComplex R =
      ∑ y ∈ Finset.range R,
        ownerQuotientMultiplicity R y *
          mertensSummatory y * conj (mertensSummatory y) := by
  simpa [ownerDiagonalComplex, mul_assoc] using!
    (owner_quotient_pushforward R hR
      (fun y => mertensSummatory y * conj (mertensSummatory y))).symm

/-- Complete original smooth/transport mixed expression, with only the
actual high-owner diagonal removed. All signed mixed terms are retained. -/
def fullOwnerGram (R : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) * conj (squareRootSmoothMass (R - 1)) -
    squareRootSmoothMass (R - 1) * conj (squareRootTransportPrimeFirst R) -
    squareRootTransportPrimeFirst R * conj (squareRootSmoothMass (R - 1)) +
    squareRootTransportPrimeFirst R * conj (squareRootTransportPrimeFirst R) -
    ownerDiagonalComplex R

def fullOwnerGamma (R : ℕ) : ℝ := (fullOwnerGram R).re

theorem full_owner_gram_eq_difference (R : ℕ) :
    fullOwnerGram R =
      (squareRootSmoothMass (R - 1) - squareRootTransportPrimeFirst R) *
        conj (squareRootSmoothMass (R - 1) - squareRootTransportPrimeFirst R) -
          ownerDiagonalComplex R := by
  unfold fullOwnerGram
  rw [map_sub]
  ring

theorem full_owner_gamma_eq_norm_sq_sub_diagonal (R : ℕ) :
    fullOwnerGamma R =
      ‖squareRootSmoothMass (R - 1) - squareRootTransportPrimeFirst R‖ ^ 2 -
        ownerDiagonal R := by
  unfold fullOwnerGamma
  rw [full_owner_gram_eq_difference, mul_conj_eq_cast_norm_sq,
    ← cast_owner_diagonal]
  simp

theorem mertens_norm_sq_eq_diagonal_add_gamma
    (R : ℕ) (hR : 2 ≤ R) :
    ‖mertensSummatory (squareRootEndpoint R)‖ ^ 2 =
      ownerDiagonal R + fullOwnerGamma R := by
  rw [full_owner_gamma_eq_norm_sq_sub_diagonal,
    smooth_sub_transport_eq_mertens R hR]
  ring

def replacementPairGram (R : ℕ) : ℂ :=
  ∑ y ∈ Finset.range R, ∑ z ∈ Finset.range R,
    (squareRootReplacementCoefficient R y * mertensSummatory y) *
      conj (squareRootReplacementCoefficient R z * mertensSummatory z)

theorem replacement_pair_gram_eq_mertens_mul_conj
    (R : ℕ) (hR : 2 ≤ R) :
    replacementPairGram R =
      mertensSummatory (squareRootEndpoint R) *
        conj (mertensSummatory (squareRootEndpoint R)) := by
  rw [mertensEndpoint_eq_recombinedReplacementRow R hR]
  unfold replacementPairGram
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]

/-- The original owner expression and the existing replacement row have
exactly the same complete signed Gram after the true owner diagonal is removed. -/
theorem full_owner_gram_eq_replacement_pair_gram_sub_diagonal
    (R : ℕ) (hR : 2 ≤ R) :
    fullOwnerGram R = replacementPairGram R - ownerDiagonalComplex R := by
  rw [full_owner_gram_eq_difference, smooth_sub_transport_eq_mertens R hR,
    replacement_pair_gram_eq_mertens_mul_conj R (by omega)]

/-- A completely explicit lower-scale kernel. Its diagonal subtraction is
the actual prime-owner multiplicity, not an unspecified compensating function. -/
def ownerRemovedReplacementGram (R : ℕ) : ℂ :=
  ∑ y ∈ Finset.range R, ∑ z ∈ Finset.range R,
    (squareRootReplacementCoefficient R y *
        conj (squareRootReplacementCoefficient R z) -
      (if y = z then ownerQuotientMultiplicity R y else 0)) *
        mertensSummatory y * conj (mertensSummatory z)

theorem owner_removed_replacement_gram_eq
    (R : ℕ) (hR : 2 ≤ R) :
    ownerRemovedReplacementGram R =
      replacementPairGram R - ownerDiagonalComplex R := by
  have hrow : ∀ y ∈ Finset.range R,
      (∑ z ∈ Finset.range R,
        (squareRootReplacementCoefficient R y *
            conj (squareRootReplacementCoefficient R z) -
          (if y = z then ownerQuotientMultiplicity R y else 0)) *
            mertensSummatory y * conj (mertensSummatory z)) =
        (∑ z ∈ Finset.range R,
          (squareRootReplacementCoefficient R y * mertensSummatory y) *
            conj (squareRootReplacementCoefficient R z * mertensSummatory z)) -
          ownerQuotientMultiplicity R y *
            mertensSummatory y * conj (mertensSummatory y) := by
    intro y hy
    calc
      _ = ∑ z ∈ Finset.range R,
          ((squareRootReplacementCoefficient R y * mertensSummatory y) *
              conj (squareRootReplacementCoefficient R z * mertensSummatory z) -
            (if y = z then ownerQuotientMultiplicity R y *
              mertensSummatory y * conj (mertensSummatory y) else 0)) := by
                apply Finset.sum_congr rfl
                intro z _hz
                by_cases heq : y = z
                · subst z
                  simp only [if_pos (Eq.refl y), map_mul]
                  ring
                · simp only [heq, ite_false, map_mul]
                  ring
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp [hy]
  unfold ownerRemovedReplacementGram
  rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib,
    ← owner_diagonal_eq_quotient_row R hR]
  rfl

theorem full_owner_gram_eq_owner_removed_replacement_gram
    (R : ℕ) (hR : 2 ≤ R) :
    fullOwnerGram R = ownerRemovedReplacementGram R := by
  rw [full_owner_gram_eq_replacement_pair_gram_sub_diagonal R hR,
    owner_removed_replacement_gram_eq R (by omega)]

/-! ## The terminal prime boundary must be clipped -/

def primeWindowCount (a b : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc a b, if p.Prime then 1 else 0

/-- At the terminal raw floor window `(R-1,R+1]`, the prime `R` is an extra
boundary point. The actual `p>R` interval is `(R,R+1]`. For `R>=2`, together with
`X_R/(R-1)=R+1` and `X_R/R=R-1`, this is the terminal raw-layer correction. -/
theorem terminal_prime_window_boundary
    (R : ℕ) (hR : 1 ≤ R) :
    primeWindowCount (R - 1) (R + 1) =
      primeWindowCount R (R + 1) + (if R.Prime then 1 else 0) := by
  have hset : Finset.Ioc (R - 1) (R + 1) =
      ({R} : Finset ℕ) ∪ Finset.Ioc R (R + 1) := by
    ext p
    simp only [Finset.mem_Ioc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj : Disjoint ({R} : Finset ℕ) (Finset.Ioc R (R + 1)) := by
    rw [Finset.disjoint_left]
    intro p hp hpr
    have hpR : p = R := Finset.mem_singleton.mp hp
    subst p
    exact (Nat.lt_irrefl R) (Finset.mem_Ioc.mp hpr).1
  unfold primeWindowCount
  rw [hset, Finset.sum_union hdisj]
  simp only [Finset.sum_singleton]
  ring

#print axioms mobius_swap_product
#print axioms smooth_eq_native_replacement_plus_owner_row
#print axioms replacement_coefficient_eq_full_rough_row
#print axioms full_owner_gram_eq_owner_removed_replacement_gram
#print axioms mertens_norm_sq_eq_diagonal_add_gamma
#print axioms terminal_prime_window_boundary

end RHLean.Proof.NativeOwnerSwapRenewal
