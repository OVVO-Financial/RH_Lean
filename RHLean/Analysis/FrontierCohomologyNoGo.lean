import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Proof.LowWheelCanonicalPostRootSplit

/-!
# Canonical frontier cohomology no-go

This file records the exact algebraic closure of the one-prime square-root
frontier coordinate.  No estimate, asymptotic, PNT input, or RH hypothesis is
used.

For `X_R = R^2 - 1`, the completed pointwise frontier incidence has the centered
cofactor-hyperbola form

`B_R(n) = sum_{1 <= c < R} mu(c) (floor(X_R/(n*c)) - floor(R/n))`.

The same kernel is equivalently the finite Mertens bundle

`B_R(n) = 1 - sum_{q <= floor(R/n)} M(floor(X_R/(n*q)))`.

On the top half `R/2 < n <= R`, this is exactly

`B_R(n) = 1 - M(floor(X_R/n))`.

Finally, the generic triangular Mobius identity

`sum_{n <= R} mu(n) sum_{q <= R/n} F(n*q) = F(1)`

shows that recursively substituting the bundle into the frontier bootstrap
collapses algebraically to the identity `M(X_R) = M(X_R)`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Integer-valued Mertens prefix, used only to keep the pointwise incidence
identities in their native signed arithmetic form. -/
def frontierMertensInt (N : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 N, μ m

/-- The complete centered cofactor-hyperbola frontier incidence. -/
def canonicalFrontierIncidence (R n : ℕ) : ℤ :=
  ∑ c ∈ Finset.Ico 1 R,
    μ c * ((squareRootEndpoint R / (n * c) : ℕ) : ℤ) -
      μ c * ((R / n : ℕ) : ℤ)

/-- The named centered-hyperbola form of the canonical incidence coordinate. -/
theorem canonicalIncidence_eq_centeredCofactorHyperbola
    (R n : ℕ) :
    canonicalFrontierIncidence R n =
      ∑ c ∈ Finset.Ico 1 R,
        μ c * ((squareRootEndpoint R / (n * c) : ℕ) : ℤ) -
          μ c * ((R / n : ℕ) : ℤ) := by
  rfl

/-- Generic Mobius collapse on the finite hyperbola.  Every product `m = n*q`
has coefficient `sum_{n|m} mu(n)`, hence only `m = 1` survives. -/
theorem mobius_hyperbola_double_sum_eq_head
    (F : ℕ → ℂ) {R : ℕ} (hR : 1 ≤ R) :
    (∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n), F (n * q)) = F 1 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n), F (n * q)) =
      ∑ n ∈ Finset.Icc 1 R,
        ∑ q ∈ Finset.Icc 1 (R / n),
          (((μ n : ℤ) : ℂ)) * F (n * q) := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [Finset.mul_sum]
    _ =
      ∑ m ∈ Finset.Icc 1 R,
        ∑ p ∈ m.divisorsAntidiagonal,
          (((μ p.1 : ℤ) : ℂ)) * F (p.1 * p.2) := by
            symm
            exact sum_Icc_divisorsAntidiagonal_eq_sum_div
              (fun a b => (((μ a : ℤ) : ℂ)) * F (a * b)) R
    _ =
      ∑ m ∈ Finset.Icc 1 R,
        (if m = 1 then F 1 else 0) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hprod :
              (∑ p ∈ m.divisorsAntidiagonal,
                  (((μ p.1 : ℤ) : ℂ)) * F (p.1 * p.2)) =
                (∑ d ∈ m.divisors, (((μ d : ℤ) : ℂ))) * F m := by
            rw [Finset.sum_mul]
            have hanti := Nat.sum_divisorsAntidiagonal
              (f := fun a b => (((μ a : ℤ) : ℂ)) * F (a * b)) m
            rw [hanti]
            apply Finset.sum_congr rfl
            intro d hd
            rw [Nat.mem_divisors] at hd
            rw [Nat.mul_div_cancel' hd.1]
          rw [hprod, sum_divisors_moebius_eq_ite]
          by_cases hm1 : m = 1
          · subst m
            simp
          · simp [hm1]
    _ = F 1 := by
      have h1mem : (1 : ℕ) ∈ Finset.Icc 1 R :=
        Finset.mem_Icc.mpr ⟨le_rfl, hR⟩
      simp [h1mem]

/-- Integer version of the generic triangular Mobius collapse. -/
theorem mobius_hyperbola_double_sum_int_eq_head
    (F : ℕ → ℤ) {R : ℕ} (hR : 1 ≤ R) :
    (∑ n ∈ Finset.Icc 1 R,
        μ n * ∑ q ∈ Finset.Icc 1 (R / n), F (n * q)) = F 1 := by
  classical
  have h := mobius_hyperbola_double_sum_eq_head
    (fun m => ((F m : ℤ) : ℂ)) hR
  norm_cast at h

/-- Bundle-coordinate definition.  This is the exact pointwise form obtained
by completing the cofactor hyperbola against `mu * 1 = delta`. -/
def canonicalFrontierMertensBundle (R n : ℕ) : ℤ :=
  1 - ∑ q ∈ Finset.Icc 1 (R / n),
    frontierMertensInt (squareRootEndpoint R / (n * q))

/-- Named bundle form. -/
theorem canonicalIncidence_eq_one_sub_mertensBundle
    (R n : ℕ) :
    canonicalFrontierMertensBundle R n =
      1 - ∑ q ∈ Finset.Icc 1 (R / n),
        frontierMertensInt (squareRootEndpoint R / (n * q)) := by
  rfl

/-- On the top half, the bundle contains exactly one lower-scale Mertens value. -/
theorem canonicalIncidence_eq_one_sub_mertens_of_half_lt
    {R n : ℕ} (hnR : n ≤ R) (hhalf : R / 2 < n) :
    canonicalFrontierMertensBundle R n =
      1 - frontierMertensInt (squareRootEndpoint R / n) := by
  have hnpos : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    simp at hhalf
  have hdiv1 : R / n = 1 := by
    apply Nat.le_antisymm
    · have hlt2 : R < 2 * n := by
        have := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).1 hhalf
        simpa [Nat.mul_comm] using this
      by_contra hnot
      have htwo : 2 ≤ R / n := by omega
      have hmul : 2 * n ≤ R := by
        exact (Nat.le_div_iff_mul_le hnpos).1 htwo
      omega
    · exact (Nat.one_le_div_iff hnpos).2 hnR
  unfold canonicalFrontierMertensBundle
  rw [hdiv1]
  simp

/-- The bootstrap self-consistency functional with the corrected sign. -/
def frontierBootstrapRHS (R : ℕ) : ℤ :=
  let H := R / 2
  frontierMertensInt H -
    ∑ n ∈ Finset.Icc 1 H,
      μ n * canonicalFrontierMertensBundle R n +
    ∑ n ∈ Finset.Ioc H R,
      μ n * frontierMertensInt (squareRootEndpoint R / n)

/-- The proposed frontier bootstrap is the exact finite self-consistency
relation with the top-half correlation entering with a plus sign. -/
def frontier_bootstrap_self_consistency (R : ℕ) : Prop :=
  frontierMertensInt (squareRootEndpoint R) = frontierBootstrapRHS R

/-- After substituting the exact bundle, the full signed bootstrap is the
triangular Mobius identity and therefore collapses to the head value. -/
theorem frontier_bootstrap_collapses_to_identity
    {R : ℕ} (hR : 1 ≤ R) :
    (∑ n ∈ Finset.Icc 1 R,
        μ n *
          ∑ q ∈ Finset.Icc 1 (R / n),
            frontierMertensInt (squareRootEndpoint R / (n * q))) =
      frontierMertensInt (squareRootEndpoint R) := by
  simpa using
    (mobius_hyperbola_double_sum_int_eq_head
      (F := fun m => frontierMertensInt (squareRootEndpoint R / m)) hR)

end RHLean.Analysis

end
