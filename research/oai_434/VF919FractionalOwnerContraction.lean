import «research.oai_434.VF919OwnerBootstrapIteration»

/-!
# Source-faithful fractional owner contraction: the exact missing bootstrap

The original complete signed NativeOwnerBound contains the smooth part,
transport, ALL prime-owner pairs, and the original diagonal.  The property
below is a quantified ARITHMETIC HYPOTHESIS, never asserted unconditionally.

If one fixed c>0 of this strength can be proved, every iteration retains a
fixed fraction of the gap between the current exponent and the critical line.
-/

noncomputable section

namespace RHLean.Analysis.OwnerPrefix

open RHLean.Analysis.MertensExponent
open OAI.SevenEighths
open OAI.SevenEighths.RHLeanActualSlotMin

/-- The unproved UNIFORM signed owner arithmetic restriction.
Its input growth hypothesis is at the CURRENT exponent, not only at 7/8. -/
def NativeUniformFractionalOwnerContraction (c : ℝ) : Prop :=
  ∀ θ : ℝ, (1 / 2 : ℝ) ≤ θ → θ ≤ 7 / 8 →
    MertensGrowthAtMost θ →
    NativeOwnerBound ((1 - c) * (2 * θ - 1))

/-- The unique exponent update under a fraction c of excess-loss removal. -/
def fractionalOwnerExponentIterate (c θ : ℝ) : ℕ → ℝ
  | 0 => θ
  | n + 1 =>
      (1 / 2 : ℝ) +
        (1 - c / 2) * (fractionalOwnerExponentIterate c θ n - 1 / 2)

theorem fractionalOwnerExponentIterate_bounds
    (c θ : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hθ0 : (1 / 2 : ℝ) ≤ θ)
    (hθ1 : θ ≤ 7 / 8) (n : ℕ) :
    (1 / 2 : ℝ) ≤ fractionalOwnerExponentIterate c θ n ∧
    fractionalOwnerExponentIterate c θ n ≤ 7 / 8 := by
  induction n with
  | zero =>
      exact ⟨hθ0, hθ1⟩
  | succ n ih =>
      change (1 / 2 : ℝ) ≤
          1 / 2 + (1 - c / 2) *
            (fractionalOwnerExponentIterate c θ n - 1 / 2) ∧
        1 / 2 + (1 - c / 2) *
            (fractionalOwnerExponentIterate c θ n - 1 / 2) ≤ 7 / 8
      have hu : 0 ≤ 1 - c / 2 := by linarith
      have hv : 1 - c / 2 ≤ 1 := by linarith
      have hgap : 0 ≤ fractionalOwnerExponentIterate c θ n - 1 / 2 :=
        by linarith only [ih.1]
      have hprod0 :
          0 ≤ (1 - c / 2) *
            (fractionalOwnerExponentIterate c θ n - 1 / 2) :=
        mul_nonneg hu hgap
      have hprod1 :
          (1 - c / 2) *
            (fractionalOwnerExponentIterate c θ n - 1 / 2) ≤
          fractionalOwnerExponentIterate c θ n - 1 / 2 :=
        by
          simpa using (mul_le_mul_of_nonneg_right hv hgap)
      constructor
      · linarith only [hprod0]
      · linarith only [hprod1, ih.2]

/-- Exact geometric orbit: fixed c contracts the positive excess by
(1-c/2) at EVERY stage, if the same source-level bound renews. -/
theorem fractionalOwnerExponentIterate_closed (c θ : ℝ) (n : ℕ) :
    fractionalOwnerExponentIterate c θ n =
      (1 / 2 : ℝ) + (θ - 1 / 2) * (1 - c / 2) ^ n := by
  induction n with
  | zero =>
      simp only [fractionalOwnerExponentIterate, pow_zero, mul_one]
      ring
  | succ n ih =>
      change (1 / 2 : ℝ) +
        (1 - c / 2) * (fractionalOwnerExponentIterate c θ n - 1 / 2) =
        1 / 2 + (θ - 1 / 2) * (1 - c / 2) ^ (n + 1)
      rw [ih, pow_succ]
      ring

/-- Formal bootstrap of the actual Mertens growth exponent from the actual
source.  The UNPROVED quantified signed-covariance statement stays visible. -/
theorem native_fractional_owner_iterated_growth
    (c θ : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hθ0 : (1 / 2 : ℝ) ≤ θ) (hθ1 : θ ≤ 7 / 8)
    (hcontract : NativeUniformFractionalOwnerContraction c)
    (hgrowth : MertensGrowthAtMost θ) :
    ∀ n : ℕ,
      MertensGrowthAtMost (fractionalOwnerExponentIterate c θ n) := by
  intro n
  induction n with
  | zero =>
      simpa only [fractionalOwnerExponentIterate] using hgrowth
  | succ n ih =>
      let θn := fractionalOwnerExponentIterate c θ n
      have hb := fractionalOwnerExponentIterate_bounds c θ hc0 hc1 hθ0 hθ1 n
      have hκ : 0 ≤ (1 - c) * (2 * θn - 1) :=
        mul_nonneg (by linarith only [hc1])
          (by dsimp [θn]; linarith only [hb.1])
      have howner := hcontract θn hb.1 hb.2 ih
      have hstep := native_growthAtMost_of_ownerBound hκ hb.1 howner ih
      have heq : (1 + 2 * θn + (1 - c) * (2 * θn - 1)) / 4 =
          1 / 2 + (1 - c / 2) * (θn - 1 / 2) := by ring
      change MertensGrowthAtMost
        (1 / 2 + (1 - c / 2) * (θn - 1 / 2))
      rw [← heq]
      exact hstep

/-- The MERGED slot gain is a valid input to the quantified contraction
if and only if the new owner arithmetic premise is supplied. -/
theorem native_fractional_owner_seeded
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcontract : NativeUniformFractionalOwnerContraction c) :
    ∃ θ : ℝ, (1 / 2 : ℝ) ≤ θ ∧ θ < 7 / 8 ∧
      ∀ n : ℕ,
        MertensGrowthAtMost (fractionalOwnerExponentIterate c θ n) := by
  obtain ⟨D, hpositive, hbeta⟩ :=
    native_beta_le_true_physical_slot_minimum
  let θ : ℝ := 7 / 8 - actualSlotMinimum D / 24
  have hθ0 : (1 / 2 : ℝ) ≤ θ := by
    dsimp [θ]
    linarith only [hbeta, HeckeZeroSupremum.half_le_beta]
  have hθ1 : θ < (7 / 8 : ℝ) := by
    dsimp [θ]
    linarith only [hpositive]
  have hgrowth : MertensGrowthAtMost θ := by
    exact growthAtMost_mono hbeta native_mertens_growth_at_hecke_beta
  exact ⟨θ, hθ0, hθ1,
    native_fractional_owner_iterated_growth c θ hc0.le hc1 hθ0 hθ1.le
      hcontract hgrowth⟩

#print axioms fractionalOwnerExponentIterate_closed
#print axioms native_fractional_owner_iterated_growth
#print axioms native_fractional_owner_seeded

end RHLean.Analysis.OwnerPrefix
end
