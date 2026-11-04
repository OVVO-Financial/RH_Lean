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

/-- A single fixed positive fractional owner contraction, UNIFORMLY
renewable at the current exponent, implies a genuine RH-strength
all-integer Mertens bound. The missing source estimate is hcontract. -/
theorem native_fractional_owner_contraction_implies_mertens_half
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcontract : NativeUniformFractionalOwnerContraction c) :
    MertensGrowthAtMost (1 / 2) := by
  obtain ⟨θ, _hθ0, _hθ1, hall⟩ :=
    native_fractional_owner_seeded c hc0 hc1 hcontract
  intro ε hε
  let q : ℝ := 1 - c / 2
  have hq0 : 0 ≤ q := by dsimp [q]; linarith only [hc1]
  have hq1 : q < 1 := by dsimp [q]; linarith only [hc0]
  have hlim : Filter.Tendsto
      (fun n : ℕ => (θ - 1 / 2) * q ^ n)
      Filter.atTop (nhds (0 : ℝ)) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    simpa only [mul_zero] using hp.const_mul (θ - 1 / 2)
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      (θ - 1 / 2) * q ^ n < ε / 2 := by
    exact hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  obtain ⟨n, hn⟩ := hsmall.exists
  have hε2 : 0 < ε / 2 := by linarith
  have hp := hall n (ε / 2) hε2
  rw [fractionalOwnerExponentIterate_closed] at hp
  have hbound : (1 / 2 : ℝ) +
      (θ - 1 / 2) * (1 - c / 2) ^ n + ε / 2 ≤ 1 / 2 + ε := by
    dsimp [q] at hn
    linarith only [hn]
  exact powerBound_mono hbound hp

/-- The complete signed owner-contraction theorem would imply RH through
the existing fully formalized Mertens/zeta-zero equivalence. The new
arithmetic estimate is a VISIBLE hypothesis, not an axiom or result. -/
theorem native_fractional_owner_contraction_implies_critical_zeros
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcontract : NativeUniformFractionalOwnerContraction c) :
    ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) := by
  exact growthAtMost_half_iff_criticalZeros.mp
    (native_fractional_owner_contraction_implies_mertens_half c hc0 hc1 hcontract)

#print axioms fractionalOwnerExponentIterate_closed
#print axioms native_fractional_owner_iterated_growth
#print axioms native_fractional_owner_seeded
#print axioms native_fractional_owner_contraction_implies_mertens_half
#print axioms native_fractional_owner_contraction_implies_critical_zeros

end RHLean.Analysis.OwnerPrefix
end
