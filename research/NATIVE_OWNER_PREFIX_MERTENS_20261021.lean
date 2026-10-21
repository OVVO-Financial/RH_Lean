import «research.NATIVE_OWNER_PREFIX_RECURRENCE_20261021»
import «research.NATIVE_OWNER_SWAP_RENEWAL_20261021»
import «research.MERTENS_EXPONENT_ENVELOPES»
import RHLean.Analysis.SquareRootTransportRealization

/-!
# Original-source specialization of the conditional owner-prefix recurrence

The real sequence below is exactly the real part of the repository's original
Mertens summatory function. The smooth mass has the original cutoff `p ≤ R`;
transport retains the original strict cutoff `p > R` at `R^2 - 1`.

The quantitative owner bound remains an explicit hypothesis. No estimate for
that complete signed interaction is asserted by this consumer.
-/

noncomputable section

namespace RHLean.Analysis.OwnerPrefix

open scoped BigOperators ArithmeticFunction.Moebius

open RHLean.Proof.NativeOwnerSwapRenewal

/-- The original Mertens function, in its real coordinate. -/
def nativeM (n : ℕ) : ℝ := (RHLean.Analysis.mertensSummatory n).re

/-- The original complete smooth population, including its unit source. -/
def nativeA (R : ℕ) : ℝ := (RHLean.Proof.squareRootSmoothMass (R - 1)).re

theorem nativeM_coe (n : ℕ) :
    (nativeM n : ℂ) = RHLean.Analysis.mertensSummatory n := by
  apply Complex.ext <;>
    simp [nativeM, RHLean.Analysis.mertensSummatory]

theorem nativeM_abs_eq_norm (n : ℕ) :
    |nativeM n| = ‖RHLean.Analysis.mertensSummatory n‖ := by
  simpa using congrArg norm (nativeM_coe n)

@[simp] theorem nativeM_one : nativeM 1 = 1 := by
  norm_num [nativeM, RHLean.Analysis.mertensSummatory, Finset.sum_range_succ]

theorem nativeM_step (n : ℕ) : |nativeM (n + 1) - nativeM n| ≤ 1 := by
  calc
    |nativeM (n + 1) - nativeM n| ≤
        ‖RHLean.Analysis.mertensSummatory (n + 1) -
          RHLean.Analysis.mertensSummatory n‖ := by
      change
        |(RHLean.Analysis.mertensSummatory (n + 1) -
          RHLean.Analysis.mertensSummatory n).re| ≤
            ‖RHLean.Analysis.mertensSummatory (n + 1) -
              RHLean.Analysis.mertensSummatory n‖
      exact Complex.abs_re_le_norm _
    _ ≤ 1 := by
      simpa using RHLean.Analysis.norm_mertensSummatory_sub_le n (n + 1) (by omega)

/-- Exact specialization: every transported value is the original Mertens
prefix, and the historical cutoff is unchanged. -/
theorem native_decomposition (R : ℕ) (hR : 2 ≤ R) :
    nativeM (endpoint R) = nativeA R - transport nativeM R := by
  have h := RHLean.Proof.squarePrefixMertens_eq_squareRootSmooth_sub_transport
    (R - 1)
  rw [RHLean.Proof.squareRootTransportMass_pred_eq_cofactorFirst R (by omega),
    RHLean.Proof.squareRootTransportCofactorFirst_eq_primeFirst,
    RHLean.Proof.squareRootTransportPrimeFirst_eq_mertensTransform R (by omega)] at h
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel (by omega)
  simpa [nativeM, nativeA, endpoint, transport, primeOwners,
    RHLean.Analysis.squarePrefixMertens, RHLean.Analysis.squarePrefixEndpoint,
    RHLean.Proof.squareRootEndpoint, hpred, Finset.sum_filter,
    apply_ite Complex.re] using congrArg Complex.re h

/-- Open arithmetic target on the original native source. -/
def NativeOwnerBound (κ : ℝ) : Prop := OwnerBound nativeM nativeA κ

theorem native_prefixAmplitude_eq_raw (B : ℕ) (hB : 2 ≤ B) :
    prefixAmplitude nativeM B = rawPrefixAmplitude nativeM B hB := by
  exact prefixAmplitude_eq_raw nativeM B hB (by simp)

/-- The generic consumer pays exactly the diagonal of the original prime
owners, expressed in the native complex norm. -/
theorem native_diagonal_eq_ownerDiagonal (R : ℕ) :
    diagonal nativeM R = ownerDiagonal R := by
  unfold diagonal primeOwners ownerDiagonal
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hprime : p.Prime
  · simp only [hprime, ite_true]
    rw [← sq_abs]
    exact congrArg (fun x : ℝ => x ^ 2)
      (nativeM_abs_eq_norm (endpoint R / p))
  · simp [hprime]

/-- The arithmetic premise in the consumer is the original complete signed
smooth/transport interaction, not a replacement residual with new weights. -/
theorem native_compensation_eq_fullOwnerGamma (R : ℕ) (hR : 2 ≤ R) :
    compensation nativeM nativeA R = fullOwnerGamma R := by
  have hreal := square_eq_diagonal_add_compensation nativeM nativeA
    (native_decomposition R hR)
  have hnative := mertens_norm_sq_eq_diagonal_add_gamma R hR
  have hsq : nativeM (endpoint R) ^ 2 =
      ‖RHLean.Analysis.mertensSummatory (RHLean.Proof.squareRootEndpoint R)‖ ^ 2 := by
    rw [← sq_abs]
    exact congrArg (fun x : ℝ => x ^ 2) (nativeM_abs_eq_norm (endpoint R))
  rw [native_diagonal_eq_ownerDiagonal] at hreal
  linarith

/-- Exact finite binding of the open owner premise to the existing native
replacement row with the actual prime-owner diagonal removed. -/
theorem native_compensation_eq_replacementGram (R : ℕ) (hR : 2 ≤ R) :
    compensation nativeM nativeA R = (ownerRemovedReplacementGram R).re := by
  rw [native_compensation_eq_fullOwnerGamma R hR, fullOwnerGamma,
    full_owner_gram_eq_owner_removed_replacement_gram R hR]

theorem native_ownerBound_iff_replacementGram (κ : ℝ) :
    NativeOwnerBound κ ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R →
        (ownerRemovedReplacementGram R).re ≤
          C * (R : ℝ) ^ (κ + ε) *
            ((RHLean.Proof.squareRootEndpoint R : ℝ) + ownerDiagonal R) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro R hR
    simpa only [native_compensation_eq_replacementGram R hR,
      native_diagonal_eq_ownerDiagonal, endpoint, RHLean.Proof.squareRootEndpoint]
      using hbound R hR
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro R hR
    simpa only [native_compensation_eq_replacementGram R hR,
      native_diagonal_eq_ownerDiagonal, endpoint, RHLean.Proof.squareRootEndpoint]
      using hbound R hR

/-- The conditional recurrence now has no supplied decomposition or step
hypotheses: those are discharged by the unchanged native source. -/
theorem native_prefix_amplitude_recurrence
    (κ : ℝ) (hκ : 0 ≤ κ) (howner : NativeOwnerBound κ) :
    ∀ ε > 0, ∃ C > 0, ∀ B ≥ 2,
      prefixAmplitude nativeM (B ^ 2) ≤
        C * (B : ℝ) ^ (κ / 2 + ε) * prefixAmplitude nativeM B := by
  exact prefix_amplitude_recurrence nativeM nativeA (κ := κ) hκ native_decomposition
    (fun n _hn => nativeM_step n) howner

theorem native_powerBound_iff (a : ℝ) :
    PowerBound nativeM a ↔ MertensExponent.MertensPowerBound a := by
  simp only [PowerBound, MertensExponent.MertensPowerBound, nativeM_abs_eq_norm,
    Real.rpow_eq_pow]

theorem native_growthAtMost_iff (a : ℝ) :
    GrowthAtMost nativeM a ↔ MertensExponent.MertensGrowthAtMost a := by
  simp only [GrowthAtMost, MertensExponent.MertensGrowthAtMost, native_powerBound_iff]

/-- Any available exponent is transferred by the same original-source owner
bound. The gain is conditional on that new arithmetic estimate. -/
theorem native_growthAtMost_of_ownerBound {κ θ : ℝ}
    (hκ : 0 ≤ κ) (hθ : (1 : ℝ) / 2 ≤ θ)
    (howner : NativeOwnerBound κ)
    (hgrowth : MertensExponent.MertensGrowthAtMost θ) :
    MertensExponent.MertensGrowthAtMost ((1 + 2 * θ + κ) / 4) := by
  apply (native_growthAtMost_iff _).mp
  exact growthAtMost_of_ownerBound nativeM nativeA hκ hθ native_decomposition
    (fun n _hn => nativeM_step n) howner ((native_growthAtMost_iff θ).mpr hgrowth)

/-- Calibration of the target: an original-owner quarter-power bound would
take the supplied 7/8 envelope to 3/4 in a single application. -/
theorem native_three_quarters_of_owner_quarter
    (howner : NativeOwnerBound (1 / 4))
    (hseven : MertensExponent.MertensGrowthAtMost (7 / 8)) :
    MertensExponent.MertensGrowthAtMost (3 / 4) := by
  have h := native_growthAtMost_of_ownerBound (κ := 1 / 4) (θ := 7 / 8)
    (by norm_num) (by norm_num) howner hseven
  norm_num at h ⊢
  exact h

theorem native_eleven_sixteenths_of_owner_zero
    (howner : NativeOwnerBound 0)
    (hseven : MertensExponent.MertensGrowthAtMost (7 / 8)) :
    MertensExponent.MertensGrowthAtMost (11 / 16) := by
  have h := native_growthAtMost_of_ownerBound (κ := 0) (θ := 7 / 8)
    (by norm_num) (by norm_num) howner hseven
  norm_num at h ⊢
  exact h

#print axioms nativeM_coe
#print axioms native_decomposition
#print axioms native_compensation_eq_replacementGram
#print axioms native_ownerBound_iff_replacementGram
#print axioms native_prefix_amplitude_recurrence
#print axioms native_growthAtMost_of_ownerBound
#print axioms native_three_quarters_of_owner_quarter
#print axioms native_eleven_sixteenths_of_owner_zero

end RHLean.Analysis.OwnerPrefix
