import «research.oai_434.VF919NativeOwnerDiagonalThreeQuarter»
import «research.oai_434.VF919ActualSlotMinRetighten»

/-!
# Reinvest the true physical-slot exponent in the genuine owner diagonal

PR #1082 pays D_R at exponent 11/4 using the original 7/8 input.
This is the variable-exponent version, specialized to the #1079
physical-slot gain.  It yields the source-faithful 2*delta saving
in the owner diagonal WITHOUT asserting the missing signed Gamma bound.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis.OwnerPrefix

open RHLean.Analysis.MertensExponent
open RHLean.Proof.NativeOwnerSwapRenewal
open OAI.SevenEighths
open OAI.SevenEighths.RHLeanActualSlotMin

/-- Variable-exponent high-prime diagonal payment, on the unchanged
p>R owner family and the actual Mobius prefix source. -/
theorem native_owner_diagonal_of_growth
    (θ : ℝ) (hθ : (1 / 2 : ℝ) ≤ θ)
    (hgrowth : MertensGrowthAtMost θ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R →
      ownerDiagonal R ≤ C * (R : ℝ) ^ (1 + 2 * θ + ε) := by
  have hglobal : GrowthAtMost nativeM θ :=
    (native_growthAtMost_iff θ).mpr hgrowth
  let t : ℝ := ε / 3
  have ht : 0 < t := by dsimp [t]; linarith
  obtain ⟨D, hD, hM⟩ := hglobal t ht
  let a : ℝ := θ - 1 / 2 + t
  have ha : 0 ≤ a := by dsimp [a]; linarith only [hθ, ht]
  have hMa : ∀ n : ℕ, 1 ≤ n →
      |nativeM n| ≤ D * (n : ℝ) ^ (a + 1 / 2) := by
    intro n hn
    convert hM n hn using 1
    dsimp [a]
    ring
  let k : ℝ := 1 + 2 / t
  have hk : 0 < k := by dsimp [k]; positivity
  let C : ℝ := k * (D + 1) ^ 2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR
  have hR0 : 0 < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hR1 : 1 ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
  have hE : prefixAmplitude nativeM R ≤
      (D + 1) * (R : ℝ) ^ a :=
    prefixAmplitude_le_of_power nativeM ha hD hMa R hR
  have hE0 : 0 ≤ prefixAmplitude nativeM R :=
    prefixAmplitude_nonneg nativeM R
  have hEtarget0 : 0 ≤ (D + 1) * (R : ℝ) ^ a := by positivity
  have hEsq : prefixAmplitude nativeM R ^ 2 ≤
      ((D + 1) * (R : ℝ) ^ a) ^ 2 :=
    (sq_le_sq₀ hE0 hEtarget0).mpr hE
  have hx : (endpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    unfold endpoint
    exact_mod_cast Nat.sub_le (R ^ 2) 1
  have hDsource :
      diagonal nativeM R ≤
        k * (endpoint R : ℝ) * (R : ℝ) ^ t *
          prefixAmplitude nativeM R ^ 2 := by
    simpa only [k] using
      (diagonal_le_rpow nativeM ht R hR)
  have hpow :
      (R : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ t *
          ((R : ℝ) ^ a) ^ (2 : ℕ) =
        (R : ℝ) ^ (1 + 2 * θ + ε) := by
    have h2 : (R : ℝ) ^ (2 : ℕ) = (R : ℝ) ^ (2 : ℝ) :=
      (Real.rpow_natCast (R : ℝ) 2).symm
    have ha2 : ((R : ℝ) ^ a) ^ (2 : ℕ) =
        (R : ℝ) ^ (a * 2) := by
      calc
        ((R : ℝ) ^ a) ^ (2 : ℕ) =
            ((R : ℝ) ^ a) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = (R : ℝ) ^ (a * 2) :=
          (Real.rpow_mul hR0.le a 2).symm
    rw [h2, ha2, ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1
    dsimp [a, t]
    ring
  rw [← native_diagonal_eq_ownerDiagonal R]
  calc
    diagonal nativeM R ≤
        k * (endpoint R : ℝ) * (R : ℝ) ^ t *
          prefixAmplitude nativeM R ^ 2 := hDsource
    _ ≤ k * (R : ℝ) ^ 2 * (R : ℝ) ^ t *
          ((D + 1) * (R : ℝ) ^ a) ^ 2 := by
            have hu : 0 ≤ k * (endpoint R : ℝ) * (R : ℝ) ^ t := by
              positivity
            have hv : 0 ≤ k * (R : ℝ) ^ t *
                ((D + 1) * (R : ℝ) ^ a) ^ 2 := by positivity
            have hsqbound := mul_le_mul_of_nonneg_left hEsq hu
            have hxbound := mul_le_mul_of_nonneg_right hx hv
            nlinarith
    _ = (k * (D + 1) ^ 2) *
          (R : ℝ) ^ (1 + 2 * θ + ε) := by
            rw [mul_pow]
            calc
              k * (R : ℝ) ^ 2 * (R : ℝ) ^ t *
                    ((D + 1) ^ 2 * ((R : ℝ) ^ a) ^ 2) =
                  (k * (D + 1) ^ 2) *
                    ((R : ℝ) ^ 2 * (R : ℝ) ^ t *
                      ((R : ℝ) ^ a) ^ 2) := by ring
              _ = _ := by rw [hpow]
    _ ≤ C * (R : ℝ) ^ (1 + 2 * θ + ε) := by
            have hp : 0 ≤ (R : ℝ) ^ (1 + 2 * θ + ε) := by
              positivity
            dsimp [C]
            nlinarith

/-- The source-geometric gain is paid TWICE in the native diagonal
exponent. This is unconditional relative to the imported analytic source. -/
theorem native_owner_diagonal_true_slot_gain :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R →
        ownerDiagonal R ≤
          C * (R : ℝ) ^ ((11 : ℝ) / 4 - 2 * δ + ε) := by
  obtain ⟨D, hD, hbeta⟩ := native_beta_le_true_physical_slot_minimum
  let δ : ℝ := actualSlotMinimum D / 24
  let θ : ℝ := 7 / 8 - δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hθ : (1 / 2 : ℝ) ≤ θ := by
    dsimp [θ, δ]
    linarith only [hbeta, HeckeZeroSupremum.half_le_beta]
  have hgrowth : MertensGrowthAtMost θ := by
    exact growthAtMost_mono hbeta native_mertens_growth_at_hecke_beta
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨C, hC, hbound⟩ :=
    native_owner_diagonal_of_growth θ hθ hgrowth ε hε
  refine ⟨C, hC, ?_⟩
  intro R hR
  have hexp : 1 + 2 * θ + ε =
      (11 : ℝ) / 4 - 2 * δ + ε := by
    dsimp [θ]
    ring
  simpa only [hexp] using hbound R hR

#print axioms native_owner_diagonal_of_growth
#print axioms native_owner_diagonal_true_slot_gain

end RHLean.Analysis.OwnerPrefix
end
