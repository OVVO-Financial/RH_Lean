import «research.NATIVE_OWNER_PREFIX_MERTENS_20261021»
import «research.oai_434.VF919NativeSevenEighthsReplay»

/-!
# The original 7/8 certificate pays the complete high-prime owner diagonal

This is an unconditional arithmetic consequence of the independently
kernel-checked original OAI 7/8 source replay. The exact high-prime
owner family p>R, endpoint R^2-1, and original Mertens values are kept.
The diagonal is genuinely below the R^3 target needed for the 3/4
square-endpoint program:

    D_R = O_epsilon (R^(11/4+epsilon)).

The still-open one-sided signed source is the REAL original fullOwnerGamma,
not an auxiliary hypothetical vector. For 3/4, it is enough to prove
fullOwnerGamma R = O_upper_epsilon(R^(3+epsilon)); the complete original
square has no other unbudgeted positive component.

This file makes NO claim that this signed estimate has been proved.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis.OwnerPrefix

open RHLean.Proof.NativeOwnerSwapRenewal

/-- The exact prime-owner diagonal inherits an R^(11/4+epsilon) bound
from the ACTUAL globally proved Mertens 7/8 estimate. This saves a
fixed quarter power against the R^3 budget for 3/4 Mertens at squares.

The proof works with the literal ownerDiagonal and exact p>R cutoff,
not with a substitute count, stochastic model, or assumed owner norm.
-/
theorem native_owner_diagonal_seven_eighths_paid
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R →
      ownerDiagonal R ≤ C * (R : ℝ) ^ ((11 : ℝ) / 4 + ε) := by
  have hgrowth : GrowthAtMost nativeM ((7 : ℝ) / 8) :=
    (native_growthAtMost_iff ((7 : ℝ) / 8)).mpr
      RHLean.Analysis.nativeReplay_mertens_growth
  let t : ℝ := ε / 3
  have ht : 0 < t := by dsimp [t]; linarith
  obtain ⟨D, hD, hM⟩ := hgrowth t ht
  let a : ℝ := (3 : ℝ) / 8 + t
  have ha : 0 ≤ a := by dsimp [a]; linarith
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
        (R : ℝ) ^ ((11 : ℝ) / 4 + ε) := by
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
          (R : ℝ) ^ ((11 : ℝ) / 4 + ε) := by
            rw [mul_pow]
            calc
              k * (R : ℝ) ^ 2 * (R : ℝ) ^ t *
                    ((D + 1) ^ 2 * ((R : ℝ) ^ a) ^ 2) =
                  (k * (D + 1) ^ 2) *
                    ((R : ℝ) ^ 2 * (R : ℝ) ^ t *
                      ((R : ℝ) ^ a) ^ 2) := by ring
              _ = _ := by rw [hpow]
    _ ≤ C * (R : ℝ) ^ ((11 : ℝ) / 4 + ε) := by
            have hp : 0 ≤ (R : ℝ) ^ ((11 : ℝ) / 4 + ε) := by
              positivity
            dsimp [C]
            nlinarith

/-- The original exact positive-part decomposition: once the diagonal
is paid, the only possible R^3 obstruction is the *positive* part
of the complete signed owner source, never its negative excursions. -/
theorem native_owner_energy_le_diagonal_add_positive_gamma
    (R : ℕ) (hR : 2 ≤ R) :
    ‖RHLean.Analysis.mertensSummatory (RHLean.Proof.squareRootEndpoint R)‖ ^ 2 ≤
      ownerDiagonal R + max 0 (fullOwnerGamma R) := by
  rw [mertens_norm_sq_eq_diagonal_add_gamma R hR]
  exact add_le_add_left (le_max_right _ _) _

#print axioms native_owner_diagonal_seven_eighths_paid
#print axioms native_owner_energy_le_diagonal_add_positive_gamma

end RHLean.Analysis.OwnerPrefix
end
