import «research.NYMAN_WITNESS_PRIME»

/-! What is lost by keeping only distinct repair sites after saturation. -/
set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace RHLean.Analysis

/-- Both band floor counts are replaced by K in the original two profiles.
This models distinct-site counting at outputs m >= 6K only. -/
def nymanWitnessClipped (K H m : ℕ) : ℝ :=
  nymanResidual (6*K) (nymanFlatCoefficient (6*K) H (fun _ => 0)) m -
    nymanFlatMoment (6*K) H / nymanFlatScale (6*K) H * m -
    nymanRidgeV K H / K / nymanFlatScale (6*K) H *
      ((nymanRidgeS (5*K) (6*K)*K - nymanRidgeS (3*K) (4*K)*K) / nymanRidgeGap K)

def nymanWitnessError (K H m : ℕ) : ℝ :=
  nymanResidual (6*K) (nymanRidgeCoeff K H) m - nymanWitnessClipped K H m

private theorem errorCounts (K H m : ℕ) (hK : 0<K) :
    let u := nymanFlatMoment (6*K) H
    let v := nymanRidgeV K H
    nymanWitnessError K H m =
      (nymanRidgeLeft K u v * ((nymanBandCount (3*K) (4*K) m:ℝ)-K) +
       nymanRidgeRight K u v * ((nymanBandCount (5*K) (6*K) m:ℝ)-K)) / nymanFlatScale (6*K) H := by
  dsimp only
  obtain ⟨hD,hP⟩ := nyman_ridge_floor_profiles K m hK
  unfold nymanWitnessError nymanWitnessClipped
  rw [nyman_ridge_residual_profiles K H m hK, hD, hP]
  unfold nymanRidgeLeft nymanRidgeRight
  ring

/-- The first doubled floor is a genuine discrepancy of the original residual. -/
theorem nyman_witness_first_clip (K H : ℕ) (hK : 0<K) (hH : 0<H) (hHK : H ≤ 3*K) :
    nymanWitnessError K H (6*K+2) = nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) /
      nymanFlatScale (6*K) H ∧ nymanWitnessError K H (6*K+2) ≠ 0 := by
  obtain ⟨hc,he⟩ := nyman_ridge_first_double K hK
  have eqn := errorCounts K H (6*K+2) hK
  dsimp only at eqn
  rw [hc,he] at eqn
  simp at eqn
  refine ⟨eqn, ?_⟩
  rw [eqn]
  exact div_ne_zero (nyman_witness_amplitudes K H hK hH hHK).1
    (nymanFlatScale_pos (6*K) H hH (by omega)).ne'

theorem nyman_witness_clip_plateau (K H m : ℕ) (hK : 0<K) (hl : 8*K ≤ m) (hr : m ≤ 9*K+2) :
    nymanWitnessError K H m = (K:ℝ)*nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) /
      nymanFlatScale (6*K) H := by
  have counts (a b j : ℕ) (hw : ∀ k ∈ Ioc a b, m/k=j) : nymanBandCount a b m = (b-a)*j := by
    unfold nymanBandCount
    calc
      _ = ∑ _k ∈ Ioc a b, j := sum_congr rfl hw
      _ = _ := by simp
  have hc := counts (3*K) (4*K) 2 (fun k hk => by
    obtain ⟨_, _⟩ := mem_Ioc.mp hk; exact Nat.div_eq_of_lt_le (by omega) (by omega))
  have he := counts (5*K) (6*K) 1 (fun k hk => by
    obtain ⟨_, _⟩ := mem_Ioc.mp hk; exact Nat.div_eq_of_lt_le (by omega) (by omega))
  rw [errorCounts K H m hK, hc, he, show 4*K-3*K=K by omega, show 6*K-5*K=K by omega]
  push_cast; ring

private theorem intervalMass (s n : ℕ) (hs : 0<s) :
    ∑ j ∈ range n, nymanWeight (s+j) = 1/(s:ℝ)-1/((s+n:ℕ):ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.add_succ, Nat.cast_succ]
    have hp : 0 < ((s+n:ℕ):ℝ) := by exact_mod_cast (show 0<s+n by omega)
    unfold nymanWeight
    field_simp; ring

/-- Exact energy of the error of the surrogate, not a lower bound on the true energy. -/
theorem nyman_witness_clip_energy (K H : ℕ) (hK : 0<K) :
    let A := nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) / nymanFlatScale (6*K) H
    (∑ j ∈ range (K+3), nymanWeight (8*K+j) * nymanWitnessError K H (8*K+j)^2) =
      ((K:ℝ)*A)^2 * (1/((8*K:ℕ):ℝ)-1/((9*K+3:ℕ):ℝ)) := by
  let A := nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) / nymanFlatScale (6*K) H
  change _ = ((K:ℝ)*A)^2 * _
  have h := intervalMass (8*K) (K+3) (by omega)
  rw [show 8*K+(K+3)=9*K+3 by omega] at h
  calc
    _ = (∑ j ∈ range (K+3), nymanWeight (8*K+j)) * ((K:ℝ)*A)^2 := by
      rw [Finset.sum_mul]
      apply sum_congr rfl
      intro j hj
      rw [nyman_witness_clip_plateau K H _ hK (by omega) (by have := mem_range.mp hj; omega)]
      dsimp only [A]; ring
    _ = _ := by rw [h]; ring

theorem nyman_witness_clip_cost (K H : ℕ) (hK : 0<K) (hH : 0<H) (hHK : H ≤ 3*K) :
    let A := nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) / nymanFlatScale (6*K) H
    (K:ℝ)/72*A^2 < ∑ j ∈ range (K+3), nymanWeight (8*K+j)*nymanWitnessError K H (8*K+j)^2 := by
  dsimp only
  rw [nyman_witness_clip_energy K H hK]
  let A := nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) / nymanFlatScale (6*K) H
  change (K:ℝ)/72*A^2 < ((K:ℝ)*A)^2 * _
  have hA : 0 < A^2 := sq_pos_of_ne_zero (div_ne_zero (nyman_witness_amplitudes K H hK hH hHK).1
    (nymanFlatScale_pos (6*K) H hH (by omega)).ne')
  have hR : (0:ℝ) < K := by exact_mod_cast hK
  push_cast
  have hs : 1/(9*(K:ℝ)+3) < 1/(9*(K:ℝ)) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  calc
    _ = ((K:ℝ)*A)^2*(1/(8*(K:ℝ))-1/(9*(K:ℝ))) := by field_simp; ring
    _ < _ := mul_lt_mul_of_pos_left (sub_lt_sub_left hs _) (by rw [mul_pow]; exact mul_pos (by positivity) hA)

end RHLean.Analysis
