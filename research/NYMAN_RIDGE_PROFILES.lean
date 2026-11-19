import «research.NYMAN_RIDGE_GEOMETRY»

/-! Finite RIDGE1 on the original residual. The solver includes the unit in
both source moments, while physical coefficients run from 2 through 6K. -/

set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace RHLean.Analysis

def nymanRidgeLeft (K : Nat) (u v : Real) : Real :=
  (u - nymanRidgeS (5*K) (6*K) * v / K) / nymanRidgeGap K
def nymanRidgeRight (K : Nat) (u v : Real) : Real :=
  (nymanRidgeS (3*K) (4*K) * v / K - u) / nymanRidgeGap K
def nymanRidgeRepair (K : Nat) (u v : Real) (k : Nat) : Real :=
  (if k ∈ Ioc (3*K) (4*K) then nymanRidgeLeft K u v else 0) +
  (if k ∈ Ioc (5*K) (6*K) then nymanRidgeRight K u v else 0)
def nymanRidgeV (K H : Nat) : Real := 2 * nymanFlatScale (6*K) H +
  ∑ k ∈ Icc 1 (6*K), nymanFlatKernel (6*K) H k
def nymanRidgeCoeff (K H : Nat) : Nat → Real := nymanFlatCoefficient (6*K) H
  (nymanRidgeRepair K (nymanFlatMoment (6*K) H) (nymanRidgeV K H))
def nymanRidgeD (K m : Nat) : Real :=
  (nymanRidgeG (3*K) (4*K) m - nymanRidgeG (5*K) (6*K) m) / nymanRidgeGap K
def nymanRidgeP (K m : Nat) : Real :=
  (nymanRidgeS (3*K) (4*K) * nymanRidgeG (5*K) (6*K) m -
    nymanRidgeS (5*K) (6*K) * nymanRidgeG (3*K) (4*K) m) / nymanRidgeGap K

private theorem gap_pos (K : Nat) (hK : 0 < K) : 0 < nymanRidgeGap K :=
  lt_of_lt_of_le (by norm_num : (0:Real) < 1/12) (nyman_ridge_gap K hK)

private theorem weighted (K : Nat) (hK : 0 < K) (u v : Real) (f : Nat → Real) :
    (∑ k ∈ Icc 2 (6*K), nymanRidgeRepair K u v k * f k) =
      nymanRidgeLeft K u v * (∑ k ∈ Ioc (3*K) (4*K), f k) +
      nymanRidgeRight K u v * (∑ k ∈ Ioc (5*K) (6*K), f k) := by
  have single (S : Finset Nat) (hs : S ⊆ Icc 2 (6*K)) (x : Real) :
      (∑ k ∈ Icc 2 (6*K), (if k ∈ S then x else 0) * f k) = x * ∑ k ∈ S, f k := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ k ∈ S, (if k ∈ S then x else 0) * f k :=
        (Finset.sum_subset hs (fun k _ hn => by simp [hn])).symm
      _ = _ := Finset.sum_congr rfl (fun k hk => by simp [hk])
  have inc (a b : Nat) (ha : 1 ≤ a) (hb : b ≤ 6*K) : Ioc a b ⊆ Icc 2 (6*K) := by
    intro k hk
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
    omega
  simp only [nymanRidgeRepair, add_mul, Finset.sum_add_distrib]
  rw [single _ (inc _ _ (by omega) (by omega)), single _ (inc _ _ (by omega) (by omega))]

private theorem masses (K : Nat) (hK : 0 < K) (u v : Real) :
    nymanCorrectionMoment (6*K) (nymanRidgeRepair K u v) = u ∧
      (∑ k ∈ Icc 2 (6*K), nymanRidgeRepair K u v k) = v := by
  have sol : nymanRidgeLeft K u v * nymanRidgeS (3*K) (4*K) +
      nymanRidgeRight K u v * nymanRidgeS (5*K) (6*K) = u ∧
      K * nymanRidgeLeft K u v + K * nymanRidgeRight K u v = v :=
    nyman_two_band_moment_solver K _ _ u v (by exact_mod_cast hK.ne')
      (sub_pos.mp (gap_pos K hK)).ne'
  constructor
  · calc
      _ = _ := by
        simpa only [nymanCorrectionMoment, nymanRidgeS, div_eq_mul_inv, one_mul] using
          weighted K hK u v (fun k => 1 / (k:Real))
      _ = u := sol.1
  · calc
      _ = (K:Real) * nymanRidgeLeft K u v + K * nymanRidgeRight K u v := by
        simpa [Nat.card_Ioc, show 4*K-3*K=K by omega, show 6*K-5*K=K by omega, mul_comm] using
          weighted K hK u v (fun _ => 1)
      _ = v := sol.2

theorem nyman_ridge_moments (K H : Nat) (hK : 0 < K) (hH : 1 ≤ H) (hHN : H < 6*K) :
    (∑ k ∈ Icc 2 (6*K), nymanRidgeCoeff K H k / (k:Real)) = 1 ∧
    (∑ k ∈ Icc 2 (6*K), nymanRidgeCoeff K H k) = 3 := by
  have hm := masses K hK (nymanFlatMoment (6*K) H) (nymanRidgeV K H)
  have hl := (nymanFlatScale_pos (6*K) H hH hHN).ne'
  constructor
  · unfold nymanRidgeCoeff
    rw [nyman_flat_reciprocal_moment (6*K) H _ hH hHN, hm.1]
    simp
  · simp only [nymanRidgeCoeff, nymanFlatCoefficient, ← Finset.sum_div, Finset.sum_sub_distrib, hm.2]
    apply (div_eq_iff hl).2
    have hu := nyman_sum_one_split (6*K) (by omega) (nymanFlatKernel (6*K) H)
    rw [nymanFlatKernel_one _ _ hH] at hu
    rw [nymanRidgeV, hu]
    ring

/-- RIDGE1's pointwise identity, on every output including zero and the full tail. -/
theorem nyman_ridge_residual_profiles (K H m : Nat) (hK : 0 < K) :
    nymanResidual (6*K) (nymanRidgeCoeff K H) m =
      nymanResidual (6*K) (nymanFlatCoefficient (6*K) H (fun _ => 0)) m -
      nymanFlatMoment (6*K) H / nymanFlatScale (6*K) H * nymanRidgeD K m -
      (nymanRidgeV K H / K / nymanFlatScale (6*K) H) * nymanRidgeP K m := by
  let u := nymanFlatMoment (6*K) H
  let v := nymanRidgeV K H
  let L := nymanFlatScale (6*K) H
  have term (k : Nat) : nymanRidgeCoeff K H k * nymanResidue k m =
      nymanFlatCoefficient (6*K) H (fun _ => 0) k * nymanResidue k m +
        nymanRidgeRepair K u v k * nymanResidue k m / L := by
    unfold nymanRidgeCoeff nymanFlatCoefficient
    dsimp only [u, v, L]
    ring
  unfold nymanResidual
  simp_rw [term]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, weighted K hK u v (fun k => nymanResidue k m)]
  unfold nymanRidgeD nymanRidgeP nymanRidgeG nymanRidgeLeft nymanRidgeRight
  dsimp only [u, v, L]
  ring

/-- On every output, the deviations from (m,0) are the signed floor counts,
not approximating profiles. Together with the two layer theorems this gives
both sides of each threshold with the literal endpoint conventions. -/
theorem nyman_ridge_floor_profiles (K m : Nat) (hK : 0 < K) :
    let c := (nymanBandCount (3*K) (4*K) m : Real)
    let e := (nymanBandCount (5*K) (6*K) m : Real)
    nymanRidgeD K m = m - (c-e) / nymanRidgeGap K ∧
    nymanRidgeP K m = (nymanRidgeS (5*K) (6*K)*c - nymanRidgeS (3*K) (4*K)*e) /
      nymanRidgeGap K := by
  dsimp only
  unfold nymanRidgeD nymanRidgeP
  rw [nyman_ridge_residue_floor, nyman_ridge_residue_floor]
  have hd := (gap_pos K hK).ne'
  constructor
  · apply (div_eq_iff hd).2
    rw [sub_mul, div_mul_cancel₀ _ hd, nymanRidgeGap]
    ring
  · congr 1
    ring

end RHLean.Analysis
