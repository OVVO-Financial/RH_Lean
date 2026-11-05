import «research.NYMAN_FLAT_TAPER_RETURN_20261104»

/-!
Finite quantitative core of 20261104-coordinator-3/C49, independently checked
by Lean Verification. A correction supported above 3K is affine on [K,3K].
Its energy cannot be made small merely by changing its constant centering.
This is a COMPONENT lower bound, never a lower bound on the full residual.
The exact signed source split below retains the potentially cancelling base.
No Mellin implication, infinite estimate, or new endpoint gain is asserted.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

def nymanBlockEnergy (K : Nat) (f : Nat -> Real) : Real :=
  Finset.sum (Icc K (3 * K)) (fun m => f m ^ 2 / ((m : Real) * (m + 1)))

def nymanCorrectionSignal (N : Nat) (d : Nat -> Real) (z : Real) (m : Nat) : Real :=
  z - Finset.sum (Icc 2 N) (fun k => d k * nymanResidue k m)

private theorem nyman_sum_range_affine_sq (n : Nat) (z lam : Real) :
    Finset.sum (range n) (fun i => (z - lam * (i : Real)) ^ 2) =
      (n : Real) * z ^ 2 - lam * z * n * (n - 1) +
        lam ^ 2 * n * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem nyman_affine_block_variance (K : Nat) (z lam : Real) :
    Finset.sum (Icc K (3 * K)) (fun m => (z - lam * (m : Real)) ^ 2) =
      (2 * (K : Real) + 1) * (z - 2 * K * lam) ^ 2 +
        lam ^ 2 * K * (K + 1) * (2 * K + 1) / 3 := by
  have hset : Icc K (3 * K) = Ico K (3 * K + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range,
    show 3 * K + 1 - K = 2 * K + 1 by omega]
  have hs : Finset.sum (range (2 * K + 1))
      (fun i => (z - lam * ((K + i : Nat) : Real)) ^ 2) =
      Finset.sum (range (2 * K + 1))
        (fun i => ((z - lam * K) - lam * (i : Real)) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  rw [hs, nyman_sum_range_affine_sq]
  push_cast
  ring

theorem nyman_affine_block_energy_lower_bound (K : Nat) (hK : 1 <= K)
    (z lam : Real) :
    lam ^ 2 * (K + 1) * (2 * K + 1) / (9 * (3 * K + 1)) <=
      nymanBlockEnergy K (fun m => z - lam * (m : Real)) := by
  have hk : (0 : Real) < K := by exact_mod_cast (show 0 < K by omega)
  have hd : (0 : Real) < (3 * K) * (3 * K + 1) := by positivity
  have hs :
      Finset.sum (Icc K (3 * K)) (fun m => (z - lam * (m : Real)) ^ 2) /
        ((3 * K) * (3 * K + 1)) <=
      nymanBlockEnergy K (fun m => z - lam * (m : Real)) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro m hm
    have hkm : K <= m := (Finset.mem_Icc.mp hm).1
    have hmK : (m : Real) <= 3 * K := by
      exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hmpos : (0 : Real) < m := by
      exact_mod_cast (show 0 < m by omega)
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact mul_le_mul hmK (by linarith) (by positivity) (by positivity)
  rw [nyman_affine_block_variance] at hs
  calc
    _ = (lam ^ 2 * K * (K + 1) * (2 * K + 1) / 3) /
        ((3 * K) * (3 * K + 1)) := by
      field_simp [ne_of_gt hk, ne_of_gt (show (0 : Real) < 3 * K + 1 by positivity)]
      ring
    _ <= ((2 * (K : Real) + 1) * (z - 2 * K * lam) ^ 2 +
        lam ^ 2 * K * (K + 1) * (2 * K + 1) / 3) /
        ((3 * K) * (3 * K + 1)) := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact le_add_of_nonneg_left (by positivity)
    _ <= _ := hs

theorem nyman_affine_block_energy_one_eighty_one (K : Nat) (hK : 1 <= K)
    (z lam : Real) :
    (6 * (K : Real) / 81) * lam ^ 2 <=
      nymanBlockEnergy K (fun m => z - lam * (m : Real)) := by
  have hc : 6 * (K : Real) / 81 <=
      (K + 1) * (2 * K + 1) / (9 * (3 * K + 1)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [show (0 : Real) <= K by positivity]
  calc
    _ <= ((K + 1) * (2 * K + 1) / (9 * (3 * K + 1))) * lam ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg lam)
    _ = lam ^ 2 * (K + 1) * (2 * K + 1) / (9 * (3 * K + 1)) := by ring
    _ <= _ := nyman_affine_block_energy_lower_bound K hK z lam

theorem nyman_high_correction_eq_affine (N L m : Nat) (d : Nat -> Real)
    (z : Real) (hm : m <= L)
    (hlow : forall k, k ∈ Icc 2 N -> k <= L -> d k = 0) :
    nymanCorrectionSignal N d z m = z - nymanCorrectionMoment N d * m := by
  have hs : Finset.sum (Icc 2 N) (fun k => d k * nymanResidue k m) =
      nymanCorrectionMoment N d * m := by
    unfold nymanCorrectionMoment
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkL : k <= L
    · simp [hlow k hk hkL]
    · have hmk : m < k := by omega
      simp only [nymanResidue, Nat.mod_eq_of_lt hmk]
      ring
  unfold nymanCorrectionSignal
  rw [hs]

theorem nyman_correction_centering_eq (N m : Nat) (d : Nat -> Real) :
    nymanCorrectionSignal N d
        (Finset.sum (Icc 2 N) (fun k => d k * (((k : Real) - 1) / (2 * k)))) m =
      -Finset.sum (Icc 2 N) (fun k =>
        d k * (nymanResidue k m - ((k : Real) - 1) / (2 * k))) := by
  simp only [nymanCorrectionSignal, mul_sub, Finset.sum_sub_distrib]
  ring

theorem nyman_high_correction_energy_lower_bound (N K : Nat) (hK : 1 <= K)
    (d : Nat -> Real) (z : Real)
    (hlow : forall k, k ∈ Icc 2 N -> k <= 3 * K -> d k = 0) :
    (6 * (K : Real) / 81) * nymanCorrectionMoment N d ^ 2 <=
      nymanBlockEnergy K (nymanCorrectionSignal N d z) := by
  have he : nymanBlockEnergy K (nymanCorrectionSignal N d z) =
      nymanBlockEnergy K (fun m => z - nymanCorrectionMoment N d * m) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [nyman_high_correction_eq_affine N (3 * K) m d z
      (Finset.mem_Icc.mp hm).2 hlow]
  rw [he]
  exact nyman_affine_block_energy_one_eighty_one K hK z (nymanCorrectionMoment N d)

theorem nyman_flat_high_correction_energy_lower_bound
    (K H : Nat) (hK : 1 <= K) (h : Nat -> Real) (z : Real)
    (hlow : forall k, k ∈ Icc 2 (3 * K) -> h k = 0)
    (hmoment : nymanCorrectionMoment (6 * K) h = nymanFlatMoment (6 * K) H) :
    (6 * (K : Real) / 81) *
        (nymanFlatMoment (6 * K) H / nymanFlatScale (6 * K) H) ^ 2 <=
      nymanBlockEnergy K (nymanCorrectionSignal (6 * K)
        (fun k => h k / nymanFlatScale (6 * K) H) z) := by
  have hs : nymanCorrectionMoment (6 * K)
        (fun k => h k / nymanFlatScale (6 * K) H) =
      nymanFlatMoment (6 * K) H / nymanFlatScale (6 * K) H := by
    rw [<- hmoment]
    unfold nymanCorrectionMoment
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hb := nyman_high_correction_energy_lower_bound (6 * K) K hK
    (fun k => h k / nymanFlatScale (6 * K) H) z (by
      intro k hk hkK
      rw [hlow k (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, hkK⟩)]
      simp)
  rwa [hs] at hb

theorem nyman_flat_residual_signed_split (N H m : Nat) (h : Nat -> Real)
    (z : Real) :
    nymanResidual N (nymanFlatCoefficient N H h) m =
      (1 - z + Finset.sum (Icc 2 N) (fun k =>
        nymanFlatKernel N H k / nymanFlatScale N H * nymanResidue k m)) +
      nymanCorrectionSignal N (fun k => h k / nymanFlatScale N H) z m := by
  have hs : Finset.sum (Icc 2 N) (fun k =>
        nymanFlatCoefficient N H h k * nymanResidue k m) =
      Finset.sum (Icc 2 N) (fun k =>
        h k / nymanFlatScale N H * nymanResidue k m) -
      Finset.sum (Icc 2 N) (fun k =>
        nymanFlatKernel N H k / nymanFlatScale N H * nymanResidue k m) := by
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    unfold nymanFlatCoefficient
    ring
  unfold nymanResidual nymanCorrectionSignal
  rw [hs]
  ring

#check nyman_affine_block_variance
#check nyman_affine_block_energy_lower_bound
#check nyman_affine_block_energy_one_eighty_one
#check nyman_high_correction_eq_affine
#check nyman_correction_centering_eq
#check nyman_high_correction_energy_lower_bound
#check nyman_flat_high_correction_energy_lower_bound
#check nyman_flat_residual_signed_split
#print axioms nyman_affine_block_variance
#print axioms nyman_affine_block_energy_lower_bound
#print axioms nyman_affine_block_energy_one_eighty_one
#print axioms nyman_high_correction_eq_affine
#print axioms nyman_correction_centering_eq
#print axioms nyman_high_correction_energy_lower_bound
#print axioms nyman_flat_high_correction_energy_lower_bound
#print axioms nyman_flat_residual_signed_split

end RHLean.Analysis
