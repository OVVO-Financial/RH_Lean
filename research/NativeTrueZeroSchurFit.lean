import «research.NativeWheelNNSComparison»
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! True-zero NNS reconciliation on the actual wheel stars. The anchor
column is retained, and its normal reading is not replaced by an
assigned determinant. See NATIVE_TRUE_ZERO_SCHUR_FIT_20261128.md. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector.TrueZeroSchur

/-- The amplitude table before row repetition. The first column is
the actual layer-constant anchor, and the others are the wheel stars. -/
def amplitude {r : ℕ} (D a : Fin (r+1) → ℝ) :
    Matrix (Fin (r+1)) (Fin (r+1)) ℝ :=
  fun i => Fin.cases (a i) (fun j =>
    D i*((if i=j.succ then 1 else 0)-(if i=0 then 1 else 0)))

private theorem unitAmplitude_det {r : ℕ} (a : Fin (r+1) → ℝ) :
    (amplitude (fun _ => 1) a).det = ∑ i, a i := by
  classical
  let B := amplitude (fun _ => 1) a
  let C := B.updateRow 0 (∑ i, B i)
  have hc : C.det = B.det := by
    simpa only [C, one_smul] using
      Matrix.det_updateRow_sum B 0 (fun _ => (1:ℝ))
  have h0 : C 0 0 = ∑ i, a i := by
    rw [show C 0 = ∑ i, B i from Matrix.updateRow_self]
    change (∑ i : Fin (r+1), (fun k : Fin (r+1) => B i k)) 0 = _
    simp [Finset.sum_apply, B, amplitude]
  have h1 (j : Fin r) : C 0 j.succ = 0 := by
    rw [show C 0 = ∑ i, B i from Matrix.updateRow_self]
    change (∑ i : Fin (r+1), (fun k : Fin (r+1) => B i k)) j.succ = _
    simp [Finset.sum_apply, B, amplitude, Finset.sum_sub_distrib]
  have hminor : C.submatrix Fin.succ Fin.succ = (1 : Matrix (Fin r) (Fin r) ℝ) := by
    ext i j
    simp [C, B, amplitude, Matrix.one_apply]
  change B.det = _
  rw [← hc, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [h0, h1, hminor]

theorem normal_div {r : ℕ} (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i)
    (i : Fin (r+1)) :
    (wheelNormal D i:ℝ) = (∏ j, (D j:ℝ))/(D i:ℝ) := by
  apply (eq_div_iff (show (D i:ℝ) ≠ 0 by exact_mod_cast (hD i).ne')).2
  simpa only [wheelNormal, Nat.cast_prod] using
    (Finset.prod_erase_mul Finset.univ (fun j => (D j:ℝ)) (Finset.mem_univ i))

/-- Exact oriented determinant on the genuine star amplitude matrix. -/
theorem amplitude_det {r : ℕ} (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i)
    (a : Fin (r+1) → ℝ) :
    (amplitude (fun i => (D i:ℝ)) a).det = ∑ i, (wheelNormal D i:ℝ)*a i := by
  classical
  have hA : amplitude (fun i => (D i:ℝ)) a =
      Matrix.diagonal (fun i => (D i:ℝ)) *
        amplitude (fun _ => 1) (fun i => a i/(D i:ℝ)) := by
    ext i j
    rw [Matrix.diagonal_mul]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [amplitude, Fin.cases_zero]
      field_simp [show (D i:ℝ) ≠ 0 by exact_mod_cast (hD i).ne']
    · simp [amplitude]
  rw [hA, Matrix.det_mul, Matrix.det_diagonal, unitAmplitude_det, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [normal_div D hD i]
  ring

/-- Insert all anchor/star readings at the original physical addresses. -/
def anchoredColumns {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (a : Fin (r+1) → ℝ) :
    Matrix (Address S) (Fin (r+1)) ℝ :=
  fun z j => amplitude (fun i => (D i:ℝ)) a z.1 j

@[simp] theorem anchoredColumns_zero {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (a : Fin (r+1) → ℝ) (z : Address S) :
    anchoredColumns S D a z 0 = a z.1 := rfl

/-- The nonanchor columns are exactly the previous physical stars. -/
theorem anchoredColumns_star {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (a : Fin (r+1) → ℝ) (z : Address S) (j : Fin r) :
    anchoredColumns S D a z j.succ = (columns S D z j:ℝ) := by
  by_cases h0 : z.1=0
  · have hne : z.1 ≠ j.succ := by rw [h0]; exact (Fin.succ_ne_zero j).symm
    simp [anchoredColumns, amplitude, columns, starColumn, h0,
      (Fin.succ_ne_zero j).symm]
  · by_cases h1 : z.1=j.succ
    · simp [anchoredColumns, amplitude, columns, starColumn, h1]
    · simp [anchoredColumns, amplitude, columns, starColumn, h0, h1]

/-- The actual four-sector NNS reassembly is the layer-weighted
augmented Gram. No normalization by a fabricated row count. -/
theorem augmented_gram {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (a : Fin (r+1) → ℝ) :
    let A := amplitude (fun i => (D i:ℝ)) a
    WheelNNS.coDiv (anchoredColumns S D a) =
      A.transpose * Matrix.diagonal (fun i => ((S i).card:ℝ)) * A := by
  intro A
  rw [WheelNNS.coDiv_eq, Matrix.mul_assoc]
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  change (∑ z : Address S, A z.1 i*A z.1 j) =
    ∑ k, A k i * (Matrix.diagonal (fun l => ((S l).card:ℝ)) * A) k j
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.diagonal_mul]
  simp [nsmul_eq_mul, mul_left_comm]

theorem augmented_det {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i) (a : Fin (r+1) → ℝ) :
    (WheelNNS.coDiv (anchoredColumns S D a)).det =
      (∏ i, ((S i).card:ℝ))*(∑ i, (wheelNormal D i:ℝ)*a i)^2 := by
  rw [augmented_gram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, amplitude_det D hD]
  ring

/-- The actual Schur correction, including the signed first moments. -/
def schur {r : ℕ} (H : Matrix (Fin (r+1)) (Fin (r+1)) ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => H i.succ j.succ-H i.succ 0*H 0 j.succ/H 0 0

private def eliminate {r : ℕ} (v : Fin r → ℝ) :
    Matrix (Fin (r+1)) (Fin (r+1)) ℝ :=
  Fin.cases (Fin.cases 1 (fun _ => 0))
    (fun i => Fin.cases (-v i) (fun j => if i=j then 1 else 0))

private theorem eliminate_det {r : ℕ} (v : Fin r → ℝ) :
    (eliminate v).det = 1 := by
  have h : (eliminate v).submatrix Fin.succ Fin.succ =
      (1 : Matrix (Fin r) (Fin r) ℝ) := by
    ext i j
    simp [eliminate, Matrix.one_apply]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [eliminate, h]

/-- Determinant reconciliation is exact and does not need the
Gram itself to be nonsingular. -/
theorem schur_det {r : ℕ} (H : Matrix (Fin (r+1)) (Fin (r+1)) ℝ)
    (hW : H 0 0 ≠ 0) : H.det = H 0 0 * (schur H).det := by
  classical
  let T := eliminate (fun i => H i.succ 0/H 0 0)
  have detT : T.det = 1 := eliminate_det _
  let J := T*H
  have dJ : J.det = H.det := by rw [show J=T*H from rfl, Matrix.det_mul, detT, one_mul]
  have h0 : J 0 0 = H 0 0 := by
    simp [J, T, eliminate, Matrix.mul_apply, Fin.sum_univ_succ]
  have h1 (i : Fin r) : J i.succ 0 = 0 := by
    simp only [J, T, eliminate, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.cases_succ, Fin.cases_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    field_simp [hW]
    ring
  have hminor : J.submatrix Fin.succ Fin.succ = schur H := by
    ext i j
    simp only [J, T, eliminate, Matrix.submatrix_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.cases_succ, Fin.cases_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, schur]
    ring
  rw [← dJ, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h0, h1, hminor]

theorem native_schur_det {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i) (a : Fin (r+1) → ℝ)
    (hW : WheelNNS.coDiv (anchoredColumns S D a) 0 0 ≠ 0) :
    let H := WheelNNS.coDiv (anchoredColumns S D a)
    (schur H).det =
      (∏ i, ((S i).card:ℝ))*(∑ i, (wheelNormal D i:ℝ)*a i)^2/H 0 0 := by
  intro H
  apply (eq_div_iff hW).2
  rw [mul_comm, ← schur_det H hW]
  exact augmented_det S D hD a

/-- The normal loss of many disjoint admissions is one joint charge:
the product of complements dominates the complement of their sum. -/
theorem prod_one_sub_ge {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i ∧ z i ≤ 1) :
    1-∑ i ∈ s, z i ≤ ∏ i ∈ s, (1-z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hzi := hz i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, 0 ≤ z j ∧ z j ≤ 1 := fun j hj =>
      hz j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    calc
      _ ≤ (1-z i)*(1-∑ j ∈ s, z j) := by
        nlinarith only [mul_nonneg hzi.1 (Finset.sum_nonneg fun j hj => (hs j hj).1)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr hzi.2)

/-- Exact joint logarithmic price, valid even before choosing a cell
weight or a prime cut. Each z is the lost probability mass. -/
theorem joint_log_loss {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) (h : (∑ i ∈ s, z i) < 1) :
    -(∑ i ∈ s, Real.log (1-z i)) ≤ -Real.log (1-∑ i ∈ s, z i) := by
  have hi (i : ι) (hm : i ∈ s) : z i < 1 :=
    (Finset.single_le_sum (fun j hj => hz j hj) hm).trans_lt h
  have hle := prod_one_sub_ge s z (fun i hm => ⟨hz i hm,(hi i hm).le⟩)
  have hlog := Real.log_le_log (sub_pos.mpr h) hle
  rw [Real.log_prod (fun i hm => (sub_pos.mpr (hi i hm)).ne')] at hlog
  linarith only [hlog]

/-- The actual partition of the native layers into disjoint admission
cells. No independent random prime hypothesis is needed. -/
theorem partition_log_loss {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K]
    (g : I → K) (z : I → ℝ) (hz : ∀ i, 0 ≤ z i) (h : (∑ i, z i) < 1) :
    let b : K → ℝ := fun k => ∑ i, if g i=k then z i else 0
    ; -(∑ k, Real.log (1-b k)) ≤ -Real.log (1-∑ i, z i) := by
  classical
  intro b
  have hb (k : K) : 0 ≤ b k := Finset.sum_nonneg fun i _ => by
    by_cases hi : g i=k <;> simp [hi,hz i]
  have hsum : (∑ k, b k) = ∑ i, z i := by
    dsimp only [b]
    rw [Finset.sum_comm]
    simp
  have h' : (∑ k, b k) < 1 := by rw [hsum]; exact h
  simpa only [hsum] using (joint_log_loss Finset.univ b (fun k _ => hb k) h')

/-- The same joint charge works for signed cell weights. -/
theorem signed_joint_log_loss {ι : Type*} (s : Finset ι) (z w : ι → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hz : ∀ i ∈ s, 0 ≤ z i)
    (hw : ∀ i ∈ s, |w i| ≤ C) (h : (∑ i ∈ s, z i) < 1) :
    |∑ i ∈ s, w i*(-Real.log (1-z i))| ≤
      C*(-Real.log (1-∑ i ∈ s, z i)) := by
  have hpos (i : ι) (hi : i ∈ s) : 0 < 1-z i :=
    sub_pos.mpr ((Finset.single_le_sum (fun j hj => hz j hj) hi).trans_lt h)
  have hn (i : ι) (hi : i ∈ s) : 0 ≤ -Real.log (1-z i) :=
    neg_nonneg.mpr (Real.log_nonpos (hpos i hi).le (sub_le_self _ (hz i hi)))
  calc
    _ ≤ ∑ i ∈ s, |w i*(-Real.log (1-z i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, C*(-Real.log (1-z i)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hn i hi)]
      exact mul_le_mul_of_nonneg_right (hw i hi) (hn i hi)
    _ = C*(-∑ i ∈ s, Real.log (1-z i)) := by
      rw [← Finset.mul_sum, Finset.sum_neg_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (joint_log_loss s z hz h) hC

end RHLean.Analysis.AlpogeThin.SlotProjector.TrueZeroSchur
