import «research.oai_434.VF919PrincipalSignedRemainder»

/-!
# Complete finite principal response

The first complete-product step of 20261110-coordinator-1513-EST/MD2,
independently accepted by 20261110-referee-3/IRR. The finite geometric
response retains every mixed slot product and the original negative mass
normalizer. This does not assert the weighted-degree cutoff, Mellin return,
response inversion, or a new global Mertens endpoint.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.PrincipalSlotEstimate
open ProbeEuler ProbeLocal

def principalResponseBase (Q : ℝ) (A eta s : ℂ) : ℂ :=
  (Q : ℂ)⁻¹ * coordR Q A s (1 / 6) +
    (1 - (Q : ℂ)⁻¹) * coordD Q eta 1 s

def principalResponseWeight (Q : ℝ) (A eta s : ℂ) : ℂ :=
  (star eta * (Q : ℂ) ^ s) * coordR Q A s (1 / 6)

/-- The geometric truncation is made before multiplying the signed slots. -/
def principalSlotPartial (K : ℕ) (Q : ℝ) (A eta s : ℂ) : ℂ :=
  (Q : ℂ)⁻¹ + (1 - (Q : ℂ)⁻¹) * (1 - principalResponseWeight Q A eta s) *
    ∑ k ∈ Finset.range (K + 1), principalResponseBase Q A eta s ^ k

private theorem principal_response_data {Q : ℝ} {A eta s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1)
    (hs : 7 / 8 ≤ s.re) :
    ‖(Q : ℂ)⁻¹‖ ≤ 1 ∧ ‖1 - (Q : ℂ)⁻¹‖ ≤ 1 ∧
    ‖principalResponseWeight Q A eta s‖ ≤ 1 ∧
    ‖principalResponseBase Q A eta s‖ ≤ 1 / 2 ∧
    ‖principalResponseBase Q A eta s‖ ≤ 2 * Q ^ (-(7 / 8 : ℝ)) ∧
    -principalSlot Q A eta s = (Q : ℂ)⁻¹ +
      (1 - (Q : ℂ)⁻¹) * (1 - principalResponseWeight Q A eta s) /
        (1 - principalResponseBase Q A eta s) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let q : ℂ := (Q : ℂ)⁻¹
  let R := coordR Q A s (1 / 6)
  let D := coordD Q eta 1 s
  let B := star eta * (Q : ℂ) ^ s
  let U := 1 - (q * R + (1 - q) * D)
  have hpow (a b : ℝ) (h : a ≤ b) : Q ^ a ≤ Q ^ b :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hqi : Q⁻¹ ≤ (1 / 4 : ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hQ0).mpr (by linarith)
  have hq : ‖q‖ = Q ^ (-1 : ℝ) := by
    simp [q, Complex.norm_real, abs_of_pos hQ0, Real.rpow_neg_one]
  have hqquarter : ‖q‖ ≤ 1 / 4 := by
    simpa only [hq, Real.rpow_neg_one] using hqi
  have h1q : ‖1 - q‖ ≤ 1 := by
    change ‖(1 : ℂ) - (Q : ℂ)⁻¹‖ ≤ 1
    rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1 - Q⁻¹)]
    exact sub_le_self _ (inv_nonneg.mpr hQ0.le)
  have hR : ‖R‖ ≤ Q ^ (3 - 6 * s.re) := by
    convert coordR_norm_le Q hQ0 A s (1 / 6) hA using 1
    norm_num
    congr 1
    ring
  have hD : ‖D‖ ≤ Q ^ (-s.re) :=
    coordD_norm_le Q hQ0 eta 1 s heta.le (by simp)
  have hB : ‖B‖ = Q ^ s.re := principal_B_norm hQ0 eta s heta
  have hRquarter : ‖R‖ ≤ 1 / 4 := by
    apply (hR.trans (hpow _ (-1) (by linarith))).trans
    simpa only [Real.rpow_neg_one] using hqi
  have hDquarter : ‖D‖ ≤ 1 / 4 := by
    apply (hD.trans (hpow _ (-(1 / 2)) (by linarith))).trans
    rw [Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow, inv_eq_one_div]
    have hroot : (4 : ℝ) ≤ Real.sqrt Q :=
      (Real.le_sqrt (by norm_num) hQ0.le).mpr (by linarith)
    exact (div_le_iff₀ (Real.sqrt_pos.mpr hQ0)).mpr (by linarith)
  have hsmall : ‖q * R + (1 - q) * D‖ ≤ 1 / 2 := by
    calc
      _ ≤ ‖q‖ * ‖R‖ + ‖1 - q‖ * ‖D‖ := by
        simpa only [norm_mul] using norm_add_le (q * R) ((1 - q) * D)
      _ ≤ (1 / 4 : ℝ) * (1 / 4) + 1 * (1 / 4) := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hdecay : ‖q * R + (1 - q) * D‖ ≤ 2 * Q ^ (-(7 / 8 : ℝ)) := by
    have hqR : ‖q‖ * ‖R‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
      rw [hq]
      calc
        _ ≤ Q ^ (-1 : ℝ) * Q ^ (3 - 6 * s.re) := by gcongr
        _ = Q ^ ((-1 : ℝ) + (3 - 6 * s.re)) := (Real.rpow_add hQ0 _ _).symm
        _ ≤ _ := hpow _ _ (by linarith)
    have hDt := hD.trans (hpow _ (-(7 / 8)) (by linarith))
    calc
      _ ≤ ‖q‖ * ‖R‖ + ‖1 - q‖ * ‖D‖ := by
        simpa only [norm_mul] using norm_add_le (q * R) ((1 - q) * D)
      _ ≤ Q ^ (-(7 / 8 : ℝ)) + 1 * Q ^ (-(7 / 8 : ℝ)) := by gcongr
      _ = _ := by ring
  have hBR : ‖B * R‖ ≤ 1 := by
    rw [norm_mul, hB]
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by gcongr
      _ = Q ^ (s.re + (3 - 6 * s.re)) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ Q ^ (0 : ℝ) := hpow _ _ (by linarith)
      _ = 1 := Real.rpow_zero Q
  have hU : U ≠ 0 := one_sub_ne_zero_of_norm_le_half _ hsmall
  have h1R : 1 - R ≠ 0 := one_sub_ne_zero_of_norm_le_half R (by linarith)
  have h1qn : 1 - q ≠ 0 := one_sub_ne_zero_of_norm_le_half q (by linarith)
  have hpqn : 1 + q ≠ 0 := by
    have h := one_sub_ne_zero_of_norm_le_half (-q)
      (by simpa using hqquarter.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2))
    simpa using h
  have hmarked : principalMarked Q A eta s = (1 + q) * (R - D) / (1 - R) := by
    unfold principalMarked
    rw [principal_V, principal_W, principal_K_signed hQ0]
    change markedFactor R q q ((1 - q) * D) (-D + q * R) 1 = _
    unfold markedFactor
    simp only [pow_one]
    field_simp
    ring
  have hratio : principalSlot Q A eta s = (1 - q) * (B * R - 1) / U - q := by
    rw [principal_slot_eq_raw hQ hA heta.le hs, principalRawFactor,
      principal_V, principal_W, hmarked, Complex.cpow_neg_one]
    change B * ((1 + q) * (R - D) / (1 - R)) /
      localFactor q q ((1 + q) * (R - D) / (1 - R)) - q = _
    have hraw : localFactor q q ((1 + q) * (R - D) / (1 - R)) =
        (1 + q) * U / ((1 - q) * (1 - R)) := by
      unfold localFactor U
      field_simp
      ring
    rw [hraw]
    calc
      _ = (1 - q) * (B * R - B * D) / U - q := by field_simp
      _ = _ := by rw [show B * D = 1 from principal_coord_cancellation hQ0 eta s heta]
  refine ⟨hqquarter.trans (by norm_num), h1q, hBR, hsmall, hdecay, ?_⟩
  change -principalSlot Q A eta s = q + (1 - q) * (1 - B * R) / U
  rw [hratio]
  ring

private theorem finite_geometric_identity {R : Type*} [CommRing R] (z : R) (K : ℕ) :
    (1 - z) * (∑ k ∈ Finset.range (K + 1), z ^ k) = 1 - z ^ (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

private theorem finite_geometric_norm_le_two (z : ℂ) (K : ℕ)
    (hz : ‖z‖ ≤ 1 / 2) : ‖∑ k ∈ Finset.range (K + 1), z ^ k‖ ≤ 2 := by
  have hid := finite_geometric_identity ‖z‖ K
  have hsum : 0 ≤ ∑ k ∈ Finset.range (K + 1), ‖z‖ ^ k :=
    Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)
  have hp : 0 ≤ ‖z‖ ^ (K + 1) := pow_nonneg (norm_nonneg _) _
  calc
    _ ≤ ∑ k ∈ Finset.range (K + 1), ‖z ^ k‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (K + 1), ‖z‖ ^ k := by simp only [norm_pow]
    _ ≤ 2 := by nlinarith

/-- Exact original symbol, not an independently chosen response model. -/
theorem principal_slot_response_exact {Q : ℝ} {A eta s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1)
    (hs : 7 / 8 ≤ s.re) :
    -principalSlot Q A eta s = (Q : ℂ)⁻¹ +
      (1 - (Q : ℂ)⁻¹) * (1 - principalResponseWeight Q A eta s) /
        (1 - principalResponseBase Q A eta s) :=
  (principal_response_data hQ hA heta hs).2.2.2.2.2

/-- Every discarded geometric power is present in this exact tail. -/
theorem principal_slot_partial_tail (K : ℕ) {Q : ℝ} {A eta s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1)
    (hs : 7 / 8 ≤ s.re) :
    -principalSlot Q A eta s - principalSlotPartial K Q A eta s =
      (1 - (Q : ℂ)⁻¹) * (1 - principalResponseWeight Q A eta s) *
        principalResponseBase Q A eta s ^ (K + 1) /
          (1 - principalResponseBase Q A eta s) := by
  obtain ⟨_, _, _, hsmall, _, heq⟩ := principal_response_data hQ hA heta hs
  have hne := one_sub_ne_zero_of_norm_le_half _ hsmall
  have hg := finite_geometric_identity (principalResponseBase Q A eta s) K
  rw [heq, principalSlotPartial]
  apply (eq_div_iff hne).mpr
  field_simp
  linear_combination -(1 - (Q : ℂ)⁻¹) *
    (1 - principalResponseWeight Q A eta s) * hg

/-- Arbitrary-order height-uniform approximation of the original signed slot. -/
theorem principal_slot_partial_error (K : ℕ) {Q : ℝ} {A eta s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1)
    (hs : 7 / 8 ≤ s.re) :
    ‖-principalSlot Q A eta s - principalSlotPartial K Q A eta s‖ ≤
      4 * (2 * Q ^ (-(7 / 8 : ℝ))) ^ (K + 1) := by
  obtain ⟨_, hq, hW, hsmall, hdecay, _⟩ := principal_response_data hQ hA heta hs
  have hW' : ‖1 - principalResponseWeight Q A eta s‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (principalResponseWeight Q A eta s)
    simp only [norm_one] at h
    linarith
  have hi := inv_one_sub_norm_le_two _ hsmall
  rw [principal_slot_partial_tail K hQ hA heta hs, div_eq_mul_inv,
    norm_mul, norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ 1 * 2 * (2 * Q ^ (-(7 / 8 : ℝ))) ^ (K + 1) * 2 := by gcongr
    _ = _ := by ring

/-- The exact and truncated factors have one common bound independent of K. -/
theorem principal_slot_partial_norms (K : ℕ) {Q : ℝ} {A eta s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1)
    (hs : 7 / 8 ≤ s.re) :
    ‖-principalSlot Q A eta s‖ ≤ 5 ∧ ‖principalSlotPartial K Q A eta s‖ ≤ 5 := by
  obtain ⟨hq, h1q, hW, hsmall, _, heq⟩ := principal_response_data hQ hA heta hs
  have hW' : ‖1 - principalResponseWeight Q A eta s‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (principalResponseWeight Q A eta s)
    simp only [norm_one] at h
    linarith
  have hi := inv_one_sub_norm_le_two _ hsmall
  have hg := finite_geometric_norm_le_two (principalResponseBase Q A eta s) K hsmall
  constructor
  · rw [heq, div_eq_mul_inv]
    calc
      _ ≤ ‖(Q : ℂ)⁻¹‖ + ‖(1 - (Q : ℂ)⁻¹) *
          (1 - principalResponseWeight Q A eta s) *
          (1 - principalResponseBase Q A eta s)⁻¹‖ := norm_add_le _ _
      _ = ‖(Q : ℂ)⁻¹‖ + ‖1 - (Q : ℂ)⁻¹‖ *
          ‖1 - principalResponseWeight Q A eta s‖ *
          ‖(1 - principalResponseBase Q A eta s)⁻¹‖ := by simp only [norm_mul]
      _ ≤ 1 + 1 * 2 * 2 := by gcongr
      _ = 5 := by norm_num
  · unfold principalSlotPartial
    calc
      _ ≤ ‖(Q : ℂ)⁻¹‖ + ‖(1 - (Q : ℂ)⁻¹) *
          (1 - principalResponseWeight Q A eta s) *
          ∑ k ∈ Finset.range (K + 1), principalResponseBase Q A eta s ^ k‖ := norm_add_le _ _
      _ = ‖(Q : ℂ)⁻¹‖ + ‖1 - (Q : ℂ)⁻¹‖ *
          ‖1 - principalResponseWeight Q A eta s‖ *
          ‖∑ k ∈ Finset.range (K + 1), principalResponseBase Q A eta s ^ k‖ := by
        simp only [norm_mul]
      _ ≤ 1 + 1 * 2 * 2 := by gcongr
      _ = 5 := by norm_num

private theorem normalized_weighted_norm {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (f : ι → ℂ) (C : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hM : 0 < ∑ i ∈ S, w i)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ C) :
    ‖(∑ i ∈ S, (w i : ℂ) * f i) / (∑ i ∈ S, w i : ℝ)‖ ≤ C := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ ∑ i ∈ S, ‖(w i : ℂ) * f i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, C * w i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hf i hi) (hw i hi)
    _ = _ := by rw [Finset.mul_sum]

private theorem norm_product_le_five {ι : Type*} (S : Finset ι)
    (f : ι → ℂ) (hf : ∀ i ∈ S, ‖f i‖ ≤ 5) :
    ‖∏ i ∈ S, f i‖ ≤ (5 : ℝ) ^ S.card := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _i ∈ S, (5 : ℝ) := by
      gcongr with i hi
      exact hf i hi
    _ = _ := by simp

private theorem product_difference_bound {ι : Type*} (S : Finset ι)
    (f g : ι → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 5) (hg : ∀ i ∈ S, ‖g i‖ ≤ 5)
    (hd : ∀ i ∈ S, ‖f i - g i‖ ≤ E) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ S.card * (5 : ℝ) ^ S.card * E := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfS := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgS := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hdS := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hind := ih hfS hgS hdS
    have hp := norm_product_le_five S g hgS
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hid : f a * (∏ i ∈ S, f i) - g a * (∏ i ∈ S, g i) =
        f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) +
        (f a - g a) * (∏ i ∈ S, g i) := by ring
    rw [hid]
    calc
      _ ≤ ‖f a‖ * ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ +
          ‖f a - g a‖ * ‖∏ i ∈ S, g i‖ := by
        simpa only [norm_mul] using norm_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i))
          ((f a - g a) * (∏ i ∈ S, g i))
      _ ≤ 5 * (S.card * (5 : ℝ) ^ S.card * E) + E * (5 : ℝ) ^ S.card := by
        gcongr
        · exact hf a (Finset.mem_insert_self _ _)
        · exact hd a (Finset.mem_insert_self _ _)
      _ ≤ (S.card + 1 : ℕ) * (5 : ℝ) ^ (S.card + 1) * E := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5) S.card) hE]

/-- Complete normalized original product. No tuple, diagonal, or mixed slot
interaction is discarded from the approximating product. -/
theorem weighted_principal_product_partial_error {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (K : ℕ) (hP : 480 ≤ P) (hs : 7 / 8 ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (heta : ∀ j ∈ S, ∀ i ∈ T j, ‖eta j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (eta j i) s) /
          principalScalar S (fun j => ∑ i ∈ T j, w j i) -
        ∏ j ∈ S, (∑ i ∈ T j, (w j i : ℂ) *
          principalSlotPartial K (Q j i) (A j i) (eta j i) s) /
            (∑ i ∈ T j, w j i : ℝ)‖ ≤
      S.card * (5 : ℝ) ^ S.card * (4 * (2 * P ^ (-(7 / 8 : ℝ))) ^ (K + 1)) := by
  let f := fun j => (∑ i ∈ T j, (w j i : ℂ) * (-principalSlot (Q j i) (A j i) (eta j i) s)) /
    (∑ i ∈ T j, w j i : ℝ)
  let g := fun j => (∑ i ∈ T j, (w j i : ℂ) * principalSlotPartial K (Q j i) (A j i) (eta j i) s) /
    (∑ i ∈ T j, w j i : ℝ)
  have hid :
      (∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (eta j i) s) /
          principalScalar S (fun j => ∑ i ∈ T j, w j i) = ∏ j ∈ S, f j := by
    rw [principalScalar_eq, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j _
    simp [f, Finset.sum_neg_distrib, div_neg, neg_div]
  rw [hid]
  change ‖(∏ j ∈ S, f j) - ∏ j ∈ S, g j‖ ≤ _
  apply product_difference_bound S f g _ (by positivity)
  · intro j hj
    apply normalized_weighted_norm (T j) (w j) _ 5 (hw j hj) (hM j hj)
    intro i hi
    exact (principal_slot_partial_norms K (hP.trans (hQ j hj i hi))
      (hA j hj i hi) (heta j hj i hi) hs).1
  · intro j hj
    apply normalized_weighted_norm (T j) (w j) _ 5 (hw j hj) (hM j hj)
    intro i hi
    exact (principal_slot_partial_norms K (hP.trans (hQ j hj i hi))
      (hA j hj i hi) (heta j hj i hi) hs).2
  · intro j hj
    have hd : f j - g j = (∑ i ∈ T j, (w j i : ℂ) *
        (-principalSlot (Q j i) (A j i) (eta j i) s -
          principalSlotPartial K (Q j i) (A j i) (eta j i) s)) /
            (∑ i ∈ T j, w j i : ℝ) := by
      simp only [f, g, mul_sub, Finset.sum_sub_distrib, sub_div]
    rw [hd]
    apply normalized_weighted_norm (T j) (w j) _ _ (hw j hj) (hM j hj)
    intro i hi
    apply (principal_slot_partial_error K (hP.trans (hQ j hj i hi))
      (hA j hj i hi) (heta j hj i hi) hs).trans
    have hmono : (Q j i) ^ (-(7 / 8 : ℝ)) ≤ P ^ (-(7 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (hQ j hj i hi) (by norm_num)
    gcongr

/-- Fix the truncation order before the source scale. No lower bound on a
positive minimum slot length is needed to attain a fixed accuracy power. -/
theorem exists_principal_truncation_order {m : ℝ} (hm : 0 < m) (rho : ℝ) :
    ∃ K : ℕ, rho ≤ (7 / 8 : ℝ) * m * (K + 1) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (rho / ((7 / 8 : ℝ) * m))
  have hc : 0 < (7 / 8 : ℝ) * m := by positivity
  have h := (div_lt_iff₀ hc).mp hK
  refine ⟨K, ?_⟩
  push_cast
  nlinarith

/-- Uniform source-scale accuracy for the complete product. The order K,
source minimum m, and requested rho are chosen before Z or any moving pool.
The finite response itself, rather than 1, is retained on the left. -/
theorem weighted_principal_product_partial_power {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ)
    (s : ℂ) (Z m rho : ℝ) (K : ℕ) (hZ : 1 ≤ Z) (hP : 480 ≤ Z ^ m)
    (horder : rho ≤ (7 / 8 : ℝ) * m * (K + 1)) (hs : 7 / 8 ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, Z ^ m ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (heta : ∀ j ∈ S, ∀ i ∈ T j, ‖eta j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (eta j i) s) /
          principalScalar S (fun j => ∑ i ∈ T j, w j i) -
        ∏ j ∈ S, (∑ i ∈ T j, (w j i : ℂ) *
          principalSlotPartial K (Q j i) (A j i) (eta j i) s) /
            (∑ i ∈ T j, w j i : ℝ)‖ ≤
      (S.card * (5 : ℝ) ^ S.card * 4 * 2 ^ (K + 1)) * Z ^ (-rho) := by
  have hZ0 : 0 ≤ Z := by linarith
  have hpower : ((Z ^ m) ^ (-(7 / 8 : ℝ))) ^ (K + 1) ≤ Z ^ (-rho) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.rpow_nonneg hZ0 m),
      ← Real.rpow_mul hZ0]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    push_cast at horder ⊢
    nlinarith
  apply (weighted_principal_product_partial_error S T w Q A eta s (Z ^ m) K
    hP hs hw hQ hA heta hM).trans
  rw [mul_pow]
  calc
    _ = (S.card * (5 : ℝ) ^ S.card * 4 * 2 ^ (K + 1)) *
        ((Z ^ m) ^ (-(7 / 8 : ℝ))) ^ (K + 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)

end SevenEighths.PrincipalSlotEstimate
end
end OAI
