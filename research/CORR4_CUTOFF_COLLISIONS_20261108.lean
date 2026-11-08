import «research.CORR4_SQUARE_CLOCK_SAMPLING_20261106»

/-!
# Literal CORR4 daughter-cutoff collisions

Claims 20261108-wheel-1/SP2 and 20261108-census-1/TC1, accepted at paper
scope by 20261108-referee-1. The sampling map is the original natural
quotient. Divisible-root events are excluded only where explicitly stated.
The doubled-cube range gives a multiplicity-two image-energy transfer,
not cancellation of the sampled Mertens values or a complete mixed-tail bill.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Exact placement needs positive roots and labels, not the active mask. -/
theorem corr4_cutoff_placement {R q : ℕ} (hR : 0 < R) (hq : 0 < q) :
    rawQ2ChildCutoff R q * (q * q) < R ^ 2 ∧
      R ^ 2 ≤ (rawQ2ChildCutoff R q + 1) * (q * q) := by
  have hd : 0 < q * q := Nat.mul_pos hq hq
  have hp := Nat.sub_add_cancel (show 1 ≤ R ^ 2 by nlinarith)
  have hm := Nat.mod_lt (R ^ 2 - 1) hd
  have hv := Nat.div_add_mod (R ^ 2 - 1) (q * q)
  unfold rawQ2ChildCutoff squareRootEndpoint
  constructor <;> nlinarith

private theorem cutoff_collision_square_lt {R S q r : ℕ}
    (hR : 0 < R) (hS : 0 < S) (hq : 0 < q) (hr : 0 < r)
    (hc : rawQ2ChildCutoff R q = rawQ2ChildCutoff S r) :
    (S * q) ^ 2 < (R * r) ^ 2 + (q * r) ^ 2 := by
  obtain ⟨hRl, _hRu⟩ := corr4_cutoff_placement hR hq
  obtain ⟨_hSl, hSu⟩ := corr4_cutoff_placement hS hr
  rw [hc] at hRl
  have hleft := Nat.mul_lt_mul_of_pos_right hRl (Nat.mul_pos hr hr)
  have hright := Nat.mul_le_mul_right (q * q) hSu
  nlinarith only [hleft, hright]

private theorem label_product_bound {q r Q : ℕ} (hq : q ≤ Q) (hr : r ≤ Q) :
    2 * (q * r) ^ 2 ≤ Q ^ 3 * (q + r) := by
  have hqr := Nat.mul_le_mul (Nat.mul_le_mul hq hr) hr
  have hrq := Nat.mul_le_mul (Nat.mul_le_mul hr hq) hq
  have hleft := Nat.mul_le_mul_left q hqr
  have hright := Nat.mul_le_mul_left r hrq
  nlinarith only [hleft, hright]

/-- The source-dependent separation criterion precedes any cube cutoff. -/
theorem corr4_collision_cross_eq {R S q r : ℕ}
    (hR : 0 < R) (hS : 0 < S) (hq : 0 < q) (hr : 0 < r)
    (hc : rawQ2ChildCutoff R q = rawQ2ChildCutoff S r)
    (hsep : (q * r) ^ 2 ≤ R * r + S * q) :
    R * r = S * q := by
  have hforward := cutoff_collision_square_lt hR hS hq hr hc
  have hbackward := cutoff_collision_square_lt hS hR hr hq hc.symm
  rcases lt_trichotomy (R * r) (S * q) with h | h | h
  · have hstep : R * r + 1 ≤ S * q := h
    have hmul := Nat.mul_le_mul_right (R * r + S * q) hstep
    nlinarith only [hforward, hsep, hmul]
  · exact h
  · have hstep : S * q + 1 ≤ R * r := h
    have hmul := Nat.mul_le_mul_right (R * r + S * q) hstep
    nlinarith only [hbackward, hsep, hmul]

private theorem event_eq_of_cross_eq {R S q r : ℕ}
    (hq : Nat.Prime q) (hr : Nat.Prime r) (hoff : ¬q ∣ R)
    (hc : R * r = S * q) : R = S ∧ q = r := by
  have hd : q ∣ R * r := by rw [hc]; exact dvd_mul_left q S
  have hqr : q ∣ r := (hq.dvd_mul.mp hd).resolve_left hoff
  have heq : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp hqr
  subst r
  exact ⟨by nlinarith [hq.pos], rfl⟩

/-- Off-ray injectivity at the closed cube threshold; only one off-ray
hypothesis is needed, and the active square mask is unnecessary here. -/
theorem corr4_offRay_collision_eq {H Q R S q r : ℕ}
    (hH : 0 < H) (hR : H ≤ R) (hS : H ≤ S)
    (hq : Nat.Prime q) (hr : Nat.Prime r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hcap : Q ^ 3 ≤ 2 * H) (hoff : ¬q ∣ R)
    (hc : rawQ2ChildCutoff R q = rawQ2ChildCutoff S r) :
    R = S ∧ q = r := by
  have hlabels := label_product_bound hqQ hrQ
  have hcube := Nat.mul_le_mul_right (q + r) hcap
  have hroot := Nat.mul_le_mul_right r hR
  have hsroot := Nat.mul_le_mul_right q hS
  have hsep : (q * r) ^ 2 ≤ R * r + S * q := by
    nlinarith only [hlabels, hcube, hroot, hsroot]
  exact event_eq_of_cross_eq hq hr hoff
    (corr4_collision_cross_eq (hH.trans_le hR) (hH.trans_le hS) hq.pos hr.pos hc hsep)

/-- At the doubled threshold a nonzero determinant has magnitude one.
This geometric statement does not require prime or odd labels. -/
theorem corr4_collision_cross_trichotomy {H Q R S q r : ℕ}
    (hH : 0 < H) (hR : H ≤ R) (hS : H ≤ S)
    (hq : 0 < q) (hr : 0 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hcap : Q ^ 3 ≤ 4 * H)
    (hc : rawQ2ChildCutoff R q = rawQ2ChildCutoff S r) :
    R * r = S * q ∨ R * r + 1 = S * q ∨ S * q + 1 = R * r := by
  have hlabels := label_product_bound hqQ hrQ
  have hcube := Nat.mul_le_mul_right (q + r) hcap
  have hroot := Nat.mul_le_mul_right r hR
  have hsroot := Nat.mul_le_mul_right q hS
  have hsep : (q * r) ^ 2 ≤ 2 * (R * r + S * q) := by
    nlinarith only [hlabels, hcube, hroot, hsroot]
  have hforward := cutoff_collision_square_lt (hH.trans_le hR) (hH.trans_le hS) hq hr hc
  have hbackward := cutoff_collision_square_lt (hH.trans_le hS) (hH.trans_le hR) hr hq hc.symm
  have hlt : R * r < S * q + 2 := by
    by_contra h
    have hstep : S * q + 2 ≤ R * r := by omega
    have hmul := Nat.mul_le_mul_right (R * r + S * q) hstep
    nlinarith only [hbackward, hsep, hmul]
  have hgt : S * q < R * r + 2 := by
    by_contra h
    have hstep : R * r + 2 ≤ S * q := by omega
    have hmul := Nat.mul_le_mul_right (R * r + S * q) hstep
    nlinarith only [hforward, hsep, hmul]
  omega

/-- Each root-parity class is injective throughout the doubled cube range. -/
theorem corr4_offRay_collision_eq_of_parity {H Q R S q r : ℕ}
    (hH : 0 < H) (hR : H ≤ R) (hS : H ≤ S)
    (hq : Nat.Prime q) (hr : Nat.Prime r) (hq2 : q ≠ 2) (hr2 : r ≠ 2)
    (hqQ : q ≤ Q) (hrQ : r ≤ Q) (hcap : Q ^ 3 ≤ 4 * H)
    (hoff : ¬q ∣ R) (hparity : R % 2 = S % 2)
    (hc : rawQ2ChildCutoff R q = rawQ2ChildCutoff S r) :
    R = S ∧ q = r := by
  have hqodd := hq.eq_two_or_odd.resolve_left hq2
  have hrodd := hr.eq_two_or_odd.resolve_left hr2
  have hmod : (R * r) % 2 = (S * q) % 2 := by
    simpa only [Nat.mul_mod, hqodd, hrodd, mul_one, Nat.mod_mod] using hparity
  rcases corr4_collision_cross_trichotomy hH hR hS hq.pos hr.pos hqQ hrQ hcap hc with h | h | h
  · exact event_eq_of_cross_eq hq hr hoff h
  · omega
  · omega

private theorem admitted_prime {R q : ℕ}
    (h : q ∈ canonicalRoughLowQ2Owners R) : Nat.Prime q ∧ q ≠ 2 := by
  have hb := Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1
  exact ⟨(mem_primesUpTo.mp hb.2).1, hb.1⟩

/-- Original admitted off-ray occurrences have no repeated cutoff in the
smaller range. This is valid on any finite root set, not just intervals. -/
theorem corr4_offRay_sum_eq_image {H Q : ℕ} (hH : 0 < H) (hcap : Q ^ 3 ≤ 2 * H)
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, H ≤ e.1 ∧ e.2 ∈ canonicalRoughLowQ2Owners e.1 ∧
      e.2 ≤ Q ∧ ¬e.2 ∣ e.1) (w : ℕ → ℝ) :
    (∑ e ∈ E, w (rawQ2ChildCutoff e.1 e.2)) =
      ∑ n ∈ E.image (fun e => rawQ2ChildCutoff e.1 e.2), w n := by
  classical
  symm
  apply Finset.sum_image
  intro e he f hf hc
  obtain ⟨hRe, hqe, heQ, heoff⟩ := hE e he
  obtain ⟨hRf, hqf, hfQ, _hfoff⟩ := hE f hf
  have h := corr4_offRay_collision_eq hH hRe hRf
    (admitted_prime hqe).1 (admitted_prime hqf).1 heQ hfQ hcap heoff hc
  exact Prod.ext h.1 h.2

/-- The original occurrence sum costs at most two copies of its image in
the doubled range. No arithmetic signs or input-energy bound are assumed. -/
theorem corr4_offRay_sum_le_twice_image {H Q : ℕ}
    (hH : 0 < H) (hcap : Q ^ 3 ≤ 4 * H) (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, H ≤ e.1 ∧ e.2 ∈ canonicalRoughLowQ2Owners e.1 ∧
      e.2 ≤ Q ∧ ¬e.2 ∣ e.1) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    (∑ e ∈ E, w (rawQ2ChildCutoff e.1 e.2)) ≤
      2 * ∑ n ∈ E.image (fun e => rawQ2ChildCutoff e.1 e.2), w n := by
  classical
  let f : ℕ × ℕ → ℕ := fun e => rawQ2ChildCutoff e.1 e.2
  have hpart (T : Finset (ℕ × ℕ)) (hTE : T ⊆ E)
      (hpar : ∀ e ∈ T, ∀ g ∈ T, e.1 % 2 = g.1 % 2) :
      (∑ e ∈ T, w (f e)) ≤ ∑ n ∈ E.image f, w n := by
    have hinj : Set.InjOn f T := by
      intro e he g hg hc
      obtain ⟨hRe, hqe, heQ, heoff⟩ := hE e (hTE he)
      obtain ⟨hRg, hqg, hgQ, _hgoff⟩ := hE g (hTE hg)
      obtain ⟨hpe, hne⟩ := admitted_prime hqe
      obtain ⟨hpg, hng⟩ := admitted_prime hqg
      have h := corr4_offRay_collision_eq_of_parity hH hRe hRg hpe hpg hne hng
        heQ hgQ hcap heoff (hpar e he g hg) hc
      exact Prod.ext h.1 h.2
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image hTE)
      (fun n _hn _hnot => hw n)
  have hzero := hpart (E.filter (fun e => e.1 % 2 = 0)) (Finset.filter_subset _ _)
    (by intro e he g hg; exact (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hg).2.symm)
  have hone := hpart (E.filter (fun e => ¬e.1 % 2 = 0)) (Finset.filter_subset _ _)
    (by
      intro e he g hg
      have he' := (Finset.mem_filter.mp he).2
      have hg' := (Finset.mem_filter.mp hg).2
      omega)
  have hsplit := Finset.sum_filter_add_sum_filter_not E
    (fun e => e.1 % 2 = 0) (fun e => w (f e))
  change (∑ e ∈ E, w (f e)) ≤ 2 * ∑ n ∈ E.image f, w n
  linarith

/-- Actual signed Mertens prefixes retain every off-ray occurrence, with
the proved factor two and no assumption on the size of the image energy. -/
theorem corr4_offRay_mertens_energy_le_twice_image {H Q : ℕ}
    (hH : 0 < H) (hcap : Q ^ 3 ≤ 4 * H) (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, H ≤ e.1 ∧ e.2 ∈ canonicalRoughLowQ2Owners e.1 ∧
      e.2 ≤ Q ∧ ¬e.2 ∣ e.1) :
    (∑ e ∈ E, (mertensSummatoryInt (rawQ2ChildCutoff e.1 e.2) : ℝ) ^ 2) ≤
      2 * ∑ n ∈ E.image (fun e => rawQ2ChildCutoff e.1 e.2),
        (mertensSummatoryInt n : ℝ) ^ 2 := by
  exact corr4_offRay_sum_le_twice_image hH hcap E hE
    (fun n => (mertensSummatoryInt n : ℝ) ^ 2) (fun n => sq_nonneg _)

/-- A legal doubled-range collision prevents silently replacing two by one. -/
theorem corr4_doubled_range_collision_witness :
    13 ^ 3 ≤ 4 * (556 : ℕ) ∧
    11 ∈ canonicalRoughLowQ2Owners 556 ∧ 13 ∈ canonicalRoughLowQ2Owners 657 ∧
    ¬11 ∣ (556 : ℕ) ∧ ¬13 ∣ (657 : ℕ) ∧
    rawQ2ChildCutoff 556 11 = 2554 ∧ rawQ2ChildCutoff 657 13 = 2554 ∧
    556 * 13 = 657 * 11 + (1 : ℕ) := by
  have hp11 : Nat.Prime 11 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  rw [corr4_mem_lowOwners_iff hp11 (by norm_num), corr4_mem_lowOwners_iff hp13 (by norm_num)]
  norm_num [rawQ2ChildCutoff, squareRootEndpoint]

end RHLean.Proof
