import «research.CORR4_CUTOFF_COLLISIONS_20261108»

set_option autoImplicit false
open scoped BigOperators
open RHLean.Proof RHLean.Analysis RHLean.Arithmetic

#check (@RHLean.Proof.corr4_cutoff_placement :
  ∀ {R q : ℕ} (_hR : 0 < R) (_hq : 0 < q),
  rawQ2ChildCutoff R q * (q * q) < R ^ 2 ∧
      R ^ 2 ≤ (rawQ2ChildCutoff R q + 1) * (q * q))
#print axioms RHLean.Proof.corr4_cutoff_placement

#check (@RHLean.Proof.corr4_collision_cross_eq :
  ∀ {R S q r : ℕ}
    (_hR : 0 < R) (_hS : 0 < S) (_hq : 0 < q) (_hr : 0 < r)
    (_hc : rawQ2ChildCutoff R q = rawQ2ChildCutoff S r)
    (_hsep : (q * r) ^ 2 ≤ R * r + S * q),
  R * r = S * q)
#print axioms RHLean.Proof.corr4_collision_cross_eq

#check (@RHLean.Proof.corr4_offRay_collision_eq :
  ∀ {H Q R S q r : ℕ}
    (_hH : 0 < H) (_hR : H ≤ R) (_hS : H ≤ S)
    (_hq : Nat.Prime q) (_hr : Nat.Prime r) (_hqQ : q ≤ Q) (_hrQ : r ≤ Q)
    (_hcap : Q ^ 3 ≤ 2 * H) (_hoff : ¬q ∣ R)
    (_hc : rawQ2ChildCutoff R q = rawQ2ChildCutoff S r),
  R = S ∧ q = r)
#print axioms RHLean.Proof.corr4_offRay_collision_eq

#check (@RHLean.Proof.corr4_collision_cross_trichotomy :
  ∀ {H Q R S q r : ℕ}
    (_hH : 0 < H) (_hR : H ≤ R) (_hS : H ≤ S)
    (_hq : 0 < q) (_hr : 0 < r) (_hqQ : q ≤ Q) (_hrQ : r ≤ Q)
    (_hcap : Q ^ 3 ≤ 4 * H)
    (_hc : rawQ2ChildCutoff R q = rawQ2ChildCutoff S r),
  R * r = S * q ∨ R * r + 1 = S * q ∨ S * q + 1 = R * r)
#print axioms RHLean.Proof.corr4_collision_cross_trichotomy

#check (@RHLean.Proof.corr4_offRay_collision_eq_of_parity :
  ∀ {H Q R S q r : ℕ}
    (_hH : 0 < H) (_hR : H ≤ R) (_hS : H ≤ S)
    (_hq : Nat.Prime q) (_hr : Nat.Prime r) (_hq2 : q ≠ 2) (_hr2 : r ≠ 2)
    (_hqQ : q ≤ Q) (_hrQ : r ≤ Q) (_hcap : Q ^ 3 ≤ 4 * H)
    (_hoff : ¬q ∣ R) (_hparity : R % 2 = S % 2)
    (_hc : rawQ2ChildCutoff R q = rawQ2ChildCutoff S r),
  R = S ∧ q = r)
#print axioms RHLean.Proof.corr4_offRay_collision_eq_of_parity

#check (@RHLean.Proof.corr4_offRay_sum_eq_image :
  ∀ {H Q : ℕ} (_hH : 0 < H) (_hcap : Q ^ 3 ≤ 2 * H)
    (E : Finset (ℕ × ℕ))
    (_hE : ∀ e ∈ E, H ≤ e.1 ∧ e.2 ∈ canonicalRoughLowQ2Owners e.1 ∧
      e.2 ≤ Q ∧ ¬e.2 ∣ e.1) (w : ℕ → ℝ),
  (∑ e ∈ E, w (rawQ2ChildCutoff e.1 e.2)) =
      ∑ n ∈ E.image (fun e => rawQ2ChildCutoff e.1 e.2), w n)
#print axioms RHLean.Proof.corr4_offRay_sum_eq_image

#check (@RHLean.Proof.corr4_offRay_sum_le_twice_image :
  ∀ {H Q : ℕ}
    (_hH : 0 < H) (_hcap : Q ^ 3 ≤ 4 * H) (E : Finset (ℕ × ℕ))
    (_hE : ∀ e ∈ E, H ≤ e.1 ∧ e.2 ∈ canonicalRoughLowQ2Owners e.1 ∧
      e.2 ≤ Q ∧ ¬e.2 ∣ e.1) (w : ℕ → ℝ) (_hw : ∀ n, 0 ≤ w n),
  (∑ e ∈ E, w (rawQ2ChildCutoff e.1 e.2)) ≤
      2 * ∑ n ∈ E.image (fun e => rawQ2ChildCutoff e.1 e.2), w n)
#print axioms RHLean.Proof.corr4_offRay_sum_le_twice_image

#check (@RHLean.Proof.corr4_offRay_mertens_energy_le_twice_image :
  ∀ {H Q : ℕ}
    (_hH : 0 < H) (_hcap : Q ^ 3 ≤ 4 * H) (E : Finset (ℕ × ℕ))
    (_hE : ∀ e ∈ E, H ≤ e.1 ∧ e.2 ∈ canonicalRoughLowQ2Owners e.1 ∧
      e.2 ≤ Q ∧ ¬e.2 ∣ e.1),
  (∑ e ∈ E, (mertensSummatoryInt (rawQ2ChildCutoff e.1 e.2) : ℝ) ^ 2) ≤
      2 * ∑ n ∈ E.image (fun e => rawQ2ChildCutoff e.1 e.2),
        (mertensSummatoryInt n : ℝ) ^ 2)
#print axioms RHLean.Proof.corr4_offRay_mertens_energy_le_twice_image

#check (@RHLean.Proof.corr4_doubled_range_collision_witness :
  13 ^ 3 ≤ 4 * (556 : ℕ) ∧
    11 ∈ canonicalRoughLowQ2Owners 556 ∧ 13 ∈ canonicalRoughLowQ2Owners 657 ∧
    ¬11 ∣ (556 : ℕ) ∧ ¬13 ∣ (657 : ℕ) ∧
    rawQ2ChildCutoff 556 11 = 2554 ∧ rawQ2ChildCutoff 657 13 = 2554 ∧
    556 * 13 = 657 * 11 + (1 : ℕ))
#print axioms RHLean.Proof.corr4_doubled_range_collision_witness


