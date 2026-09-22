import Mathlib
import «research.GLOBAL_RETURNED_CORE_GLOBAL_FIRST_OWNER_SITE_FUBINI»
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_CELL_SUM»

/-!
# Arbitrary-site first-owner cell Fubini

The global least-owner fibre is ordered in both coordinate orientations.  The
raw-parent cell coordinate instead orients every first-owner pair with the
p-free endpoint first and the p-divisible endpoint second.

For an arbitrary signed site v, this file proves:

  ordered first-owner mass = 2 * oriented first-owner mass,

and the oriented mass is exactly the sum over the existing lower-signature
base×child cell products.  Thus any global first-owner energy budget can be
inserted into the raw-parent cell DAG with no multiplicity ambiguity.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Arbitrary-site mass on the existing arithmetically oriented p-free ×
p-divisible first-owner carrier. -/
def lowOwnerFirstOwnerOrientedCrossPairMassWith
    (R p : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ mn ∈ lowOwnerFirstOwnerOrientedCrossPairCarrier R p,
    v mn.1 * v mn.2

/-- First-owner fibre with a p-free first endpoint. -/
def lowOwnerGlobalFirstOwnerPFreeFirstFiber
    (R p : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerGlobalFirstOwnerPairFiber R p).filter fun mn =>
    ¬ p ∣ mn.1

/-- First-owner fibre with a p-divisible first endpoint. -/
def lowOwnerGlobalFirstOwnerPDivFirstFiber
    (R p : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerGlobalFirstOwnerPairFiber R p).filter fun mn =>
    p ∣ mn.1

/-- The p-free-first half of the global ordered first-owner fibre is literally
the existing oriented cell carrier. -/
theorem lowOwnerGlobalFirstOwnerPFreeFirstFiber_eq_oriented
    {R p : ℕ} (hp : p.Prime) :
    lowOwnerGlobalFirstOwnerPFreeFirstFiber R p =
      lowOwnerFirstOwnerOrientedCrossPairCarrier R p := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hfirst, hfree⟩
    rcases Finset.mem_filter.mp hfirst with ⟨hoff, howner⟩
    rcases Finset.mem_filter.mp hoff with ⟨hprod, hne⟩
    rcases Finset.mem_product.mp hprod with ⟨hm, hn⟩
    have hdata :=
      (isSquarefreePairFreshPrimeOwner_iff_sameLowerSignature_dvdXor
        hp hm hn hne).1 howner
    rcases hdata.2 with hleft | hright
    · exact False.elim (hfree hleft.1)
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hm, hn⟩,
          ⟨hdata.1, hright.2, hright.1⟩⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hprod, hdata⟩
    rcases Finset.mem_product.mp hprod with ⟨hm, hn⟩
    have hne : m ≠ n := by
      intro hmn
      subst n
      exact hdata.2.1 hdata.2.2
    have howner :=
      (isSquarefreePairFreshPrimeOwner_iff_sameLowerSignature_dvdXor
        hp hm hn hne).2
        ⟨hdata.1, Or.inr ⟨hdata.2.2, hdata.2.1⟩⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hm, hn⟩, hne⟩,
          howner⟩,
        hdata.2.1⟩

/-- The p-divisible-first half is the coordinate swap of the oriented carrier. -/
theorem lowOwnerGlobalFirstOwnerPDivFirstFiber_eq_swapImage
    {R p : ℕ} (hp : p.Prime) :
    lowOwnerGlobalFirstOwnerPDivFirstFiber R p =
      (lowOwnerFirstOwnerOrientedCrossPairCarrier R p).image Prod.swap := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hfirst, hpdiv⟩
    rcases Finset.mem_filter.mp hfirst with ⟨hoff, howner⟩
    rcases Finset.mem_filter.mp hoff with ⟨hprod, hne⟩
    rcases Finset.mem_product.mp hprod with ⟨hm, hn⟩
    have hdata :=
      (isSquarefreePairFreshPrimeOwner_iff_sameLowerSignature_dvdXor
        hp hm hn hne).1 howner
    rcases hdata.2 with hleft | hright
    · have horient :
          (n, m) ∈ lowOwnerFirstOwnerOrientedCrossPairCarrier R p := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hn, hm⟩,
            ⟨hdata.1.symm, hleft.2, hleft.1⟩⟩
      exact Finset.mem_image.mpr ⟨(n, m), horient, rfl⟩
    · exact False.elim (hright.2 hpdiv)
  · intro h
    rcases Finset.mem_image.mp h with ⟨ab, hab, habEq⟩
    rcases ab with ⟨a, b⟩
    have hpair : (m, n) = (b, a) := by
      simpa using habEq.symm
    cases hpair
    rcases Finset.mem_filter.mp hab with ⟨hprod, hdata⟩
    rcases Finset.mem_product.mp hprod with ⟨ha, hb⟩
    have hne : b ≠ a := by
      intro hba
      subst b
      exact hdata.2.1 hdata.2.2
    have howner :
        IsSquarefreePairFreshPrimeOwner p b a := by
      have hsig :=
        (isSquarefreePairFreshPrimeOwner_iff_sameLowerSignature_dvdXor
          hp hb ha hne)
      exact hsig.2
        ⟨hdata.1.symm, Or.inl ⟨hdata.2.2, hdata.2.1⟩⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hb, ha⟩, hne⟩,
          howner⟩,
        hdata.2.2⟩

/-- The two orientation halves partition the global first-owner fibre. -/
theorem lowOwnerGlobalFirstOwnerPairMassWith_eq_orientation_halves
    (R p : ℕ) (v : ℕ → ℝ) :
    lowOwnerGlobalFirstOwnerPairMassWith R p v =
      (∑ mn ∈ lowOwnerGlobalFirstOwnerPDivFirstFiber R p,
        v mn.1 * v mn.2) +
      (∑ mn ∈ lowOwnerGlobalFirstOwnerPFreeFirstFiber R p,
        v mn.1 * v mn.2) := by
  unfold lowOwnerGlobalFirstOwnerPairMassWith
    lowOwnerGlobalFirstOwnerPDivFirstFiber
    lowOwnerGlobalFirstOwnerPFreeFirstFiber
  let S := lowOwnerGlobalFirstOwnerPairFiber R p
  let f : ℕ × ℕ → ℝ := fun mn => v mn.1 * v mn.2
  have h :=
    Finset.sum_filter_add_sum_filter_not
      (s := S) (p := fun mn : ℕ × ℕ => p ∣ mn.1) (f := f)
  simpa [S, f, add_comm] using h.symm

/-- Swapping the two coordinates preserves an arbitrary scalar site product. -/
theorem sum_swapImage_siteProduct_eq
    (S : Finset (ℕ × ℕ)) (v : ℕ → ℝ) :
    (∑ mn ∈ S.image Prod.swap, v mn.1 * v mn.2) =
      ∑ mn ∈ S, v mn.1 * v mn.2 := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro mn _hmn
    rcases mn with ⟨m, n⟩
    simp [mul_comm]
  · intro a _ha b _hb hab
    have := congrArg Prod.swap hab
    simpa using this

/-- **Ordered least-owner mass = twice the oriented raw-parent carrier mass.** -/
theorem lowOwnerGlobalFirstOwnerPairMassWith_eq_two_oriented
    {R p : ℕ} (hp : p.Prime) (v : ℕ → ℝ) :
    lowOwnerGlobalFirstOwnerPairMassWith R p v =
      2 * lowOwnerFirstOwnerOrientedCrossPairMassWith R p v := by
  rw [lowOwnerGlobalFirstOwnerPairMassWith_eq_orientation_halves]
  rw [lowOwnerGlobalFirstOwnerPDivFirstFiber_eq_swapImage hp,
    lowOwnerGlobalFirstOwnerPFreeFirstFiber_eq_oriented hp]
  rw [sum_swapImage_siteProduct_eq]
  unfold lowOwnerFirstOwnerOrientedCrossPairMassWith
  ring

/-- Arbitrary-site product mass on one lower-signature base×child cell. -/
def lowOwnerFirstOwnerCellGramWith
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
      (lowOwnerFirstOwnerChildFiber R p sig),
    v ab.1 * v ab.2

/-- The oriented arbitrary-site first-owner mass is exactly the sum of its
existing lower-signature cell fibres. -/
theorem sum_lowOwnerFirstOwnerCellGramWith_eq_oriented
    (R p : ℕ) (v : ℕ → ℝ) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCellGramWith R p sig v) =
      lowOwnerFirstOwnerOrientedCrossPairMassWith R p v := by
  let S := lowOwnerFirstOwnerOrientedCrossPairCarrier R p
  let T := lowOwnerFirstOwnerSignatureSet R p
  let g : ℕ × ℕ → Finset ℕ := fun ab =>
    squarefreeLowerPrimeSignature p ab.1
  let f : ℕ × ℕ → ℝ := fun ab => v ab.1 * v ab.2
  have hmaps : ∀ ab ∈ S, g ab ∈ T := by
    intro ab hab
    rcases Finset.mem_filter.mp hab with ⟨hprod, _hdata⟩
    have haCar := (Finset.mem_product.mp hprod).1
    exact Finset.mem_image.mpr ⟨ab.1, haCar, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmaps f
  unfold lowOwnerFirstOwnerCellGramWith
    lowOwnerFirstOwnerOrientedCrossPairMassWith
  calc
    (∑ sig ∈ T,
      ∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerChildFiber R p sig),
        v ab.1 * v ab.2) =
      ∑ sig ∈ T, ∑ ab ∈ S with g ab = sig, f ab := by
        apply Finset.sum_congr rfl
        intro sig _hsig
        have hset :=
          lowOwnerFirstOwnerOrientedCrossPairCarrier_filter_signature_eq_product
            R p sig
        change
          (∑ ab ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
              (lowOwnerFirstOwnerChildFiber R p sig), f ab) =
            ∑ ab ∈ S.filter (fun ab => g ab = sig), f ab
        rw [show S.filter (fun ab => g ab = sig) =
            (lowOwnerFirstOwnerBaseFiber R p sig).product
              (lowOwnerFirstOwnerChildFiber R p sig) by
          simpa [S, g] using hset]
    _ = ∑ ab ∈ S, f ab := hfiber
    _ = _ := rfl

/-- **Raw-parent cell form of the global ordered first-owner mass.** -/
theorem lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
    {R p : ℕ} (hp : p.Prime) (v : ℕ → ℝ) :
    lowOwnerGlobalFirstOwnerPairMassWith R p v =
      2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerCellGramWith R p sig v := by
  rw [lowOwnerGlobalFirstOwnerPairMassWith_eq_two_oriented hp,
    ← sum_lowOwnerFirstOwnerCellGramWith_eq_oriented]

end RHLean.Proof
