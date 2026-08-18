import Mathlib
import RHLean.Analysis.LeastSquareCompleteSuperorbitRecombination
import RHLean.Analysis.PrimeWheelRecoveredMertensCriterion
import RHLean.Arithmetic.PrimeSquareCollisionCRT

/-!
# Coherent outside-prime sign layer and the square-root prime wheel

The least-owner deletion analysis leaves one coherent selected-CRT baseline.
This file identifies what that baseline is missing without introducing a new
estimate.

There are two exact levels of the same statement.

* Pointwise, the prime-wheel local factor is literally the product of the
  square-survival mask and the ordinary first-power sign factor.  Thus the raw
  seeded prime wheel already combines square deletion and ordinary prime sign
  flips in one local operator.
* On the one-prime degree-one CRT baseline, square deletion alone leaves the
  zero-free weight `p^2 - 6`.  The missing ordinary sign layer contributes
  exactly `-2 (p - 1)`, so the recombined weight is
  `p^2 - 2 p - 4`, exactly the nonzero weight-one Walsh baseline identified in
  `SelectedCRTBaseline`.

Finally, under square-root coverage, substituting the pointwise factorization
into the existing `raw - 2 * smooth` recovery theorem gives the actual Moebius
coefficient exactly.  No norm, independence hypothesis, or channelwise triangle
inequality appears here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Ordinary first-power sign supplied by one prime coordinate. -/
def ordinaryPrimeSignFactor (p n : ℕ) : ℤ :=
  if p ∣ n then -1 else 1

/-- Square-survival factor supplied by one prime coordinate. -/
def primeSquareSurvivalFactor (p n : ℕ) : ℤ :=
  if p ^ 2 ∣ n then 0 else 1

/-- **Exact local recombination.**  The prime-wheel local comb is square
survival times the ordinary prime sign.  A square hit kills the site, a
first-power hit flips it, and a miss leaves it unchanged. -/
theorem localPrimeComb_eq_squareSurvival_mul_ordinarySign
    (p n : ℕ) :
    localPrimeComb p n =
      primeSquareSurvivalFactor p n * ordinaryPrimeSignFactor p n := by
  by_cases hsq : p ^ 2 ∣ n
  · simp [localPrimeComb, primeSquareSurvivalFactor,
      ordinaryPrimeSignFactor, hsq]
  · by_cases hd : p ∣ n
    · simp [localPrimeComb, primeSquareSurvivalFactor,
        ordinaryPrimeSignFactor, hsq, hd]
    · simp [localPrimeComb, primeSquareSurvivalFactor,
        ordinaryPrimeSignFactor, hsq, hd]

/-- Product square-survival mask for a finite selected prime set. -/
def finitePrimeSquareSurvivalMask (P : Finset ℕ) (n : ℕ) : ℤ :=
  ∏ p ∈ P, primeSquareSurvivalFactor p n

/-- The selected sign field is exactly the product of the ordinary local sign
factors. -/
theorem selectedPrimeSign_eq_ordinaryPrimeSignProduct
    (P : Finset ℕ) (n : ℕ) :
    selectedPrimeSign P n =
      ∏ p ∈ P, ordinaryPrimeSignFactor p n := by
  rfl

/-- **Finite pointwise bridge.**  The seeded prime wheel is the selected
ordinary sign field multiplied by the complete selected square-survival mask,
with the repository's fixed seed orientation `-1`. -/
theorem seededPrimeComb_eq_neg_survival_mul_selectedPrimeSign
    (P : Finset ℕ) (n : ℕ) :
    seededPrimeComb P n =
      -(finitePrimeSquareSurvivalMask P n * selectedPrimeSign P n) := by
  classical
  unfold seededPrimeComb finitePrimeSquareSurvivalMask selectedPrimeSign
  have hprod :
      (∏ p ∈ P, localPrimeComb p n) =
        ∏ p ∈ P,
          (primeSquareSurvivalFactor p n * ordinaryPrimeSignFactor p n) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact localPrimeComb_eq_squareSurvival_mul_ordinarySign p n
  rw [hprod, Finset.prod_mul_distrib]
  rfl

/-- On a selected-square-zero-free site the survival mask is identically one. -/
theorem finitePrimeSquareSurvivalMask_eq_one_of_zeroFree
    (P : Finset ℕ) (n : ℕ)
    (hzero : ∀ p ∈ P, ¬ p ^ 2 ∣ n) :
    finitePrimeSquareSurvivalMask P n = 1 := by
  classical
  unfold finitePrimeSquareSurvivalMask
  apply Finset.prod_eq_one
  intro p hp
  simp [primeSquareSurvivalFactor, hzero p hp]

/-- Hence before any outside square is encountered, the raw seeded wheel is
exactly the negative selected sign field. -/
theorem seededPrimeComb_eq_neg_selectedPrimeSign_of_zeroFree
    (P : Finset ℕ) (n : ℕ)
    (hzero : ∀ p ∈ P, ¬ p ^ 2 ∣ n) :
    seededPrimeComb P n = -selectedPrimeSign P n := by
  rw [seededPrimeComb_eq_neg_survival_mul_selectedPrimeSign,
    finitePrimeSquareSurvivalMask_eq_one_of_zeroFree P n hzero]
  ring

/-- **Square-root wheel closure in selected-sign coordinates.**  Under the
existing square-root coverage hypothesis, the selected ordinary sign field,
the selected square-deletion mask, and the smooth-core correction recombine to
the actual Moebius coefficient exactly. -/
theorem selectedSign_squareDeletion_smooth_eq_moebius
    (P : Finset ℕ) {upper n : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hcover : PrimeWheelSqrtCoverage P upper)
    (hnpos : 0 < n) (hnupper : n ≤ upper) :
    -(finitePrimeSquareSurvivalMask P n * selectedPrimeSign P n) -
        2 * primeWheelSmoothCoreSite P upper n =
      μ n := by
  have hcorr :=
    correctedPrimeWheelSite_eq_moebius
      P hprime hcover hnpos hnupper
  rw [← seededPrimeComb_eq_neg_survival_mul_selectedPrimeSign P n]
  simpa [correctedPrimeWheelSite] using hcorr

/-! ## Generic six-root bridge for the physical transition -/

/-- The six physical collision roots are the three current-cell roots and the
three next-cell roots.  The compressed middle forms `2*k+1` and `2*k+3` have
exactly the same odd-prime square roots as `4*k+2` and `4*k+6`. -/
def tTransitionCollisionRoots (p : ℕ) : Finset (ZMod (p ^ 2)) :=
  currentCollisionRoots p ∪ nextCollisionRoots p

/-- A bounded residue solves `4*k+r = 0 mod p^2` exactly when its natural cast
is the existing collision root. -/
theorem fin_cast_eq_collisionRoot_iff_dvd_four_add
    {p : ℕ} (hp : p.Prime) (hpgt : 2 < p)
    (r : ℕ) (k : Fin (p ^ 2)) :
    p ^ 2 ∣ 4 * k.val + r ↔
      (k.val : ZMod (p ^ 2)) = collisionRoot (p ^ 2) r := by
  have h4 := four_coprime_primeSquare p hp hpgt
  have hInv :
      (4 : ZMod (p ^ 2))⁻¹ * (4 : ZMod (p ^ 2)) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one 4 h4
  constructor
  · intro hdvd
    have hz :
        ((4 * k.val + r : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (4 * k.val + r) (p ^ 2)).2 hdvd
    push_cast at hz
    have hfour :
        (4 : ZMod (p ^ 2)) * (k.val : ZMod (p ^ 2)) =
          -(r : ZMod (p ^ 2)) := by
      calc
        (4 : ZMod (p ^ 2)) * (k.val : ZMod (p ^ 2)) =
            ((4 : ZMod (p ^ 2)) * (k.val : ZMod (p ^ 2)) +
              (r : ZMod (p ^ 2))) - (r : ZMod (p ^ 2)) := by ring
        _ = 0 - (r : ZMod (p ^ 2)) := by rw [hz]
        _ = -(r : ZMod (p ^ 2)) := by ring
    unfold collisionRoot
    calc
      (k.val : ZMod (p ^ 2)) =
          1 * (k.val : ZMod (p ^ 2)) := by ring
      _ = ((4 : ZMod (p ^ 2))⁻¹ * (4 : ZMod (p ^ 2))) *
          (k.val : ZMod (p ^ 2)) := by rw [hInv]
      _ = (4 : ZMod (p ^ 2))⁻¹ *
          ((4 : ZMod (p ^ 2)) * (k.val : ZMod (p ^ 2))) := by ring
      _ = (4 : ZMod (p ^ 2))⁻¹ * (-(r : ZMod (p ^ 2))) := by rw [hfour]
      _ = -(r : ZMod (p ^ 2)) * (4 : ZMod (p ^ 2))⁻¹ := by ring
  · intro hroot
    apply (ZMod.natCast_eq_zero_iff (4 * k.val + r) (p ^ 2)).1
    push_cast
    rw [hroot]
    have h := four_mul_collisionRoot (p ^ 2) r h4
    rw [h]
    ring

/-- The compressed affine form `2*k+c` has the collision root with physical
offset `2*c`, because `2` is a unit modulo every odd prime square. -/
theorem fin_cast_eq_collisionRoot_iff_dvd_two_add
    {p : ℕ} (hp : p.Prime) (hpgt : 2 < p)
    (c : ℕ) (k : Fin (p ^ 2)) :
    p ^ 2 ∣ 2 * k.val + c ↔
      (k.val : ZMod (p ^ 2)) = collisionRoot (p ^ 2) (2 * c) := by
  have hpne : p ≠ 2 := by omega
  have h2p : Nat.Coprime 2 p :=
    (hp.odd_of_ne_two hpne).coprime_two_left
  have h2 : Nat.Coprime 2 (p ^ 2) := by
    rw [pow_two]
    exact Nat.Coprime.mul_right h2p h2p
  have hInv :
      (2 : ZMod (p ^ 2))⁻¹ * (2 : ZMod (p ^ 2)) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one 2 h2
  constructor
  · intro hdvd
    apply (fin_cast_eq_collisionRoot_iff_dvd_four_add hp hpgt (2 * c) k).1
    rcases hdvd with ⟨d, hd⟩
    refine ⟨2 * d, ?_⟩
    calc
      4 * k.val + 2 * c = 2 * (2 * k.val + c) := by ring
      _ = 2 * ((p ^ 2) * d) := by rw [hd]
      _ = (p ^ 2) * (2 * d) := by ring
  · intro hroot
    have hdvd4 :=
      (fin_cast_eq_collisionRoot_iff_dvd_four_add hp hpgt (2 * c) k).2 hroot
    have hz4 :
        ((4 * k.val + 2 * c : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (4 * k.val + 2 * c) (p ^ 2)).2 hdvd4
    push_cast at hz4
    apply (ZMod.natCast_eq_zero_iff (2 * k.val + c) (p ^ 2)).1
    push_cast
    have hfactor :
        (4 : ZMod (p ^ 2)) * (k.val : ZMod (p ^ 2)) +
            (2 : ZMod (p ^ 2)) * (c : ZMod (p ^ 2)) =
          (2 : ZMod (p ^ 2)) *
            ((2 : ZMod (p ^ 2)) * (k.val : ZMod (p ^ 2)) +
              (c : ZMod (p ^ 2))) := by ring
    rw [hfactor] at hz4
    calc
      (2 : ZMod (p ^ 2)) * (k.val : ZMod (p ^ 2)) +
          (c : ZMod (p ^ 2)) =
        1 * ((2 : ZMod (p ^ 2)) * (k.val : ZMod (p ^ 2)) +
          (c : ZMod (p ^ 2))) := by ring
      _ = ((2 : ZMod (p ^ 2))⁻¹ * (2 : ZMod (p ^ 2))) *
          ((2 : ZMod (p ^ 2)) * (k.val : ZMod (p ^ 2)) +
            (c : ZMod (p ^ 2))) := by rw [hInv]
      _ = (2 : ZMod (p ^ 2))⁻¹ *
          ((2 : ZMod (p ^ 2)) *
            ((2 : ZMod (p ^ 2)) * (k.val : ZMod (p ^ 2)) +
              (c : ZMod (p ^ 2)))) := by ring
      _ = (2 : ZMod (p ^ 2))⁻¹ * 0 := by rw [hz4]
      _ = 0 := by ring

/-- The six transition divisibility conditions are exactly membership in the
six physical collision roots. -/
theorem transitionSquareDivisor_iff_mem_collisionRoots
    {p : ℕ} (hp : p.Prime) (hpgt : 2 < p)
    (k : Fin (p ^ 2)) :
    (∃ i : Fin 6, p ^ 2 ∣ tTransitionForm i k.val) ↔
      (k.val : ZMod (p ^ 2)) ∈ tTransitionCollisionRoots p := by
  simp only [tTransitionCollisionRoots, currentCollisionRoots,
    nextCollisionRoots, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · left; left
      exact (fin_cast_eq_collisionRoot_iff_dvd_four_add hp hpgt 1 k).1
        (by simpa [tTransitionForm] using hi)
    · left; right; left
      exact (fin_cast_eq_collisionRoot_iff_dvd_two_add hp hpgt 1 k).1
        (by simpa [tTransitionForm] using hi)
    · left; right; right
      exact (fin_cast_eq_collisionRoot_iff_dvd_four_add hp hpgt 3 k).1
        (by simpa [tTransitionForm] using hi)
    · right; left
      exact (fin_cast_eq_collisionRoot_iff_dvd_four_add hp hpgt 5 k).1
        (by simpa [tTransitionForm] using hi)
    · right; right; left
      exact (fin_cast_eq_collisionRoot_iff_dvd_two_add hp hpgt 3 k).1
        (by simpa [tTransitionForm] using hi)
    · right; right; right
      exact (fin_cast_eq_collisionRoot_iff_dvd_four_add hp hpgt 7 k).1
        (by simpa [tTransitionForm] using hi)
  · intro h
    rcases h with (h1 | h2 | h3) | (h5 | h6 | h7)
    · exact ⟨0, by
        simpa [tTransitionForm] using
          (fin_cast_eq_collisionRoot_iff_dvd_four_add hp hpgt 1 k).2 h1⟩
    · exact ⟨1, by
        simpa [tTransitionForm] using
          (fin_cast_eq_collisionRoot_iff_dvd_two_add hp hpgt 1 k).2 h2⟩
    · exact ⟨2, by
        simpa [tTransitionForm] using
          (fin_cast_eq_collisionRoot_iff_dvd_four_add hp hpgt 3 k).2 h3⟩
    · exact ⟨3, by
        simpa [tTransitionForm] using
          (fin_cast_eq_collisionRoot_iff_dvd_four_add hp hpgt 5 k).2 h5⟩
    · exact ⟨4, by
        simpa [tTransitionForm] using
          (fin_cast_eq_collisionRoot_iff_dvd_two_add hp hpgt 3 k).2 h6⟩
    · exact ⟨5, by
        simpa [tTransitionForm] using
          (fin_cast_eq_collisionRoot_iff_dvd_four_add hp hpgt 7 k).2 h7⟩

/-- Current and next three-root families are disjoint once the prime square is
larger than all six physical offsets. -/
theorem currentCollisionRoots_disjoint_nextCollisionRoots
    (p : ℕ) (hp : p.Prime) (hpgt : 2 < p) :
    Disjoint (currentCollisionRoots p) (nextCollisionRoots p) := by
  have h4 := four_coprime_primeSquare p hp hpgt
  have hm : 8 ≤ p ^ 2 := by nlinarith
  have hroot_ne (a b : ℕ) (ha : a ≤ 3) (hb : 5 ≤ b) (hb7 : b ≤ 7) :
      collisionRoot (p ^ 2) a ≠ collisionRoot (p ^ 2) b := by
    intro h
    have heq := collisionRoot_injective_of_lt
      (p ^ 2) a b h4 (by omega) (by omega) h
    omega
  rw [Finset.disjoint_left]
  intro z hzCurrent hzNext
  simp only [currentCollisionRoots, Finset.mem_insert,
    Finset.mem_singleton] at hzCurrent
  simp only [nextCollisionRoots, Finset.mem_insert,
    Finset.mem_singleton] at hzNext
  rcases hzCurrent with h1 | h2 | h3
  · rcases hzNext with h5 | h6 | h7
    · exact (hroot_ne 1 5 (by omega) (by omega) (by omega)) (h1.symm.trans h5)
    · exact (hroot_ne 1 6 (by omega) (by omega) (by omega)) (h1.symm.trans h6)
    · exact (hroot_ne 1 7 (by omega) (by omega) (by omega)) (h1.symm.trans h7)
  · rcases hzNext with h5 | h6 | h7
    · exact (hroot_ne 2 5 (by omega) (by omega) (by omega)) (h2.symm.trans h5)
    · exact (hroot_ne 2 6 (by omega) (by omega) (by omega)) (h2.symm.trans h6)
    · exact (hroot_ne 2 7 (by omega) (by omega) (by omega)) (h2.symm.trans h7)
  · rcases hzNext with h5 | h6 | h7
    · exact (hroot_ne 3 5 (by omega) (by omega) (by omega)) (h3.symm.trans h5)
    · exact (hroot_ne 3 6 (by omega) (by omega) (by omega)) (h3.symm.trans h6)
    · exact (hroot_ne 3 7 (by omega) (by omega) (by omega)) (h3.symm.trans h7)

/-- The generic physical transition has exactly six distinct prime-square
collision roots. -/
theorem tTransitionCollisionRoots_card
    (p : ℕ) (hp : p.Prime) (hpgt : 2 < p) :
    (tTransitionCollisionRoots p).card = 6 := by
  unfold tTransitionCollisionRoots
  rw [Finset.card_union_of_disjoint
      (currentCollisionRoots_disjoint_nextCollisionRoots p hp hpgt),
    currentCollisionRoots_card p hp hpgt,
    nextCollisionRoots_card p hp hpgt]

/-- **Generic six-root residue theorem.**  Every prime `p >= 11` has exactly six
least-owner square-deletion residues modulo `p^2`.  This discharges the general
finite residue-count bridge left algebraic in `FinitePrimeTMixing`. -/
theorem leastOwnerDeletionResidues_card_six
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (leastOwnerDeletionResidues p).card = 6 := by
  have hpgt : 2 < p := by omega
  letI : NeZero (p ^ 2) :=
    ⟨Nat.ne_of_gt (pow_pos hp.pos 2)⟩
  let emb : Fin (p ^ 2) ↪ ZMod (p ^ 2) :=
    { toFun := fun k => (k.val : ZMod (p ^ 2))
      inj' := by
        intro a b hab
        apply Fin.ext
        have hmod :=
          (ZMod.natCast_eq_natCast_iff' a.val b.val (p ^ 2)).1 hab
        simpa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hmod }
  have hmap :
      (leastOwnerDeletionResidues p).map emb =
        tTransitionCollisionRoots p := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_map.mp hz with ⟨k, hk, hkz⟩
      have hcond : ∃ i : Fin 6, p ^ 2 ∣ tTransitionForm i k.val := by
        simpa [leastOwnerDeletionResidues] using hk
      have hroot :=
        (transitionSquareDivisor_iff_mem_collisionRoots hp hpgt k).1 hcond
      rw [← hkz]
      exact hroot
    · intro hz
      let k : Fin (p ^ 2) := ⟨z.val, ZMod.val_lt z⟩
      have hkcast : (k.val : ZMod (p ^ 2)) = z := by
        change (z.val : ZMod (p ^ 2)) = z
        exact ZMod.natCast_zmod_val z
      have hkroot :
          (k.val : ZMod (p ^ 2)) ∈ tTransitionCollisionRoots p := by
        rw [hkcast]
        exact hz
      have hcond :=
        (transitionSquareDivisor_iff_mem_collisionRoots hp hpgt k).2 hkroot
      apply Finset.mem_map.mpr
      refine ⟨k, ?_, ?_⟩
      · simpa [leastOwnerDeletionResidues] using hcond
      · exact hkcast
  calc
    (leastOwnerDeletionResidues p).card =
        ((leastOwnerDeletionResidues p).map emb).card := by simp
    _ = (tTransitionCollisionRoots p).card := by rw [hmap]
    _ = 6 := tTransitionCollisionRoots_card p hp hpgt

/-! ## The same split on the complete one-prime CRT baseline -/

/-- Signed degree-one correction contributed by the ordinary first-power sign
layer after square-zero residues have already been deleted. -/
def onePrimeOrdinarySignCorrectionWeight (p : ℕ) : ℚ :=
  -2 * onePrimeSingleFlipWeight p

/-- The ordinary sign correction has the closed form `-2 (p - 1)`. -/
theorem onePrimeOrdinarySignCorrectionWeight_eq (p : ℕ) :
    onePrimeOrdinarySignCorrectionWeight p =
      -2 * ((p : ℚ) - 1) := by
  unfold onePrimeOrdinarySignCorrectionWeight onePrimeSingleFlipWeight
  ring

/-- **Exact deletion/sign recombination of the degree-one baseline.**  Deleting
the six square-zero residues leaves the zero-free weight; the one relevant
first-power sign-flip class then contributes `-2` times its class weight. -/
theorem onePrimeDegreeOneBaselineWeight_eq_zeroFree_add_signCorrection
    (p : ℕ) :
    onePrimeDegreeOneBaselineWeight p =
      onePrimeZeroFreeWeight p + onePrimeOrdinarySignCorrectionWeight p := by
  unfold onePrimeDegreeOneBaselineWeight onePrimeOrdinarySignCorrectionWeight
  rw [← onePrimeWeight_partition p]
  ring

/-- Closed recombination formula: starting from all `p^2` residues, the square
kill costs `6` and the ordinary sign layer costs `2 (p - 1)`. -/
theorem onePrimeDegreeOneBaselineWeight_eq_raw_sub_deletion_sub_sign
    (p : ℕ) :
    onePrimeDegreeOneBaselineWeight p =
      (p : ℚ) ^ 2 - 6 - 2 * ((p : ℚ) - 1) := by
  rw [onePrimeDegreeOneBaselineWeight_eq]
  ring

/-- Scalar stage form.  For any coherent incoming baseline `B`, square deletion
and the ordinary sign correction stay signed and recombine before any norm is
taken. -/
theorem onePrimeStageBaseline_recombination
    (p : ℕ) (B : ℚ) :
    onePrimeDegreeOneBaselineWeight p * B =
      onePrimeZeroFreeWeight p * B +
        onePrimeOrdinarySignCorrectionWeight p * B := by
  rw [onePrimeDegreeOneBaselineWeight_eq_zeroFree_add_signCorrection]
  ring

/-- For a generic prime, the same deletion-plus-sign quantity is exactly the
zero-free mass times the already-formalized weight-one Walsh multiplier. -/
theorem onePrimeDeletionAndSign_eq_zeroFree_mul_walsh
    {p : ℕ} (hp : 11 ≤ p) :
    onePrimeZeroFreeWeight p + onePrimeOrdinarySignCorrectionWeight p =
      onePrimeZeroFreeWeight p * onePrimeWalshFactor p 1 := by
  rw [← onePrimeDegreeOneBaselineWeight_eq_zeroFree_add_signCorrection]
  exact onePrimeDegreeOneBaselineWeight_eq_zeroFree_mul_walsh hp

/-- Adjoining a fresh prime to a finite coherent baseline performs exactly the
same signed deletion-plus-ordinary-sign recombination. -/
theorem finitePrimeDegreeOneBaselineWeight_insert_eq_deletion_add_sign
    {P : Finset ℕ} {q : ℕ} (hq : q ∉ P) :
    finitePrimeDegreeOneBaselineWeight (insert q P) =
      onePrimeZeroFreeWeight q * finitePrimeDegreeOneBaselineWeight P +
        onePrimeOrdinarySignCorrectionWeight q *
          finitePrimeDegreeOneBaselineWeight P := by
  classical
  unfold finitePrimeDegreeOneBaselineWeight
  rw [Finset.prod_insert hq]
  rw [onePrimeDegreeOneBaselineWeight_eq_zeroFree_add_signCorrection]
  ring

/-! ## Direct recombination with the least-owner mass from PR #404 -/

/-- Ordinary first-power sign correction attached to the conditioned least-owner
stage baseline.  This is the missing signed layer after the square-deletion
channel has been removed. -/
def leastOwnerOrdinarySignCorrectionMass
    (P : Finset ℕ) (q : ℕ) : ℝ :=
  (-2 * ((q : ℝ) - 1)) * leastOwnerStageBaseline P q

/-- **Exact #404-to-prime-wheel bookkeeping.**  Start with `q^2` copies of the
conditioned incoming stage baseline.  Subtract the complete least-owner square
deletion mass from PR #404, then add the ordinary first-power sign correction.
The result is one signed coefficient multiplying the same coherent baseline.
No local root cardinality has been substituted yet. -/
theorem leastOwnerCompleteDeletion_add_ordinarySign_recombine
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) :
    (q : ℝ) ^ 2 * leastOwnerStageBaseline P q -
        leastOwnerCompleteChannelMass P q +
          leastOwnerOrdinarySignCorrectionMass P q =
      ((q : ℝ) ^ 2 - ((leastOwnerDeletionResidues q).card : ℝ) -
          2 * ((q : ℝ) - 1)) * leastOwnerStageBaseline P q := by
  rw [leastOwnerCompleteChannelMass_eq_card_mul_baseline P hP hq hqP]
  unfold leastOwnerOrdinarySignCorrectionMass
  ring

/-- With the generic six-root theorem, the physical least-owner recombination
is exactly the one-prime degree-one baseline from the finite CRT Walsh law. -/
theorem leastOwnerCompleteDeletion_add_ordinarySign_eq_degreeOneBaseline
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqP : q ∉ P)
    (hq11 : 11 ≤ q) :
    (q : ℝ) ^ 2 * leastOwnerStageBaseline P q -
        leastOwnerCompleteChannelMass P q +
          leastOwnerOrdinarySignCorrectionMass P q =
      ((onePrimeDegreeOneBaselineWeight q : ℚ) : ℝ) *
        leastOwnerStageBaseline P q := by
  rw [leastOwnerCompleteDeletion_add_ordinarySign_recombine P hP hq hqP,
    leastOwnerDeletionResidues_card_six hq hq11,
    onePrimeDegreeOneBaselineWeight_eq_raw_sub_deletion_sub_sign]
  push_cast
  ring

/-- **Hypothesis-free generic Walsh closure.**  For every outside prime
`q >= 11`, the complete least-owner square deletion and the missing ordinary
sign layer recombine exactly to the existing weight-one Walsh multiplier. -/
theorem leastOwnerCompleteDeletion_add_ordinarySign_eq_walsh
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqP : q ∉ P)
    (hq11 : 11 ≤ q) :
    (q : ℝ) ^ 2 * leastOwnerStageBaseline P q -
        leastOwnerCompleteChannelMass P q +
          leastOwnerOrdinarySignCorrectionMass P q =
      ((onePrimeZeroFreeWeight q * onePrimeWalshFactor q 1 : ℚ) : ℝ) *
        leastOwnerStageBaseline P q := by
  rw [leastOwnerCompleteDeletion_add_ordinarySign_eq_degreeOneBaseline
    P hP hq hqP hq11]
  rw [onePrimeDegreeOneBaselineWeight_eq_zeroFree_mul_walsh hq11]

end RHLean.Analysis
