import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergFactorFourFubini

/-!
# Exact prime-two fold of the factor-four signed K2 shell

The physical-product Fubini shell is partitioned by parity.  Every nonzero
Möbius term with even divisor has the form `d = 2*m` with `m` odd.  It pairs
bijectively with the odd-divisor, even-quotient term `(m, 2*k)` at the same
physical product.  Terms with `4 | d` vanish because Möbius is zero.

Thus one exact prime-two fold writes the shell as

* an odd--odd core, on which the prime `2` occurs in neither coordinate; and
* a paired correction in which the leading `log^2 m` mode has cancelled.

No absolute value is taken in this file.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Physical pairs representing the factor-four annulus. -/
def nativePNTSignedK2FactorFourPairSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun dk =>
      N / 4 < dk.1 * dk.2 ∧ dk.1 * dk.2 ≤ N

/-- The same factor-four shell written directly on physical pairs. -/
def nativePNTSignedK2FactorFourPairMass (N : ℕ) : ℝ :=
  ∑ dk ∈ nativePNTSignedK2FactorFourPairSet N,
    nativePNTSignedK2RecipFubiniAtom dk.1 dk.2

@[simp] theorem mem_nativePNTSignedK2FactorFourPairSet
    {N d k : ℕ} :
    (d, k) ∈ nativePNTSignedK2FactorFourPairSet N ↔
      d ∈ Finset.Icc 1 N ∧ k ∈ Finset.Icc 1 N ∧
        N / 4 < d * k ∧ d * k ≤ N := by
  simp [nativePNTSignedK2FactorFourPairSet]

/-- For a fixed positive divisor, the quotient interval is exactly the
physical-product condition. -/
private theorem nativePNTSignedK2FactorFour_inner_set
    (N d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
    Finset.Ioc ((N / 4) / d) (N / d) =
      (Finset.Icc 1 N).filter fun k =>
        N / 4 < d * k ∧ d * k ≤ N := by
  ext k
  have hdI := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := by omega
  simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hlow, hup⟩
    have hkpos : 0 < k := by omega
    have hlow' : N / 4 < k * d :=
      (Nat.div_lt_iff_lt_mul hdpos).1 hlow
    have hup' : k * d ≤ N :=
      (Nat.le_div_iff_mul_le hdpos).1 hup
    have hkN : k ≤ N := by
      calc
        k = 1 * k := by simp
        _ ≤ d * k := Nat.mul_le_mul_right k hdI.1
        _ = k * d := by omega
        _ ≤ N := hup'
    exact ⟨⟨by omega, hkN⟩,
      by simpa [Nat.mul_comm] using hlow',
      by simpa [Nat.mul_comm] using hup'⟩
  · rintro ⟨⟨_hk1, _hkN⟩, hlow, hup⟩
    constructor
    · apply (Nat.div_lt_iff_lt_mul hdpos).2
      simpa [Nat.mul_comm] using hlow
    · apply (Nat.le_div_iff_mul_le hdpos).2
      simpa [Nat.mul_comm] using hup

/-- The nested quotient Fubini shell and the physical-pair shell are identical. -/
theorem nativePNTSignedK2RecipDoubleShell_eq_pairMass
    (N : ℕ) :
    nativePNTSignedK2RecipDoubleShell N =
      nativePNTSignedK2FactorFourPairMass N := by
  classical
  unfold nativePNTSignedK2RecipDoubleShell
    nativePNTSignedK2FactorFourPairMass
    nativePNTSignedK2FactorFourPairSet
  rw [Finset.sum_filter]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  have hset := nativePNTSignedK2FactorFour_inner_set N d hd
  calc
    (∑ k ∈ Finset.Ioc ((N / 4) / d) (N / d),
        nativePNTSignedK2RecipFubiniAtom d k) =
      ∑ k ∈ (Finset.Icc 1 N).filter (fun k =>
          N / 4 < d * k ∧ d * k ≤ N),
        nativePNTSignedK2RecipFubiniAtom d k := by rw [← hset]
    _ = ∑ k ∈ Finset.Icc 1 N,
        if N / 4 < d * k ∧ d * k ≤ N then
          nativePNTSignedK2RecipFubiniAtom d k
        else 0 := by rw [Finset.sum_filter]

/-- Odd-divisor part of the physical pair set. -/
def nativePNTSignedK2FactorFourOddPairSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (nativePNTSignedK2FactorFourPairSet N).filter fun dk => Odd dk.1

/-- Odd-divisor, odd-quotient core left after one prime-two fold. -/
def nativePNTSignedK2FactorFourOddOddSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (nativePNTSignedK2FactorFourOddPairSet N).filter fun dk => Odd dk.2

/-- Odd-divisor, even-quotient half of the prime-two matched family. -/
def nativePNTSignedK2FactorFourOddEvenSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (nativePNTSignedK2FactorFourOddPairSet N).filter fun dk => Even dk.2

/-- Even-divisor half of the prime-two matched family. -/
def nativePNTSignedK2FactorFourEvenSet (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (nativePNTSignedK2FactorFourPairSet N).filter fun dk => Even dk.1

/-- Parent pairs for the map `(m,k) -> (2*m,k)` before removing parents with
zero Möbius child. -/
def nativePNTSignedK2FactorFourPrimeTwoParentAllSet
    (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun mk =>
      N / 4 < (2 * mk.1) * mk.2 ∧ (2 * mk.1) * mk.2 ≤ N

/-- Nonzero prime-two parents.  Oddness is exactly the freshness condition for
`2`. -/
def nativePNTSignedK2FactorFourPrimeTwoParentSet
    (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    (nativePNTSignedK2FactorFourPrimeTwoParentAllSet N).filter fun mk => Odd mk.1

@[simp] theorem mem_nativePNTSignedK2FactorFourPrimeTwoParentAllSet
    {N m k : ℕ} :
    (m, k) ∈ nativePNTSignedK2FactorFourPrimeTwoParentAllSet N ↔
      m ∈ Finset.Icc 1 N ∧ k ∈ Finset.Icc 1 N ∧
        N / 4 < (2 * m) * k ∧ (2 * m) * k ≤ N := by
  simp [nativePNTSignedK2FactorFourPrimeTwoParentAllSet]

@[simp] theorem mem_nativePNTSignedK2FactorFourPrimeTwoParentSet
    {N m k : ℕ} :
    (m, k) ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N ↔
      m ∈ Finset.Icc 1 N ∧ k ∈ Finset.Icc 1 N ∧
        N / 4 < (2 * m) * k ∧ (2 * m) * k ≤ N ∧ Odd m := by
  simp [nativePNTSignedK2FactorFourPrimeTwoParentSet,
    nativePNTSignedK2FactorFourPrimeTwoParentAllSet, and_assoc]

/-- A doubled even parent contains the square `2^2`, hence its Möbius atom is
zero. -/
theorem nativePNTSignedK2RecipFubiniAtom_two_mul_eq_zero_of_even
    (m k : ℕ) (hm : Even m) :
    nativePNTSignedK2RecipFubiniAtom (2 * m) k = 0 := by
  have hnot : ¬ Squarefree (2 * m) := by
    intro hsq
    rcases hm with ⟨r, hr⟩
    have hfour : 2 * 2 ∣ 2 * m := by
      refine ⟨r, ?_⟩
      omega
    exact Nat.prime_two.not_isUnit (hsq 2 hfour)
  have hmuZ : (μ : ArithmeticFunction ℝ) (2 * m) = 0 := by
    change (((μ (2 * m) : ℤ) : ℝ)) = 0
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot]
    norm_num
  simp [nativePNTSignedK2RecipFubiniAtom, hmuZ]

/-- Arbitrary finite sums split exactly into odd and even first coordinates. -/
private theorem factorFour_sum_eq_odd_add_even
    (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) :
    (∑ z ∈ s, f z) =
      (∑ z ∈ s.filter (fun z => Odd z.1), f z) +
        ∑ z ∈ s.filter (fun z => Even z.1), f z := by
  calc
    (∑ z ∈ s, f z) =
      ∑ z ∈ s,
        ((if Odd z.1 then f z else 0) +
          (if Even z.1 then f z else 0)) := by
        apply Finset.sum_congr rfl
        intro z _hz
        by_cases hodd : Odd z.1
        · have hneven : ¬ Even z.1 := Nat.not_even_iff_odd.mpr hodd
          simp [hodd, hneven]
        · have heven : Even z.1 := Nat.not_odd_iff_even.mp hodd
          simp [hodd, heven]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]

/-- The odd-divisor family splits exactly into odd and even quotients. -/
private theorem factorFour_odd_sum_eq_oddOdd_add_oddEven
    (N : ℕ) :
    (∑ dk ∈ nativePNTSignedK2FactorFourOddPairSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) =
      (∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
      ∑ dk ∈ nativePNTSignedK2FactorFourOddEvenSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2 := by
  simpa [nativePNTSignedK2FactorFourOddOddSet,
    nativePNTSignedK2FactorFourOddEvenSet] using
    factorFour_sum_eq_odd_add_even
      (nativePNTSignedK2FactorFourOddPairSet N)
      (fun dk => nativePNTSignedK2RecipFubiniAtom dk.1 dk.2)

/-- Reindex the odd-divisor/even-quotient half by `k = 2*r`. -/
private theorem factorFour_oddEven_sum_eq_parent_right
    (N : ℕ) :
    (∑ dk ∈ nativePNTSignedK2FactorFourOddEvenSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) =
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
        nativePNTSignedK2RecipFubiniAtom mk.1 (2 * mk.2) := by
  classical
  symm
  refine Finset.sum_bij
    (fun mk _hmk => (mk.1, 2 * mk.2)) ?_ ?_ ?_ ?_
  · intro mk hmk
    rcases mem_nativePNTSignedK2FactorFourPrimeTwoParentSet.mp hmk with
      ⟨hmI, hkI, hlow, hup, hmodd⟩
    have hm1 := (Finset.mem_Icc.mp hmI).1
    have hk1 := (Finset.mem_Icc.mp hkI).1
    have h2kN : 2 * mk.2 ≤ N := by
      calc
        2 * mk.2 = 1 * (2 * mk.2) := by ring
        _ ≤ mk.1 * (2 * mk.2) := Nat.mul_le_mul_right (2 * mk.2) hm1
        _ = (2 * mk.1) * mk.2 := by ring
        _ ≤ N := hup
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact mem_nativePNTSignedK2FactorFourPairSet.mpr
          ⟨hmI, Finset.mem_Icc.mpr ⟨by omega, h2kN⟩,
            by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlow,
            by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hup⟩
      · exact hmodd
    · exact even_two_mul mk.2
  · intro a _ha b _hb hab
    apply Prod.ext
    · exact congrArg Prod.fst hab
    · have h := congrArg Prod.snd hab
      simp only at h
      omega
  · intro dk hdk
    rcases Finset.mem_filter.mp hdk with ⟨hoddSet, hkeven⟩
    rcases Finset.mem_filter.mp hoddSet with ⟨hpair, hdodd⟩
    rcases mem_nativePNTSignedK2FactorFourPairSet.mp hpair with
      ⟨hdI, hkI, hlow, hup⟩
    have hkI' := Finset.mem_Icc.mp hkI
    have hdouble : 2 * (dk.2 / 2) = dk.2 :=
      Nat.two_mul_div_two_of_even hkeven
    have hhalf1 : 1 ≤ dk.2 / 2 := by
      have hkgt : 1 < dk.2 := by
        have hk0 : dk.2 ≠ 0 := by omega
        exact Nat.one_lt_of_ne_zero_of_even hk0 hkeven
      omega
    have hhalfN : dk.2 / 2 ≤ N :=
      (Nat.div_le_self dk.2 2).trans hkI'.2
    refine ⟨(dk.1, dk.2 / 2), ?_, ?_⟩
    · apply mem_nativePNTSignedK2FactorFourPrimeTwoParentSet.mpr
      refine ⟨hdI, Finset.mem_Icc.mpr ⟨hhalf1, hhalfN⟩, ?_, ?_, hdodd⟩
      · simpa [hdouble, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlow
      · simpa [hdouble, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hup
    · apply Prod.ext <;> simp [hdouble]
  · intro mk _hmk
    rfl

/-- Reindex all even-divisor pairs by `d = 2*m`. -/
private theorem factorFour_even_sum_eq_parentAll_left
    (N : ℕ) :
    (∑ dk ∈ nativePNTSignedK2FactorFourEvenSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) =
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentAllSet N,
        nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2 := by
  classical
  symm
  refine Finset.sum_bij
    (fun mk _hmk => (2 * mk.1, mk.2)) ?_ ?_ ?_ ?_
  · intro mk hmk
    rcases mem_nativePNTSignedK2FactorFourPrimeTwoParentAllSet.mp hmk with
      ⟨hmI, hkI, hlow, hup⟩
    have hm1 := (Finset.mem_Icc.mp hmI).1
    have h2mN : 2 * mk.1 ≤ N := by
      calc
        2 * mk.1 = (2 * mk.1) * 1 := by simp
        _ ≤ (2 * mk.1) * mk.2 :=
          Nat.mul_le_mul_left (2 * mk.1) (Finset.mem_Icc.mp hkI).1
        _ ≤ N := hup
    apply Finset.mem_filter.mpr
    exact ⟨mem_nativePNTSignedK2FactorFourPairSet.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, h2mN⟩, hkI, hlow, hup⟩,
      even_two_mul mk.1⟩
  · intro a _ha b _hb hab
    apply Prod.ext
    · have h := congrArg Prod.fst hab
      simp only at h
      omega
    · exact congrArg Prod.snd hab
  · intro dk hdk
    rcases Finset.mem_filter.mp hdk with ⟨hpair, hdeven⟩
    rcases mem_nativePNTSignedK2FactorFourPairSet.mp hpair with
      ⟨hdI, hkI, hlow, hup⟩
    have hdI' := Finset.mem_Icc.mp hdI
    have hdouble : 2 * (dk.1 / 2) = dk.1 :=
      Nat.two_mul_div_two_of_even hdeven
    have hhalf1 : 1 ≤ dk.1 / 2 := by
      have hdgt : 1 < dk.1 := by
        have hd0 : dk.1 ≠ 0 := by omega
        exact Nat.one_lt_of_ne_zero_of_even hd0 hdeven
      omega
    have hhalfN : dk.1 / 2 ≤ N :=
      (Nat.div_le_self dk.1 2).trans hdI'.2
    refine ⟨(dk.1 / 2, dk.2), ?_, ?_⟩
    · apply mem_nativePNTSignedK2FactorFourPrimeTwoParentAllSet.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hhalf1, hhalfN⟩, hkI,
        by simpa [hdouble] using hlow,
        by simpa [hdouble] using hup⟩
    · apply Prod.ext <;> simp [hdouble]
  · intro mk _hmk
    rfl

/-- Parents with even `m` make a zero child, so the all-parent sum restricts
exactly to the odd parent set. -/
private theorem factorFour_parentAll_left_eq_parentOdd_left
    (N : ℕ) :
    (∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentAllSet N,
        nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2) =
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
        nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2 := by
  classical
  calc
    (∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentAllSet N,
        nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2) =
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentAllSet N,
        if Odd mk.1 then
          nativePNTSignedK2RecipFubiniAtom (2 * mk.1) mk.2
        else 0 := by
          apply Finset.sum_congr rfl
          intro mk _hmk
          by_cases hodd : Odd mk.1
          · simp [hodd]
          · have heven : Even mk.1 := Nat.not_odd_iff_even.mp hodd
            rw [nativePNTSignedK2RecipFubiniAtom_two_mul_eq_zero_of_even
              mk.1 mk.2 heven]
            simp [hodd]
    _ = _ := by
      unfold nativePNTSignedK2FactorFourPrimeTwoParentSet
      rw [Finset.sum_filter]

/-- **Exact prime-two factor-four fold.**  The quadratic signed shell is one
odd--odd core plus a lower-degree prime-two correction.  The leading
`log^2(m)` mode has disappeared from every correction atom. -/
theorem nativePNTSignedK2FactorFourPairMass_eq_oddOdd_add_primeTwo
    (N : ℕ) :
    nativePNTSignedK2FactorFourPairMass N =
      (∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
        (-(μ : ArithmeticFunction ℝ) mk.1 *
          ((Real.log (2 : ℝ)) ^ 2 +
            2 * Real.log (2 : ℝ) * Real.log (mk.1 : ℝ)) /
          (((mk.1 * 2) * mk.2 : ℕ) : ℝ)) := by
  classical
  have hfirst := factorFour_sum_eq_odd_add_even
    (nativePNTSignedK2FactorFourPairSet N)
    (fun dk => nativePNTSignedK2RecipFubiniAtom dk.1 dk.2)
  have hsplit :
      nativePNTSignedK2FactorFourPairMass N =
        (∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
        (∑ dk ∈ nativePNTSignedK2FactorFourOddEvenSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
        ∑ dk ∈ nativePNTSignedK2FactorFourEvenSet N,
          nativePNTSignedK2RecipFubiniAtom dk.1 dk.2 := by
    unfold nativePNTSignedK2FactorFourPairMass at hfirst ⊢
    have hodd := factorFour_odd_sum_eq_oddOdd_add_oddEven N
    simpa [nativePNTSignedK2FactorFourOddPairSet,
      nativePNTSignedK2FactorFourEvenSet, hodd, add_assoc] using hfirst
  rw [hsplit, factorFour_oddEven_sum_eq_parent_right,
    factorFour_even_sum_eq_parentAll_left,
    factorFour_parentAll_left_eq_parentOdd_left]
  rw [← Finset.sum_add_distrib]
  ring_nf
  apply add_left_cancel
  apply Finset.sum_congr rfl
  intro mk hmk
  rcases mem_nativePNTSignedK2FactorFourPrimeTwoParentSet.mp hmk with
    ⟨hmI, hkI, _hlow, _hup, hmodd⟩
  have hk1 := (Finset.mem_Icc.mp hkI).1
  have hpair := nativePNTSignedK2RecipFubiniAtom_two_sameProduct
    mk.1 mk.2 hmodd hk1
  linarith

/-- The original factor-four interval inherits the exact prime-two fold. -/
theorem nativePNTSignedK2RecipInterval_four_eq_oddOdd_add_primeTwo
    (N : ℕ) :
    nativePNTSignedK2RecipInterval N 4 =
      (∑ dk ∈ nativePNTSignedK2FactorFourOddOddSet N,
        nativePNTSignedK2RecipFubiniAtom dk.1 dk.2) +
      ∑ mk ∈ nativePNTSignedK2FactorFourPrimeTwoParentSet N,
        (-(μ : ArithmeticFunction ℝ) mk.1 *
          ((Real.log (2 : ℝ)) ^ 2 +
            2 * Real.log (2 : ℝ) * Real.log (mk.1 : ℝ)) /
          (((mk.1 * 2) * mk.2 : ℕ) : ℝ)) := by
  rw [nativePNTSignedK2RecipInterval_four_eq_doubleShell,
    nativePNTSignedK2RecipDoubleShell_eq_pairMass,
    nativePNTSignedK2FactorFourPairMass_eq_oddOdd_add_primeTwo]

end RHLean.Analysis
