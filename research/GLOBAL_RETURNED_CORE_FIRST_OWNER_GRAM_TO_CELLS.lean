import Mathlib
import «research.GLOBAL_RETURNED_CORE_FIRST_OWNER_CELL_SUM»
import «research.COVARIANCE_RECIPROCAL_OWNER_CONGESTION»

/-!
# Actual AMP first-owner Gram equals the signed owner-cell sum

This file closes the finite Fubini gap between the unordered AMP Gram used by
`GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM` and the arithmetic p-free/p-divisible
cell orientation used by the signed cell telescope.

No estimate occurs here.  Zero Moebius sites are deleted exactly, and every
remaining unordered first-owner pair is oriented by the unique endpoint not
divisible by its owner prime.  Multiplication of the two real site weights is
unchanged by that orientation.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The nested positive-lag owner Gram is exactly the same sum on the standard
positive physical pair carrier.  The omitted zero endpoint contributes zero. -/
theorem lowOwnerZeroFrequencyFirstOwnerGram_eq_positivePairCarrier
    (R p : ℕ) :
    lowOwnerZeroFrequencyFirstOwnerGram R p =
      ∑ mn ∈ mertensPositivePhysicalPairCarrier (squareRootEndpoint R),
        if IsSquarefreePairFreshPrimeOwner p mn.1 mn.2 then
          lowOwnerZeroFrequencyMobiusSite R mn.1 *
            lowOwnerZeroFrequencyMobiusSite R mn.2
        else 0 := by
  classical
  have houter :
      Finset.Icc 1 (squareRootEndpoint R) =
        Finset.Ico 1 (squareRootEndpoint R + 1) := by
    ext n
    simp
    omega
  symm
  calc
    (∑ mn ∈ mertensPositivePhysicalPairCarrier (squareRootEndpoint R),
        if IsSquarefreePairFreshPrimeOwner p mn.1 mn.2 then
          lowOwnerZeroFrequencyMobiusSite R mn.1 *
            lowOwnerZeroFrequencyMobiusSite R mn.2
        else 0) =
      ∑ mn ∈ (Finset.Icc 1 (squareRootEndpoint R)).product
          (Finset.Icc 1 (squareRootEndpoint R)),
        if mn.1 < mn.2 then
          (if IsSquarefreePairFreshPrimeOwner p mn.1 mn.2 then
            lowOwnerZeroFrequencyMobiusSite R mn.1 *
              lowOwnerZeroFrequencyMobiusSite R mn.2
           else 0)
        else 0 := by
      unfold mertensPositivePhysicalPairCarrier
      rw [Finset.sum_filter]
    _ = ∑ m ∈ Finset.Icc 1 (squareRootEndpoint R),
        ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          if m < n then
            (if IsSquarefreePairFreshPrimeOwner p m n then
              lowOwnerZeroFrequencyMobiusSite R m *
                lowOwnerZeroFrequencyMobiusSite R n
             else 0)
          else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Icc 1 (squareRootEndpoint R))
          (t := Finset.Icc 1 (squareRootEndpoint R))
          (f := fun mn : ℕ × ℕ =>
            if mn.1 < mn.2 then
              (if IsSquarefreePairFreshPrimeOwner p mn.1 mn.2 then
                lowOwnerZeroFrequencyMobiusSite R mn.1 *
                  lowOwnerZeroFrequencyMobiusSite R mn.2
               else 0)
            else 0))
    _ = ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        ∑ m ∈ Finset.Icc 1 (squareRootEndpoint R),
          if m < n then
            (if IsSquarefreePairFreshPrimeOwner p m n then
              lowOwnerZeroFrequencyMobiusSite R m *
                lowOwnerZeroFrequencyMobiusSite R n
             else 0)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Ico 1 (squareRootEndpoint R + 1),
        ∑ m ∈ Finset.Ico 1 n,
          if IsSquarefreePairFreshPrimeOwner p m n then
            lowOwnerZeroFrequencyMobiusSite R m *
              lowOwnerZeroFrequencyMobiusSite R n
          else 0 := by
      rw [← houter]
      apply Finset.sum_congr rfl
      intro n hn
      have hnX : n ≤ squareRootEndpoint R := (Finset.mem_Icc.mp hn).2
      have hfilter :
          (Finset.Icc 1 (squareRootEndpoint R)).filter (fun m => m < n) =
            Finset.Ico 1 n := by
        ext m
        simp
        omega
      rw [← Finset.sum_filter, hfilter]
    _ = ∑ n ∈ Finset.Ico 1 (squareRootEndpoint R + 1),
        ∑ m ∈ Finset.Ico 0 n,
          if IsSquarefreePairFreshPrimeOwner p m n then
            lowOwnerZeroFrequencyMobiusSite R m *
              lowOwnerZeroFrequencyMobiusSite R n
          else 0 := by
      apply Finset.sum_congr rfl
      intro n _hn
      symm
      apply Finset.sum_subset
      · intro m hm
        have hdata := Finset.mem_Ico.mp hm
        exact Finset.mem_Ico.mpr ⟨by omega, hdata.2⟩
      · intro m hm0 hmnot
        have hmData := Finset.mem_Ico.mp hm0
        have hmzero : m = 0 := by
          by_contra hmne
          have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hmne
          exact hmnot (Finset.mem_Ico.mpr ⟨hm1, hmData.2⟩)
        subst m
        simp [lowOwnerZeroFrequencyMobiusSite_zero]
    _ = ∑ n ∈ Finset.Ico 0 (squareRootEndpoint R + 1),
        ∑ m ∈ Finset.Ico 0 n,
          if IsSquarefreePairFreshPrimeOwner p m n then
            lowOwnerZeroFrequencyMobiusSite R m *
              lowOwnerZeroFrequencyMobiusSite R n
          else 0 := by
      symm
      apply Finset.sum_subset
      · intro n hn
        have hdata := Finset.mem_Ico.mp hn
        exact Finset.mem_Ico.mpr ⟨by omega, hdata.2⟩
      · intro n hn0 hnnot
        have hnData := Finset.mem_Ico.mp hn0
        have hnzero : n = 0 := by
          by_contra hnne
          have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hnne
          exact hnnot (Finset.mem_Ico.mpr ⟨hn1, hnData.2⟩)
        subst n
        simp
    _ = lowOwnerZeroFrequencyFirstOwnerGram R p := by
      rfl

/-- Nonzero squarefree unordered pairs owned first by `p`. -/
def lowOwnerFirstOwnerUnorderedPairCarrier
    (R p : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerNonzeroMobiusCarrier R).product
      (lowOwnerNonzeroMobiusCarrier R)).filter fun mn =>
    mn.1 < mn.2 ∧ IsSquarefreePairFreshPrimeOwner p mn.1 mn.2

/-- Deleting zero-Moebius sites from the positive owner sum is exact. -/
theorem lowOwnerPositiveOwnerSum_eq_unorderedNonzeroCarrier
    (R p : ℕ) :
    (∑ mn ∈ mertensPositivePhysicalPairCarrier (squareRootEndpoint R),
      if IsSquarefreePairFreshPrimeOwner p mn.1 mn.2 then
        lowOwnerZeroFrequencyMobiusSite R mn.1 *
          lowOwnerZeroFrequencyMobiusSite R mn.2
      else 0) =
      ∑ mn ∈ lowOwnerFirstOwnerUnorderedPairCarrier R p,
        lowOwnerZeroFrequencyMobiusSite R mn.1 *
          lowOwnerZeroFrequencyMobiusSite R mn.2 := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro mn hmn
    rcases Finset.mem_filter.mp hmn with ⟨hprod, hdata⟩
    rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
    rcases Finset.mem_filter.mp hmCar with ⟨hmIcc, _hmMu⟩
    rcases Finset.mem_filter.mp hnCar with ⟨hnIcc, _hnMu⟩
    exact Finset.mem_filter.mpr
      ⟨mem_mertensPositivePhysicalPairCarrier.mpr
        ⟨(Finset.mem_Icc.mp hmIcc).1, (Finset.mem_Icc.mp hmIcc).2,
          (Finset.mem_Icc.mp hnIcc).1, (Finset.mem_Icc.mp hnIcc).2,
          hdata.1⟩,
        hdata.2⟩
  · intro mn hmnOwner hmnNot
    rcases Finset.mem_filter.mp hmnOwner with ⟨hphys, howner⟩
    rcases mem_mertensPositivePhysicalPairCarrier.mp hphys with
      ⟨hm1, hmX, hn1, hnX, hmnlt⟩
    by_cases hmMu : realMoebiusStep mn.1 = 0
    · simp [lowOwnerZeroFrequencyMobiusSite, hmMu]
    · by_cases hnMu : realMoebiusStep mn.2 = 0
      · simp [lowOwnerZeroFrequencyMobiusSite, hnMu]
      · exfalso
        apply hmnNot
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ⟨hmnlt, howner⟩⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hm1, hmX⟩, hmMu⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hn1, hnX⟩, hnMu⟩

/-- Arithmetic orientation: put the p-free endpoint first. -/
def lowOwnerFirstOwnerArithmeticOrient
    (p : ℕ) (mn : ℕ × ℕ) : ℕ × ℕ :=
  if p ∣ mn.1 then (mn.2, mn.1) else mn

/-- Every unordered nonzero first-owner pair lands in the p-free/p-divisible
oriented carrier. -/
theorem lowOwnerFirstOwnerArithmeticOrient_mem
    {R p : ℕ} (hp : p.Prime) {mn : ℕ × ℕ}
    (hmn : mn ∈ lowOwnerFirstOwnerUnorderedPairCarrier R p) :
    lowOwnerFirstOwnerArithmeticOrient p mn ∈
      lowOwnerFirstOwnerOrientedCrossPairCarrier R p := by
  rcases Finset.mem_filter.mp hmn with ⟨hprod, hdata⟩
  rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
  have hcell :=
    (isSquarefreePairFreshPrimeOwner_iff_sameLowerSignature_dvdXor
      hp hmCar hnCar (ne_of_lt hdata.1)).mp hdata.2
  by_cases hpm : p ∣ mn.1
  · have hpn : ¬ p ∣ mn.2 := by
      rcases hcell.2 with h | h
      · exact h.2
      · exact False.elim (h.2 hpm)
    simp [lowOwnerFirstOwnerArithmeticOrient, hpm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hnCar, hmCar⟩,
        ⟨hcell.1.symm, hpn, hpm⟩⟩
  · have hpn : p ∣ mn.2 := by
      rcases hcell.2 with h | h
      · exact False.elim (hpm h.1)
      · exact h.1
    simp [lowOwnerFirstOwnerArithmeticOrient, hpm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmCar, hnCar⟩,
        ⟨hcell.1, hpm, hpn⟩⟩

/-- Sorting an arithmetically oriented unordered pair recovers the original
positive-lag pair. -/
theorem covarianceOrderedPair_arithmeticOrient_eq
    {R p : ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈ lowOwnerFirstOwnerUnorderedPairCarrier R p) :
    covarianceOrderedPair
        (lowOwnerFirstOwnerArithmeticOrient p mn).1
        (lowOwnerFirstOwnerArithmeticOrient p mn).2 = mn := by
  have hlt := (Finset.mem_filter.mp hmn).2.1
  by_cases hpm : p ∣ mn.1
  · rw [lowOwnerFirstOwnerArithmeticOrient]
    simp only [if_pos hpm]
    rw [covarianceOrderedPair_comm]
    exact covarianceOrderedPair_eq_of_lt hlt
  · rw [lowOwnerFirstOwnerArithmeticOrient]
    simp only [if_neg hpm]
    exact covarianceOrderedPair_eq_of_lt hlt

/-- Every p-free/p-divisible oriented pair has a unique positive-lag preimage. -/
theorem lowOwnerFirstOwnerOrientedCrossPair_has_unorderedPreimage
    {R p : ℕ} (hp : p.Prime) {ab : ℕ × ℕ}
    (hab : ab ∈ lowOwnerFirstOwnerOrientedCrossPairCarrier R p) :
    ∃ mn ∈ lowOwnerFirstOwnerUnorderedPairCarrier R p,
      lowOwnerFirstOwnerArithmeticOrient p mn = ab := by
  rcases Finset.mem_filter.mp hab with ⟨hprod, hdata⟩
  rcases Finset.mem_product.mp hprod with ⟨haCar, hbCar⟩
  have habNe : ab.1 ≠ ab.2 := by
    intro heq
    apply hdata.2.1
    rw [heq]
    exact hdata.2.2
  by_cases hlt : ab.1 < ab.2
  · refine ⟨ab, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨hprod, ⟨hlt, ?_⟩⟩
      exact (isSquarefreePairFreshPrimeOwner_iff_sameLowerSignature_dvdXor
        hp haCar hbCar (ne_of_lt hlt)).mpr
          ⟨hdata.1, Or.inr ⟨hdata.2.2, hdata.2.1⟩⟩
    · simp [lowOwnerFirstOwnerArithmeticOrient, hdata.2.1]
  · have hrev : ab.2 < ab.1 := by omega
    let mn : ℕ × ℕ := (ab.2, ab.1)
    refine ⟨mn, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hbCar, haCar⟩, ⟨hrev, ?_⟩⟩
      exact (isSquarefreePairFreshPrimeOwner_iff_sameLowerSignature_dvdXor
        hp hbCar haCar (ne_of_lt hrev)).mpr
          ⟨hdata.1.symm, Or.inl ⟨hdata.2.2, hdata.2.1⟩⟩
    · dsimp [mn, lowOwnerFirstOwnerArithmeticOrient]
      simp [hdata.2.2]

/-- Arithmetic orientation preserves the signed pair weight exactly. -/
theorem lowOwnerFirstOwnerArithmeticOrient_pairWeight
    (R p : ℕ) (mn : ℕ × ℕ) :
    lowOwnerZeroFrequencyMobiusSite R
        (lowOwnerFirstOwnerArithmeticOrient p mn).1 *
      lowOwnerZeroFrequencyMobiusSite R
        (lowOwnerFirstOwnerArithmeticOrient p mn).2 =
      lowOwnerZeroFrequencyMobiusSite R mn.1 *
        lowOwnerZeroFrequencyMobiusSite R mn.2 := by
  by_cases hpm : p ∣ mn.1
  · simp [lowOwnerFirstOwnerArithmeticOrient, hpm, mul_comm]
  · simp [lowOwnerFirstOwnerArithmeticOrient, hpm]

/-- The unordered actual first-owner carrier and the arithmetic-oriented cell
carrier have identical signed mass. -/
theorem sum_lowOwnerFirstOwnerUnorderedPairCarrier_eq_orientedCrossPairs
    {R p : ℕ} (hp : p.Prime) :
    (∑ mn ∈ lowOwnerFirstOwnerUnorderedPairCarrier R p,
      lowOwnerZeroFrequencyMobiusSite R mn.1 *
        lowOwnerZeroFrequencyMobiusSite R mn.2) =
      ∑ ab ∈ lowOwnerFirstOwnerOrientedCrossPairCarrier R p,
        lowOwnerZeroFrequencyMobiusSite R ab.1 *
          lowOwnerZeroFrequencyMobiusSite R ab.2 := by
  refine Finset.sum_bij
    (fun mn _hmn => lowOwnerFirstOwnerArithmeticOrient p mn)
    (fun mn hmn => lowOwnerFirstOwnerArithmeticOrient_mem hp hmn)
    ?_ ?_ ?_
  · intro mn hmn uv huv heq
    calc
      mn = covarianceOrderedPair
          (lowOwnerFirstOwnerArithmeticOrient p mn).1
          (lowOwnerFirstOwnerArithmeticOrient p mn).2 :=
        (covarianceOrderedPair_arithmeticOrient_eq hmn).symm
      _ = covarianceOrderedPair
          (lowOwnerFirstOwnerArithmeticOrient p uv).1
          (lowOwnerFirstOwnerArithmeticOrient p uv).2 := by rw [heq]
      _ = uv := covarianceOrderedPair_arithmeticOrient_eq huv
  · intro ab hab
    exact lowOwnerFirstOwnerOrientedCrossPair_has_unorderedPreimage hp hab
  · intro mn _hmn
    exact lowOwnerFirstOwnerArithmeticOrient_pairWeight R p mn

/-- **Exact final finite Fubini.**  For a genuine prime owner, the actual AMP
first-owner Gram is exactly the sum of the signed lower-signature cell Grams.
This is the bridge needed to apply the complete-cell energy telescope globally. -/
theorem lowOwnerZeroFrequencyFirstOwnerGram_eq_sum_cells
    {R p : ℕ} (hp : p.Prime) :
    lowOwnerZeroFrequencyFirstOwnerGram R p =
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerCellGram R p sig := by
  rw [lowOwnerZeroFrequencyFirstOwnerGram_eq_positivePairCarrier,
    lowOwnerPositiveOwnerSum_eq_unorderedNonzeroCarrier,
    sum_lowOwnerFirstOwnerUnorderedPairCarrier_eq_orientedCrossPairs hp,
    ← sum_lowOwnerFirstOwnerCellGram_eq_orientedCrossPairs]

end RHLean.Proof
