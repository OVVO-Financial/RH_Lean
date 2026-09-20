import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_PHYSICAL_FRAME_BRIDGE»
import «research.GLOBAL_RETURNED_CORE_STOKES_TWO_STEP_BOUNDARY_NORMAL_FORM»

/-!
# Exceptional Stokes terminal frame closure

The #758/#759 terminal support is only the two largest first-owner primes.
The maximal owner is already nonpositive.  The second-largest owner has one
remaining top-prime coordinate; top-half orbit collapse reduces its complete
interior to the single toggle orbit {1,t}.  Evaluating the two Dirichlet
coordinates there gives a uniform terminal upper bound 4, hence unit frame
domination from the existing R^2/18 frame diagonal.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem one_mem_lowOwnerStokesSecondPrime_emptyBase
    {R : ℕ} (hR : 56 ≤ R) :
    1 ∈ lowOwnerFirstOwnerBaseFiber
      R (lowOwnerStokesSecondPrime R hR) ∅ := by
  let s := lowOwnerStokesSecondPrime R hR
  have hsPrime : s.Prime := by
    simpa [s] using lowOwnerStokesSecondPrime_prime hR
  have hX1 : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 2 ≤ R ^ 2 := by nlinarith
    omega
  unfold lowOwnerFirstOwnerBaseFiber
  apply Finset.mem_filter.mpr
  constructor
  · unfold lowOwnerNonzeroMobiusCarrier
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨by norm_num, hX1⟩
    · norm_num [RHLean.Analysis.realMoebiusStep]
  · constructor
    · simp [squarefreeLowerPrimeSignature, squarefreePrimeFace]
    · intro hs1
      exact hsPrime.ne_one (Nat.dvd_one.mp hs1)

private theorem top_mem_lowOwnerStokesSecondPrime_emptyBase
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesTopPrime R hR ∈
      lowOwnerFirstOwnerBaseFiber
        R (lowOwnerStokesSecondPrime R hR) ∅ := by
  let s := lowOwnerStokesSecondPrime R hR
  let t := lowOwnerStokesTopPrime R hR
  have hsPrime : s.Prime := by
    simpa [s] using lowOwnerStokesSecondPrime_prime hR
  have htPrime : t.Prime := by
    simpa [t] using lowOwnerStokesTopPrime_prime hR
  have hst : s < t := by
    simpa [s, t] using lowOwnerStokesSecondPrime_lt_topPrime hR
  have htMem : t ∈ primesUpTo (squareRootEndpoint R) := by
    simpa [t] using lowOwnerStokesTopPrime_mem hR
  have htX : t ≤ squareRootEndpoint R :=
    (mem_primesUpTo.mp htMem).2
  have hsig : squarefreeLowerPrimeSignature s t = ∅ := by
    have h :=
      squarefreeLowerPrimeSignature_mul_larger_prime
        (p := s) (r := t) (a := 1) htPrime hst (by norm_num)
    simpa [squarefreeLowerPrimeSignature, squarefreePrimeFace] using h
  have hsNotDvd : ¬ s ∣ t := by
    intro hdiv
    have heq : s = t :=
      (Nat.prime_dvd_prime_iff_eq hsPrime htPrime).mp hdiv
    exact (ne_of_lt hst) heq
  unfold lowOwnerFirstOwnerBaseFiber
  apply Finset.mem_filter.mpr
  constructor
  · unfold lowOwnerNonzeroMobiusCarrier
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨htPrime.one_le, htX⟩
    · unfold RHLean.Analysis.realMoebiusStep
      rw [ArithmeticFunction.moebius_apply_prime htPrime]
      norm_num
  · exact ⟨hsig, hsNotDvd⟩

private theorem lowOwnerStokesSecondPrime_topInterior_eq_pair
    {R : ℕ} (hR : 56 ≤ R) :
    primeInteriorPart
        (lowOwnerStokesTopPrime R hR)
        (lowOwnerFirstOwnerBaseFiber
          R (lowOwnerStokesSecondPrime R hR) ∅) =
      ({1, lowOwnerStokesTopPrime R hR} : Finset ℕ) := by
  let s := lowOwnerStokesSecondPrime R hR
  let t := lowOwnerStokesTopPrime R hR
  have htPrime : t.Prime := by
    simpa [t] using lowOwnerStokesTopPrime_prime hR
  have htTop : squareRootEndpoint R / 2 < t := by
    simpa [t] using squareRootEndpoint_half_lt_lowOwnerStokesTopPrime hR
  apply Finset.Subset.antisymm
  · simpa [s, t] using
      (lowOwnerFirstOwner_topPrimeInterior_subset_one_insert_prime
        (R := R) (p := s) (q := t) (sig := ∅) htPrime htTop)
  · intro n hn
    have h1Base :
        1 ∈ lowOwnerFirstOwnerBaseFiber R s ∅ := by
      simpa [s] using one_mem_lowOwnerStokesSecondPrime_emptyBase hR
    have htBase :
        t ∈ lowOwnerFirstOwnerBaseFiber R s ∅ := by
      simpa [s, t] using top_mem_lowOwnerStokesSecondPrime_emptyBase hR
    have htNotDvdOne : ¬ t ∣ 1 := by
      intro hdiv
      exact htPrime.ne_one (Nat.dvd_one.mp hdiv)
    have htoggleOne : primeCarrierToggle t 1 = t := by
      rw [primeCarrierToggle_of_not_dvd htNotDvdOne]
      simp
    have htSq : ¬ t ^ 2 ∣ t := by
      intro hdiv
      have hle : t ^ 2 ≤ t := Nat.le_of_dvd htPrime.pos hdiv
      nlinarith [htPrime.two_le]
    have htoggleTop : primeCarrierToggle t t = 1 := by
      rw [primeCarrierToggle_of_dvd (dvd_refl t) htSq]
      simp [htPrime.ne_zero]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact mem_primeInteriorPart.mpr ⟨h1Base, by simpa [htoggleOne] using htBase⟩
    · exact mem_primeInteriorPart.mpr ⟨htBase, by simpa [htoggleTop] using h1Base⟩

private theorem lowOwnerStokesSecondPrime_topInterior_eq_empty_of_sig_ne_empty
    {R : ℕ} (hR : 56 ≤ R) {sig : Finset ℕ} (hsig : sig ≠ ∅) :
    primeInteriorPart
        (lowOwnerStokesTopPrime R hR)
        (lowOwnerFirstOwnerBaseFiber
          R (lowOwnerStokesSecondPrime R hR) sig) = ∅ := by
  let s := lowOwnerStokesSecondPrime R hR
  let t := lowOwnerStokesTopPrime R hR
  have htPrime : t.Prime := by
    simpa [t] using lowOwnerStokesTopPrime_prime hR
  have hst : s < t := by
    simpa [s, t] using lowOwnerStokesSecondPrime_lt_topPrime hR
  have htTop : squareRootEndpoint R / 2 < t := by
    simpa [t] using squareRootEndpoint_half_lt_lowOwnerStokesTopPrime hR
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro n hn
  have hsub :=
    lowOwnerFirstOwner_topPrimeInterior_subset_one_insert_prime
      (R := R) (p := s) (q := t) (sig := sig) htPrime htTop hn
  rcases Finset.mem_insert.mp hsub with h1 | ht
  · subst n
    have hbase := (mem_primeInteriorPart.mp hn).1
    have hdata := (Finset.mem_filter.mp hbase).2.1
    have hone : squarefreeLowerPrimeSignature s 1 = ∅ := by
      simp [squarefreeLowerPrimeSignature, squarefreePrimeFace]
    rw [hone] at hdata
    exact hsig hdata.symm
  · have hnt : n = t := Finset.mem_singleton.mp ht
    subst n
    have hbase := (mem_primeInteriorPart.mp hn).1
    have hdata := (Finset.mem_filter.mp hbase).2.1
    have htopSig : squarefreeLowerPrimeSignature s t = ∅ := by
      have h :=
        squarefreeLowerPrimeSignature_mul_larger_prime
          (p := s) (r := t) (a := 1) htPrime hst (by norm_num)
      simpa [squarefreeLowerPrimeSignature, squarefreePrimeFace] using h
    rw [htopSig] at hdata
    exact hsig hdata.symm

private theorem lowOwnerStokesTopPrime_reciprocalDaughterWeight_eq_zero
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerReciprocalDaughterWeight R
      (lowOwnerStokesTopPrime R hR) = 0 := by
  let t := lowOwnerStokesTopPrime R hR
  have htTop : squareRootEndpoint R / 2 < t := by
    simpa [t] using squareRootEndpoint_half_lt_lowOwnerStokesTopPrime hR
  unfold lowOwnerReciprocalDaughterWeight
  apply Finset.sum_eq_zero
  intro q hq
  have hbase : q ∈ (primesUpTo (R - 1)).erase 2 :=
    (Finset.mem_sdiff.mp hq).1
  have hqPrime : q.Prime :=
    (mem_primesUpTo.mp (Finset.mem_erase.mp hbase).2).1
  have hqNeTwo : q ≠ 2 := (Finset.mem_erase.mp hbase).1
  have hqThree : 3 ≤ q := by
    have hqTwo := hqPrime.two_le
    omega
  have hden : 2 ≤ q * q := by nlinarith
  have hdiv :
      squareRootEndpoint R / (q * q) ≤ squareRootEndpoint R / 2 :=
    Nat.div_le_div_left hden (by norm_num)
  have hnot :
      ¬ t ≤ rawQ2ChildCutoff R q := by
    unfold rawQ2ChildCutoff
    omega
  simp [t, hnot]

private theorem lowOwnerStokesTopPrime_baseCoefficient_eq_one
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerDirichletBaseCoefficient R
      (lowOwnerStokesTopPrime R hR) = 1 := by
  let t := lowOwnerStokesTopPrime R hR
  have htMem : t ∈ primesUpTo (squareRootEndpoint R) := by
    simpa [t] using lowOwnerStokesTopPrime_mem hR
  have htX : t ≤ squareRootEndpoint R :=
    (mem_primesUpTo.mp htMem).2
  have htTop : squareRootEndpoint R / 2 < t := by
    simpa [t] using squareRootEndpoint_half_lt_lowOwnerStokesTopPrime hR
  have hRhalf : R ≤ squareRootEndpoint R / 2 :=
    root_le_half_squareRootEndpoint hR
  have hRt : R ≤ t := by omega
  have hqzero :
      lowOwnerReciprocalDaughterWeight R t = 0 := by
    simpa [t] using lowOwnerStokesTopPrime_reciprocalDaughterWeight_eq_zero hR
  unfold lowOwnerDirichletBaseCoefficient lowOwnerPhysicalDirichletWeight
  rw [if_pos htX]
  unfold lowOwnerZeroFrequencyMobiusWeight lowOwnerFarTailWeight
  rw [if_pos hRt, hqzero]
  norm_num

private theorem lowOwnerStokes_one_baseCoefficient_eq_reciprocal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerDirichletBaseCoefficient R 1 =
      lowOwnerReciprocalDaughterWeight R 1 := by
  have hX1 : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 2 ≤ R ^ 2 := by nlinarith
    omega
  have hR1 : ¬ R ≤ 1 := by omega
  unfold lowOwnerDirichletBaseCoefficient lowOwnerPhysicalDirichletWeight
  rw [if_pos hX1]
  unfold lowOwnerZeroFrequencyMobiusWeight lowOwnerFarTailWeight
  rw [if_neg hR1]
  ring

private theorem lowOwnerReciprocalDaughterWeight_antitone_at_one
    {R n : ℕ} (hn : 1 ≤ n) :
    lowOwnerReciprocalDaughterWeight R n ≤
      lowOwnerReciprocalDaughterWeight R 1 := by
  unfold lowOwnerReciprocalDaughterWeight
  apply Finset.sum_le_sum
  intro q hq
  have hbase : q ∈ (primesUpTo (R - 1)).erase 2 :=
    (Finset.mem_sdiff.mp hq).1
  have hqPrime : q.Prime :=
    (mem_primesUpTo.mp (Finset.mem_erase.mp hbase).2).1
  by_cases hnY : n ≤ rawQ2ChildCutoff R q
  · have h1Y : 1 ≤ rawQ2ChildCutoff R q := hn.trans hnY
    simp [hnY, h1Y]
  · by_cases h1Y : 1 ≤ rawQ2ChildCutoff R q
    · simp [hnY, h1Y]
      positivity
    · simp [hnY, h1Y]

private theorem lowOwnerStokesSecondPrime_baseCoefficient_le_one_add_H
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerDirichletBaseCoefficient R
        (lowOwnerStokesSecondPrime R hR) ≤
      1 + lowOwnerReciprocalDaughterWeight R 1 := by
  let s := lowOwnerStokesSecondPrime R hR
  have hsMem : s ∈ primesUpTo (squareRootEndpoint R) := by
    exact (Finset.mem_erase.mp (lowOwnerStokesSecondPrime_mem_erase hR)).2
  have hsX : s ≤ squareRootEndpoint R :=
    (mem_primesUpTo.mp hsMem).2
  have hsOne : 1 ≤ s :=
    (mem_primesUpTo.mp hsMem).1.one_le
  have hd :=
    lowOwnerReciprocalDaughterWeight_antitone_at_one
      (R := R) (n := s) hsOne
  unfold lowOwnerDirichletBaseCoefficient lowOwnerPhysicalDirichletWeight
  rw [if_pos hsX]
  unfold lowOwnerZeroFrequencyMobiusWeight lowOwnerFarTailWeight
  by_cases hRs : R ≤ s
  · rw [if_pos hRs]
    linarith
  · rw [if_neg hRs]
    linarith

private theorem lowOwnerStokesSecondPrime_returned_top_eq_zero
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerDirichletReturnedCoefficient R
      (lowOwnerStokesSecondPrime R hR)
      (lowOwnerStokesTopPrime R hR) = 0 := by
  let s := lowOwnerStokesSecondPrime R hR
  let t := lowOwnerStokesTopPrime R hR
  have hsPrime : s.Prime := by
    simpa [s] using lowOwnerStokesSecondPrime_prime hR
  have htTop : squareRootEndpoint R / 2 < t := by
    simpa [t] using squareRootEndpoint_half_lt_lowOwnerStokesTopPrime hR
  have hX2t : squareRootEndpoint R < 2 * t := by omega
  have h2st : 2 * t ≤ s * t := by
    exact Nat.mul_le_mul_right t hsPrime.two_le
  have hout : squareRootEndpoint R < s * t := hX2t.trans_le h2st
  unfold lowOwnerDirichletReturnedCoefficient lowOwnerPhysicalDirichletWeight
  rw [if_neg (Nat.not_le_of_lt hout)]

private theorem lowOwnerStokesSecondPrime_returned_one_eq_base_second
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerDirichletReturnedCoefficient R
        (lowOwnerStokesSecondPrime R hR) 1 =
      lowOwnerDirichletBaseCoefficient R
        (lowOwnerStokesSecondPrime R hR) := by
  simp [lowOwnerDirichletReturnedCoefficient,
    lowOwnerDirichletBaseCoefficient]

private theorem lowOwnerStokesSecondPrime_empty_baseDifferenceAmplitude
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesSignedAmplitude
        (primeInteriorPart (lowOwnerStokesTopPrime R hR)
          (lowOwnerFirstOwnerBaseFiber
            R (lowOwnerStokesSecondPrime R hR) ∅))
        (lowOwnerStokesToggleDifference
          (lowOwnerStokesTopPrime R hR)
          (lowOwnerDirichletBaseCoefficient R)) =
      2 * (lowOwnerReciprocalDaughterWeight R 1 - 1) := by
  let t := lowOwnerStokesTopPrime R hR
  have htPrime : t.Prime := by
    simpa [t] using lowOwnerStokesTopPrime_prime hR
  have htNotDvdOne : ¬ t ∣ 1 := by
    intro hdiv
    exact htPrime.ne_one (Nat.dvd_one.mp hdiv)
  have htSq : ¬ t ^ 2 ∣ t := by
    intro hdiv
    have hle : t ^ 2 ≤ t := Nat.le_of_dvd htPrime.pos hdiv
    nlinarith [htPrime.two_le]
  have htoggleOne : primeCarrierToggle t 1 = t := by
    rw [primeCarrierToggle_of_not_dvd htNotDvdOne]
    simp
  have htoggleTop : primeCarrierToggle t t = 1 := by
    rw [primeCarrierToggle_of_dvd (dvd_refl t) htSq]
    simp [htPrime.ne_zero]
  have hI := lowOwnerStokesSecondPrime_topInterior_eq_pair hR
  have hL1 := lowOwnerStokes_one_baseCoefficient_eq_reciprocal hR
  have hLt := lowOwnerStokesTopPrime_baseCoefficient_eq_one hR
  unfold lowOwnerStokesSignedAmplitude lowOwnerStokesToggleDifference
  rw [hI]
  have h1t : 1 ≠ t := by omega
  simp [t, h1t, htoggleOne, htoggleTop, hL1, hLt,
    othelloRealMoebius, ArithmeticFunction.moebius_apply_prime htPrime]
  ring

private theorem lowOwnerStokesSecondPrime_empty_returnedDifferenceAmplitude
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesSignedAmplitude
        (primeInteriorPart (lowOwnerStokesTopPrime R hR)
          (lowOwnerFirstOwnerBaseFiber
            R (lowOwnerStokesSecondPrime R hR) ∅))
        (lowOwnerStokesToggleDifference
          (lowOwnerStokesTopPrime R hR)
          (lowOwnerDirichletReturnedCoefficient
            R (lowOwnerStokesSecondPrime R hR))) =
      2 * lowOwnerDirichletBaseCoefficient R
        (lowOwnerStokesSecondPrime R hR) := by
  let t := lowOwnerStokesTopPrime R hR
  have htPrime : t.Prime := by
    simpa [t] using lowOwnerStokesTopPrime_prime hR
  have htNotDvdOne : ¬ t ∣ 1 := by
    intro hdiv
    exact htPrime.ne_one (Nat.dvd_one.mp hdiv)
  have htSq : ¬ t ^ 2 ∣ t := by
    intro hdiv
    have hle : t ^ 2 ≤ t := Nat.le_of_dvd htPrime.pos hdiv
    nlinarith [htPrime.two_le]
  have htoggleOne : primeCarrierToggle t 1 = t := by
    rw [primeCarrierToggle_of_not_dvd htNotDvdOne]
    simp
  have htoggleTop : primeCarrierToggle t t = 1 := by
    rw [primeCarrierToggle_of_dvd (dvd_refl t) htSq]
    simp [htPrime.ne_zero]
  have hI := lowOwnerStokesSecondPrime_topInterior_eq_pair hR
  have hJ1 := lowOwnerStokesSecondPrime_returned_one_eq_base_second hR
  have hJt := lowOwnerStokesSecondPrime_returned_top_eq_zero hR
  unfold lowOwnerStokesSignedAmplitude lowOwnerStokesToggleDifference
  rw [hI]
  have h1t : 1 ≠ t := by omega
  simp [t, h1t, htoggleOne, htoggleTop, hJ1, hJt,
    othelloRealMoebius, ArithmeticFunction.moebius_apply_prime htPrime]
  ring

private theorem lowOwnerStokesSecondPrime_terminal_eq_two_one_sub_H_mul_L
    {R : ℕ} (hR : 56 ≤ R) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet
        R (lowOwnerStokesSecondPrime R hR),
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary
        R (lowOwnerStokesSecondPrime R hR) sig) =
      2 * (1 - lowOwnerReciprocalDaughterWeight R 1) *
        lowOwnerDirichletBaseCoefficient R
          (lowOwnerStokesSecondPrime R hR) := by
  let s := lowOwnerStokesSecondPrime R hR
  let t := lowOwnerStokesTopPrime R hR
  have hsched :
      lowOwnerFirstOwnerCanonicalStokesSchedule R s = [t] := by
    simpa [s, t] using lowOwnerStokesSecondPrime_schedule_eq_single_top hR
  rw [sum_lowOwnerFirstOwnerTopTerminal_eq_neg_half_interiorDifferenceProduct_of_schedule_single
    hsched]
  have hEmptyMem :
      (∅ : Finset ℕ) ∈ lowOwnerFirstOwnerSignatureSet R s := by
    unfold lowOwnerFirstOwnerSignatureSet
    have h1Base :
        1 ∈ lowOwnerFirstOwnerBaseFiber R s ∅ := by
      simpa [s] using one_mem_lowOwnerStokesSecondPrime_emptyBase hR
    have h1Car := (Finset.mem_filter.mp h1Base).1
    refine Finset.mem_image.mpr ⟨1, h1Car, ?_⟩
    simp [squarefreeLowerPrimeSignature, squarefreePrimeFace]
  rw [Finset.sum_eq_single (∅ : Finset ℕ)]
  · have hA :=
      lowOwnerStokesSecondPrime_empty_baseDifferenceAmplitude hR
    have hB :=
      lowOwnerStokesSecondPrime_empty_returnedDifferenceAmplitude hR
    rw [hA, hB]
    ring
  · intro sig hsigMem hsigNe
    have hI :=
      lowOwnerStokesSecondPrime_topInterior_eq_empty_of_sig_ne_empty
        hR hsigNe
    rw [hI]
    simp [lowOwnerStokesSignedAmplitude]
  · exact hEmptyMem

theorem lowOwnerStokesSecondPrime_terminal_le_four
    {R : ℕ} (hR : 56 ≤ R) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet
        R (lowOwnerStokesSecondPrime R hR),
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary
        R (lowOwnerStokesSecondPrime R hR) sig) ≤ 4 := by
  rw [lowOwnerStokesSecondPrime_terminal_eq_two_one_sub_H_mul_L hR]
  let H := lowOwnerReciprocalDaughterWeight R 1
  let L := lowOwnerDirichletBaseCoefficient R
    (lowOwnerStokesSecondPrime R hR)
  have hH : 0 ≤ H := by
    dsimp [H]
    exact lowOwnerReciprocalDaughterWeight_nonneg R 1
  have hL : 0 ≤ L := by
    dsimp [L, lowOwnerDirichletBaseCoefficient]
    exact lowOwnerPhysicalDirichletWeight_nonneg R
      (lowOwnerStokesSecondPrime R hR)
  have hLup : L ≤ 1 + H := by
    dsimp [L, H]
    exact lowOwnerStokesSecondPrime_baseCoefficient_le_one_add_H hR
  by_cases hHone : 1 ≤ H
  · have hnonpos : 2 * (1 - H) * L ≤ 0 := by
      have hdiff : 1 - H ≤ 0 := by linarith
      nlinarith
    linarith
  · have hHlt : H < 1 := lt_of_not_ge hHone
    have hLlt : L < 2 := by linarith
    nlinarith

private theorem lowOwnerStokesTopTerminalOwnerSet_eq_top_two
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesTopTerminalOwnerSet R =
      ({lowOwnerStokesTopPrime R hR,
        lowOwnerStokesSecondPrime R hR} : Finset ℕ) := by
  apply Finset.Subset.antisymm
  · exact lowOwnerStokesTopTerminalOwnerSet_subset_top_two hR
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with htop | hsecond
    · subst p
      unfold lowOwnerStokesTopTerminalOwnerSet
      apply Finset.mem_filter.mpr
      exact ⟨lowOwnerStokesTopPrime_mem hR, by
        rw [lowOwnerStokesTopPrime_schedule_eq_nil hR]
        simp⟩
    · subst p
      unfold lowOwnerStokesTopTerminalOwnerSet
      apply Finset.mem_filter.mpr
      have hsMem :=
        (Finset.mem_erase.mp (lowOwnerStokesSecondPrime_mem_erase hR)).2
      exact ⟨hsMem, by
        rw [lowOwnerStokesSecondPrime_schedule_eq_single_top hR]
        simp⟩

theorem lowOwnerCanonicalSignedStokesTopTerminalBoundary_le_four
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesTopTerminalBoundary R ≤ 4 := by
  rw [lowOwnerCanonicalSignedStokesTopTerminalBoundary_eq_terminalOwnerSum]
  rw [lowOwnerStokesTopTerminalOwnerSet_eq_top_two hR]
  have hne :
      lowOwnerStokesTopPrime R hR ≠
        lowOwnerStokesSecondPrime R hR := by
    exact ne_of_gt (lowOwnerStokesSecondPrime_lt_topPrime hR)
  simp only [Finset.sum_insert, Finset.mem_singleton, hne, not_false_eq_true,
    Finset.sum_singleton]
  have htop := sum_lowOwnerStokesTopPrimeTerminal_nonpos hR
  have hsecond := lowOwnerStokesSecondPrime_terminal_le_four hR
  linarith

/-- **Exceptional terminal sector closed.**  The zero-owner contribution is
nonpositive and the one-owner contribution is at most 4.  Since R>=56 and the
natural odd-prime frame is at least R^2/18, the entire exceptional terminal is
dominated with unit frame constant. -/
theorem lowOwnerStokesExceptionalTerminalFrameDomination_one :
    LowOwnerStokesExceptionalTerminalFrameDomination 1 := by
  intro R hR
  rw [← lowOwnerCanonicalSignedStokesTopTerminalBoundary_eq_terminalOwnerSum]
  have hterm := lowOwnerCanonicalSignedStokesTopTerminalBoundary_le_four hR
  have hframe :=
    root_sq_over_eighteen_le_lowOwnerStokesOddPrimePeriodFrameMajorant hR
  have hfour :
      (4 : ℝ) ≤ (R : ℝ) ^ 2 / 18 := by
    have hRreal : (56 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith
  calc
    lowOwnerCanonicalSignedStokesTopTerminalBoundary R ≤ 4 := hterm
    _ ≤ (R : ℝ) ^ 2 / 18 := hfour
    _ ≤ lowOwnerStokesOddPrimePeriodFrameMajorant R hR := hframe
    _ = 1 * lowOwnerStokesOddPrimePeriodFrameMajorant R hR := by ring

end RHLean.Proof
