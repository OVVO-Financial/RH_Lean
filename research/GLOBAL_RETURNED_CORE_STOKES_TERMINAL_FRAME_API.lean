import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_TWO_STEP_BOUNDARY_NORMAL_FORM»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_RANK_BASE»
import «research.GLOBAL_RETURNED_CORE_STOKES_CLIP_AMPLITUDE_FACTOR»
import «research.GLOBAL_RETURNED_CORE_STOKES_NATURAL_PERIOD_WHEEL»
import «research.STOKES_ENDPOINT_MAX_ALIGNMENT_FRAME»

/-!
# Clean exceptional Stokes terminal frame API

This file isolates the zero/one-owner terminal geometry from the experimental
physical-frame bridge.  It provides only the stable ingredients needed by the
terminal closure:

* the natural odd-prime frame and its root-scale lower bound;
* the largest and second-largest physical first-owner primes;
* the exact one-coordinate schedule at the second-largest owner;
* the top-half collapse of the corresponding physical interior;
* support of the terminal owner set on the top two owners.

No clip estimate and no RH conclusion is imported here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof
namespace StokesTerminalFrame

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-! ## Natural prime-period frame -/

def oddPrimePeriodSet (R : ℕ) : Finset ℕ :=
  (lowOwnerStokesWheelPrimes R).erase 2

theorem oddPrimePeriodSet_prime
    {R p : ℕ} (hp : p ∈ oddPrimePeriodSet R) :
    p.Prime := by
  exact lowOwnerStokesWheelPrimes_prime (Finset.mem_erase.mp hp).2

theorem oddPrimePeriodSet_dvd_naturalModulus
    {R p : ℕ} (hR : 56 ≤ R)
    (hp : p ∈ oddPrimePeriodSet R) :
    p ∣ (lowOwnerStokesNaturalWheelSystem R hR).modulus := by
  have hpWheel : p ∈ lowOwnerStokesWheelPrimes R :=
    (Finset.mem_erase.mp hp).2
  exact dvd_trans (dvd_pow_self p (by norm_num))
    (prime_sq_dvd_lowOwnerStokesNaturalWheelModulus hR hpWheel)

def frameMajorant
    (R : ℕ) (hR : 56 ≤ R) : ℝ :=
  primePeriodReciprocalFrameMajorant
    (lowOwnerStokesNaturalWheelSystem R hR)
    (squareRootEndpoint R)
    (oddPrimePeriodSet R)

theorem three_mem_oddPrimePeriodSet
    {R : ℕ} (hR : 56 ≤ R) :
    3 ∈ oddPrimePeriodSet R := by
  have hcut : 3 ≤ Nat.sqrt (squareRootEndpoint R) := by
    have h5 := five_le_lowOwnerStokesWheelCutoff hR
    omega
  have h3wheel : 3 ∈ lowOwnerStokesWheelPrimes R := by
    unfold lowOwnerStokesWheelPrimes
    exact mem_primesUpTo.mpr ⟨by norm_num, hcut⟩
  unfold oddPrimePeriodSet
  exact Finset.mem_erase.mpr ⟨by norm_num, h3wheel⟩

theorem one_ninth_le_reciprocalSquareMass
    {R : ℕ} (hR : 56 ≤ R) :
    (1 / 9 : ℝ) ≤
      ∑ p ∈ oddPrimePeriodSet R,
        ((1 : ℝ) / (p : ℝ)) ^ 2 := by
  have h3 := three_mem_oddPrimePeriodSet hR
  have hsplit := Finset.sum_erase_add
    (s := oddPrimePeriodSet R)
    (f := fun p => ((1 : ℝ) / (p : ℝ)) ^ 2) h3
  have hrest :
      0 ≤ ∑ p ∈ (oddPrimePeriodSet R).erase 3,
        (((p : ℝ) ^ 2)⁻¹) := by
    positivity
  norm_num at hsplit ⊢
  linarith

theorem root_sq_over_eighteen_le_frameMajorant
    {R : ℕ} (hR : 56 ≤ R) :
    (R : ℝ) ^ 2 / 18 ≤ frameMajorant R hR := by
  let W := lowOwnerStokesNaturalWheelSystem R hR
  let X := squareRootEndpoint R
  let S := oddPrimePeriodSet R
  have hmass :
      (1 / 9 : ℝ) ≤
        ∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2 := by
    simpa [S] using one_ninth_le_reciprocalSquareMass hR
  have hoff :
      0 ≤ primePeriodReciprocalOffDiagonalMajorant W X S := by
    unfold primePeriodReciprocalOffDiagonalMajorant
    apply Finset.sum_nonneg
    intro p hp
    apply Finset.sum_nonneg
    intro q hq
    positivity
  have hdiag :
      (X : ℝ) / 9 ≤ primePeriodReciprocalDiagonalMajorant X S := by
    unfold primePeriodReciprocalDiagonalMajorant
    have hX0 : 0 ≤ (X : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmass hX0
    nlinarith
  have hframeX :
      (X : ℝ) / 9 ≤
        primePeriodReciprocalFrameMajorant W X S := by
    unfold primePeriodReciprocalFrameMajorant
    linarith
  have hnat : R ^ 2 ≤ 2 * squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 2 ≤ R ^ 2 := by nlinarith
    omega
  have hreal :
      (R : ℝ) ^ 2 ≤ 2 * (squareRootEndpoint R : ℝ) := by
    exact_mod_cast hnat
  change (R : ℝ) ^ 2 / 18 ≤
    primePeriodReciprocalFrameMajorant W X S
  have hXreal : (X : ℝ) = (squareRootEndpoint R : ℝ) := by rfl
  rw [hXreal] at hframeX
  nlinarith

/-! ## Top two physical owners -/

def topTerminalOwnerSet (R : ℕ) : Finset ℕ :=
  (primesUpTo (squareRootEndpoint R)).filter fun p =>
    (lowOwnerFirstOwnerCanonicalStokesSchedule R p).length ≤ 1

private theorem fullPrimeSet_nonempty
    {R : ℕ} (hR : 56 ≤ R) :
    (primesUpTo (squareRootEndpoint R)).Nonempty := by
  refine ⟨2, mem_primesUpTo.mpr ⟨Nat.prime_two, ?_⟩⟩
  unfold squareRootEndpoint
  have hsq : 3 ≤ R ^ 2 := by nlinarith
  omega

def topPrime (R : ℕ) (hR : 56 ≤ R) : ℕ :=
  (primesUpTo (squareRootEndpoint R)).max'
    (fullPrimeSet_nonempty hR)

theorem topPrime_mem
    {R : ℕ} (hR : 56 ≤ R) :
    topPrime R hR ∈ primesUpTo (squareRootEndpoint R) := by
  exact Finset.max'_mem _ _

private theorem eraseTop_nonempty
    {R : ℕ} (hR : 56 ≤ R) :
    ((primesUpTo (squareRootEndpoint R)).erase
      (topPrime R hR)).Nonempty := by
  have h5 : 5 ∈ primesUpTo (squareRootEndpoint R) := by
    apply mem_primesUpTo.mpr
    constructor
    · norm_num
    · unfold squareRootEndpoint
      have hsq : 6 ≤ R ^ 2 := by nlinarith
      omega
  have htop5 :
      5 ≤ topPrime R hR :=
    Finset.le_max' _ 5 h5
  have h2 : 2 ∈ primesUpTo (squareRootEndpoint R) := by
    exact mem_primesUpTo.mpr ⟨Nat.prime_two, by
      unfold squareRootEndpoint
      have hsq : 3 ≤ R ^ 2 := by nlinarith
      omega⟩
  have hne : 2 ≠ topPrime R hR := by omega
  exact ⟨2, Finset.mem_erase.mpr ⟨hne, h2⟩⟩

def secondPrime (R : ℕ) (hR : 56 ≤ R) : ℕ :=
  ((primesUpTo (squareRootEndpoint R)).erase
      (topPrime R hR)).max'
    (eraseTop_nonempty hR)

theorem secondPrime_mem_erase
    {R : ℕ} (hR : 56 ≤ R) :
    secondPrime R hR ∈
      (primesUpTo (squareRootEndpoint R)).erase
        (topPrime R hR) := by
  exact Finset.max'_mem _ _

theorem secondPrime_prime
    {R : ℕ} (hR : 56 ≤ R) :
    (secondPrime R hR).Prime := by
  have hmem := (Finset.mem_erase.mp
    (secondPrime_mem_erase hR)).2
  exact (mem_primesUpTo.mp hmem).1

theorem secondPrime_lt_topPrime
    {R : ℕ} (hR : 56 ≤ R) :
    secondPrime R hR < topPrime R hR := by
  have hsErase := secondPrime_mem_erase hR
  have hsNe :
      secondPrime R hR ≠ topPrime R hR :=
    (Finset.mem_erase.mp hsErase).1
  have hsMem := (Finset.mem_erase.mp hsErase).2
  have hsLe :
      secondPrime R hR ≤ topPrime R hR :=
    Finset.le_max' _ _ hsMem
  omega

theorem secondPrime_schedule_eq_single_top
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerFirstOwnerCanonicalStokesSchedule
        R (secondPrime R hR) =
      [topPrime R hR] := by
  let s := secondPrime R hR
  let t := topPrime R hR
  have hst : s < t := by
    simpa [s, t] using secondPrime_lt_topPrime hR
  have htMem : t ∈ primesUpTo (squareRootEndpoint R) := by
    simpa [t] using topPrime_mem hR
  have htFull : t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2 htMem
  have htSched :
      t ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R s := by
    simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using
      (show t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ s < t
        from ⟨htFull, hst⟩)
  have huniq :
      ∀ q ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R s, q = t := by
    intro q hq
    have hqData :
        q ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ s < q := by
      simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using hq
    have hqMem : q ∈ primesUpTo (squareRootEndpoint R) := by
      unfold squareRootCanonicalRoughDescendingPrimeSchedule at hqData
      exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).1 hqData.1
    by_contra hqt
    have hqErase :
        q ∈ (primesUpTo (squareRootEndpoint R)).erase t :=
      Finset.mem_erase.mpr ⟨hqt, hqMem⟩
    have hqLeS : q ≤ s := by
      simpa [s, t] using
        Finset.le_max'
          ((primesUpTo (squareRootEndpoint R)).erase t) q hqErase
    omega
  have hnodup :=
    lowOwnerFirstOwnerCanonicalStokesSchedule_nodup R s
  generalize hsched : lowOwnerFirstOwnerCanonicalStokesSchedule R s = ps at htSched huniq hnodup
  cases ps with
  | nil =>
      simp at htSched
  | cons a tail =>
      have ha : a = t := huniq a (by simp)
      subst a
      cases tail with
      | nil =>
          rfl
      | cons b rest =>
          have hb : b = t := huniq b (by simp)
          subst b
          simp at hnodup

theorem topPrime_prime
    {R : ℕ} (hR : 56 ≤ R) :
    (topPrime R hR).Prime := by
  exact (mem_primesUpTo.mp (topPrime_mem hR)).1

theorem endpoint_half_lt_topPrime
    {R : ℕ} (hR : 56 ≤ R) :
    squareRootEndpoint R / 2 < topPrime R hR := by
  have hX : 3 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 4 ≤ R ^ 2 := by nlinarith
    omega
  have hhalf : squareRootEndpoint R / 2 ≠ 0 := by omega
  obtain ⟨q, hqPrime, hqLow, hqHigh⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (squareRootEndpoint R / 2) hhalf
  have hqX : q ≤ squareRootEndpoint R := by omega
  have hqMem : q ∈ primesUpTo (squareRootEndpoint R) :=
    mem_primesUpTo.mpr ⟨hqPrime, hqX⟩
  have hqTop :
      q ≤ topPrime R hR :=
    Finset.le_max' _ q hqMem
  omega

theorem topPrime_schedule_eq_nil
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerFirstOwnerCanonicalStokesSchedule
        R (topPrime R hR) = [] := by
  unfold lowOwnerFirstOwnerCanonicalStokesSchedule
  apply List.filter_eq_nil_iff.2
  intro q hq
  have hqMem : q ∈ primesUpTo (squareRootEndpoint R) := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule at hq
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).1 hq
  have hqLe :
      q ≤ topPrime R hR :=
    Finset.le_max' _ q hqMem
  simpa only [decide_eq_true_eq] using (Nat.not_lt_of_ge hqLe)

theorem topTerminalOwnerSet_subset_top_two
    {R : ℕ} (hR : 56 ≤ R) :
    topTerminalOwnerSet R ⊆
      ({topPrime R hR, secondPrime R hR} : Finset ℕ) := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpS, hlen⟩
  let t := topPrime R hR
  let s := secondPrime R hR
  by_cases hpt : p = t
  · simp [hpt, t]
  by_cases hps : p = s
  · simp [hps, s]
  exfalso
  have htS : t ∈ primesUpTo (squareRootEndpoint R) := by
    simpa [t] using topPrime_mem hR
  have hsErase :
      s ∈ (primesUpTo (squareRootEndpoint R)).erase t := by
    simpa [s, t] using secondPrime_mem_erase hR
  have hsS : s ∈ primesUpTo (squareRootEndpoint R) :=
    (Finset.mem_erase.mp hsErase).2
  have hst : s ≠ t := (Finset.mem_erase.mp hsErase).1
  have hptLe : p ≤ t := by
    simpa [t] using Finset.le_max'
      (primesUpTo (squareRootEndpoint R)) p hpS
  have hptLt : p < t := by omega
  have hpErase :
      p ∈ (primesUpTo (squareRootEndpoint R)).erase t :=
    Finset.mem_erase.mpr ⟨hpt, hpS⟩
  have hpsLe : p ≤ s := by
    simpa [s, t] using Finset.le_max'
      ((primesUpTo (squareRootEndpoint R)).erase t) p hpErase
  have hpsLt : p < s := by omega
  have htFull :
      t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2 htS
  have hsFull :
      s ∈ squareRootCanonicalRoughDescendingPrimeSchedule R := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2 hsS
  have htSched :
      t ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using
      (show t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ p < t
        from ⟨htFull, hptLt⟩)
  have hsSched :
      s ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using
      (show s ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ p < s
        from ⟨hsFull, hpsLt⟩)
  generalize hsched :
      lowOwnerFirstOwnerCanonicalStokesSchedule R p = ps at hlen htSched hsSched
  cases ps with
  | nil =>
      simp at htSched
  | cons a tail =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at htSched hsSched
          exact hst (hsSched.trans htSched.symm)
      | cons b rest =>
          simp at hlen

theorem secondPrime_topInterior_subset_pair
    {R : ℕ} (hR : 56 ≤ R) {sig : Finset ℕ} :
    primeInteriorPart (topPrime R hR)
        (lowOwnerFirstOwnerBaseFiber R (secondPrime R hR) sig) ⊆
      ({1, topPrime R hR} : Finset ℕ) := by
  exact lowOwnerFirstOwner_topPrimeInterior_subset_one_insert_prime
    (R := R) (p := secondPrime R hR) (q := topPrime R hR) (sig := sig)
    (topPrime_prime hR) (endpoint_half_lt_topPrime hR)


/-! ## Zero-owner terminal: favorable sign -/

theorem topPrime_admittedBase_eq_one
    {R : ℕ} (hR : 56 ≤ R) {sig : Finset ℕ} {a : ℕ}
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber
      R (topPrime R hR) sig) :
    a = 1 := by
  rcases Finset.mem_filter.mp ha with ⟨haBase, hpaX⟩
  have haCar := (Finset.mem_filter.mp haBase).1
  have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar).2
  have htop := endpoint_half_lt_topPrime hR
  have hXlt :
      squareRootEndpoint R < 2 * topPrime R hR := by
    omega
  by_contra hne
  have ha2 : 2 ≤ a := by omega
  have hmul :
      2 * topPrime R hR ≤ topPrime R hR * a := by
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul_right (topPrime R hR) ha2
  omega

theorem topPrime_emptyBase_eq_one
    {R : ℕ} (hR : 56 ≤ R) {a : ℕ}
    (ha : a ∈ lowOwnerFirstOwnerBaseFiber R (topPrime R hR) ∅) :
    a = 1 := by
  rcases Finset.mem_filter.mp ha with ⟨haCar, hdata⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar with
    ⟨_haSq, haPos⟩
  by_contra hane
  obtain ⟨q, hqPrime, hqDvd⟩ :=
    Nat.exists_prime_and_dvd (by omega : a ≠ 1)
  have haIcc := (Finset.mem_filter.mp haCar).1
  have haX := (Finset.mem_Icc.mp haIcc).2
  have hqLeA : q ≤ a := Nat.le_of_dvd haPos hqDvd
  have hqX : q ≤ squareRootEndpoint R := hqLeA.trans haX
  have hqMem : q ∈ primesUpTo (squareRootEndpoint R) :=
    mem_primesUpTo.mpr ⟨hqPrime, hqX⟩
  have hqTop : q ≤ topPrime R hR :=
    Finset.le_max' _ q hqMem
  have hqNeTop : q ≠ topPrime R hR := by
    intro heq
    subst q
    exact hdata.2 hqDvd
  have hqLtTop : q < topPrime R hR := by omega
  have hqFace : q ∈ squarefreePrimeFace a := by
    unfold squarefreePrimeFace
    exact Nat.mem_primeFactors.mpr ⟨hqPrime, hqDvd, Nat.ne_of_gt haPos⟩
  have hqSig :
      q ∈ squarefreeLowerPrimeSignature (topPrime R hR) a :=
    Finset.mem_filter.mpr ⟨hqFace, hqLtTop⟩
  rw [hdata.1] at hqSig
  simp at hqSig

theorem topPrime_emptyBaseAmplitude_nonneg
    {R : ℕ} (hR : 56 ≤ R) :
    0 ≤ lowOwnerFirstOwnerBaseAmplitude R (topPrime R hR) ∅ := by
  unfold lowOwnerFirstOwnerBaseAmplitude
  apply Finset.sum_nonneg
  intro a ha
  have ha1 := topPrime_emptyBase_eq_one hR ha
  subst a
  unfold lowOwnerZeroFrequencyMobiusSite
  have hw := lowOwnerZeroFrequencyMobiusWeight_nonneg R 1
  norm_num [RHLean.Analysis.realMoebiusStep] at hw ⊢
  exact hw

theorem topPrime_emptyReturnedAmplitude_nonneg
    {R : ℕ} (hR : 56 ≤ R) :
    0 ≤ lowOwnerFirstOwnerReturnedChildParentAmplitude
      R (topPrime R hR) ∅ := by
  unfold lowOwnerFirstOwnerReturnedChildParentAmplitude
  apply Finset.sum_nonneg
  intro a ha
  have ha1 := topPrime_admittedBase_eq_one hR ha
  subst a
  have hw :=
    lowOwnerZeroFrequencyMobiusWeight_nonneg R (topPrime R hR)
  norm_num [RHLean.Analysis.realMoebiusStep] at hw ⊢
  exact hw

theorem topPrime_returnedAmplitude_eq_zero_of_signature_ne_empty
    {R : ℕ} (hR : 56 ≤ R) {sig : Finset ℕ}
    (hsig : sig ≠ ∅) :
    lowOwnerFirstOwnerReturnedChildParentAmplitude
      R (topPrime R hR) sig = 0 := by
  unfold lowOwnerFirstOwnerReturnedChildParentAmplitude
  apply Finset.sum_eq_zero
  intro a ha
  have ha1 := topPrime_admittedBase_eq_one hR ha
  subst a
  have hbase := (Finset.mem_filter.mp ha).1
  have hsigOne := (Finset.mem_filter.mp hbase).2.1
  have hone :
      squarefreeLowerPrimeSignature (topPrime R hR) 1 = ∅ := by
    simp [squarefreeLowerPrimeSignature, squarefreePrimeFace]
  rw [hone] at hsigOne
  exact (hsig hsigOne.symm).elim

theorem topPrimeTerminal_nonpos
    {R : ℕ} (hR : 56 ≤ R) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R (topPrime R hR),
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary
        R (topPrime R hR) sig) ≤ 0 := by
  have hp := topPrime_prime hR
  have hsched := topPrime_schedule_eq_nil hR
  rw [sum_lowOwnerFirstOwnerTopTerminal_eq_neg_two_base_mul_returned_of_schedule_nil
    hp hsched]
  apply Finset.sum_nonpos
  intro sig _hsigMem
  by_cases hsig : sig = ∅
  · subst sig
    have hB := topPrime_emptyBaseAmplitude_nonneg hR
    have hJ := topPrime_emptyReturnedAmplitude_nonneg hR
    nlinarith
  · rw [topPrime_returnedAmplitude_eq_zero_of_signature_ne_empty hR hsig]
    norm_num


/-! ## One-owner terminal: explicit top toggle orbit -/

private theorem one_mem_secondPrime_emptyBase
    {R : ℕ} (hR : 56 ≤ R) :
    1 ∈ lowOwnerFirstOwnerBaseFiber R (secondPrime R hR) ∅ := by
  let s := secondPrime R hR
  have hsPrime : s.Prime := by
    simpa [s] using secondPrime_prime hR
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

private theorem top_mem_secondPrime_emptyBase
    {R : ℕ} (hR : 56 ≤ R) :
    topPrime R hR ∈
      lowOwnerFirstOwnerBaseFiber R (secondPrime R hR) ∅ := by
  let s := secondPrime R hR
  let t := topPrime R hR
  have hsPrime : s.Prime := by
    simpa [s] using secondPrime_prime hR
  have htPrime : t.Prime := by
    simpa [t] using topPrime_prime hR
  have hst : s < t := by
    simpa [s, t] using secondPrime_lt_topPrime hR
  have htMem : t ∈ primesUpTo (squareRootEndpoint R) := by
    simpa [t] using topPrime_mem hR
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

theorem secondPrime_topInterior_eq_pair
    {R : ℕ} (hR : 56 ≤ R) :
    primeInteriorPart (topPrime R hR)
        (lowOwnerFirstOwnerBaseFiber R (secondPrime R hR) ∅) =
      ({1, topPrime R hR} : Finset ℕ) := by
  let s := secondPrime R hR
  let t := topPrime R hR
  have htPrime : t.Prime := by
    simpa [t] using topPrime_prime hR
  apply Finset.Subset.antisymm
  · simpa [s, t] using
      (secondPrime_topInterior_subset_pair (R := R) hR (sig := ∅))
  · intro n hn
    have h1Base :
        1 ∈ lowOwnerFirstOwnerBaseFiber R s ∅ := by
      simpa [s] using one_mem_secondPrime_emptyBase hR
    have htBase :
        t ∈ lowOwnerFirstOwnerBaseFiber R s ∅ := by
      simpa [s, t] using top_mem_secondPrime_emptyBase hR
    have htNotDvdOne : ¬ t ∣ 1 := by
      intro hdiv
      exact htPrime.ne_one (Nat.dvd_one.mp hdiv)
    have htoggleOne : primeCarrierToggle t 1 = t := by
      simpa using (primeCarrierToggle_of_not_dvd htNotDvdOne)
    have htSq : ¬ t ^ 2 ∣ t := by
      intro hdiv
      have hle : t ^ 2 ≤ t := Nat.le_of_dvd htPrime.pos hdiv
      nlinarith [htPrime.two_le]
    have htoggleTop : primeCarrierToggle t t = 1 := by
      simpa [Nat.div_self htPrime.ne_zero] using
        (primeCarrierToggle_of_dvd (dvd_refl t) htSq)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact mem_primeInteriorPart.mpr
        ⟨h1Base, by simpa [htoggleOne] using htBase⟩
    · exact mem_primeInteriorPart.mpr
        ⟨htBase, by simpa [htoggleTop] using h1Base⟩

theorem secondPrime_topInterior_eq_empty_of_sig_ne_empty
    {R : ℕ} (hR : 56 ≤ R) {sig : Finset ℕ} (hsig : sig ≠ ∅) :
    primeInteriorPart (topPrime R hR)
        (lowOwnerFirstOwnerBaseFiber R (secondPrime R hR) sig) = ∅ := by
  let s := secondPrime R hR
  let t := topPrime R hR
  have htPrime : t.Prime := by
    simpa [t] using topPrime_prime hR
  have hst : s < t := by
    simpa [s, t] using secondPrime_lt_topPrime hR
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hsub :=
    secondPrime_topInterior_subset_pair
      (R := R) hR (sig := sig) hn
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

private theorem topPrime_reciprocalDaughterWeight_eq_zero
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerReciprocalDaughterWeight R (topPrime R hR) = 0 := by
  let t := topPrime R hR
  have htTop : squareRootEndpoint R / 2 < t := by
    simpa [t] using endpoint_half_lt_topPrime hR
  unfold lowOwnerReciprocalDaughterWeight
  apply Finset.sum_eq_zero
  intro q hq
  have hbase : q ∈ (primesUpTo (R - 1)).erase 2 :=
    (Finset.mem_sdiff.mp hq).1
  have hqNeTwo : q ≠ 2 := (Finset.mem_erase.mp hbase).1
  have hqPrime : q.Prime :=
    (mem_primesUpTo.mp (Finset.mem_erase.mp hbase).2).1
  have hqThree : 3 ≤ q := by
    have hqTwo := hqPrime.two_le
    omega
  have hden : 2 ≤ q * q := by nlinarith
  have hdiv :
      squareRootEndpoint R / (q * q) ≤ squareRootEndpoint R / 2 :=
    Nat.div_le_div_left hden (by norm_num)
  have hnot : ¬ t ≤ rawQ2ChildCutoff R q := by
    unfold rawQ2ChildCutoff
    omega
  simp [t, hnot]

private theorem topPrime_baseCoefficient_eq_one
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerDirichletBaseCoefficient R (topPrime R hR) = 1 := by
  let t := topPrime R hR
  have htMem : t ∈ primesUpTo (squareRootEndpoint R) := by
    simpa [t] using topPrime_mem hR
  have htX : t ≤ squareRootEndpoint R :=
    (mem_primesUpTo.mp htMem).2
  have htTop : squareRootEndpoint R / 2 < t := by
    simpa [t] using endpoint_half_lt_topPrime hR
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hge : 3 * R ≤ R * R := Nat.mul_le_mul (by omega : 3 ≤ R) (le_refl R)
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 hmul
  have hRt : R ≤ t := hhalf.trans (Nat.le_of_lt htTop)
  have hqzero :
      lowOwnerReciprocalDaughterWeight R t = 0 := by
    simpa [t] using topPrime_reciprocalDaughterWeight_eq_zero hR
  unfold lowOwnerDirichletBaseCoefficient lowOwnerPhysicalDirichletWeight
  rw [if_pos htX]
  unfold lowOwnerZeroFrequencyMobiusWeight lowOwnerFarTailWeight
  rw [if_pos hRt, hqzero]
  norm_num

private theorem one_baseCoefficient_eq_reciprocal
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

private theorem reciprocalDaughterWeight_le_at_one
    {R n : ℕ} (hn : 1 ≤ n) :
    lowOwnerReciprocalDaughterWeight R n ≤
      lowOwnerReciprocalDaughterWeight R 1 := by
  unfold lowOwnerReciprocalDaughterWeight
  apply Finset.sum_le_sum
  intro q _hq
  by_cases hnY : n ≤ rawQ2ChildCutoff R q
  · have h1Y : 1 ≤ rawQ2ChildCutoff R q := hn.trans hnY
    simp [hnY, h1Y]
  · by_cases h1Y : 1 ≤ rawQ2ChildCutoff R q
    · simp [hnY, h1Y]
    · simp [hnY, h1Y]

private theorem secondPrime_baseCoefficient_le_one_add_H
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerDirichletBaseCoefficient R (secondPrime R hR) ≤
      1 + lowOwnerReciprocalDaughterWeight R 1 := by
  let s := secondPrime R hR
  have hsMem : s ∈ primesUpTo (squareRootEndpoint R) :=
    (Finset.mem_erase.mp (secondPrime_mem_erase hR)).2
  have hsX : s ≤ squareRootEndpoint R :=
    (mem_primesUpTo.mp hsMem).2
  have hsOne : 1 ≤ s :=
    (mem_primesUpTo.mp hsMem).1.one_le
  have hd :=
    reciprocalDaughterWeight_le_at_one (R := R) (n := s) hsOne
  unfold lowOwnerDirichletBaseCoefficient lowOwnerPhysicalDirichletWeight
  rw [if_pos hsX]
  unfold lowOwnerZeroFrequencyMobiusWeight lowOwnerFarTailWeight
  by_cases hRs : R ≤ s
  · rw [if_pos hRs]
    linarith
  · rw [if_neg hRs]
    linarith

private theorem secondPrime_returned_top_eq_zero
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerDirichletReturnedCoefficient R
      (secondPrime R hR) (topPrime R hR) = 0 := by
  let s := secondPrime R hR
  let t := topPrime R hR
  have hsPrime : s.Prime := by
    simpa [s] using secondPrime_prime hR
  have htTop : squareRootEndpoint R / 2 < t := by
    simpa [t] using endpoint_half_lt_topPrime hR
  have hX2t : squareRootEndpoint R < 2 * t := by omega
  have h2st : 2 * t ≤ s * t :=
    Nat.mul_le_mul_right t hsPrime.two_le
  have hout : squareRootEndpoint R < s * t := hX2t.trans_le h2st
  unfold lowOwnerDirichletReturnedCoefficient lowOwnerPhysicalDirichletWeight
  rw [if_neg (Nat.not_le_of_lt hout)]

private theorem secondPrime_returned_one_eq_base
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerDirichletReturnedCoefficient R (secondPrime R hR) 1 =
      lowOwnerDirichletBaseCoefficient R (secondPrime R hR) := by
  simp [lowOwnerDirichletReturnedCoefficient, lowOwnerDirichletBaseCoefficient]

private theorem secondPrime_empty_baseDifferenceAmplitude
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesSignedAmplitude
        (primeInteriorPart (topPrime R hR)
          (lowOwnerFirstOwnerBaseFiber R (secondPrime R hR) ∅))
        (lowOwnerStokesToggleDifference
          (topPrime R hR) (lowOwnerDirichletBaseCoefficient R)) =
      2 * (lowOwnerReciprocalDaughterWeight R 1 - 1) := by
  let t := topPrime R hR
  have htPrime : t.Prime := by
    simpa [t] using topPrime_prime hR
  have htNotDvdOne : ¬ t ∣ 1 := by
    intro hdiv
    exact htPrime.ne_one (Nat.dvd_one.mp hdiv)
  have htSq : ¬ t ^ 2 ∣ t := by
    intro hdiv
    have hle : t ^ 2 ≤ t := Nat.le_of_dvd htPrime.pos hdiv
    nlinarith [htPrime.two_le]
  have htoggleOne : primeCarrierToggle t 1 = t := by
    simpa using (primeCarrierToggle_of_not_dvd htNotDvdOne)
  have htoggleTop : primeCarrierToggle t t = 1 := by
    simpa [Nat.div_self htPrime.ne_zero] using
      (primeCarrierToggle_of_dvd (dvd_refl t) htSq)
  have hI := secondPrime_topInterior_eq_pair hR
  have hL1 := one_baseCoefficient_eq_reciprocal hR
  have hLt := topPrime_baseCoefficient_eq_one hR
  unfold lowOwnerStokesSignedAmplitude lowOwnerStokesToggleDifference
  rw [hI]
  have h1t : 1 ≠ t := by omega
  simp [t, h1t, htoggleOne, htoggleTop, hL1, hLt,
    othelloRealMoebius, ArithmeticFunction.moebius_apply_prime htPrime]
  ring

private theorem secondPrime_empty_returnedDifferenceAmplitude
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesSignedAmplitude
        (primeInteriorPart (topPrime R hR)
          (lowOwnerFirstOwnerBaseFiber R (secondPrime R hR) ∅))
        (lowOwnerStokesToggleDifference
          (topPrime R hR)
          (lowOwnerDirichletReturnedCoefficient R (secondPrime R hR))) =
      2 * lowOwnerDirichletBaseCoefficient R (secondPrime R hR) := by
  let t := topPrime R hR
  have htPrime : t.Prime := by
    simpa [t] using topPrime_prime hR
  have htNotDvdOne : ¬ t ∣ 1 := by
    intro hdiv
    exact htPrime.ne_one (Nat.dvd_one.mp hdiv)
  have htSq : ¬ t ^ 2 ∣ t := by
    intro hdiv
    have hle : t ^ 2 ≤ t := Nat.le_of_dvd htPrime.pos hdiv
    nlinarith [htPrime.two_le]
  have htoggleOne : primeCarrierToggle t 1 = t := by
    simpa using (primeCarrierToggle_of_not_dvd htNotDvdOne)
  have htoggleTop : primeCarrierToggle t t = 1 := by
    simpa [Nat.div_self htPrime.ne_zero] using
      (primeCarrierToggle_of_dvd (dvd_refl t) htSq)
  have hI := secondPrime_topInterior_eq_pair hR
  have hJ1 := secondPrime_returned_one_eq_base hR
  have hJt := secondPrime_returned_top_eq_zero hR
  unfold lowOwnerStokesSignedAmplitude lowOwnerStokesToggleDifference
  rw [hI]
  have h1t : 1 ≠ t := by omega
  simp [t, h1t, htoggleOne, htoggleTop, hJ1, hJt,
    othelloRealMoebius, ArithmeticFunction.moebius_apply_prime htPrime]
  ring

theorem secondPrimeTerminal_eq_two_one_sub_H_mul_L
    {R : ℕ} (hR : 56 ≤ R) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R (secondPrime R hR),
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary
        R (secondPrime R hR) sig) =
      2 * (1 - lowOwnerReciprocalDaughterWeight R 1) *
        lowOwnerDirichletBaseCoefficient R (secondPrime R hR) := by
  let s := secondPrime R hR
  let t := topPrime R hR
  have hsched :
      lowOwnerFirstOwnerCanonicalStokesSchedule R s = [t] := by
    simpa [s, t] using secondPrime_schedule_eq_single_top hR
  rw [sum_lowOwnerFirstOwnerTopTerminal_eq_neg_half_interiorDifferenceProduct_of_schedule_single
    hsched]
  have hEmptyMem :
      (∅ : Finset ℕ) ∈ lowOwnerFirstOwnerSignatureSet R s := by
    unfold lowOwnerFirstOwnerSignatureSet
    have h1Base :
        1 ∈ lowOwnerFirstOwnerBaseFiber R s ∅ := by
      simpa [s] using one_mem_secondPrime_emptyBase hR
    have h1Car := (Finset.mem_filter.mp h1Base).1
    refine Finset.mem_image.mpr ⟨1, h1Car, ?_⟩
    simp [squarefreeLowerPrimeSignature, squarefreePrimeFace]
  rw [Finset.sum_eq_single (∅ : Finset ℕ)]
  · have hA := secondPrime_empty_baseDifferenceAmplitude hR
    have hB := secondPrime_empty_returnedDifferenceAmplitude hR
    rw [hA, hB]
    ring
  · intro sig _hsigMem hsigNe
    have hI :=
      secondPrime_topInterior_eq_empty_of_sig_ne_empty hR hsigNe
    rw [hI]
    simp [lowOwnerStokesSignedAmplitude]
  · intro hnot
    exact (hnot hEmptyMem).elim

theorem secondPrimeTerminal_le_four
    {R : ℕ} (hR : 56 ≤ R) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R (secondPrime R hR),
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary
        R (secondPrime R hR) sig) ≤ 4 := by
  rw [secondPrimeTerminal_eq_two_one_sub_H_mul_L hR]
  let H := lowOwnerReciprocalDaughterWeight R 1
  let L := lowOwnerDirichletBaseCoefficient R (secondPrime R hR)
  have hH : 0 ≤ H := by
    dsimp [H]
    exact lowOwnerReciprocalDaughterWeight_nonneg R 1
  have hL : 0 ≤ L := by
    dsimp [L, lowOwnerDirichletBaseCoefficient]
    exact lowOwnerPhysicalDirichletWeight_nonneg R (secondPrime R hR)
  have hLup : L ≤ 1 + H := by
    dsimp [L, H]
    exact secondPrime_baseCoefficient_le_one_add_H hR
  by_cases hHone : 1 ≤ H
  · have hdiff : 1 - H ≤ 0 := by linarith
    have hprod : (1 - H) * L ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hdiff hL
    nlinarith
  · have hHlt : H < 1 := lt_of_not_ge hHone
    have hdiff0 : 0 ≤ 1 - H := by linarith
    have hdiff1 : 1 - H ≤ 1 := by linarith
    have hLle : L ≤ 2 := by linarith
    have hprod : (1 - H) * L ≤ 1 * 2 :=
      mul_le_mul hdiff1 hLle hL (by norm_num)
    nlinarith

theorem topTerminalOwnerSet_eq_top_two
    {R : ℕ} (hR : 56 ≤ R) :
    topTerminalOwnerSet R =
      ({topPrime R hR, secondPrime R hR} : Finset ℕ) := by
  apply Finset.Subset.antisymm
  · exact topTerminalOwnerSet_subset_top_two hR
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with htop | hsecond
    · subst p
      unfold topTerminalOwnerSet
      apply Finset.mem_filter.mpr
      exact ⟨topPrime_mem hR, by
        rw [topPrime_schedule_eq_nil hR]
        simp⟩
    · subst p
      unfold topTerminalOwnerSet
      apply Finset.mem_filter.mpr
      have hsMem := (Finset.mem_erase.mp (secondPrime_mem_erase hR)).2
      exact ⟨hsMem, by
        rw [secondPrime_schedule_eq_single_top hR]
        simp⟩

def exceptionalTerminalBoundary (R : ℕ) : ℝ :=
  ∑ p ∈ topTerminalOwnerSet R,
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig

theorem exceptionalTerminalBoundary_le_four
    {R : ℕ} (hR : 56 ≤ R) :
    exceptionalTerminalBoundary R ≤ 4 := by
  unfold exceptionalTerminalBoundary
  rw [topTerminalOwnerSet_eq_top_two hR]
  have hne : topPrime R hR ≠ secondPrime R hR :=
    ne_of_gt (secondPrime_lt_topPrime hR)
  simp only [Finset.sum_insert, Finset.mem_singleton, hne,
    not_false_eq_true, Finset.sum_singleton]
  have htop := topPrimeTerminal_nonpos hR
  have hsecond := secondPrimeTerminal_le_four hR
  linarith

/-- **Exceptional terminal sector closed with unit frame constant.** -/
theorem exceptionalTerminalBoundary_le_frame
    {R : ℕ} (hR : 56 ≤ R) :
    exceptionalTerminalBoundary R ≤ frameMajorant R hR := by
  have hterm := exceptionalTerminalBoundary_le_four hR
  have hframe := root_sq_over_eighteen_le_frameMajorant hR
  have hfour : (4 : ℝ) ≤ (R : ℝ) ^ 2 / 18 := by
    have hRreal : (56 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith
  exact hterm.trans (hfour.trans hframe)


/-- Unit-frame formulation of the closed exceptional terminal sector. -/
def ExceptionalTerminalFrameDomination (C : ℝ) : Prop :=
  ∀ (R : ℕ) (hR : 56 ≤ R),
    exceptionalTerminalBoundary R ≤ C * frameMajorant R hR

theorem lowOwnerStokesExceptionalTerminalFrameDomination_one :
    ExceptionalTerminalFrameDomination 1 := by
  intro R hR
  simpa using exceptionalTerminalBoundary_le_frame hR

end StokesTerminalFrame
end RHLean.Proof
