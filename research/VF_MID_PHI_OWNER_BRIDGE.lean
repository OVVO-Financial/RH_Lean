import Mathlib
import «research.EXACT_LI_PURE_MODEL_CLOSURE»
import «research.VF_MID_DYADIC_OWNER_EXACT»

/-!
# Exact Phi transform from frequency states to VF owner counts

This file supplies the finite algebraic bridge between the repository's signed
largest-prime frequency states and the positive least-prime-factor owner
populations used by the direct VF-mid square-block route.

For a frequency state S define

  Phi_S(N,y) = sum_{1 <= k <= N} S(floor(N/k),y).

The transform has the same one-site hard-core recurrence as the original state.
For the actual-prime frequency it is exactly the fixed-prefix survivor count
F_y(N).  Consequently one VF least-prime owner fibre is exactly a difference
of two transformed actual-prime states at the two cofactor endpoints.

The final section subtracts an all-scale Li state and records the exact signed
displacement recurrence on Phi itself.  These are identities only: no
continuous-to-discrete estimate, owner-level Li cancellation estimate, PNT
remainder estimate, or RH-scale bound is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## The finite quotient-sum transform -/

/-- Finite quotient-sum transform of a two-parameter frequency state. -/
def primeFrequencyCumulativeTransform
    (S : ℕ → ℕ → ℂ) (N y : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, S (N / k) y

/-- Summing one activated floor child over harmonic quotients is exactly the
same transform at the divided endpoint. -/
theorem sum_activatedFloorChild_quotients
    (F : ℕ → ℂ) (N q : ℕ) (hq : 1 ≤ q) :
    (∑ k ∈ Finset.Icc 1 N,
        activatedFloorChild F q (N / k)) =
      ∑ k ∈ Finset.Icc 1 (N / q), F ((N / q) / k) := by
  classical
  have hqpos : 0 < q := by omega
  have hset :
      (Finset.Icc 1 N).filter (fun k => q ≤ N / k) =
        Finset.Icc 1 (N / q) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hkN⟩, hqdiv⟩
      have hkpos : 0 < k := by omega
      have hmul : q * k ≤ N :=
        (Nat.le_div_iff_mul_le hkpos).1 hqdiv
      have hkdiv : k ≤ N / q :=
        (Nat.le_div_iff_mul_le hqpos).2 (by
          simpa [Nat.mul_comm] using hmul)
      exact ⟨hk1, hkdiv⟩
    · rintro ⟨hk1, hkdiv⟩
      have hkpos : 0 < k := by omega
      have hkN : k ≤ N :=
        hkdiv.trans (Nat.div_le_self N q)
      have hmul : k * q ≤ N :=
        (Nat.le_div_iff_mul_le hqpos).1 hkdiv
      have hqdiv : q ≤ N / k :=
        (Nat.le_div_iff_mul_le hkpos).2 (by
          simpa [Nat.mul_comm] using hmul)
      exact ⟨⟨hk1, hkN⟩, hqdiv⟩
  calc
    (∑ k ∈ Finset.Icc 1 N,
        activatedFloorChild F q (N / k)) =
      ∑ k ∈ Finset.Icc 1 N,
        if q ≤ N / k then F ((N / k) / q) else 0 := by
          apply Finset.sum_congr rfl
          intro k _hk
          simp [activatedFloorChild]
    _ = ∑ k ∈ (Finset.Icc 1 N).filter (fun k => q ≤ N / k),
        F ((N / k) / q) := by
          rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.Icc 1 (N / q), F ((N / k) / q) := by
          rw [hset]
    _ = ∑ k ∈ Finset.Icc 1 (N / q), F ((N / q) / k) := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- The quotient-sum transform inherits the exact fresh-site hard-core update. -/
theorem primeFrequencyCumulativeTransform_cutoff_succ
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S)
    (N y : ℕ) (hy : 1 ≤ y) :
    primeFrequencyCumulativeTransform S N (y + 1) =
      primeFrequencyCumulativeTransform S N y -
        w (y + 1) *
          primeFrequencyCumulativeTransform S (N / (y + 1)) y := by
  unfold primeFrequencyCumulativeTransform
  calc
    (∑ k ∈ Finset.Icc 1 N, S (N / k) (y + 1)) =
      ∑ k ∈ Finset.Icc 1 N,
        frequencyHardCoreUpdate (w (y + 1)) (y + 1)
          (fun m => S m y) (N / k) := by
            apply Finset.sum_congr rfl
            intro k _hk
            exact primeFrequencyState_cutoff_succ hS (N / k) y hy
    _ = (∑ k ∈ Finset.Icc 1 N, S (N / k) y) -
        w (y + 1) *
          (∑ k ∈ Finset.Icc 1 (N / (y + 1)),
            S ((N / (y + 1)) / k) y) := by
          unfold frequencyHardCoreUpdate
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          rw [sum_activatedFloorChild_quotients
            (fun m => S m y) N (y + 1) (by omega)]

/-- Same recurrence indexed directly by the new cutoff q. -/
theorem primeFrequencyCumulativeTransform_cutoff_step
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S)
    (N q : ℕ) (hq : 2 ≤ q) :
    primeFrequencyCumulativeTransform S N q =
      primeFrequencyCumulativeTransform S N (q - 1) -
        w q * primeFrequencyCumulativeTransform S (N / q) (q - 1) := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have h :=
    primeFrequencyCumulativeTransform_cutoff_succ
      hS N (q - 1) (by omega : 1 ≤ q - 1)
  simpa only [hpred] using h

/-! ## The actual-prime transform is exactly the positive survivor count -/

private theorem primesUpTo_one_eq_empty :
    primesUpTo 1 = ∅ := by
  ext p
  simp only [mem_primesUpTo, Finset.notMem_empty, iff_false]
  rintro ⟨hp, hp1⟩
  have hp2 := hp.two_le
  omega

theorem vfMidPrefixWheelCounting_one (N : ℕ) :
    vfMidPrefixWheelCounting 1 N = N := by
  classical
  unfold vfMidPrefixWheelCounting lowWheelHighSurvivor
  rw [primesUpTo_one_eq_empty]
  simp [Nat.card_Ioc]

private theorem actualPrimeState_cutoff_one
    {A : ℕ → ℕ → ℂ}
    (hA : IsAllScaleActualPrimeState A)
    {x : ℕ} (hx : 1 ≤ x) :
    A x 1 = 1 := by
  have hA' : IsPrimeFrequencyState primeSievePrimeIndicator A := hA
  rw [hA' x 1]
  unfold primeFrequencyStep
  rw [min_eq_right hx]
  simp

private theorem primesUpTo_eq_insert_pred
    {p : ℕ} (hp : p.Prime) :
    primesUpTo p = insert p (primesUpTo (p - 1)) := by
  ext q
  simp only [mem_primesUpTo, Finset.mem_insert]
  constructor
  · rintro ⟨hq, hqp⟩
    by_cases heq : q = p
    · exact Or.inl heq
    · exact Or.inr ⟨hq, by omega⟩
  · rintro (rfl | ⟨hq, hqpred⟩)
    · exact ⟨hp, le_rfl⟩
    · exact ⟨hq, by omega⟩

private theorem primesUpTo_eq_pred_of_not_prime
    {q : ℕ} (hq1 : 1 ≤ q) (hq : ¬ q.Prime) :
    primesUpTo q = primesUpTo (q - 1) := by
  ext p
  simp only [mem_primesUpTo]
  constructor
  · rintro ⟨hp, hpq⟩
    refine ⟨hp, ?_⟩
    by_contra hnot
    have hpEq : p = q := by omega
    exact hq (hpEq ▸ hp)
  · rintro ⟨hp, hppred⟩
    exact ⟨hp, by omega⟩

/-- Adding one actual prime coordinate gives the same fresh-prime recurrence
for the positive prefix count.  This is proved from the already-compiled exact
Boolean-face floor expansion, with no asymptotic estimate. -/
theorem vfMidPrefixWheelCounting_cast_int_prime_step
    {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (vfMidPrefixWheelCounting p N : ℤ) =
      (vfMidPrefixWheelCounting (p - 1) N : ℤ) -
        (vfMidPrefixWheelCounting (p - 1) (N / p) : ℤ) := by
  classical
  have hset := primesUpTo_eq_insert_pred hp
  have hpnot : p ∉ primesUpTo (p - 1) := by
    intro hmem
    have hpLe := (mem_primesUpTo.mp hmem).2
    have hp2 := hp.two_le
    omega
  rw [vfMidPrefixWheelCounting_cast_int_eq_faceFloorSum,
    vfMidPrefixWheelCounting_cast_int_eq_faceFloorSum,
    vfMidPrefixWheelCounting_cast_int_eq_faceFloorSum,
    hset, Finset.sum_powerset_insert hpnot]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : p ∉ t :=
    Finset.notMem_of_mem_powerset_of_notMem ht hpnot
  have hprod :
      primeFaceProduct (insert p t) = p * primeFaceProduct t := by
    simp [primeFaceProduct, hpt]
  have hsign :
      booleanCubeSign (insert p t) = -booleanCubeSign t := by
    unfold booleanCubeSign
    rw [Finset.card_insert_of_notMem hpt, pow_succ]
    ring
  rw [hprod, hsign, Nat.div_div_eq_div_mul]
  ring

/-- Unified actual-prime recurrence for the complex-cast survivor count. -/
theorem vfMidPrefixWheelCounting_cast_complex_step
    (N q : ℕ) (hq : 2 ≤ q) :
    (vfMidPrefixWheelCounting q N : ℂ) =
      (vfMidPrefixWheelCounting (q - 1) N : ℂ) -
        primeSievePrimeIndicator q *
          (vfMidPrefixWheelCounting (q - 1) (N / q) : ℂ) := by
  by_cases hp : q.Prime
  · have hZ := vfMidPrefixWheelCounting_cast_int_prime_step hp N
    have hC := congrArg (fun z : ℤ => (z : ℂ)) hZ
    simpa [primeSievePrimeIndicator, hp] using hC
  · have hset :=
      primesUpTo_eq_pred_of_not_prime (q := q) (by omega) hp
    have hcount :
        vfMidPrefixWheelCounting q N =
          vfMidPrefixWheelCounting (q - 1) N := by
      unfold vfMidPrefixWheelCounting lowWheelHighSurvivor
      rw [hset]
    rw [hcount]
    simp [primeSievePrimeIndicator, hp]

/-- **Exact counting transform.**  Any state solving the actual-prime
largest-prime recursion becomes, after the finite quotient-sum transform,
exactly the positive fixed-prefix survivor count used by the VF construction. -/
theorem actualPrimeCumulativeTransform_eq_prefixWheelCounting
    {A : ℕ → ℕ → ℂ}
    (hA : IsAllScaleActualPrimeState A)
    (N y : ℕ) (hy : 1 ≤ y) :
    primeFrequencyCumulativeTransform A N y =
      (vfMidPrefixWheelCounting y N : ℂ) := by
  have hA' : IsPrimeFrequencyState primeSievePrimeIndicator A := hA
  have hbase :
      ∀ N : ℕ,
        primeFrequencyCumulativeTransform A N 1 =
          (vfMidPrefixWheelCounting 1 N : ℂ) := by
    intro M
    unfold primeFrequencyCumulativeTransform
    calc
      (∑ k ∈ Finset.Icc 1 M, A (M / k) 1) =
          ∑ _k ∈ Finset.Icc 1 M, (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkI := Finset.mem_Icc.mp hk
            have hkpos : 0 < k := by omega
            have hchild : 1 ≤ M / k :=
              (Nat.one_le_div_iff hkpos).2 hkI.2
            exact actualPrimeState_cutoff_one hA hchild
      _ = (M : ℂ) := by
            rw [Finset.sum_const, Nat.card_Icc]
            simp
      _ = (vfMidPrefixWheelCounting 1 M : ℂ) := by
            rw [vfMidPrefixWheelCounting_one]
  have hmain :
      ∀ k N : ℕ,
        primeFrequencyCumulativeTransform A N (k + 1) =
          (vfMidPrefixWheelCounting (k + 1) N : ℂ) := by
    intro k
    induction k with
    | zero =>
        intro M
        simpa using hbase M
    | succ k ih =>
        intro M
        have hstep :=
          primeFrequencyCumulativeTransform_cutoff_step
            hA' M (k + 2) (by omega : 2 ≤ k + 2)
        have hprefix :=
          vfMidPrefixWheelCounting_cast_complex_step
            M (k + 2) (by omega : 2 ≤ k + 2)
        calc
          primeFrequencyCumulativeTransform A M (Nat.succ k + 1) =
              primeFrequencyCumulativeTransform A M (k + 1) -
                primeSievePrimeIndicator (k + 2) *
                  primeFrequencyCumulativeTransform A (M / (k + 2)) (k + 1) := by
                    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hstep
          _ = (vfMidPrefixWheelCounting (k + 1) M : ℂ) -
                primeSievePrimeIndicator (k + 2) *
                  (vfMidPrefixWheelCounting (k + 1) (M / (k + 2)) : ℂ) := by
                    rw [ih M, ih (M / (k + 2))]
          _ = (vfMidPrefixWheelCounting (Nat.succ k + 1) M : ℂ) := by
                    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hprefix.symm
  cases y with
  | zero => omega
  | succ k =>
      simpa [Nat.succ_eq_add_one] using hmain k N

/-! ## Exact owner endpoints in Phi coordinates -/

/-- Cofactor interval whose survivors of every prime below p are exactly the
children of the p-owned composites in the R-th open square block. -/
def vfMidSquareBandOwnerPrefixChildren (R p : ℕ) : Finset ℕ :=
  (Finset.Ioc (R ^ 2 / p) (((R + 1) ^ 2 - 1) / p)).filter
    (lowWheelHighSurvivor (p - 1))

private theorem roughAbove_pred_iff_lowWheelHighSurvivor
    {p m : ℕ} (hm0 : m ≠ 0) :
    RoughAbove (p - 1) m ↔ lowWheelHighSurvivor (p - 1) m := by
  unfold RoughAbove lowWheelHighSurvivor
  constructor
  · intro hrough q hq hqdiv
    have hqPrime := prime_of_mem_primesUpTo hq
    have hqFac : q ∈ m.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqPrime, hqdiv, hm0⟩
    have hgt := hrough q hqFac
    have hle := (mem_primesUpTo.mp hq).2
    omega
  · intro hsurv q hqFac
    have hqData := Nat.mem_primeFactors.mp hqFac
    by_contra hnot
    have hqle : q ≤ p - 1 := by omega
    have hqMem :=
      mem_primesUpTo_of_prime_le hqData.1 hqle
    exact hsurv q hqMem hqData.2.1

/-- The repository's existing rough-child owner fibre is literally the
survivor interval appearing in the Phi endpoint formula. -/
theorem vfMidSquareBandCompositeOwnerChildren_eq_prefixChildren
    {R p : ℕ} (hR : 3 ≤ R)
    (hp : p ∈ vfMidSquareBandOwnerPrimes R) :
    vfMidSquareBandCompositeOwnerChildren R p =
      vfMidSquareBandOwnerPrefixChildren R p := by
  rw [vfMidSquareBandCompositeOwnerChildren_eq_rough hR hp]
  have hpData := mem_vfMidSquareBandOwnerPrimes.mp hp
  have hpPrime := hpData.1
  have hpLeR := hpData.2
  have hp2 := hpPrime.two_le
  ext m
  constructor
  · intro hm
    rcases Finset.mem_filter.mp hm with ⟨hmIcc, hdata⟩
    rcases Finset.mem_Icc.mp hmIcc with ⟨hpm, _hmTop⟩
    rcases hdata with ⟨hlo, hhi, hrough⟩
    have hm0 : m ≠ 0 := by omega
    have hlower : R ^ 2 / p < m := by
      apply (Nat.div_lt_iff_lt_mul hpPrime.pos).2
      simpa [Nat.mul_comm] using hlo
    have hupperMul : p * m ≤ (R + 1) ^ 2 - 1 := by
      have hUpos : 0 < (R + 1) ^ 2 := by positivity
      omega
    have hupper : m ≤ ((R + 1) ^ 2 - 1) / p := by
      apply (Nat.le_div_iff_mul_le hpPrime.pos).2
      simpa [Nat.mul_comm] using hupperMul
    have hsurv :=
      (roughAbove_pred_iff_lowWheelHighSurvivor hm0).1 hrough
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hlower, hupper⟩, hsurv⟩
  · intro hm
    rcases Finset.mem_filter.mp hm with ⟨hmIoc, hsurv⟩
    rcases Finset.mem_Ioc.mp hmIoc with ⟨hlower, hupper⟩
    have hmpos : 0 < m :=
      lt_of_le_of_lt (Nat.zero_le (R ^ 2 / p)) hlower
    have hm0 : m ≠ 0 := Nat.ne_of_gt hmpos
    have hrough :=
      (roughAbove_pred_iff_lowWheelHighSurvivor hm0).2 hsurv
    have hloMul : R ^ 2 < m * p :=
      (Nat.div_lt_iff_lt_mul hpPrime.pos).1 hlower
    have hlo : R ^ 2 < p * m := by
      simpa [Nat.mul_comm] using hloMul
    have hupperMul : m * p ≤ (R + 1) ^ 2 - 1 :=
      (Nat.le_div_iff_mul_le hpPrime.pos).1 hupper
    have hhi : p * m < (R + 1) ^ 2 := by
      have hUpos : 0 < (R + 1) ^ 2 := by positivity
      have : p * m ≤ (R + 1) ^ 2 - 1 := by
        simpa [Nat.mul_comm] using hupperMul
      omega
    have hpSqLe : p * p ≤ R * R :=
      Nat.mul_le_mul hpLeR hpLeR
    have hpLeDiv : p ≤ R ^ 2 / p := by
      apply (Nat.le_div_iff_mul_le hpPrime.pos).2
      simpa [pow_two] using hpSqLe
    have hpm : p ≤ m := by omega
    have hmTop : m ≤ R ^ 2 - 1 := by
      by_contra hnot
      have hmR2 : R ^ 2 ≤ m := by omega
      have h2le : 2 * (R ^ 2) ≤ p * m := by
        exact Nat.mul_le_mul hp2 hmR2
      have hexp : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
      have hgap : R ^ 2 + 2 * R < 2 * (R ^ 2) := by
        nlinarith
      rw [hexp] at hupperMul
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpm, hmTop⟩, ⟨hlo, hhi, hrough⟩⟩

/-- Cardinal form of the exact owner/cofactor interval identification. -/
theorem vfMidSquareBandCompositeOwner_card_eq_prefixIntervalCounting
    {R p : ℕ} (hR : 3 ≤ R)
    (hp : p ∈ vfMidSquareBandOwnerPrimes R) :
    (vfMidSquareBandCompositeOwner R p).card =
      vfMidPrefixWheelIntervalCounting
        (p - 1) (R ^ 2 / p) (((R + 1) ^ 2 - 1) / p) := by
  calc
    (vfMidSquareBandCompositeOwner R p).card =
        (vfMidSquareBandCompositeOwnerChildren R p).card := by
          symm
          exact vfMidSquareBandCompositeOwnerChildren_card R p
    _ = (vfMidSquareBandOwnerPrefixChildren R p).card := by
          rw [vfMidSquareBandCompositeOwnerChildren_eq_prefixChildren hR hp]
    _ = vfMidPrefixWheelIntervalCounting
          (p - 1) (R ^ 2 / p) (((R + 1) ^ 2 - 1) / p) := by
          rfl

private theorem vfMidOwnerPrefixLower_le_upper
    {R p : ℕ} :
    R ^ 2 / p ≤ ((R + 1) ^ 2 - 1) / p := by
  have hexp : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
  have hnum : R ^ 2 ≤ (R + 1) ^ 2 - 1 := by
    rw [hexp]
    omega
  exact Nat.div_le_div_right hnum

/-- **Exact owner endpoint formula.**  A p-owned composite in the R-th open
square block is exactly an actual-prime Phi survivor between the two quotient
endpoints. -/
theorem vfMidSquareBandCompositeOwner_card_eq_actualPhiDifference
    {A : ℕ → ℕ → ℂ} {R p : ℕ}
    (hA : IsAllScaleActualPrimeState A)
    (hR : 3 ≤ R)
    (hp : p ∈ vfMidSquareBandOwnerPrimes R) :
    ((vfMidSquareBandCompositeOwner R p).card : ℂ) =
      primeFrequencyCumulativeTransform A
          (((R + 1) ^ 2 - 1) / p) (p - 1) -
        primeFrequencyCumulativeTransform A
          (R ^ 2 / p) (p - 1) := by
  have hpPrime := (mem_vfMidSquareBandOwnerPrimes.mp hp).1
  have hcut : 1 ≤ p - 1 := by
    have hp2 := hpPrime.two_le
    omega
  have hcard :=
    vfMidSquareBandCompositeOwner_card_eq_prefixIntervalCounting hR hp
  have hsplit :=
    vfMidPrefixWheelCounting_add_intervalCounting
      (p - 1) (R ^ 2 / p) (((R + 1) ^ 2 - 1) / p)
      vfMidOwnerPrefixLower_le_upper
  rw [← hcard] at hsplit
  have hsplitC :
      (vfMidPrefixWheelCounting (p - 1) (R ^ 2 / p) : ℂ) +
          ((vfMidSquareBandCompositeOwner R p).card : ℂ) =
        (vfMidPrefixWheelCounting (p - 1)
          (((R + 1) ^ 2 - 1) / p) : ℂ) := by
    exact_mod_cast hsplit
  rw [actualPrimeCumulativeTransform_eq_prefixWheelCounting
        hA (((R + 1) ^ 2 - 1) / p) (p - 1) hcut,
      actualPrimeCumulativeTransform_eq_prefixWheelCounting
        hA (R ^ 2 / p) (p - 1) hcut]
  linear_combination hsplitC

/-! ## Signed actual-minus-Li displacement after the Phi transform -/

/-- Signed transformed displacement between an actual-prime state and a
comparison frequency state. -/
def primeFrequencyCumulativeDisplacement
    (A L : ℕ → ℕ → ℂ) (N y : ℕ) : ℂ :=
  primeFrequencyCumulativeTransform A N y -
    primeFrequencyCumulativeTransform L N y

/-- **Exact transformed displacement recurrence.**  The forcing term and its
lower-triangular propagation survive the quotient-sum transform with their
signs intact. -/
theorem primeFrequencyCumulativeDisplacement_cutoff_step
    {A L : ℕ → ℕ → ℂ}
    (hA : IsAllScaleActualPrimeState A)
    (hL : IsAllScaleLiState L)
    (N q : ℕ) (hq : 2 ≤ q) :
    primeFrequencyCumulativeDisplacement A L N q =
      primeFrequencyCumulativeDisplacement A L N (q - 1) -
        primeSievePNTDensity q *
          primeFrequencyCumulativeDisplacement A L (N / q) (q - 1) -
        (primeSievePrimeIndicator q - primeSievePNTDensity q) *
          primeFrequencyCumulativeTransform A (N / q) (q - 1) := by
  have hA' : IsPrimeFrequencyState primeSievePrimeIndicator A := hA
  have hL' : IsPrimeFrequencyState primeSievePNTDensity L := hL
  have hAstep :=
    primeFrequencyCumulativeTransform_cutoff_step hA' N q hq
  have hLstep :=
    primeFrequencyCumulativeTransform_cutoff_step hL' N q hq
  unfold primeFrequencyCumulativeDisplacement
  rw [hAstep, hLstep]
  ring

/-- Each physical owner fibre is therefore exactly a transformed Li endpoint
difference plus the transformed actual-minus-Li displacement endpoint
difference.  This is the precise finite handoff to the later stability
problem; no bound on either bracket is asserted. -/
theorem vfMidSquareBandCompositeOwner_card_eq_liPhi_add_displacement
    {A L : ℕ → ℕ → ℂ} {R p : ℕ}
    (hA : IsAllScaleActualPrimeState A)
    (_hL : IsAllScaleLiState L)
    (hR : 3 ≤ R)
    (hp : p ∈ vfMidSquareBandOwnerPrimes R) :
    ((vfMidSquareBandCompositeOwner R p).card : ℂ) =
      (primeFrequencyCumulativeTransform L
          (((R + 1) ^ 2 - 1) / p) (p - 1) -
        primeFrequencyCumulativeTransform L
          (R ^ 2 / p) (p - 1)) +
      (primeFrequencyCumulativeDisplacement A L
          (((R + 1) ^ 2 - 1) / p) (p - 1) -
        primeFrequencyCumulativeDisplacement A L
          (R ^ 2 / p) (p - 1)) := by
  rw [vfMidSquareBandCompositeOwner_card_eq_actualPhiDifference
    hA hR hp]
  unfold primeFrequencyCumulativeDisplacement
  ring

end RHLean.Analysis
