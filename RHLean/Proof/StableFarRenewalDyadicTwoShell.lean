import Mathlib
import RHLean.Proof.RoughDyadicQ2Compression
import RHLean.Proof.StableFarWallCrossingOwnerWindow
import RHLean.Proof.StableFarWallSignedReassembly
import RHLean.Proof.ComplexVerticalLineSquarefreeDiagonal
import RHLean.Proof.SurvivorDyadicStaticCancellation

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

def stableFarRenewalOwnerGeometry
    (R q r e p : ℕ) : Prop :=
  q * r * e * p ≤ squareRootEndpoint R ∧
    squareRootEndpoint R < q * q * r * e * p

def stableFarRenewalOwnerActive
    (R q r e p : ℕ) : Prop :=
  q ∈ primesUpTo (R - 1) ∧ r < q ∧
    stableFarRenewalOwnerGeometry R q r e p

theorem mem_crossingOuterOwnerSet_iff_active
    {R q r e p : ℕ} :
    q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) ↔
      stableFarRenewalOwnerActive R q r e p := by
  simp [lowWheelFarPrimeQ2CrossingOuterOwnerSet,
    stableFarRenewalOwnerActive, stableFarRenewalOwnerGeometry]

theorem renewalOwner_child_cut_implies_parent
    {R q r e p : ℕ}
    (hchild : q * r * (2 * e) * p ≤ squareRootEndpoint R) :
    q * r * e * p ≤ squareRootEndpoint R := by
  have hmono : q * r * e * p ≤ q * r * (2 * e) * p := by
    gcongr
    omega
  exact hmono.trans hchild

theorem renewalOwner_parent_cross_implies_child
    {R q r e p : ℕ}
    (hparent : squareRootEndpoint R < q * q * r * e * p) :
    squareRootEndpoint R < q * q * r * (2 * e) * p := by
  have hmono : q * q * r * e * p ≤ q * q * r * (2 * e) * p := by
    gcongr
    omega
  exact hparent.trans_le hmono

theorem renewalOwner_activity_mismatch_iff_two_shells
    {R q r e p : ℕ} :
    ¬ (stableFarRenewalOwnerGeometry R q r e p ↔
        stableFarRenewalOwnerGeometry R q r (2 * e) p) ↔
      ((q * r * e * p ≤ squareRootEndpoint R ∧
          squareRootEndpoint R < q * q * r * e * p ∧
          ¬ (q * r * (2 * e) * p ≤ squareRootEndpoint R)) ∨
       (q * r * (2 * e) * p ≤ squareRootEndpoint R ∧
          squareRootEndpoint R < q * q * r * (2 * e) * p ∧
          ¬ (squareRootEndpoint R < q * q * r * e * p))) := by
  have hcut :
      q * r * (2 * e) * p ≤ squareRootEndpoint R →
        q * r * e * p ≤ squareRootEndpoint R :=
    renewalOwner_child_cut_implies_parent
  have hcross :
      squareRootEndpoint R < q * q * r * e * p →
        squareRootEndpoint R < q * q * r * (2 * e) * p :=
    renewalOwner_parent_cross_implies_child
  unfold stableFarRenewalOwnerGeometry
  tauto

theorem crossingOuterOwnerSet_membership_mismatch_iff_two_shells
    {R q r e p : ℕ} :
    ¬ (q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) ↔
        q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p))) ↔
      (q ∈ primesUpTo (R - 1) ∧ r < q ∧
        ((q * r * e * p ≤ squareRootEndpoint R ∧
            squareRootEndpoint R < q * q * r * e * p ∧
            ¬ (q * r * (2 * e) * p ≤ squareRootEndpoint R)) ∨
         (q * r * (2 * e) * p ≤ squareRootEndpoint R ∧
            squareRootEndpoint R < q * q * r * (2 * e) * p ∧
            ¬ (squareRootEndpoint R < q * q * r * e * p)))) := by
  rw [mem_crossingOuterOwnerSet_iff_active,
    mem_crossingOuterOwnerSet_iff_active]
  by_cases hqmem : q ∈ primesUpTo (R - 1)
  · by_cases hrq : r < q
    · simp only [stableFarRenewalOwnerActive, hqmem, hrq, true_and]
      exact renewalOwner_activity_mismatch_iff_two_shells
    · simp [stableFarRenewalOwnerActive, hqmem, hrq]
  · simp [stableFarRenewalOwnerActive, hqmem]


/-- Squarefree physical site obtained by transporting an old-owner renewal label
off its q-square collision and retaining one copy of the old owner. -/
def stableFarRenewalTransportSite (q r e p : ℕ) : ℕ :=
  q * r * e * p

/-- Any admissible old owner whose first-power product is physical transports
to an honest squarefree site in the canonical shell. -/
theorem renewalTransportSite_mem_squarefreeShell_of_cut
    {R q r e p : ℕ} (hR : 2 ≤ R)
    (hy : (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R)
    (hqOld : q ∈ primesUpTo (R - 1)) (hrq : r < q)
    (hcut : q * r * e * p ≤ squareRootEndpoint R) :
    stableFarRenewalTransportSite q r e p ∈
      orderedEulerCutSquarefreeShell R := by
  have hyBase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelFarPrimeLowCofactorTriples_iff_data.mp hyBase with
    ⟨hrPrime, hrR, he1, hpPrime, hpR, heSq, her, _hyCut⟩
  rcases mem_primesUpTo.mp hqOld with ⟨hqPrime, hqPred⟩
  have hRpos : 0 < R := by omega
  have hqR : q < R := Nat.lt_of_le_pred hRpos hqPred
  have hePos : 0 < e := by omega
  have hrePos : 0 < r * e := Nat.mul_pos hrPrime.pos hePos
  have hre1 : 1 ≤ r * e := by omega
  have hreFresh : ¬ r ∣ e :=
    squareRootLowPrimePrime_fresh_of_lpf_lt he1 hrPrime her
  have hreCop : Nat.Coprime r e :=
    (hrPrime.coprime_iff_not_dvd).2 hreFresh
  have hreSq : Squarefree (r * e) :=
    (Nat.squarefree_mul hreCop).2 ⟨hrPrime.squarefree, heSq⟩
  have hlpf_re : canonicalLargestPrimeFactor (r * e) = r := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough he1 hrPrime her
  have hreq : canonicalLargestPrimeFactor (r * e) < q := by
    rw [hlpf_re]
    exact hrq
  have hqFresh : ¬ q ∣ r * e :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hre1 hqPrime hreq
  have hqCop : Nat.Coprime q (r * e) :=
    (hqPrime.coprime_iff_not_dvd).2 hqFresh
  have hqreSq : Squarefree (q * (r * e)) :=
    (Nat.squarefree_mul hqCop).2 ⟨hqPrime.squarefree, hreSq⟩
  have hqrePos : 0 < q * (r * e) := Nat.mul_pos hqPrime.pos hrePos
  have hqre1 : 1 ≤ q * (r * e) := by omega
  have hlpf_qre : canonicalLargestPrimeFactor (q * (r * e)) = q := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hre1 hqPrime hreq
  have hqrep : canonicalLargestPrimeFactor (q * (r * e)) < p := by
    rw [hlpf_qre]
    omega
  have hpFresh : ¬ p ∣ q * (r * e) :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hqre1 hpPrime hqrep
  have hpCop : Nat.Coprime (q * (r * e)) p :=
    ((hpPrime.coprime_iff_not_dvd).2 hpFresh).symm
  have hsq : Squarefree ((q * (r * e)) * p) :=
    (Nat.squarefree_mul hpCop).2 ⟨hqreSq, hpPrime.squarefree⟩
  have hsiteLe :
      stableFarRenewalTransportSite q r e p ≤ squareRootEndpoint R := by
    simpa [stableFarRenewalTransportSite, Nat.mul_assoc] using hcut
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hne
  apply mem_orderedEulerCutSquarefreeShell.mpr
  refine ⟨?_, ?_, ?_⟩
  · have hqreRawPos : 0 < q * r * e := by
      simpa [Nat.mul_assoc] using
        Nat.mul_pos (Nat.mul_pos hqPrime.pos hrPrime.pos) hePos
    have hqreRaw1 : 1 ≤ q * r * e := by omega
    have hpSite : p ≤ stableFarRenewalTransportSite q r e p := by
      have hmul := Nat.mul_le_mul_right p hqreRaw1
      simpa [stableFarRenewalTransportSite, Nat.mul_assoc] using hmul
    omega
  · have hlt : stableFarRenewalTransportSite q r e p < R * R :=
      hsiteLe.trans_lt hXlt
    simpa [pow_two] using hlt
  · simpa [stableFarRenewalTransportSite, Nat.mul_assoc] using hsq

/-- The transported squarefree site carries exactly the sign-reversed returned
cofactor weight. -/
theorem renewalTransportSite_weight_eq_neg_returned
    {R q r e p : ℕ}
    (hy : (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R)
    (hqOld : q ∈ primesUpTo (R - 1)) (hrq : r < q) :
    canonicalMoebiusWeight (stableFarRenewalTransportSite q r e p) =
      -canonicalMoebiusWeight e := by
  have hyBase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases mem_lowWheelFarPrimeLowCofactorTriples_iff_data.mp hyBase with
    ⟨hrPrime, hrR, he1, hpPrime, hpR, _heSq, her, _hyCut⟩
  rcases mem_primesUpTo.mp hqOld with ⟨hqPrime, hqPred⟩
  have hRpos : 0 < R := hrPrime.pos.trans hrR
  have hqR : q < R := Nat.lt_of_le_pred hRpos hqPred
  have hePos : 0 < e := by omega
  have hrePos : 0 < r * e := Nat.mul_pos hrPrime.pos hePos
  have hre1 : 1 ≤ r * e := by omega
  have hreFresh : ¬ r ∣ e :=
    squareRootLowPrimePrime_fresh_of_lpf_lt he1 hrPrime her
  have hreFlip :
      canonicalMoebiusWeight (r * e) = -canonicalMoebiusWeight e := by
    have h := canonicalMoebiusWeight_mul_freshPrime hrPrime hreFresh
    simpa [Nat.mul_comm] using h
  have hlpf_re : canonicalLargestPrimeFactor (r * e) = r := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough he1 hrPrime her
  have hreq : canonicalLargestPrimeFactor (r * e) < q := by
    rw [hlpf_re]
    exact hrq
  have hqFresh : ¬ q ∣ r * e :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hre1 hqPrime hreq
  have hqFlip :
      canonicalMoebiusWeight (q * (r * e)) =
        -canonicalMoebiusWeight (r * e) := by
    have h := canonicalMoebiusWeight_mul_freshPrime hqPrime hqFresh
    simpa [Nat.mul_comm] using h
  have hqrePos : 0 < q * (r * e) := Nat.mul_pos hqPrime.pos hrePos
  have hqre1 : 1 ≤ q * (r * e) := by omega
  have hlpf_qre : canonicalLargestPrimeFactor (q * (r * e)) = q := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hre1 hqPrime hreq
  have hqrep : canonicalLargestPrimeFactor (q * (r * e)) < p := by
    rw [hlpf_qre]
    omega
  have hpFresh : ¬ p ∣ q * (r * e) :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hqre1 hpPrime hqrep
  have hpFlip :
      canonicalMoebiusWeight ((q * (r * e)) * p) =
        -canonicalMoebiusWeight (q * (r * e)) :=
    canonicalMoebiusWeight_mul_freshPrime hpPrime hpFresh
  change canonicalMoebiusWeight (q * r * e * p) = -canonicalMoebiusWeight e
  rw [show q * r * e * p = (q * (r * e)) * p by ring, hpFlip, hqFlip, hreFlip]
  ring

/-- The transported renewal site retains the full ordered prime hierarchy
P+(e) < r < q < R < p, so its arithmetic factorization recovers every label. -/
theorem renewalTransportSite_unique
    {R q r e p q' r' e' p' : ℕ}
    (hr : r.Prime) (he1 : 1 ≤ e)
    (her : canonicalLargestPrimeFactor e < r)
    (hq : q.Prime) (hrq : r < q) (hqR : q < R)
    (hp : p.Prime) (hRp : R < p)
    (hr' : r'.Prime) (he1' : 1 ≤ e')
    (her' : canonicalLargestPrimeFactor e' < r')
    (hq' : q'.Prime) (hrq' : r' < q') (hqR' : q' < R)
    (hp' : p'.Prime) (hRp' : R < p')
    (heq :
      stableFarRenewalTransportSite q r e p =
        stableFarRenewalTransportSite q' r' e' p') :
    q = q' ∧ r = r' ∧ e = e' ∧ p = p' := by
  have hePos : 0 < e := by omega
  have hrePos : 0 < r * e := Nat.mul_pos hr.pos hePos
  have hre1 : 1 ≤ r * e := by omega
  have hlpf_re : canonicalLargestPrimeFactor (r * e) = r := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough he1 hr her
  have hreq : canonicalLargestPrimeFactor (r * e) < q := by
    rw [hlpf_re]
    exact hrq
  have hqrePos : 0 < q * (r * e) := Nat.mul_pos hq.pos hrePos
  have hqre1 : 1 ≤ q * (r * e) := by omega
  have hlpf_qre : canonicalLargestPrimeFactor (q * (r * e)) = q := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hre1 hq hreq
  have hqrep : canonicalLargestPrimeFactor (q * (r * e)) < p := by
    rw [hlpf_qre]
    omega
  have hlpf_site :
      canonicalLargestPrimeFactor ((q * (r * e)) * p) = p :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hqre1 hp hqrep

  have hePos' : 0 < e' := by omega
  have hrePos' : 0 < r' * e' := Nat.mul_pos hr'.pos hePos'
  have hre1' : 1 ≤ r' * e' := by omega
  have hlpf_re' : canonicalLargestPrimeFactor (r' * e') = r' := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough he1' hr' her'
  have hreq' : canonicalLargestPrimeFactor (r' * e') < q' := by
    rw [hlpf_re']
    exact hrq'
  have hqrePos' : 0 < q' * (r' * e') := Nat.mul_pos hq'.pos hrePos'
  have hqre1' : 1 ≤ q' * (r' * e') := by omega
  have hlpf_qre' : canonicalLargestPrimeFactor (q' * (r' * e')) = q' := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hre1' hq' hreq'
  have hqrep' : canonicalLargestPrimeFactor (q' * (r' * e')) < p' := by
    rw [hlpf_qre']
    omega
  have hlpf_site' :
      canonicalLargestPrimeFactor ((q' * (r' * e')) * p') = p' :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hqre1' hp' hqrep'

  have heqNested :
      (q * (r * e)) * p = (q' * (r' * e')) * p' := by
    simpa [stableFarRenewalTransportSite, Nat.mul_assoc] using heq
  have hpp : p = p' := by
    rw [← hlpf_site, ← hlpf_site', heqNested]
  subst p'
  have hcore : q * (r * e) = q' * (r' * e') :=
    Nat.mul_right_cancel hp.pos heqNested
  have hqq : q = q' := by
    rw [← hlpf_qre, ← hlpf_qre', hcore]
  subst q'
  have hre : r * e = r' * e' :=
    Nat.mul_left_cancel hq.pos hcore
  have hrr : r = r' := by
    rw [← hlpf_re, ← hlpf_re', hre]
  subst r'
  have hee : e = e' :=
    Nat.mul_left_cancel hr.pos hre
  exact ⟨rfl, rfl, hee, rfl⟩

/-- On actual returned states and old-owner shell data, the transported map is
globally injective. -/
theorem renewalTransportSite_unique_of_descended
    {R q r e p q' r' e' p' : ℕ}
    (hy : (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R)
    (hy' : (r', (e', p')) ∈ lowWheelFarPrimeQ2DescendedTriples R)
    (hqOld : q ∈ primesUpTo (R - 1)) (hrq : r < q)
    (hqOld' : q' ∈ primesUpTo (R - 1)) (hrq' : r' < q')
    (heq :
      stableFarRenewalTransportSite q r e p =
        stableFarRenewalTransportSite q' r' e' p') :
    q = q' ∧ r = r' ∧ e = e' ∧ p = p' := by
  have hyBase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  have hyBase' : (r', (e', p')) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy').1
  rcases mem_lowWheelFarPrimeLowCofactorTriples_iff_data.mp hyBase with
    ⟨hr, hrR, he1, hp, hpR, _heSq, her, _hcut⟩
  rcases mem_lowWheelFarPrimeLowCofactorTriples_iff_data.mp hyBase' with
    ⟨hr', hrR', he1', hp', hpR', _heSq', her', _hcut'⟩
  rcases mem_primesUpTo.mp hqOld with ⟨hq, hqPred⟩
  rcases mem_primesUpTo.mp hqOld' with ⟨hq', hqPred'⟩
  have hRpos : 0 < R := hr.pos.trans hrR
  have hqR : q < R := Nat.lt_of_le_pred hRpos hqPred
  have hqR' : q' < R := Nat.lt_of_le_pred hRpos hqPred'
  have hRp : R < p := by omega
  have hRp' : R < p' := by omega
  exact renewalTransportSite_unique
    hr he1 her hq hrq hqR hp hRp
    hr' he1' her' hq' hrq' hqR' hp' hRp' heq

def stableFarRenewalFirstCutShell
    (R q r e p : ℕ) : Prop :=
  q ∈ primesUpTo (R - 1) ∧ r < q ∧
    q * r * e * p ≤ squareRootEndpoint R ∧
    squareRootEndpoint R < q * q * r * e * p ∧
    ¬ (q * r * (2 * e) * p ≤ squareRootEndpoint R)

/-- Second renewal defect shell: doubling e creates the q-square crossing
while the doubled first-power product remains physical. -/
def stableFarRenewalSecondCrossShell
    (R q r e p : ℕ) : Prop :=
  q ∈ primesUpTo (R - 1) ∧ r < q ∧
    q * r * (2 * e) * p ≤ squareRootEndpoint R ∧
    squareRootEndpoint R < q * q * r * (2 * e) * p ∧
    ¬ (squareRootEndpoint R < q * q * r * e * p)

/-- The two-shell theorem in named form. -/
theorem crossingOuterOwnerSet_membership_mismatch_iff_named_shells
    {R q r e p : ℕ} :
    ¬ (q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) ↔
        q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p))) ↔
      (stableFarRenewalFirstCutShell R q r e p ∨
        stableFarRenewalSecondCrossShell R q r e p) := by
  constructor
  · intro h
    have hs :=
      (crossingOuterOwnerSet_membership_mismatch_iff_two_shells
        (R := R) (q := q) (r := r) (e := e) (p := p)).mp h
    unfold stableFarRenewalFirstCutShell stableFarRenewalSecondCrossShell
    tauto
  · intro h
    apply
      (crossingOuterOwnerSet_membership_mismatch_iff_two_shells
        (R := R) (q := q) (r := r) (e := e) (p := p)).mpr
    unfold stableFarRenewalFirstCutShell stableFarRenewalSecondCrossShell at h
    tauto

def stableFarCenteredRenewalCoeff
    (R r e p : ℕ) : ℂ :=
  1 - ((lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p))).card : ℂ)

def stableFarCenteredRenewalWeight
    (R r e p : ℕ) : ℂ :=
  stableFarCenteredRenewalCoeff R r e p * canonicalMoebiusWeight e

theorem stableFarCenteredRenewalWeight_add_double
    {R r e p : ℕ} (he : Odd e) :
    stableFarCenteredRenewalWeight R r e p +
        stableFarCenteredRenewalWeight R r (2 * e) p =
      (((lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p))).card : ℂ) -
        ((lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p))).card : ℂ)) *
          canonicalMoebiusWeight e := by
  unfold stableFarCenteredRenewalWeight stableFarCenteredRenewalCoeff
  rw [canonicalMoebiusWeight_two_mul, if_pos he]
  ring

def stableFarRenewalOwnerIndicatorDifference
    (R q r e p : ℕ) : ℤ :=
  (if q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p))
    then 1 else 0) -
  (if q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p))
    then 1 else 0)


theorem ownerIndicatorDifference_eq_neg_one_of_firstCutShell
    {R q r e p : ℕ}
    (h : stableFarRenewalFirstCutShell R q r e p) :
    stableFarRenewalOwnerIndicatorDifference R q r e p = -1 := by
  rcases h with ⟨hq, hrq, hcut, hcross, hchildCut⟩
  have hparent :
      q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) := by
    exact mem_crossingOuterOwnerSet_iff_active.mpr
      ⟨hq, hrq, hcut, hcross⟩
  have hchild :
      q ∉ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p)) := by
    intro hc
    have hcData := mem_crossingOuterOwnerSet_iff_active.mp hc
    exact hchildCut hcData.2.2.1
  simp [stableFarRenewalOwnerIndicatorDifference, hparent, hchild]

theorem ownerIndicatorDifference_eq_one_of_secondCrossShell
    {R q r e p : ℕ}
    (h : stableFarRenewalSecondCrossShell R q r e p) :
    stableFarRenewalOwnerIndicatorDifference R q r e p = 1 := by
  rcases h with ⟨hq, hrq, hchildCut, hchildCross, hparentCross⟩
  have hchild :
      q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p)) := by
    exact mem_crossingOuterOwnerSet_iff_active.mpr
      ⟨hq, hrq, hchildCut, hchildCross⟩
  have hparent :
      q ∉ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) := by
    intro hp0
    have hpData := mem_crossingOuterOwnerSet_iff_active.mp hp0
    exact hparentCross hpData.2.2.2
  simp [stableFarRenewalOwnerIndicatorDifference, hparent, hchild]

/-- On shell 1 the pointwise renewal contribution is the transported Mobius
weight itself: it is the negative of the canonical child charge. -/
theorem firstCutShell_indicator_weight_eq_transportWeight
    {R q r e p : ℕ}
    (hy : (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R)
    (h : stableFarRenewalFirstCutShell R q r e p) :
    ((stableFarRenewalOwnerIndicatorDifference R q r e p : ℤ) : ℂ) *
        canonicalMoebiusWeight e =
      canonicalMoebiusWeight (stableFarRenewalTransportSite q r e p) := by
  rcases h with ⟨hq, hrq, hcut, hcross, hchildCut⟩
  rw [ownerIndicatorDifference_eq_neg_one_of_firstCutShell
      ⟨hq, hrq, hcut, hcross, hchildCut⟩]
  push_cast
  rw [renewalTransportSite_weight_eq_neg_returned hy hq hrq]
  ring

/-- On shell 2 the pointwise renewal contribution is exactly the canonical
child charge, namely minus the transported Mobius weight. -/
theorem secondCrossShell_indicator_weight_eq_neg_transportWeight
    {R q r e p : ℕ}
    (hy : (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R)
    (h : stableFarRenewalSecondCrossShell R q r e p) :
    ((stableFarRenewalOwnerIndicatorDifference R q r e p : ℤ) : ℂ) *
        canonicalMoebiusWeight e =
      -canonicalMoebiusWeight (stableFarRenewalTransportSite q r e p) := by
  rcases h with ⟨hq, hrq, hchildCut, hchildCross, hparentCross⟩
  have hcut : q * r * e * p ≤ squareRootEndpoint R :=
    renewalOwner_child_cut_implies_parent hchildCut
  rw [ownerIndicatorDifference_eq_one_of_secondCrossShell
      ⟨hq, hrq, hchildCut, hchildCross, hparentCross⟩]
  push_cast
  rw [renewalTransportSite_weight_eq_neg_returned hy hq hrq]
  ring

/-- Both renewal shells transport to the canonical squarefree physical shell. -/
theorem firstCutShell_transportSite_mem_squarefreeShell
    {R q r e p : ℕ} (hR : 2 ≤ R)
    (hy : (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R)
    (h : stableFarRenewalFirstCutShell R q r e p) :
    stableFarRenewalTransportSite q r e p ∈
      orderedEulerCutSquarefreeShell R := by
  rcases h with ⟨hq, hrq, hcut, _hcross, _hchildCut⟩
  exact renewalTransportSite_mem_squarefreeShell_of_cut hR hy hq hrq hcut

theorem secondCrossShell_transportSite_mem_squarefreeShell
    {R q r e p : ℕ} (hR : 2 ≤ R)
    (hy : (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R)
    (h : stableFarRenewalSecondCrossShell R q r e p) :
    stableFarRenewalTransportSite q r e p ∈
      orderedEulerCutSquarefreeShell R := by
  rcases h with ⟨hq, hrq, hchildCut, _hchildCross, _hparentCross⟩
  have hcut : q * r * e * p ≤ squareRootEndpoint R :=
    renewalOwner_child_cut_implies_parent hchildCut
  exact renewalTransportSite_mem_squarefreeShell_of_cut hR hy hq hrq hcut


theorem renewalOwnerIndicatorDifference_ne_zero_imp_two_shells
    {R q r e p : ℕ}
    (hne : stableFarRenewalOwnerIndicatorDifference R q r e p ≠ 0) :
    q ∈ primesUpTo (R - 1) ∧ r < q ∧
      ((q * r * e * p ≤ squareRootEndpoint R ∧
          squareRootEndpoint R < q * q * r * e * p ∧
          ¬ (q * r * (2 * e) * p ≤ squareRootEndpoint R)) ∨
       (q * r * (2 * e) * p ≤ squareRootEndpoint R ∧
          squareRootEndpoint R < q * q * r * (2 * e) * p ∧
          ¬ (squareRootEndpoint R < q * q * r * e * p))) := by
  have hmismatch :
      ¬ (q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) ↔
          q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p))) := by
    intro hiff
    unfold stableFarRenewalOwnerIndicatorDifference at hne
    by_cases hparent :
        q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p))
    · have hchild := hiff.mp hparent
      simp [hparent, hchild] at hne
    · have hchild :
          q ∉ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p)) := by
        intro hc
        exact hparent (hiff.mpr hc)
      simp [hparent, hchild] at hne
  exact (crossingOuterOwnerSet_membership_mismatch_iff_two_shells).mp hmismatch


theorem crossingOuterOwnerSet_card_difference_eq_indicator_sum
    (R r e p : ℕ) :
    ((lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p))).card : ℤ) -
        ((lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p))).card : ℤ) =
      ∑ q ∈ primesUpTo (R - 1),
        stableFarRenewalOwnerIndicatorDifference R q r e p := by
  have hchild :
      ((lowWheelFarPrimeQ2CrossingOuterOwnerSet R
          (r, (2 * e, p))).card : ℤ) =
        ∑ q ∈ primesUpTo (R - 1),
          if q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R
            (r, (2 * e, p)) then (1 : ℤ) else 0 := by
    unfold lowWheelFarPrimeQ2CrossingOuterOwnerSet
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro q hq
    simp [hq]
  have hparent :
      ((lowWheelFarPrimeQ2CrossingOuterOwnerSet R
          (r, (e, p))).card : ℤ) =
        ∑ q ∈ primesUpTo (R - 1),
          if q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R
            (r, (e, p)) then (1 : ℤ) else 0 := by
    unfold lowWheelFarPrimeQ2CrossingOuterOwnerSet
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro q hq
    simp [hq]
  rw [hchild, hparent]
  unfold stableFarRenewalOwnerIndicatorDifference
  rw [Finset.sum_sub_distrib]

theorem stableFarCenteredRenewalWeight_add_double_eq_ownerDifferenceSum
    {R r e p : ℕ} (he : Odd e) :
    stableFarCenteredRenewalWeight R r e p +
        stableFarCenteredRenewalWeight R r (2 * e) p =
      ((∑ q ∈ primesUpTo (R - 1),
          stableFarRenewalOwnerIndicatorDifference R q r e p : ℤ) : ℂ) *
        canonicalMoebiusWeight e := by
  rw [stableFarCenteredRenewalWeight_add_double he]
  have hcast := congrArg (fun z : ℤ => (z : ℂ))
    (crossingOuterOwnerSet_card_difference_eq_indicator_sum R r e p)
  push_cast at hcast
  rw [hcast]
  push_cast
  rfl


/-! ## Global multiplicity-one transport of the renewal defect -/

abbrev StableFarRenewalShellTag := ℕ × (ℕ × (ℕ × ℕ))

def stableFarRenewalTwoShellCarrier
    (R : ℕ) : Finset StableFarRenewalShellTag :=
  ((primesUpTo (R - 1)).product
      (lowWheelFarPrimeQ2DescendedTriples R)).filter fun t =>
    stableFarRenewalFirstCutShell R t.1 t.2.1 t.2.2.1 t.2.2.2 ∨
      stableFarRenewalSecondCrossShell R t.1 t.2.1 t.2.2.1 t.2.2.2

def stableFarRenewalTwoShellTransport
    (t : StableFarRenewalShellTag) : ℕ :=
  stableFarRenewalTransportSite t.1 t.2.1 t.2.2.1 t.2.2.2

theorem stableFarRenewalTwoShellCarrier_data
    {R : ℕ} {t : StableFarRenewalShellTag}
    (ht : t ∈ stableFarRenewalTwoShellCarrier R) :
    t.1 ∈ primesUpTo (R - 1) ∧
      t.2 ∈ lowWheelFarPrimeQ2DescendedTriples R ∧
      (stableFarRenewalFirstCutShell R t.1 t.2.1 t.2.2.1 t.2.2.2 ∨
        stableFarRenewalSecondCrossShell R t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  rcases Finset.mem_filter.mp ht with ⟨hprod, hshell⟩
  rcases Finset.mem_product.mp hprod with ⟨hq, hy⟩
  exact ⟨hq, hy, hshell⟩

/-- The transported renewal defect has global multiplicity one.  No two
different owner/returned-coordinate shell atoms land on the same squarefree
physical site. -/
theorem stableFarRenewalTwoShellTransport_injOn
    (R : ℕ) :
    Set.InjOn stableFarRenewalTwoShellTransport
      (stableFarRenewalTwoShellCarrier R :
        Set StableFarRenewalShellTag) := by
  intro a ha b hb hab
  have haFin : a ∈ stableFarRenewalTwoShellCarrier R := by simpa using ha
  have hbFin : b ∈ stableFarRenewalTwoShellCarrier R := by simpa using hb
  rcases a with ⟨q, ⟨r, ⟨e, p⟩⟩⟩
  rcases b with ⟨q', ⟨r', ⟨e', p'⟩⟩⟩
  rcases stableFarRenewalTwoShellCarrier_data haFin with
    ⟨hqOld, hy, hshell⟩
  rcases stableFarRenewalTwoShellCarrier_data hbFin with
    ⟨hqOld', hy', hshell'⟩
  have hrq : r < q := by
    rcases hshell with hfirst | hsecond
    · exact hfirst.2.1
    · exact hsecond.2.1
  have hrq' : r' < q' := by
    rcases hshell' with hfirst | hsecond
    · exact hfirst.2.1
    · exact hsecond.2.1
  have hlabels :=
    renewalTransportSite_unique_of_descended
      hy hy' hqOld hrq hqOld' hrq'
      (by simpa [stableFarRenewalTwoShellTransport] using hab)
  rcases hlabels with ⟨hqq, hrr, hee, hpp⟩
  exact Prod.ext hqq (Prod.ext hrr (Prod.ext hee hpp))

def stableFarRenewalTwoShellImage (R : ℕ) : Finset ℕ :=
  (stableFarRenewalTwoShellCarrier R).image
    stableFarRenewalTwoShellTransport

/-- Every transported renewal defect lies on the same canonical squarefree
physical shell that carries the canonical defect ledger. -/
theorem stableFarRenewalTwoShellImage_subset_squarefreeShell
    {R : ℕ} (hR : 2 ≤ R) :
    stableFarRenewalTwoShellImage R ⊆ orderedEulerCutSquarefreeShell R := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨t, ht, rfl⟩
  rcases t with ⟨q, ⟨r, ⟨e, p⟩⟩⟩
  rcases stableFarRenewalTwoShellCarrier_data ht with
    ⟨_hqOld, hy, hshell⟩
  rcases hshell with hfirst | hsecond
  · simpa [stableFarRenewalTwoShellTransport] using
      firstCutShell_transportSite_mem_squarefreeShell hR hy hfirst
  · simpa [stableFarRenewalTwoShellTransport] using
      secondCrossShell_transportSite_mem_squarefreeShell hR hy hsecond

/-- The image census loses no atoms: the global physical transport is genuinely
multiplicity-free. -/
theorem stableFarRenewalTwoShellImage_card_eq_carrier
    (R : ℕ) :
    (stableFarRenewalTwoShellImage R).card =
      (stableFarRenewalTwoShellCarrier R).card := by
  unfold stableFarRenewalTwoShellImage
  exact Finset.card_image_iff.mpr
    (stableFarRenewalTwoShellTransport_injOn R)


/-! ## Full returned-fibre dyadic reassembly -/

def stableFarReturnedCofactorCutoff (R r p : ℕ) : ℕ :=
  squareRootEndpoint R / (r * r * p)

def stableFarCenteredReturnedFibre
    (R r p : ℕ) : ℂ :=
  ∑ e ∈ squareRootLowPrimeGoSmoothCofactors r
      (stableFarReturnedCofactorCutoff R r p),
    stableFarCenteredRenewalWeight R r e p

/-- The whole centered returned fibre, not an isolated owner shell, pairs
exactly under e -> 2e.  The baseline disappears from every interior pair; only
the owner-window finite difference and the explicit q-rough top boundary
remain. -/
theorem stableFarCenteredReturnedFibre_eq_ownerDifference_add_boundary
    {R r p : ℕ} (hr : r.Prime) (hrgt : 2 < r) :
    stableFarCenteredReturnedFibre R r p =
      (∑ d ∈ oddCofactorPrefix
          (stableFarReturnedCofactorCutoff R r p / 2),
        if canonicalLargestPrimeFactor d < r then
          (((lowWheelFarPrimeQ2CrossingOuterOwnerSet
              R (r, (2 * d, p))).card : ℂ) -
            ((lowWheelFarPrimeQ2CrossingOuterOwnerSet
              R (r, (d, p))).card : ℂ)) *
            canonicalMoebiusWeight d
        else 0) +
      ∑ d ∈ roughDyadicCofactorBoundary r
          (stableFarReturnedCofactorCutoff R r p),
        stableFarCenteredRenewalWeight R r d p := by
  unfold stableFarCenteredReturnedFibre
  change
    (∑ e ∈ squareRootLowPrimeGoSmoothCofactors r
        (stableFarReturnedCofactorCutoff R r p),
      stableFarCenteredRenewalCoeff R r e p * canonicalMoebiusWeight e) = _
  rw [squareRootLowPrimeGoSmoothCofactorWeightedMass_eq_dyadicPairs_add_boundary
    hr hrgt (fun e => stableFarCenteredRenewalCoeff R r e p)]
  congr 1
  · apply Finset.sum_congr rfl
    intro d _hd
    by_cases hrough : canonicalLargestPrimeFactor d < r
    · rw [if_pos hrough, if_pos hrough]
      unfold stableFarCenteredRenewalCoeff
      ring
    · simp [hrough]

/-- Expanding the owner-cardinality difference by finite Fubini removes the
last prime-count abstraction.  Every paired returned cofactor is now a signed
sum of pointwise old-owner changes, before any absolute value. -/
theorem stableFarCenteredReturnedFibre_eq_ownerIndicatorSum_add_boundary
    {R r p : ℕ} (hr : r.Prime) (hrgt : 2 < r) :
    stableFarCenteredReturnedFibre R r p =
      (∑ d ∈ oddCofactorPrefix
          (stableFarReturnedCofactorCutoff R r p / 2),
        if canonicalLargestPrimeFactor d < r then
          (((∑ q ∈ primesUpTo (R - 1),
              stableFarRenewalOwnerIndicatorDifference R q r d p : ℤ) : ℂ) *
            canonicalMoebiusWeight d)
        else 0) +
      ∑ d ∈ roughDyadicCofactorBoundary r
          (stableFarReturnedCofactorCutoff R r p),
        stableFarCenteredRenewalWeight R r d p := by
  rw [stableFarCenteredReturnedFibre_eq_ownerDifference_add_boundary hr hrgt]
  congr 1
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hrough : canonicalLargestPrimeFactor d < r
  · rw [if_pos hrough, if_pos hrough]
    have hcast := congrArg (fun z : ℤ => (z : ℂ))
      (crossingOuterOwnerSet_card_difference_eq_indicator_sum R r d p)
    push_cast at hcast
    rw [hcast]
    push_cast
    rfl
  · simp [hrough]



/-! ## Production returned-coordinate Fubini -/

def stableFarRenewalCoordinatePairs (R : ℕ) : Finset (ℕ × ℕ) :=
  (lowWheelFarPrimeQ2DescendedTriples R).image fun y => (y.1, y.2.2)

theorem mem_lowWheelFarPrimeQ2DescendedTriples_iff_renewalCofactor
    {R r e p : ℕ} :
    (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R ↔
      r.Prime ∧ r < R ∧ p.Prime ∧ R + 8 ≤ p ∧
        e ∈ squareRootLowPrimeGoSmoothCofactors r
          (stableFarReturnedCofactorCutoff R r p) := by
  constructor
  · intro hdesc
    have hbase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp hdesc).1
    have hq2 := (Finset.mem_filter.mp hdesc).2
    rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
      ⟨hr, hrR, he1, hp, hpR, heSq, her, _hcut⟩
    have hdenPos : 0 < r * r * p :=
      Nat.mul_pos (Nat.mul_pos hr.pos hr.pos) hp.pos
    have heCut : e ≤ stableFarReturnedCofactorCutoff R r p := by
      unfold stableFarReturnedCofactorCutoff
      apply (Nat.le_div_iff_mul_le hdenPos).2
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq2
    refine ⟨hr, hrR, hp, hpR, ?_⟩
    exact mem_squareRootLowPrimeGoSmoothCofactors.mpr
      ⟨he1, heCut, heSq, her⟩
  · rintro ⟨hr, hrR, hp, hpR, he⟩
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp he with
      ⟨he1, heCut, heSq, heRough⟩
    have hdenPos : 0 < r * r * p :=
      Nat.mul_pos (Nat.mul_pos hr.pos hr.pos) hp.pos
    have hq2raw : e * (r * r * p) ≤ squareRootEndpoint R := by
      apply (Nat.le_div_iff_mul_le hdenPos).1
      simpa [stableFarReturnedCofactorCutoff] using heCut
    have hq2 : r * r * e * p ≤ squareRootEndpoint R := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq2raw
    have hbaseCut : r * e * p ≤ squareRootEndpoint R := by
      have hr1 : 1 ≤ r := hr.one_le
      have hle : r * e * p ≤ r * r * e * p := by
        have h := Nat.mul_le_mul_right (r * e * p) hr1
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
      exact hle.trans hq2
    have hbase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
      lowWheelFarPrimeLowCofactorTriple_mem_of_data
        hr hrR he1 hp hpR heSq heRough hbaseCut
    exact Finset.mem_filter.mpr ⟨hbase, hq2⟩

theorem stableFarRenewalCoordinatePair_data
    {R : ℕ} {rp : ℕ × ℕ}
    (hrp : rp ∈ stableFarRenewalCoordinatePairs R) :
    rp.1.Prime ∧ rp.1 < R ∧ rp.2.Prime ∧ R + 8 ≤ rp.2 := by
  rcases Finset.mem_image.mp hrp with ⟨y, hy, hcoord⟩
  rcases y with ⟨r, ⟨e, p⟩⟩
  have hdata :=
    (mem_lowWheelFarPrimeQ2DescendedTriples_iff_renewalCofactor).1 hy
  have hrEq : r = rp.1 := congrArg Prod.fst hcoord
  have hpEq : p = rp.2 := congrArg Prod.snd hcoord
  subst r
  subst p
  exact ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2.1⟩

def stableFarRenewalCoordinateFiber
    (R : ℕ) (rp : ℕ × ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeQ2DescendedTriples R).filter fun y =>
    (y.1, y.2.2) = rp

theorem stableFarRenewalCoordinateFiber_eq_cofactorImage
    {R : ℕ} {rp : ℕ × ℕ}
    (hrp : rp ∈ stableFarRenewalCoordinatePairs R) :
    stableFarRenewalCoordinateFiber R rp =
      (squareRootLowPrimeGoSmoothCofactors rp.1
        (stableFarReturnedCofactorCutoff R rp.1 rp.2)).image
          (fun e => (rp.1, (e, rp.2))) := by
  have hdata := stableFarRenewalCoordinatePair_data hrp
  ext y
  rcases y with ⟨r, ⟨e, p⟩⟩
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hdesc, hcoord⟩
    have hrEq : r = rp.1 := congrArg Prod.fst hcoord
    have hpEq : p = rp.2 := congrArg Prod.snd hcoord
    subst r
    subst p
    have he :=
      (mem_lowWheelFarPrimeQ2DescendedTriples_iff_renewalCofactor).1 hdesc
    exact Finset.mem_image.mpr ⟨e, he.2.2.2.2, rfl⟩
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨e', he', heq⟩
    have hdesc :
        (rp.1, (e', rp.2)) ∈ lowWheelFarPrimeQ2DescendedTriples R :=
      (mem_lowWheelFarPrimeQ2DescendedTriples_iff_renewalCofactor).2
        ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2, he'⟩
    have hz :
        (rp.1, (e', rp.2)) ∈ stableFarRenewalCoordinateFiber R rp :=
      Finset.mem_filter.mpr ⟨hdesc, rfl⟩
    rw [heq] at hz
    exact hz

theorem stableFarRenewalCoordinateFiber_centeredMass
    {R : ℕ} {rp : ℕ × ℕ}
    (hrp : rp ∈ stableFarRenewalCoordinatePairs R) :
    (∑ y ∈ stableFarRenewalCoordinateFiber R rp,
      (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
        canonicalMoebiusWeight y.2.1) =
      stableFarCenteredReturnedFibre R rp.1 rp.2 := by
  rw [stableFarRenewalCoordinateFiber_eq_cofactorImage hrp]
  rw [Finset.sum_image]
  · unfold stableFarCenteredReturnedFibre
    apply Finset.sum_congr rfl
    intro e he
    have hdata := stableFarRenewalCoordinatePair_data hrp
    have hdesc :
        (rp.1, (e, rp.2)) ∈ lowWheelFarPrimeQ2DescendedTriples R :=
      (mem_lowWheelFarPrimeQ2DescendedTriples_iff_renewalCofactor).2
        ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2, he⟩
    have hm :=
      lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_ownerSet_card hdesc
    rw [hm]
    rfl
  · intro a _ha b _hb hab
    exact congrArg (fun y : ℕ × (ℕ × ℕ) => y.2.1) hab

/-- **Global production Fubini.**  The repo's actual centered q² tower is the
sum of the exact returned fibres that the weighted dyadic theorem compresses. -/
theorem farFourQ2CenteredTower_eq_sum_stableFarCenteredReturnedFibre
    (R : ℕ) :
    farFourQ2CenteredTower R =
      ∑ rp ∈ stableFarRenewalCoordinatePairs R,
        stableFarCenteredReturnedFibre R rp.1 rp.2 := by
  let S := lowWheelFarPrimeQ2DescendedTriples R
  let T := stableFarRenewalCoordinatePairs R
  let g : ℕ × (ℕ × ℕ) → ℕ × ℕ := fun y => (y.1, y.2.2)
  let f : ℕ × (ℕ × ℕ) → ℂ := fun y =>
    (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
      canonicalMoebiusWeight y.2.1
  have hmaps : ∀ y ∈ S, g y ∈ T := by
    intro y hy
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmaps f
  have hraw :
      (∑ y ∈ S, f y) =
        ∑ rp ∈ T, ∑ y ∈ S with g y = rp, f y := hfiber.symm
  unfold farFourQ2CenteredTower
  change (∑ y ∈ S, f y) =
    ∑ rp ∈ T, stableFarCenteredReturnedFibre R rp.1 rp.2
  rw [hraw]
  apply Finset.sum_congr rfl
  intro rp hrp
  change
    (∑ y ∈ stableFarRenewalCoordinateFiber R rp,
      (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
        canonicalMoebiusWeight y.2.1) =
      stableFarCenteredReturnedFibre R rp.1 rp.2
  exact stableFarRenewalCoordinateFiber_centeredMass hrp



/-! ## Owner-two / odd-returned-owner split -/

def stableFarRenewalOwnerTwoCoordinatePairs (R : ℕ) : Finset (ℕ × ℕ) :=
  (stableFarRenewalCoordinatePairs R).filter fun rp => rp.1 = 2

def stableFarRenewalOddCoordinatePairs (R : ℕ) : Finset (ℕ × ℕ) :=
  (stableFarRenewalCoordinatePairs R).filter fun rp => rp.1 ≠ 2

/-- The actual centered q² tower is an explicit owner-two packet plus the
dyadically compressed odd-returned-owner fibres. -/
theorem farFourQ2CenteredTower_eq_ownerTwo_add_oddDyadicFibres
    (R : ℕ) :
    farFourQ2CenteredTower R =
      (∑ rp ∈ stableFarRenewalOwnerTwoCoordinatePairs R,
        stableFarCenteredReturnedFibre R rp.1 rp.2) +
      ∑ rp ∈ stableFarRenewalOddCoordinatePairs R,
        ((∑ d ∈ oddCofactorPrefix
            (stableFarReturnedCofactorCutoff R rp.1 rp.2 / 2),
          if canonicalLargestPrimeFactor d < rp.1 then
            (((∑ q ∈ primesUpTo (R - 1),
                stableFarRenewalOwnerIndicatorDifference
                  R q rp.1 d rp.2 : ℤ) : ℂ) *
              canonicalMoebiusWeight d)
          else 0) +
        ∑ d ∈ roughDyadicCofactorBoundary rp.1
            (stableFarReturnedCofactorCutoff R rp.1 rp.2),
          stableFarCenteredRenewalWeight R rp.1 d rp.2) := by
  rw [farFourQ2CenteredTower_eq_sum_stableFarCenteredReturnedFibre]
  let S := stableFarRenewalCoordinatePairs R
  let f : ℕ × ℕ → ℂ := fun rp =>
    stableFarCenteredReturnedFibre R rp.1 rp.2
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not S (fun rp => rp.1 = 2) f
  change (∑ rp ∈ S, f rp) = _
  rw [← hsplit]
  congr 1
  apply Finset.sum_congr rfl
  intro rp hrpOdd
  rcases Finset.mem_filter.mp hrpOdd with ⟨hrp, hrne⟩
  have hdata := stableFarRenewalCoordinatePair_data hrp
  have hrgt : 2 < rp.1 := by
    have hr2 := hdata.1.two_le
    omega
  simpa [f] using
    stableFarCenteredReturnedFibre_eq_ownerIndicatorSum_add_boundary
      hdata.1 hrgt



/-! ## The unpaired returned top boundary has no doubled owner -/

/-- On the unpaired q-rough top dyadic boundary of one returned fibre, doubling
the returned cofactor already crosses the first-power cutoff for every possible
old owner.  Hence the doubled child has no old owner at all. -/
theorem crossingOuterOwnerSet_double_eq_empty_of_roughBoundary
    {R r p d : ℕ} (hr : r.Prime) (hp : p.Prime)
    (hd : d ∈ roughDyadicCofactorBoundary r
      (stableFarReturnedCofactorCutoff R r p)) :
    lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * d, p)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨_hqOld, hrq, hcut, _hcross⟩
  have hdWall := (mem_roughDyadicCofactorBoundary.mp hd).1
  have hhalf :=
    (mem_dyadicCofactorBoundary.mp hdWall).2.2.2
  have hdenPos : 0 < r * r * p :=
    Nat.mul_pos (Nat.mul_pos hr.pos hr.pos) hp.pos
  have hXlt : squareRootEndpoint R < (2 * d) * (r * r * p) := by
    unfold stableFarReturnedCofactorCutoff at hhalf
    exact (Nat.div_lt_iff_lt_mul hdenPos).1 hhalf
  have hrqle : r ≤ q := Nat.le_of_lt hrq
  have hmul :
      (2 * d) * (r * r * p) ≤ q * r * (2 * d) * p := by
    have h :=
      Nat.mul_le_mul_right (r * (2 * d) * p) hrqle
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  exact (Nat.not_lt_of_ge hcut) (hXlt.trans_le hmul)

/-- Consequently the centered weight on the unpaired top boundary is its
native Mobius weight plus the same owner-window finite difference used on the
paired interior. -/
theorem stableFarCenteredRenewalWeight_eq_difference_add_native_of_roughBoundary
    {R r p d : ℕ} (hr : r.Prime) (hp : p.Prime)
    (hd : d ∈ roughDyadicCofactorBoundary r
      (stableFarReturnedCofactorCutoff R r p)) :
    stableFarCenteredRenewalWeight R r d p =
      ((((lowWheelFarPrimeQ2CrossingOuterOwnerSet
          R (r, (2 * d, p))).card : ℂ) -
        ((lowWheelFarPrimeQ2CrossingOuterOwnerSet
          R (r, (d, p))).card : ℂ)) *
          canonicalMoebiusWeight d) +
        canonicalMoebiusWeight d := by
  have hempty :=
    crossingOuterOwnerSet_double_eq_empty_of_roughBoundary hr hp hd
  unfold stableFarCenteredRenewalWeight stableFarCenteredRenewalCoeff
  rw [hempty]
  simp
  ring


/-! ## Complete returned-fibre recombination -/

def stableFarRenewalOwnerDifferenceWeight
    (R r p d : ℕ) : ℂ :=
  (((lowWheelFarPrimeQ2CrossingOuterOwnerSet
      R (r, (2 * d, p))).card : ℂ) -
    ((lowWheelFarPrimeQ2CrossingOuterOwnerSet
      R (r, (d, p))).card : ℂ)) *
    canonicalMoebiusWeight d

def stableFarRenewalOwnerDifferenceMass
    (R r p B : ℕ) : ℂ :=
  ∑ d ∈ oddCofactorPrefix B,
    if canonicalLargestPrimeFactor d < r then
      stableFarRenewalOwnerDifferenceWeight R r p d
    else 0

/-- **Complete fibre normal form.**  After exact dyadic pairing, every renewal
multiplicity is carried by one owner-window finite-difference field over the
whole odd r-rough prefix.  The only unpaired term is the native, unweighted
r-rough dyadic boundary mass already used by the q² ChildFar compression. -/
theorem stableFarCenteredReturnedFibre_eq_fullDifference_add_roughBoundaryMass
    {R r p : ℕ} (hr : r.Prime) (hrgt : 2 < r) (hp : p.Prime) :
    stableFarCenteredReturnedFibre R r p =
      stableFarRenewalOwnerDifferenceMass R r p
        (stableFarReturnedCofactorCutoff R r p) +
      roughDyadicCofactorBoundaryMass r
        (stableFarReturnedCofactorCutoff R r p) := by
  let B := stableFarReturnedCofactorCutoff R r p
  let F : ℕ → ℂ := fun d =>
    if canonicalLargestPrimeFactor d < r then
      stableFarRenewalOwnerDifferenceWeight R r p d
    else 0
  have hbase :=
    stableFarCenteredReturnedFibre_eq_ownerDifference_add_boundary
      (R := R) (r := r) (p := p) hr hrgt
  change stableFarCenteredReturnedFibre R r p =
      (∑ d ∈ oddCofactorPrefix (B / 2), F d) +
        ∑ d ∈ roughDyadicCofactorBoundary r B,
          stableFarCenteredRenewalWeight R r d p at hbase
  have hboundary :
      (∑ d ∈ roughDyadicCofactorBoundary r B,
          stableFarCenteredRenewalWeight R r d p) =
        (∑ d ∈ roughDyadicCofactorBoundary r B,
          stableFarRenewalOwnerDifferenceWeight R r p d) +
        ∑ d ∈ roughDyadicCofactorBoundary r B,
          canonicalMoebiusWeight d := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    exact
      stableFarCenteredRenewalWeight_eq_difference_add_native_of_roughBoundary
        hr hp hd
  have hdefectBoundary :
      (∑ d ∈ dyadicCofactorBoundary B, F d) =
        ∑ d ∈ roughDyadicCofactorBoundary r B,
          stableFarRenewalOwnerDifferenceWeight R r p d := by
    unfold F roughDyadicCofactorBoundary
    rw [Finset.sum_filter]
  have hsubset := oddCofactorPrefix_half_subset B
  have hpartition :
      (∑ d ∈ dyadicCofactorBoundary B, F d) +
        ∑ d ∈ oddCofactorPrefix (B / 2), F d =
      ∑ d ∈ oddCofactorPrefix B, F d := by
    unfold dyadicCofactorBoundary
    exact Finset.sum_sdiff hsubset
  have hrecombine :
      (∑ d ∈ oddCofactorPrefix (B / 2), F d) +
          (∑ d ∈ dyadicCofactorBoundary B, F d) =
        ∑ d ∈ oddCofactorPrefix B, F d := by
    rw [add_comm]
    exact hpartition
  calc
    stableFarCenteredReturnedFibre R r p =
        (∑ d ∈ oddCofactorPrefix (B / 2), F d) +
          ∑ d ∈ roughDyadicCofactorBoundary r B,
            stableFarCenteredRenewalWeight R r d p := hbase
    _ =
        (∑ d ∈ oddCofactorPrefix (B / 2), F d) +
          ((∑ d ∈ roughDyadicCofactorBoundary r B,
              stableFarRenewalOwnerDifferenceWeight R r p d) +
            ∑ d ∈ roughDyadicCofactorBoundary r B,
              canonicalMoebiusWeight d) := by rw [hboundary]
    _ =
        (∑ d ∈ oddCofactorPrefix (B / 2), F d) +
          ((∑ d ∈ dyadicCofactorBoundary B, F d) +
            ∑ d ∈ roughDyadicCofactorBoundary r B,
              canonicalMoebiusWeight d) := by rw [hdefectBoundary]
    _ =
        ((∑ d ∈ oddCofactorPrefix (B / 2), F d) +
          ∑ d ∈ dyadicCofactorBoundary B, F d) +
            ∑ d ∈ roughDyadicCofactorBoundary r B,
              canonicalMoebiusWeight d := by ring
    _ =
        (∑ d ∈ oddCofactorPrefix B, F d) +
          ∑ d ∈ roughDyadicCofactorBoundary r B,
            canonicalMoebiusWeight d := by rw [hrecombine]
    _ =
        stableFarRenewalOwnerDifferenceMass R r p
            (stableFarReturnedCofactorCutoff R r p) +
          roughDyadicCofactorBoundaryMass r
            (stableFarReturnedCofactorCutoff R r p) := by
      simp [stableFarRenewalOwnerDifferenceMass,
        roughDyadicCofactorBoundaryMass, B, F]


/-! ## Exact returned far-prime range and #785 boundary-column splice -/

theorem mem_stableFarRenewalCoordinatePairs_iff
    {R r p : ℕ} :
    (r, p) ∈ stableFarRenewalCoordinatePairs R ↔
      r.Prime ∧ r < R ∧
        p ∈ frozenPrimeUniverseHighPrimeSet (R + 7)
          (squareRootEndpoint R / (r * r)) := by
  constructor
  · intro hrp
    rcases Finset.mem_image.mp hrp with ⟨y, hy, hcoord⟩
    rcases y with ⟨r', ⟨e, p'⟩⟩
    have hrEq : r' = r := congrArg Prod.fst hcoord
    have hpEq : p' = p := congrArg Prod.snd hcoord
    subst r'
    subst p'
    have hdata :=
      (mem_lowWheelFarPrimeQ2DescendedTriples_iff_renewalCofactor).1 hy
    rcases hdata with ⟨hr, hrR, hp, hpR, he⟩
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp he with
      ⟨he1, heCut, _heSq, _heRough⟩
    have hB1 :
        1 ≤ stableFarReturnedCofactorCutoff R r p :=
      he1.trans heCut
    have hdenPos : 0 < r * r * p :=
      Nat.mul_pos (Nat.mul_pos hr.pos hr.pos) hp.pos
    have hprod : r * r * p ≤ squareRootEndpoint R := by
      unfold stableFarReturnedCofactorCutoff at hB1
      exact (Nat.one_le_div_iff hdenPos).1 hB1
    have hrrPos : 0 < r * r := Nat.mul_pos hr.pos hr.pos
    have hpUpper : p ≤ squareRootEndpoint R / (r * r) := by
      apply (Nat.le_div_iff_mul_le hrrPos).2
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprod
    exact ⟨hr, hrR,
      mem_frozenPrimeUniverseHighPrimeSet.mpr
        ⟨hp, by omega, hpUpper⟩⟩
  · rintro ⟨hr, hrR, hpSet⟩
    rcases mem_frozenPrimeUniverseHighPrimeSet.mp hpSet with
      ⟨hp, hpLo, hpUpper⟩
    have hrrPos : 0 < r * r := Nat.mul_pos hr.pos hr.pos
    have hprod0 : p * (r * r) ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hrrPos).1 hpUpper
    have hprod : r * r * p ≤ squareRootEndpoint R := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprod0
    have hdenPos : 0 < r * r * p :=
      Nat.mul_pos hrrPos hp.pos
    have hcut1 :
        1 ≤ stableFarReturnedCofactorCutoff R r p := by
      unfold stableFarReturnedCofactorCutoff
      exact (Nat.one_le_div_iff hdenPos).2 hprod
    have hone :
        1 ∈ squareRootLowPrimeGoSmoothCofactors r
          (stableFarReturnedCofactorCutoff R r p) := by
      apply mem_squareRootLowPrimeGoSmoothCofactors.mpr
      refine ⟨by norm_num, hcut1, squarefree_one, ?_⟩
      simpa [canonicalLargestPrimeFactor] using hr.one_lt
    have hdesc :
        (r, (1, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R :=
      (mem_lowWheelFarPrimeQ2DescendedTriples_iff_renewalCofactor).2
        ⟨hr, hrR, hp, by omega, hone⟩
    exact Finset.mem_image.mpr ⟨(r, (1, p)), hdesc, rfl⟩

def stableFarRenewalFarPrimeSet (R r : ℕ) : Finset ℕ :=
  ((stableFarRenewalCoordinatePairs R).filter fun rp => rp.1 = r).image
    Prod.snd

theorem stableFarRenewalFarPrimeSet_eq_highPrimeSet
    {R r : ℕ} (hr : r.Prime) (hrR : r < R) :
    stableFarRenewalFarPrimeSet R r =
      frozenPrimeUniverseHighPrimeSet (R + 7)
        (squareRootEndpoint R / (r * r)) := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨rp, hrpFilter, hrpSnd⟩
    rcases Finset.mem_filter.mp hrpFilter with ⟨hrp, hrpFst⟩
    have hdata := (mem_stableFarRenewalCoordinatePairs_iff).1 hrp
    have hrEq : rp.1 = r := hrpFst
    have hpEq : rp.2 = p := hrpSnd
    simpa [hrEq, hpEq] using hdata.2.2
  · intro hp
    have hrp :
        (r, p) ∈ stableFarRenewalCoordinatePairs R :=
      (mem_stableFarRenewalCoordinatePairs_iff).2 ⟨hr, hrR, hp⟩
    apply Finset.mem_image.mpr
    refine ⟨(r, p), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hrp, rfl⟩

def stableFarRenewalRoughBoundaryColumn (R r : ℕ) : ℂ :=
  ∑ p ∈ stableFarRenewalFarPrimeSet R r,
    roughDyadicCofactorBoundaryMass r
      (stableFarReturnedCofactorCutoff R r p)

theorem stableFarRenewalRoughBoundaryColumn_eq_q2DaughterFarRoughDyadicColumn
    {R r : ℕ} (hr : r.Prime) (hrR : r < R) :
    stableFarRenewalRoughBoundaryColumn R r =
      q2DaughterFarRoughDyadicColumn R r := by
  rw [stableFarRenewalFarPrimeSet_eq_highPrimeSet hr hrR]
  unfold stableFarRenewalRoughBoundaryColumn
    q2DaughterFarRoughDyadicColumn
  dsimp
  apply Finset.sum_congr rfl
  intro p _hp
  congr 1
  simp [stableFarReturnedCofactorCutoff,
    Nat.div_div_eq_div_mul, Nat.mul_assoc]

end RHLean.Proof
