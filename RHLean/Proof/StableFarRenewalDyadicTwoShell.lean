import Mathlib
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
  rcases lowWheelFarPrimeLowCofactorTriple_data hyBase with
    ⟨hrPrime, hrR, he1, hpPrime, hpR, heSq, her, _hyCut⟩
  rcases mem_primesUpTo.mp hqOld with ⟨hqPrime, hqPred⟩
  have hRpos : 0 < R := by omega
  have hqR : q < R := Nat.lt_of_le_pred hRpos hqPred
  have hreFresh : ¬ r ∣ e :=
    squareRootLowPrimePrime_fresh_of_lpf_lt he1 hrPrime her
  have hreCop : Nat.Coprime r e :=
    (hrPrime.coprime_iff_not_dvd).2 hreFresh
  have hreSq : Squarefree (r * e) :=
    (Nat.squarefree_mul hreCop).2 ⟨hrPrime.squarefree, heSq⟩
  have hre1 : 1 ≤ r * e := by positivity
  have hlpf_re : canonicalLargestPrimeFactor (r * e) = r := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        (by omega : 0 < e) hrPrime her
  have hreq : canonicalLargestPrimeFactor (r * e) < q := by
    rw [hlpf_re]
    exact hrq
  have hqFresh : ¬ q ∣ r * e :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hre1 hqPrime hreq
  have hqCop : Nat.Coprime q (r * e) :=
    (hqPrime.coprime_iff_not_dvd).2 hqFresh
  have hqreSq : Squarefree (q * (r * e)) :=
    (Nat.squarefree_mul hqCop).2 ⟨hqPrime.squarefree, hreSq⟩
  have hqre1 : 1 ≤ q * (r * e) := by positivity
  have hlpf_qre : canonicalLargestPrimeFactor (q * (r * e)) = q := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        hre1 hqPrime hreq
  have hqrep : canonicalLargestPrimeFactor (q * (r * e)) < p := by
    rw [hlpf_qre]
    omega
  have hpFresh : ¬ p ∣ q * (r * e) :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hqre1 hpPrime hqrep
  have hpCop : Nat.Coprime (q * (r * e)) p :=
    ((hpPrime.coprime_iff_not_dvd).2 hpFresh).symm
  have hsq : Squarefree ((q * (r * e)) * p) :=
    (Nat.squarefree_mul hpCop).2 ⟨hqreSq, hpPrime.squarefree⟩
  apply mem_orderedEulerCutSquarefreeShell.mpr
  refine ⟨?_, ?_, ?_⟩
  · have hpSite : p ≤ stableFarRenewalTransportSite q r e p := by
      unfold stableFarRenewalTransportSite
      have hprod : 1 ≤ q * r * e := by positivity
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_right p hprod
    omega
  · unfold stableFarRenewalTransportSite squareRootEndpoint at hcut ⊢
    omega
  · simpa [stableFarRenewalTransportSite, Nat.mul_assoc] using hsq

/-- The transported squarefree site carries exactly the sign-reversed returned
cofactor weight. -/
theorem renewalTransportSite_weight_eq_neg_returned
    {R q r e p : ℕ}
    (hy : (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R)
    (hqOld : q ∈ primesUpTo (R - 1)) (hrq : r < q)
    (hcut : q * r * e * p ≤ squareRootEndpoint R) :
    canonicalMoebiusWeight (stableFarRenewalTransportSite q r e p) =
      -canonicalMoebiusWeight e := by
  have hyBase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hy).1
  rcases lowWheelFarPrimeLowCofactorTriple_data hyBase with
    ⟨hrPrime, hrR, he1, hpPrime, hpR, heSq, her, _hyCut⟩
  rcases mem_primesUpTo.mp hqOld with ⟨hqPrime, hqPred⟩
  have hRpos : 0 < R := hrPrime.pos.trans hrR
  have hqR : q < R := Nat.lt_of_le_pred hRpos hqPred
  have hreFresh : ¬ r ∣ e :=
    squareRootLowPrimePrime_fresh_of_lpf_lt he1 hrPrime her
  have hreFlip :
      canonicalMoebiusWeight (r * e) = -canonicalMoebiusWeight e := by
    have h := canonicalMoebiusWeight_mul_freshPrime hrPrime hreFresh
    simpa [Nat.mul_comm] using h
  have hre1 : 1 ≤ r * e := by positivity
  have hlpf_re : canonicalLargestPrimeFactor (r * e) = r := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        (by omega : 0 < e) hrPrime her
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
  have hqre1 : 1 ≤ q * (r * e) := by positivity
  have hlpf_qre : canonicalLargestPrimeFactor (q * (r * e)) = q := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        hre1 hqPrime hreq
  have hqrep : canonicalLargestPrimeFactor (q * (r * e)) < p := by
    rw [hlpf_qre]
    omega
  have hpFresh : ¬ p ∣ q * (r * e) :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hqre1 hpPrime hqrep
  have hpFlip :
      canonicalMoebiusWeight ((q * (r * e)) * p) =
        -canonicalMoebiusWeight (q * (r * e)) :=
    canonicalMoebiusWeight_mul_freshPrime hpPrime hpFresh
  unfold stableFarRenewalTransportSite
  rw [show q * r * e * p = (q * (r * e)) * p by ring, hpFlip, hqFlip, hreFlip]
  ring


/-- First renewal defect shell: the old owner is active at e, but doubling e
pushes the first-power product through the endpoint. -/

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
  have hlpf_re : canonicalLargestPrimeFactor (r * e) = r := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        (by omega : 0 < e) hr her
  have hre1 : 1 ≤ r * e := by positivity
  have hreq : canonicalLargestPrimeFactor (r * e) < q := by
    rw [hlpf_re]
    exact hrq
  have hlpf_qre : canonicalLargestPrimeFactor (q * (r * e)) = q := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hre1 hq hreq
  have hqre1 : 1 ≤ q * (r * e) := by positivity
  have hqrep : canonicalLargestPrimeFactor (q * (r * e)) < p := by
    rw [hlpf_qre]
    omega
  have hlpf_site :
      canonicalLargestPrimeFactor ((q * (r * e)) * p) = p :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hqre1 hp hqrep

  have hlpf_re' : canonicalLargestPrimeFactor (r' * e') = r' := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        (by omega : 0 < e') hr' her'
  have hre1' : 1 ≤ r' * e' := by positivity
  have hreq' : canonicalLargestPrimeFactor (r' * e') < q' := by
    rw [hlpf_re']
    exact hrq'
  have hlpf_qre' : canonicalLargestPrimeFactor (q' * (r' * e')) = q' := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hre1' hq' hreq'
  have hqre1' : 1 ≤ q' * (r' * e') := by positivity
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
  rcases lowWheelFarPrimeLowCofactorTriple_data hyBase with
    ⟨hr, hrR, he1, hp, hpR, _heSq, her, _hcut⟩
  rcases lowWheelFarPrimeLowCofactorTriple_data hyBase' with
    ⟨hr', hrR', he1', hp', hpR', _heSq', her', _hcut'⟩
  rcases mem_primesUpTo.mp hqOld with ⟨hq, hqPred⟩
  rcases mem_primesUpTo.mp hqOld' with ⟨hq', hqPred'⟩
  have hRpos : 0 < R := hr.pos.trans hrR
  have hqR : q < R := Nat.lt_of_le_pred hRpos hqPred
  have hqR' : q' < R := Nat.lt_of_le_pred hRpos hqPred'
  exact renewalTransportSite_unique
    hr he1 her hq hrq hqR hp (by omega)
    hr' he1' her' hq' hrq' hqR' hp' (by omega) heq

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
  exact crossingOuterOwnerSet_membership_mismatch_iff_two_shells

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
  rw [renewalTransportSite_weight_eq_neg_returned hy hq hrq hcut]
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
  rw [renewalTransportSite_weight_eq_neg_returned hy hq hrq hcut]
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

end RHLean.Proof
