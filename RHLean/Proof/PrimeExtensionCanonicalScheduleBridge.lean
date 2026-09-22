import Mathlib
import RHLean.Analysis.FiniteWheelReciprocalMertensImprovement
import RHLean.Proof.FarSurvivorRenewal_is_LowerMertens
import RHLean.Proof.PrimeExtensionPhysicalResponse
import RHLean.Proof.Post787BoundaryMainTermObstruction

/-!
# Canonical schedule bridge for the prime-extension telescope

The exact #789 extension telescope builds a wheel by adjoining fresh primes.
The physical Euler ledger elsewhere in the repository consumes the same prime
coordinates in descending order.  This module supplies the finite schedule
dictionary.

At the square endpoint `X_R = R^2 - 1`:

* the canonical descending schedule is every prime at most `X_R`;
* the #789 extension schedule is its reverse, so the wheel is built in
  increasing prime order;
* every `p >= R` has `floor(X_R / p^2) = 0`, hence contributes zero to the
  true q^2 Mertens column.

Therefore the Mertens amplitude sum exposed by the corrected #789 telescope is
literally `squareEndpointQ2MertensColumn R`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Canonical physical chronology: all active primes, largest first. -/
def primeExtensionCanonicalDescendingSchedule (R : ℕ) : List ℕ :=
  (primesUpTo (squareRootEndpoint R)).sort (fun a b : ℕ => a ≥ b)

/-- Canonical #789 chronology: the same primes, adjoined smallest first. -/
def primeExtensionCanonicalAscendingSchedule (R : ℕ) : List ℕ :=
  (primeExtensionCanonicalDescendingSchedule R).reverse

private theorem exists_split_of_mem {a : ℕ} {l : List ℕ} (ha : a ∈ l) :
    ∃ pre post : List ℕ, l = pre ++ a :: post := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨[], l, rfl⟩
      · rcases ih ha with ⟨pre, post, hsplit⟩
        refine ⟨b :: pre, post, ?_⟩
        simp [hsplit]

private theorem sorted_ge_nodup_prefix_before_current
    {pre post : List ℕ} {q : ℕ}
    (hsorted : List.Sorted (fun a b : ℕ => a ≥ b) (pre ++ q :: post))
    (hnodup : (pre ++ q :: post).Nodup) :
    ∀ r ∈ pre, q < r := by
  have hge := (List.pairwise_append.mp hsorted).2.2
  have hne := (List.pairwise_append.mp hnodup).2.2
  intro r hr
  have hqr : q ≤ r := hge r hr q (by simp)
  have hrq : r ≠ q := hne r hr q (by simp)
  omega

/-- The canonical descending list satisfies the production complete-schedule
predicate used by the raw Euler ledger. -/
theorem primeExtensionCanonicalDescendingSchedule_complete
    (R : ℕ) :
    SquareRootCanonicalRoughCompleteDescendingSchedule R
      (primeExtensionCanonicalDescendingSchedule R) := by
  let S := primesUpTo (squareRootEndpoint R)
  let ps := S.sort (fun a b : ℕ => a ≥ b)
  change SquareRootCanonicalRoughCompleteDescendingSchedule R ps
  have hsorted : List.Sorted (fun a b : ℕ => a ≥ b) ps := by
    dsimp [ps]
    exact Finset.sort_sorted (· ≥ ·) _
  have hnodup : ps.Nodup := by
    dsimp [ps]
    exact Finset.sort_nodup _ _
  constructor
  · intro p hp
    have hpS : p ∈ S := by
      dsimp [ps] at hp
      exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).mp hp
    dsimp [S] at hpS
    exact prime_of_mem_primesUpTo hpS
  · intro q hq hqUpper
    have hqS : q ∈ S := by
      dsimp [S]
      exact mem_primesUpTo_of_prime_le hq hqUpper
    have hqps : q ∈ ps := by
      dsimp [ps]
      exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2 hqS
    rcases exists_split_of_mem hqps with ⟨pre, post, hsplit⟩
    refine ⟨pre, post, hsplit, ?_, ?_⟩
    · intro r hr
      apply prime_of_mem_primesUpTo
      have hrps : r ∈ ps := by
        rw [hsplit]
        simp [hr]
      have hrS : r ∈ S := by
        dsimp [ps] at hrps
        exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).mp hrps
      simpa [S] using hrS
    · intro r hr
      rw [hsplit] at hsorted hnodup
      exact sorted_ge_nodup_prefix_before_current hsorted hnodup r hr

private theorem primeExtensionChainAdmissible_of_squarefree_disjoint
    {W : ℕ} {ps : List ℕ}
    (hW : Squarefree W)
    (hprime : ∀ p ∈ ps, p.Prime)
    (hnodup : ps.Nodup)
    (hdisj : ∀ p ∈ ps, ¬ p ∣ W) :
    PrimeExtensionChainAdmissible W ps := by
  induction ps generalizing W with
  | nil =>
      simp [PrimeExtensionChainAdmissible]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hnot : p ∉ ps := (List.nodup_cons.mp hnodup).1
      have hnodupTail : ps.Nodup := (List.nodup_cons.mp hnodup).2
      have hprimeTail : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hpndvd : ¬ p ∣ W := hdisj p (by simp)
      have hcop : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpndvd
      have hsq : Squarefree (p * W) :=
        (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, hW⟩
      have hdisjTail : ∀ q ∈ ps, ¬ q ∣ p * W := by
        intro q hq hqdiv
        have hqPrime := hprimeTail q hq
        rcases hqPrime.dvd_mul.mp hqdiv with hqp | hqW
        · rcases hp.eq_one_or_self_of_dvd q hqp with hq1 | hqpEq
          · exact hqPrime.ne_one hq1
          · subst q
            exact hnot hq
        · exact hdisj q (by simp [hq]) hqW
      simp only [PrimeExtensionChainAdmissible]
      exact ⟨hp, hsq, ih hsq hprimeTail hnodupTail hdisjTail⟩

/-- Reversing the complete physical chronology gives an admissible #789
prime-extension chain starting from the trivial wheel. -/
theorem primeExtensionCanonicalAscendingSchedule_admissible
    (R : ℕ) :
    PrimeExtensionChainAdmissible 1
      (primeExtensionCanonicalAscendingSchedule R) := by
  have hdescNodup :
      (primeExtensionCanonicalDescendingSchedule R).Nodup := by
    unfold primeExtensionCanonicalDescendingSchedule
    exact Finset.sort_nodup _ _
  have hascNodup :
      (primeExtensionCanonicalAscendingSchedule R).Nodup := by
    unfold primeExtensionCanonicalAscendingSchedule
    simpa using hdescNodup.reverse
  have hascPrime :
      ∀ p ∈ primeExtensionCanonicalAscendingSchedule R, p.Prime := by
    intro p hp
    have hpdesc : p ∈ primeExtensionCanonicalDescendingSchedule R := by
      simpa [primeExtensionCanonicalAscendingSchedule] using hp
    unfold primeExtensionCanonicalDescendingSchedule at hpdesc
    exact prime_of_mem_primesUpTo
      ((Finset.mem_sort (fun a b : ℕ => a ≥ b)).mp hpdesc)
  have hdisj :
      ∀ p ∈ primeExtensionCanonicalAscendingSchedule R, ¬ p ∣ 1 := by
    intro p hp hpd
    have hpPrime := hascPrime p hp
    have hple : p ≤ 1 := Nat.le_of_dvd (by omega) hpd
    omega
  exact primeExtensionChainAdmissible_of_squarefree_disjoint
    (by simp) hascPrime hascNodup hdisj

private theorem primeExtensionMertensSum_eq_toFinset
    (x : ℕ) {ps : List ℕ} (hnodup : ps.Nodup) :
    primeExtensionMertensSum x ps =
      ∑ p ∈ ps.toFinset, mertensSummatoryInt (x / (p * p)) := by
  induction ps with
  | nil =>
      simp [primeExtensionMertensSum]
  | cons p ps ih =>
      have hnot : p ∉ ps := (List.nodup_cons.mp hnodup).1
      have htail : ps.Nodup := (List.nodup_cons.mp hnodup).2
      simp [primeExtensionMertensSum, ih htail, hnot]

private theorem canonicalAscending_toFinset (R : ℕ) :
    (primeExtensionCanonicalAscendingSchedule R).toFinset =
      primesUpTo (squareRootEndpoint R) := by
  ext p
  simp [primeExtensionCanonicalAscendingSchedule,
    primeExtensionCanonicalDescendingSchedule]

/-- Above the square root the q² daughter cutoff is zero. -/
private theorem mertensSquareDaughter_eq_zero_of_root_le
    {R p : ℕ} (hpR : R ≤ p) :
    mertensSummatoryInt (squareRootEndpoint R / (p * p)) = 0 := by
  have hlt : squareRootEndpoint R < p * p := by
    unfold squareRootEndpoint
    nlinarith
  rw [Nat.div_eq_of_lt hlt]
  simp [mertensSummatoryInt]

/-- **Canonical q²-column identification.**

The true Mertens amplitude column extracted from the complete #789 extension
chronology is exactly the repository's existing all-prime q² daughter column. -/
theorem primeExtensionCanonicalMertensSum_eq_squareEndpointQ2MertensColumn
    (R : ℕ) (hR : 2 ≤ R) :
    primeExtensionMertensSum (squareRootEndpoint R)
        (primeExtensionCanonicalAscendingSchedule R) =
      squareEndpointQ2MertensColumn R := by
  have hnodup :
      (primeExtensionCanonicalAscendingSchedule R).Nodup := by
    unfold primeExtensionCanonicalAscendingSchedule
    have h :
        (primeExtensionCanonicalDescendingSchedule R).Nodup := by
      unfold primeExtensionCanonicalDescendingSchedule
      exact Finset.sort_nodup _ _
    simpa using h.reverse
  rw [primeExtensionMertensSum_eq_toFinset (squareRootEndpoint R) hnodup,
    canonicalAscending_toFinset]
  unfold squareEndpointQ2MertensColumn
  have hsub :
      primesUpTo (R - 1) ⊆ primesUpTo (squareRootEndpoint R) := by
    intro p hp
    have hpData := mem_primesUpTo.mp hp
    apply mem_primesUpTo.mpr
    refine ⟨hpData.1, hpData.2.trans ?_⟩
    unfold squareRootEndpoint
    nlinarith
  symm
  apply Finset.sum_subset hsub
  intro p hpBig hpNotSmall
  have hpData := mem_primesUpTo.mp hpBig
  have hpR : R ≤ p := by
    by_contra hlt
    have hpLe : p ≤ R - 1 := by omega
    exact hpNotSmall (mem_primesUpTo.mpr ⟨hpData.1, hpLe⟩)
  exact mertensSquareDaughter_eq_zero_of_root_le hpR


/-! ## Saturated terminal wheel and response collapse -/

private theorem primeExtensionWheel_eq_listProd_mul
    (W : ℕ) (ps : List ℕ) :
    primeExtensionWheel W ps = ps.prod * W := by
  induction ps generalizing W with
  | nil =>
      simp [primeExtensionWheel]
  | cons p ps ih =>
      rw [primeExtensionWheel, ih]
      simp only [List.prod_cons]
      ac_rfl

private theorem listProd_eq_toFinsetProd
    {ps : List ℕ} (hnodup : ps.Nodup) :
    ps.prod = ps.toFinset.prod id := by
  induction ps with
  | nil =>
      simp
  | cons p ps ih =>
      have hnot : p ∉ ps := (List.nodup_cons.mp hnodup).1
      have htail : ps.Nodup := (List.nodup_cons.mp hnodup).2
      simp [hnot, ih htail]

/-- The complete canonical #789 chain terminates at the product of every prime
coordinate active at the endpoint. -/
theorem primeExtensionCanonicalTerminalWheel_eq_primorialWheelProduct
    (R : ℕ) :
    primeExtensionWheel 1 (primeExtensionCanonicalAscendingSchedule R) =
      primorialWheelProduct (primesUpTo (squareRootEndpoint R)) := by
  have hnodup :
      (primeExtensionCanonicalAscendingSchedule R).Nodup := by
    unfold primeExtensionCanonicalAscendingSchedule
    have h :
        (primeExtensionCanonicalDescendingSchedule R).Nodup := by
      unfold primeExtensionCanonicalDescendingSchedule
      exact Finset.sort_nodup _ _
    simpa using h.reverse
  rw [primeExtensionWheel_eq_listProd_mul, mul_one,
    listProd_eq_toFinsetProd hnodup, canonicalAscending_toFinset]
  rfl

/-- A wheel containing every prime through the cutoff has exactly one rough
seat in that prefix: the unit seat. -/
private theorem roughMertens_fullPrimeWheel_eq_one
    {X : ℕ} (hX : 1 ≤ X) :
    roughMertens (primorialWheelProduct (primesUpTo X)) X = 1 := by
  unfold roughMertens
  rw [Finset.sum_eq_single 1]
  · simp [roughMoebius]
  · intro n hn hn1
    have hnle : n ≤ X := by
      have hnlt : n < X + 1 := Finset.mem_range.mp hn
      omega
    by_cases hn0 : n = 0
    · subst n
      simp [roughMoebius]
    · obtain ⟨p, hpPrime, hpdn⟩ :=
        Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      have hpLeN : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdn
      have hpLeX : p ≤ X := hpLeN.trans hnle
      have hpMem : p ∈ primesUpTo X :=
        mem_primesUpTo.mpr ⟨hpPrime, hpLeX⟩
      have hprimeSet : ∀ q ∈ primesUpTo X, q.Prime := by
        intro q hq
        exact prime_of_mem_primesUpTo hq
      have hpdW : p ∣ primorialWheelProduct (primesUpTo X) :=
        (prime_dvd_primorialWheelProduct_iff hpPrime hprimeSet).2 hpMem
      have hncop :
          ¬ Nat.Coprime n (primorialWheelProduct (primesUpTo X)) := by
        intro hcop
        have hpgcd :
            p ∣ Nat.gcd n (primorialWheelProduct (primesUpTo X)) :=
          Nat.dvd_gcd hpdn hpdW
        have hpone : p ∣ 1 := by
          simpa [hcop.gcd_eq_one] using hpgcd
        exact hpPrime.not_dvd_one hpone
      simp [roughMoebius, hncop]
  · intro hnot
    apply hnot
    exact Finset.mem_range.mpr (by omega)

/-- Hence the terminal rough amplitude of the complete canonical chain is
literally one. -/
theorem roughMertens_primeExtensionCanonicalTerminal_eq_one
    (R : ℕ) (hR : 2 ≤ R) :
    roughMertens
        (primeExtensionWheel 1 (primeExtensionCanonicalAscendingSchedule R))
        (squareRootEndpoint R) = 1 := by
  rw [primeExtensionCanonicalTerminalWheel_eq_primorialWheelProduct]
  apply roughMertens_fullPrimeWheel_eq_one
  unfold squareRootEndpoint
  nlinarith

private theorem roughMertens_one_eq_mertensSummatoryInt (X : ℕ) :
    roughMertens 1 X = mertensSummatoryInt X := by
  unfold roughMertens mertensSummatoryInt roughMoebius
  simp

/-- **Complete canonical amplitude response.**

After saturating the wheel, every chronological response term collapses to one
closed finite identity: unit terminal minus the endpoint Mertens amplitude minus
the complete q² daughter column. -/
theorem primeExtensionCanonicalPhysicalResponseSum_eq
    (R : ℕ) (hR : 2 ≤ R) :
    roughPrimeExtensionPhysicalResponseSum 1 (squareRootEndpoint R)
        (primeExtensionCanonicalAscendingSchedule R) =
      1 - mertensSummatoryInt (squareRootEndpoint R) -
        squareEndpointQ2MertensColumn R := by
  have hchain :=
    primeExtensionCanonicalAscendingSchedule_admissible R
  have hamp :=
    roughMertens_primeExtensionChain_physical_amplitude
      (W := 1) (x := squareRootEndpoint R)
      (ps := primeExtensionCanonicalAscendingSchedule R) hchain
  rw [roughMertens_one_eq_mertensSummatoryInt,
    roughMertens_primeExtensionCanonicalTerminal_eq_one R hR,
    primeExtensionCanonicalMertensSum_eq_squareEndpointQ2MertensColumn R hR]
      at hamp
  linarith

/-- **Chronological response = existing physical synthesis error.**

All q² daughter amplitudes cancel when the complete chronological response is
reassembled against the existing covariance identity.  What remains is only
the already-formalized all-prime ownerwise physical synthesis error, the unit
terminal, the predecessor Mertens endpoint, and the explicit root correction.
No inequality is used. -/
theorem primeExtensionCanonicalPhysicalResponseSum_cast_eq_ownerwiseError
    (R : ℕ) (hR : 56 ≤ R) :
    ((roughPrimeExtensionPhysicalResponseSum 1 (squareRootEndpoint R)
        (primeExtensionCanonicalAscendingSchedule R) : ℤ) : ℂ) =
      1 - mertensSummatory (R - 1) +
        farFourAllPrimeOwnerwiseSynthesisError R -
        frozenTopFarRoughRootCorrection R := by
  have hresp :=
    primeExtensionCanonicalPhysicalResponseSum_eq R (by omega)
  have hcorr :=
    squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint
      R (by omega)
  have hphysical :=
    roughCorrelation_add_rootCorrection_eq_oddMertensColumn_add_ownerwiseError
      R hR
  have hq2 :=
    squareEndpointQ2MertensColumn_eq_oddColumn_add_two R (by omega)
  have hcast := congrArg (fun z : ℤ => (z : ℂ)) hresp
  push_cast at hcast
  simp only [mertensSummatoryInt_cast] at hcast
  unfold farFourOddMertensColumn farFourOwnerwiseSynthesisError at hphysical
  push_cast at hphysical
  rw [hq2] at hcast
  push_cast at hcast
  have hcorr' :
      squareRootCanonicalRoughCorrelation R =
        mertensSummatory (R - 1) -
          mertensSummatory (squareRootEndpoint R) := hcorr
  linear_combination hcast + hphysical - hcorr'



/-! ## Canonical energy reassembly -/

/-- On the canonical square-endpoint chain, the off-diagonal covariance is
literally the square of the complete q² Mertens column minus the #789 diagonal
daughter energy. -/
theorem primeExtensionCanonicalMertensCrossCovariance_eq
    (R : ℕ) (hR : 2 ≤ R) :
    primeExtensionMertensCrossCovariance (squareRootEndpoint R)
        (primeExtensionCanonicalAscendingSchedule R) =
      squareEndpointQ2MertensColumn R ^ 2 -
        primeExtensionMertensSquareSum (squareRootEndpoint R)
          (primeExtensionCanonicalAscendingSchedule R) := by
  unfold primeExtensionMertensCrossCovariance
  rw [primeExtensionCanonicalMertensSum_eq_squareEndpointQ2MertensColumn R hR]

/-- **Canonical #789 energy response in assembled physical coordinates.**

Write `Q_R` for the complete q² Mertens amplitude column and `S_R` for the
chronological physical-response amplitude.  The full signed Gamma correction is

`crossCov_R + 2 Q_R S_R + S_R^2 - 2 Q_R - 2 S_R`.

Thus the obstruction to treating the #789 correction as a linear physical
boundary is exactly the off-diagonal owner covariance together with the
quadratic response terms. -/
theorem roughPrimeExtensionCanonicalPhysicalGammaSum_eq_covariance_reassembly
    (R : ℕ) (hR : 2 ≤ R) :
    roughPrimeExtensionPhysicalGammaSum 1 (squareRootEndpoint R)
        (primeExtensionCanonicalAscendingSchedule R) =
      primeExtensionMertensCrossCovariance (squareRootEndpoint R)
          (primeExtensionCanonicalAscendingSchedule R) +
        2 * squareEndpointQ2MertensColumn R *
          roughPrimeExtensionPhysicalResponseSum 1 (squareRootEndpoint R)
            (primeExtensionCanonicalAscendingSchedule R) +
        roughPrimeExtensionPhysicalResponseSum 1 (squareRootEndpoint R)
            (primeExtensionCanonicalAscendingSchedule R) ^ 2 -
        2 * squareEndpointQ2MertensColumn R -
        2 * roughPrimeExtensionPhysicalResponseSum 1 (squareRootEndpoint R)
            (primeExtensionCanonicalAscendingSchedule R) := by
  have hchain :=
    primeExtensionCanonicalAscendingSchedule_admissible R
  have h :=
    roughPrimeExtensionPhysicalGammaSum_eq_crossCovariance_reassembly
      (W := 1) (x := squareRootEndpoint R)
      (ps := primeExtensionCanonicalAscendingSchedule R) hchain
  rw [primeExtensionCanonicalMertensSum_eq_squareEndpointQ2MertensColumn R hR,
    roughMertens_primeExtensionCanonicalTerminal_eq_one R hR] at h
  simpa using h

/-- Equivalent diagonal-energy form: after exposing the covariance explicitly,
the diagonal q² daughter energy cancels against the covariance deficit in the
assembled square. -/
theorem roughPrimeExtensionCanonicalPhysicalGammaSum_eq_q2Square_sub_diagonal
    (R : ℕ) (hR : 2 ≤ R) :
    roughPrimeExtensionPhysicalGammaSum 1 (squareRootEndpoint R)
        (primeExtensionCanonicalAscendingSchedule R) =
      squareEndpointQ2MertensColumn R ^ 2 -
        primeExtensionMertensSquareSum (squareRootEndpoint R)
          (primeExtensionCanonicalAscendingSchedule R) +
        2 * squareEndpointQ2MertensColumn R *
          roughPrimeExtensionPhysicalResponseSum 1 (squareRootEndpoint R)
            (primeExtensionCanonicalAscendingSchedule R) +
        roughPrimeExtensionPhysicalResponseSum 1 (squareRootEndpoint R)
            (primeExtensionCanonicalAscendingSchedule R) ^ 2 -
        2 * squareEndpointQ2MertensColumn R -
        2 * roughPrimeExtensionPhysicalResponseSum 1 (squareRootEndpoint R)
            (primeExtensionCanonicalAscendingSchedule R) := by
  rw [roughPrimeExtensionCanonicalPhysicalGammaSum_eq_covariance_reassembly R hR,
    primeExtensionCanonicalMertensCrossCovariance_eq R hR]



/-! ## Direct #789 / #788 coordinate equivalence -/

/-- The predecessor square-prefix endpoint is the native `R^2-1` endpoint. -/
private theorem squarePrefixEndpoint_pred_eq_squareRootEndpoint
    (R : ℕ) (hR : 1 ≤ R) :
    squarePrefixEndpoint (R - 1) = squareRootEndpoint R := by
  unfold squarePrefixEndpoint squareRootEndpoint
  rw [Nat.sub_add_cancel hR]

/-- **#789 and #788 are the same complete energy telescope.**

On the canonical complete prime-extension chain, the terminal wheel contributes
the unit energy.  The diagonal q² daughter energy plus the full signed #789
Gamma response is therefore exactly the square of #788's already assembled
physical interior plus its genuine root boundary.

No norm, inequality, asymptotic estimate, or positivity statement enters this
identity. -/
theorem primeExtensionCanonicalEnergy_eq_post787CoupledPhysicalSquare
    (R : ℕ) (hR : 56 ≤ R) :
    (1 : ℂ) +
        (primeExtensionMertensSquareSum (squareRootEndpoint R)
          (primeExtensionCanonicalAscendingSchedule R) : ℂ) +
        (roughPrimeExtensionPhysicalGammaSum 1 (squareRootEndpoint R)
          (primeExtensionCanonicalAscendingSchedule R) : ℂ) =
      (post787CoupledInterior R + finalCompensatedRootBoundary R) ^ 2 := by
  have hchain :=
    primeExtensionCanonicalAscendingSchedule_admissible R
  have henergy :=
    roughMertens_sq_primeExtensionChain_physical
      (W := 1) (x := squareRootEndpoint R)
      (ps := primeExtensionCanonicalAscendingSchedule R) hchain
  rw [roughMertens_one_eq_mertensSummatoryInt,
    roughMertens_primeExtensionCanonicalTerminal_eq_one R (by omega)]
      at henergy
  have henergyCast := congrArg (fun z : ℤ => (z : ℂ)) henergy
  push_cast at henergyCast
  simp only [mertensSummatoryInt_cast] at henergyCast
  have h788 :=
    squarePrefixMertens_eq_post787CoupledInterior_add_rootBoundary R hR
  have hend :=
    squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega)
  unfold squarePrefixMertens at h788
  rw [hend] at h788
  calc
    (1 : ℂ) +
          (primeExtensionMertensSquareSum (squareRootEndpoint R)
            (primeExtensionCanonicalAscendingSchedule R) : ℂ) +
          (roughPrimeExtensionPhysicalGammaSum 1 (squareRootEndpoint R)
            (primeExtensionCanonicalAscendingSchedule R) : ℂ) =
        mertensSummatory (squareRootEndpoint R) ^ 2 := by
          linear_combination -henergyCast
    _ = (post787CoupledInterior R + finalCompensatedRootBoundary R) ^ 2 := by
          rw [h788]


/-- The existing global Euler/q² bridge, now instantiated on the canonical
prime chronology with no external schedule witness. -/
theorem canonicalRawLedger_add_rootCorrection_eq_oddMertensColumn_add_ownerwiseError
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootCanonicalRoughAdaptiveRawLedger R
          (primeExtensionCanonicalDescendingSchedule R)
          (Finset.Icc 1 (squareRootEndpoint R))
          (fun _ => (1 : ℂ)) +
        frozenTopFarRoughRootCorrection R =
      farFourOddMertensColumn R + farFourOwnerwiseSynthesisError R := by
  exact
    adaptiveRawLedger_add_rootCorrection_eq_oddMertensColumn_add_ownerwiseError_of_completeSchedule
      R hR (primeExtensionCanonicalDescendingSchedule R)
      (primeExtensionCanonicalDescendingSchedule_complete R)

end RHLean.Proof
