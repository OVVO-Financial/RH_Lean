import Mathlib
import RHLean.Proof.FarSurvivorRenewal_is_LowerMertens
import RHLean.Proof.PrimeExtensionPhysicalResponse

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
