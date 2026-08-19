import Mathlib
import RHLean.Proof.PrimeCombVisualizationDynamics

/-!
# Ordered-prime recurrence for the visualization frames

`PrimeCombVisualizationDynamics` records the literal operational masks used by
the animation: kill, first hit, and later-touch flip.  This file proves that
those operational updates are not a second model.  When `S` consists of primes
strictly smaller than the fresh prime `p`, one animation step is exactly the
closed-form frame obtained by adjoining `p` to the processed prime set.

Thus the visualization really is a prime-by-prime recurrence on the frame
state, while the closed form remains available for global geometric arguments.
No estimate occurs here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Before the fresh prime `p`, ordinary selected-divisor touch and proper-
multiple touch coincide on every site strictly beyond `p`. -/
theorem primeCombFrameProperTouched_iff_touched_of_beforePrime
    (S : Finset ℕ) {p n : ℕ}
    (hSlt : ∀ q ∈ S, q < p) (hpn : p < n) :
    PrimeCombFrameProperTouched S n ↔ PrimeCombFrameTouched S n := by
  constructor
  · rintro ⟨q, hqS, _hqn, hqdiv⟩
    unfold PrimeCombFrameTouched primeCombFrameDivisors
    exact ⟨q, Finset.mem_filter.mpr ⟨hqS, hqdiv⟩⟩
  · rintro ⟨q, hq⟩
    have hqData := Finset.mem_filter.mp hq
    exact ⟨q, hqData.1, (hSlt q hqData.1).trans hpn, hqData.2⟩

private theorem primeCombFrameAlive_of_no_square
    {S : Finset ℕ} {n : ℕ}
    (hn0 : n ≠ 0) (hn1 : n ≠ 1)
    (hnoSquare : ¬ PrimeCombFrameSquareHit S n) :
    PrimeCombFrameAlive S n := by
  unfold PrimeCombFrameAlive primeCombFrameSite
  rw [if_neg hn0, if_neg hn1, if_neg hnoSquare]
  dsimp
  by_cases hdiv : primeCombFrameDivisors S n = ∅
  · rw [if_pos (Finset.card_eq_zero.mpr hdiv)]
    norm_num
  · have hcard : (primeCombFrameDivisors S n).card ≠ 0 :=
      Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hdiv)
    rw [if_neg hcard]
    exact pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0)

private theorem primeCombFrameDivisors_prime_eq_empty
    (S : Finset ℕ) {p : ℕ}
    (hpPrime : p.Prime)
    (hSPrime : ∀ q ∈ S, q.Prime)
    (hSlt : ∀ q ∈ S, q < p) :
    primeCombFrameDivisors S p = ∅ := by
  classical
  ext q
  simp only [primeCombFrameDivisors, Finset.mem_filter, Finset.notMem_empty,
    iff_false]
  intro h
  rcases h with ⟨hqS, hqdiv⟩
  have hqPrime := hSPrime q hqS
  rcases (Nat.dvd_prime hpPrime).mp hqdiv with hq1 | hqp
  · exact hqPrime.ne_one hq1
  · subst q
    exact (Nat.lt_irrefl p) (hSlt p hqS)

/-- **Operational recurrence equals the closed frame.**  If `S` contains only
primes smaller than the fresh prime `p`, the literal kill/first-hit/flip step
is exactly the frame obtained from the processed coordinate set `insert p S`.
This is the frame-by-frame correctness theorem for the animation. -/
theorem primeCombAnimationStepSite_eq_insert
    (S : Finset ℕ) (p n : ℕ)
    (hpPrime : p.Prime)
    (hSPrime : ∀ q ∈ S, q.Prime)
    (hSlt : ∀ q ∈ S, q < p) :
    primeCombAnimationStepSite S p n =
      primeCombFrameSite (insert p S) n := by
  classical
  have hpS : p ∉ S := by
    intro hpMem
    exact (Nat.lt_irrefl p) (hSlt p hpMem)
  by_cases hn0 : n = 0
  · subst n
    simp [primeCombAnimationStepSite, PrimeCombFrameKilled,
      PrimeCombFrameFlipped, PrimeCombFrameAlive]
  by_cases hn1 : n = 1
  · subst n
    have hNotProper : ¬ PrimeCombFrameProperMultiple p 1 := by
      intro h
      unfold PrimeCombFrameProperMultiple at h
      have hp2 : 2 ≤ p := hpPrime.two_le
      omega
    have hNotKilled : ¬ PrimeCombFrameKilled S p 1 := by
      intro h
      exact hNotProper h.2.1
    have hNotFlipped : ¬ PrimeCombFrameFlipped S p 1 := by
      intro h
      exact hNotProper h.2.1
    simp [primeCombAnimationStepSite, hNotKilled, hNotFlipped]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases hOldSquare : PrimeCombFrameSquareHit S n
  · have hOldZero : primeCombFrameSite S n = 0 := by
      simp [primeCombFrameSite, hn0, hn1, hOldSquare]
    have hNotAlive : ¬ PrimeCombFrameAlive S n := by
      simp [PrimeCombFrameAlive, hOldZero]
    have hNotKilled : ¬ PrimeCombFrameKilled S p n := by
      intro h
      exact hNotAlive h.1
    have hNotFlipped : ¬ PrimeCombFrameFlipped S p n := by
      intro h
      exact hNotAlive h.1
    have hNewSquare : PrimeCombFrameSquareHit (insert p S) n :=
      (primeCombFrameSquareHit_insert S p n).2 (Or.inr hOldSquare)
    rw [show primeCombAnimationStepSite S p n = 0 by
      simp [primeCombAnimationStepSite, hNotKilled, hNotFlipped, hOldZero]]
    simp [primeCombFrameSite, hn0, hn1, hNewSquare]
  have hAlive : PrimeCombFrameAlive S n :=
    primeCombFrameAlive_of_no_square hn0 hn1 hOldSquare
  by_cases hPSquare : p ^ 2 ∣ n
  · have hpdiv : p ∣ n := by
      rcases hPSquare with ⟨k, hk⟩
      refine ⟨p * k, ?_⟩
      simpa [pow_two, Nat.mul_assoc] using hk
    have hp2le : p ^ 2 ≤ n := Nat.le_of_dvd hnpos hPSquare
    have hplt : p < n := by
      have hpp : p < p ^ 2 := by
        nlinarith [hpPrime.two_le]
      exact hpp.trans_le hp2le
    have hproper : PrimeCombFrameProperMultiple p n := ⟨hplt, hpdiv⟩
    have hkilled : PrimeCombFrameKilled S p n :=
      ⟨hAlive, hproper, hPSquare⟩
    have hNewSquare : PrimeCombFrameSquareHit (insert p S) n :=
      (primeCombFrameSquareHit_insert S p n).2 (Or.inl hPSquare)
    rw [primeCombAnimationStepSite_eq_zero_of_killed S hkilled]
    simp [primeCombFrameSite, hn0, hn1, hNewSquare]
  have hNewNoSquare : ¬ PrimeCombFrameSquareHit (insert p S) n := by
    rw [primeCombFrameSquareHit_insert]
    simp [hPSquare, hOldSquare]
  by_cases hpdiv : p ∣ n
  · by_cases hplt : p < n
    · have hproper : PrimeCombFrameProperMultiple p n := ⟨hplt, hpdiv⟩
      have hpNotOldDivisor : p ∉ primeCombFrameDivisors S n := by
        simp [primeCombFrameDivisors, hpS]
      by_cases hProperTouched : PrimeCombFrameProperTouched S n
      · have hflipped : PrimeCombFrameFlipped S p n :=
          ⟨hAlive, hproper, hProperTouched, hPSquare⟩
        have hTouched : PrimeCombFrameTouched S n :=
          (primeCombFrameProperTouched_iff_touched_of_beforePrime
            S hSlt hplt).1 hProperTouched
        have hOldCardNe : (primeCombFrameDivisors S n).card ≠ 0 :=
          Finset.card_ne_zero.mpr hTouched
        have hOld :
            primeCombFrameSite S n =
              (-1 : ℤ) ^ (primeCombFrameDivisors S n).card := by
          unfold primeCombFrameSite
          rw [if_neg hn0, if_neg hn1, if_neg hOldSquare]
          dsimp
          rw [if_neg hOldCardNe]
        have hNewCard :
            (primeCombFrameDivisors (insert p S) n).card =
              (primeCombFrameDivisors S n).card + 1 := by
          rw [primeCombFrameDivisors_insert S p n, if_pos hpdiv,
            Finset.card_insert_of_notMem hpNotOldDivisor]
        have hNew :
            primeCombFrameSite (insert p S) n =
              (-1 : ℤ) ^ ((primeCombFrameDivisors S n).card + 1) := by
          unfold primeCombFrameSite
          rw [if_neg hn0, if_neg hn1, if_neg hNewNoSquare]
          dsimp
          rw [hNewCard, if_neg (by omega)]
        rw [primeCombAnimationStepSite_eq_neg_of_flipped S hflipped,
          hOld, hNew, pow_succ]
        ring
      · have hNotTouched : ¬ PrimeCombFrameTouched S n := by
          intro htouched
          exact hProperTouched
            ((primeCombFrameProperTouched_iff_touched_of_beforePrime
              S hSlt hplt).2 htouched)
        have hOldCardZero : (primeCombFrameDivisors S n).card = 0 := by
          by_contra hcard
          exact hNotTouched (Finset.card_ne_zero.mp hcard)
        have hfirst : PrimeCombFrameFirstHit S p n :=
          ⟨hAlive, hproper, hProperTouched, hPSquare⟩
        have hOld : primeCombFrameSite S n = -1 := by
          unfold primeCombFrameSite
          rw [if_neg hn0, if_neg hn1, if_neg hOldSquare]
          dsimp
          rw [if_pos hOldCardZero]
        have hNewCard :
            (primeCombFrameDivisors (insert p S) n).card = 1 := by
          rw [primeCombFrameDivisors_insert S p n, if_pos hpdiv,
            Finset.card_insert_of_notMem hpNotOldDivisor, hOldCardZero]
        have hNew : primeCombFrameSite (insert p S) n = -1 := by
          unfold primeCombFrameSite
          rw [if_neg hn0, if_neg hn1, if_neg hNewNoSquare]
          dsimp
          rw [hNewCard]
          norm_num
        rw [primeCombAnimationStepSite_eq_of_firstHit S hfirst, hOld, hNew]
    · have hpLeN : p ≤ n := Nat.le_of_dvd hnpos hpdiv
      have hnLeP : n ≤ p := Nat.le_of_not_gt hplt
      have hnp : n = p := Nat.le_antisymm hnLeP hpLeN
      subst n
      have hOldDivisors : primeCombFrameDivisors S p = ∅ :=
        primeCombFrameDivisors_prime_eq_empty S hpPrime hSPrime hSlt
      have hNotProper : ¬ PrimeCombFrameProperMultiple p p := by
        intro h
        exact (Nat.lt_irrefl p) h.1
      have hNotKilled : ¬ PrimeCombFrameKilled S p p := by
        intro h
        exact hNotProper h.2.1
      have hNotFlipped : ¬ PrimeCombFrameFlipped S p p := by
        intro h
        exact hNotProper h.2.1
      have hOld : primeCombFrameSite S p = -1 := by
        unfold primeCombFrameSite
        rw [if_neg hpPrime.ne_zero, if_neg hpPrime.ne_one,
          if_neg hOldSquare]
        dsimp
        rw [hOldDivisors]
        norm_num
      have hNewCard :
          (primeCombFrameDivisors (insert p S) p).card = 1 := by
        rw [primeCombFrameDivisors_insert S p p, if_pos (dvd_refl p),
          hOldDivisors]
        simp
      have hNew : primeCombFrameSite (insert p S) p = -1 := by
        unfold primeCombFrameSite
        rw [if_neg hpPrime.ne_zero, if_neg hpPrime.ne_one,
          if_neg hNewNoSquare]
        dsimp
        rw [hNewCard]
        norm_num
      simp [primeCombAnimationStepSite, hNotKilled, hNotFlipped, hOld, hNew]
  · have hNotProper : ¬ PrimeCombFrameProperMultiple p n := by
      intro h
      exact hpdiv h.2
    have hNotKilled : ¬ PrimeCombFrameKilled S p n := by
      intro h
      exact hNotProper h.2.1
    have hNotFlipped : ¬ PrimeCombFrameFlipped S p n := by
      intro h
      exact hNotProper h.2.1
    have hFrameEq :
        primeCombFrameSite (insert p S) n = primeCombFrameSite S n := by
      simp only [primeCombFrameSite, hn0, hn1, if_false,
        hNewNoSquare, hOldSquare, primeCombFrameDivisors_insert,
        hpdiv]
    rw [hFrameEq]
    simp [primeCombAnimationStepSite, hNotKilled, hNotFlipped]

/-! ## Literal ordered-prime corollaries -/

/-- The animation's `hit |= proper_multiple` assignment, as an exact logical
recurrence for the hit mask. -/
theorem primeCombFrameProperTouched_insert_iff
    (S : Finset ℕ) (p n : ℕ) :
    PrimeCombFrameProperTouched (insert p S) n ↔
      PrimeCombFrameProperTouched S n ∨ PrimeCombFrameProperMultiple p n := by
  unfold PrimeCombFrameProperTouched PrimeCombFrameProperMultiple
  constructor
  · rintro ⟨q, hq, hqn, hqdiv⟩
    rcases Finset.mem_insert.mp hq with hqp | hqS
    · subst q
      exact Or.inr ⟨hqn, hqdiv⟩
    · exact Or.inl ⟨q, hqS, hqn, hqdiv⟩
  · rintro (⟨q, hqS, hqn, hqdiv⟩ | ⟨hpn, hpdiv⟩)
    · exact ⟨q, Finset.mem_insert_of_mem hqS, hqn, hqdiv⟩
    · exact ⟨p, Finset.mem_insert_self p S, hpn, hpdiv⟩

/-- **Each successive rake can touch no more multiplier seats.**  Increasing
the prime coordinate shrinks the hyperbolic multiplier bunch. -/
theorem primeCombProperMultiplierSet_antitone
    {W p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    primeCombProperMultiplierSet q W ⊆ primeCombProperMultiplierSet p W := by
  intro k hk
  have hq : 0 < q := hp.trans_le hpq
  have hkData := (mem_primeCombProperMultiplierSet_iff hq).1 hk
  apply (mem_primeCombProperMultiplierSet_iff hp).2
  exact ⟨hkData.1, (Nat.mul_le_mul_left k hpq).trans hkData.2⟩

/-- Cardinal form of the shrinking-rake law. -/
theorem card_primeCombProperMultiplierSet_antitone
    {W p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    (primeCombProperMultiplierSet q W).card ≤
      (primeCombProperMultiplierSet p W).card :=
  Finset.card_le_card (primeCombProperMultiplierSet_antitone hp hpq)

/-- At a prime coordinate, the full ambient prime set is exactly the previous
prime frame plus the fresh coordinate. -/
theorem primesUpTo_eq_insert_pred_of_prime
    {p : ℕ} (hp : p.Prime) :
    primesUpTo p = insert p (primesUpTo (p - 1)) := by
  classical
  ext q
  simp only [mem_primesUpTo, Finset.mem_insert]
  constructor
  · rintro ⟨hqPrime, hqp⟩
    by_cases hqpEq : q = p
    · exact Or.inl hqpEq
    · exact Or.inr ⟨hqPrime, by omega⟩
  · rintro (hqp | ⟨hqPrime, hqPred⟩)
    · subst q
      exact ⟨hp, le_rfl⟩
    · exact ⟨hqPrime, by omega⟩

/-- The abstract insertion recurrence is therefore the literal increasing-prime
animation when the old frame is `primesUpTo (p-1)`. -/
theorem primeCombAnimationStepSite_primesUpTo_pred_eq
    (p n : ℕ) (hp : p.Prime) :
    primeCombAnimationStepSite (primesUpTo (p - 1)) p n =
      primeCombFrameSite (primesUpTo p) n := by
  have hSPrime : ∀ q ∈ primesUpTo (p - 1), q.Prime := by
    intro q hq
    exact prime_of_mem_primesUpTo hq
  have hSlt : ∀ q ∈ primesUpTo (p - 1), q < p := by
    intro q hq
    have hqPred := (mem_primesUpTo.mp hq).2
    omega
  calc
    primeCombAnimationStepSite (primesUpTo (p - 1)) p n =
        primeCombFrameSite (insert p (primesUpTo (p - 1))) n :=
      primeCombAnimationStepSite_eq_insert
        (primesUpTo (p - 1)) p n hp hSPrime hSlt
    _ = primeCombFrameSite (primesUpTo p) n := by
      rw [primesUpTo_eq_insert_pred_of_prime hp]

end RHLean.Proof
