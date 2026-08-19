import Mathlib
import RHLean.Proof.PrimeCombVisualizationFrames

/-!
# Operational transitions of the prime-comb visualization

This module formalizes the Boolean masks and frame update used by
`prime_comb_viz 2.py`.  The processed-prime set is the state coordinate; a
single next-prime step is divided into exactly the channels shown in the
animation:

* `alive`;
* proper-multiple rake;
* square kill;
* first proper hit;
* later flip.

The operational update is first defined directly from those masks.  It is then
proved equal, site by site, to inserting the next prime into the exact frame
from `PrimeCombVisualizationFrames`.  Summing the pointwise identity gives the
animation assertion

```text
Delta B = - killMass - 2 * flipMass.
```

No estimate occurs here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## The next-prime and event predicates -/

/-- `p` is the next prime after every coordinate already present in `S`. -/
def PrimeCombNextPrime (S : Finset ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p ∉ S ∧ ∀ q ∈ S, q.Prime ∧ q < p

/-- The exact proper-multiple condition.  For a positive divisor `p` this is
identical to the visualization mask `2*p <= n` together with `p | n`. -/
def PrimeCombFrameRake (p n : ℕ) : Prop :=
  p < n ∧ p ∣ n

/-- The site is nonwhite before the prime acts. -/
def PrimeCombFrameAlive (S : Finset ℕ) (n : ℕ) : Prop :=
  primeCombFrameSite S n ≠ 0

/-- Exact `killed` mask from the visualization. -/
def PrimeCombFrameKillEvent (S : Finset ℕ) (p n : ℕ) : Prop :=
  PrimeCombFrameAlive S n ∧ PrimeCombFrameRake p n ∧ p ^ 2 ∣ n

/-- Exact `first_hit` mask from the visualization. -/
def PrimeCombFrameFirstHitEvent (S : Finset ℕ) (p n : ℕ) : Prop :=
  PrimeCombFrameAlive S n ∧ PrimeCombFrameRake p n ∧
    ¬ p ^ 2 ∣ n ∧ ¬ PrimeCombFrameProperTouched S n

/-- Exact `flipped` mask from the visualization. -/
def PrimeCombFrameFlipEvent (S : Finset ℕ) (p n : ℕ) : Prop :=
  PrimeCombFrameAlive S n ∧ PrimeCombFrameRake p n ∧
    ¬ p ^ 2 ∣ n ∧ PrimeCombFrameProperTouched S n

/-- The operational site update implemented by the visualization.  First hits
are intentionally absent because they leave the displayed `-1` unchanged. -/
def primeCombOperationalStepSite
    (S : Finset ℕ) (p n : ℕ) : ℤ :=
  if PrimeCombFrameKillEvent S p n then 0
  else if PrimeCombFrameFlipEvent S p n then -primeCombFrameSite S n
  else primeCombFrameSite S n

/-- Signed mass after applying one operational prime step. -/
def primeCombOperationalStepPrefixMass
    (S : Finset ℕ) (p W : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 W, primeCombOperationalStepSite S p n

/-- Signed mass killed by one frame, measured before the update exactly as in
the Python diagnostic. -/
def primeCombFrameKillMass (S : Finset ℕ) (p W : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 W,
    if PrimeCombFrameKillEvent S p n then primeCombFrameSite S n else 0

/-- Signed mass flipped by one frame, measured before the update. -/
def primeCombFrameFlipMass (S : Finset ℕ) (p W : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 W,
    if PrimeCombFrameFlipEvent S p n then primeCombFrameSite S n else 0

/-- Number of first-touch seats in one frame. -/
def primeCombFrameFirstHitCount (S : Finset ℕ) (p W : ℕ) : ℕ :=
  ((Finset.Icc 1 W).filter fun n => PrimeCombFrameFirstHitEvent S p n).card

/-- Number of later-flip seats in one frame. -/
def primeCombFrameFlipCount (S : Finset ℕ) (p W : ℕ) : ℕ :=
  ((Finset.Icc 1 W).filter fun n => PrimeCombFrameFlipEvent S p n).card

/-- Number of square-kill seats in one frame. -/
def primeCombFrameKillCount (S : Finset ℕ) (p W : ℕ) : ℕ :=
  ((Finset.Icc 1 W).filter fun n => PrimeCombFrameKillEvent S p n).card

/-- The actual ascending animation uses exactly `primesUpTo (p-1)` before a
prime `p` is processed. -/
theorem primeCombNextPrime_primesUpTo_pred
    {p : ℕ} (hp : p.Prime) :
    PrimeCombNextPrime (primesUpTo (p - 1)) p := by
  refine ⟨hp, ?_, ?_⟩
  · intro hpMem
    have hpLe := (mem_primesUpTo.mp hpMem).2
    omega
  · intro q hq
    have hqData := mem_primesUpTo.mp hq
    exact ⟨hqData.1, by omega⟩

/-- The `hit` Boolean updates by setting every proper multiple of `p` to true. -/
theorem primeCombFrameProperTouched_insert_iff
    (S : Finset ℕ) (p n : ℕ) :
    PrimeCombFrameProperTouched (insert p S) n ↔
      PrimeCombFrameRake p n ∨ PrimeCombFrameProperTouched S n := by
  simp only [PrimeCombFrameProperTouched, PrimeCombFrameRake,
    Finset.mem_insert]
  constructor
  · rintro ⟨q, hqp | hqS, hqn, hqdiv⟩
    · subst q
      exact Or.inl ⟨hqn, hqdiv⟩
    · exact Or.inr ⟨q, hqS, hqn, hqdiv⟩
  · rintro (hpRake | hOld)
    · exact ⟨p, Or.inl rfl, hpRake.1, hpRake.2⟩
    · rcases hOld with ⟨q, hqS, hqn, hqdiv⟩
      exact ⟨q, Or.inr hqS, hqn, hqdiv⟩

/-- On a genuine rake seat, selected-divisor touch and the visualization's
proper-touch Boolean are the same because all earlier selected primes lie below
`p<n`. -/
theorem primeCombFrameTouched_iff_properTouched_of_nextPrime_rake
    {S : Finset ℕ} {p n : ℕ}
    (hnext : PrimeCombNextPrime S p)
    (hrake : PrimeCombFrameRake p n) :
    PrimeCombFrameTouched S n ↔ PrimeCombFrameProperTouched S n := by
  constructor
  · intro ht
    rcases ht with ⟨q, hq⟩
    have hqData := Finset.mem_filter.mp hq
    have hqNext := hnext.2.2 q hqData.1
    exact ⟨q, hqData.1, hqNext.2.trans hrake.1, hqData.2⟩
  · rintro ⟨q, hqS, _hqn, hqdiv⟩
    exact ⟨q, Finset.mem_filter.mpr ⟨hqS, hqdiv⟩⟩

/-- Square-kill and later-flip masks are disjoint. -/
theorem primeCombFrameKillEvent_not_flip
    {S : Finset ℕ} {p n : ℕ}
    (hkill : PrimeCombFrameKillEvent S p n) :
    ¬ PrimeCombFrameFlipEvent S p n := by
  intro hflip
  exact hflip.2.2.1 hkill.2.2

/-- First-hit and later-flip masks are disjoint. -/
theorem primeCombFrameFirstHitEvent_not_flip
    {S : Finset ℕ} {p n : ℕ}
    (hfirst : PrimeCombFrameFirstHitEvent S p n) :
    ¬ PrimeCombFrameFlipEvent S p n := by
  intro hflip
  exact hfirst.2.2.2 hflip.2.2.2

/-! ## Sitewise transition laws -/

private theorem primeCombFrameSite_ne_zero_of_no_square
    (S : Finset ℕ) {n : ℕ}
    (hnpos : 0 < n) (hn1 : n ≠ 1)
    (hsquare : ¬ PrimeCombFrameSquareHit S n) :
    primeCombFrameSite S n ≠ 0 := by
  unfold primeCombFrameSite
  simp [Nat.ne_of_gt hnpos, hn1, hsquare]

/-- A prime not dividing the site has no effect. -/
theorem primeCombFrameSite_insert_eq_self_of_not_dvd
    (S : Finset ℕ) {p n : ℕ} (hpn : ¬ p ∣ n) :
    primeCombFrameSite (insert p S) n = primeCombFrameSite S n := by
  have hp2 : ¬ p ^ 2 ∣ n := by
    intro hp2n
    exact hpn (dvd_trans (by exact ⟨p, by simp [pow_two]⟩) hp2n)
  simp [primeCombFrameSite, primeCombFrameDivisors_insert, hpn, hp2]

/-- If no square is present, insertion of a fresh divisor either leaves the
untouched `-1` unchanged or flips an already-touched sign. -/
theorem primeCombFrameSite_insert_of_rake_no_square
    (S : Finset ℕ) {p n : ℕ}
    (hpS : p ∉ S)
    (hrake : PrimeCombFrameRake p n)
    (hOldSquare : ¬ PrimeCombFrameSquareHit S n)
    (hpSquare : ¬ p ^ 2 ∣ n) :
    primeCombFrameSite (insert p S) n =
      if PrimeCombFrameTouched S n then
        -primeCombFrameSite S n
      else
        primeCombFrameSite S n := by
  classical
  have hnpos : 0 < n := by omega
  have hn1 : n ≠ 1 := by omega
  have hpDiv : p ∣ n := hrake.2
  have hpNotDivisors : p ∉ primeCombFrameDivisors S n := by
    intro hpMem
    exact hpS (Finset.mem_filter.mp hpMem).1
  have hNewSquare : ¬ PrimeCombFrameSquareHit (insert p S) n := by
    simpa using (not_or_intro hpSquare hOldSquare)
  by_cases ht : PrimeCombFrameTouched S n
  · have hcard : (primeCombFrameDivisors S n).card ≠ 0 :=
      Finset.card_ne_zero.mpr ht
    have hcardInsert :
        (insert p (primeCombFrameDivisors S n)).card =
          (primeCombFrameDivisors S n).card + 1 := by
      rw [Finset.card_insert_of_notMem hpNotDivisors]
    simp only [if_pos ht]
    unfold primeCombFrameSite
    rw [if_neg (Nat.ne_of_gt hnpos), if_neg hn1, if_neg hNewSquare,
      primeCombFrameDivisors_insert, if_pos hpDiv,
      if_neg (Nat.ne_of_gt hnpos), if_neg hn1, if_neg hOldSquare]
    dsimp
    rw [hcardInsert, if_neg hcard]
    have hsucc :
        (-1 : ℤ) ^ ((primeCombFrameDivisors S n).card + 1) =
          -((-1 : ℤ) ^ (primeCombFrameDivisors S n).card) := by
      rw [pow_succ]
      ring
    rw [hsucc]
  · have hcard : (primeCombFrameDivisors S n).card = 0 := by
      by_contra hne
      exact ht (Finset.card_ne_zero.mp hne)
    have hcardInsert :
        (insert p (primeCombFrameDivisors S n)).card = 1 := by
      rw [Finset.card_insert_of_notMem hpNotDivisors, hcard]
      simp
    simp only [if_neg ht]
    unfold primeCombFrameSite
    rw [if_neg (Nat.ne_of_gt hnpos), if_neg hn1, if_neg hNewSquare,
      primeCombFrameDivisors_insert, if_pos hpDiv,
      if_neg (Nat.ne_of_gt hnpos), if_neg hn1, if_neg hOldSquare]
    dsimp
    simp [hcardInsert, hcard]

/-- A prime-square event kills the new frame site. -/
theorem primeCombFrameSite_insert_eq_zero_of_kill
    {S : Finset ℕ} {p n : ℕ}
    (hkill : PrimeCombFrameKillEvent S p n) :
    primeCombFrameSite (insert p S) n = 0 := by
  have hnpos : 0 < n := by omega
  have hn1 : n ≠ 1 := by omega
  have hsquare : PrimeCombFrameSquareHit (insert p S) n := by
    exact (primeCombFrameSquareHit_insert S p n).2 (Or.inl hkill.2.2)
  simp [primeCombFrameSite, Nat.ne_of_gt hnpos, hn1, hsquare]

/-- At a first proper hit the displayed value is `-1` and does not move. -/
theorem primeCombFrameSite_insert_eq_self_of_firstHit
    {S : Finset ℕ} {p n : ℕ}
    (hnext : PrimeCombNextPrime S p)
    (hfirst : PrimeCombFrameFirstHitEvent S p n) :
    primeCombFrameSite (insert p S) n = primeCombFrameSite S n := by
  have hOldSquare : ¬ PrimeCombFrameSquareHit S n := by
    intro hsq
    have hnpos : 0 < n := by omega
    have hn1 : n ≠ 1 := by omega
    have hz : primeCombFrameSite S n = 0 := by
      simp [primeCombFrameSite, Nat.ne_of_gt hnpos, hn1, hsq]
    exact hfirst.1 hz
  have htouchIff :=
    primeCombFrameTouched_iff_properTouched_of_nextPrime_rake hnext hfirst.2.1
  have hnotTouch : ¬ PrimeCombFrameTouched S n := by
    intro ht
    exact hfirst.2.2.2 (htouchIff.mp ht)
  rw [primeCombFrameSite_insert_of_rake_no_square S hnext.2.1
    hfirst.2.1 hOldSquare hfirst.2.2.1]
  simp [hnotTouch]

/-- At a later nonsquare hit the displayed value flips sign. -/
theorem primeCombFrameSite_insert_eq_neg_of_flip
    {S : Finset ℕ} {p n : ℕ}
    (hnext : PrimeCombNextPrime S p)
    (hflip : PrimeCombFrameFlipEvent S p n) :
    primeCombFrameSite (insert p S) n = -primeCombFrameSite S n := by
  have hOldSquare : ¬ PrimeCombFrameSquareHit S n := by
    intro hsq
    have hnpos : 0 < n := by omega
    have hn1 : n ≠ 1 := by omega
    have hz : primeCombFrameSite S n = 0 := by
      simp [primeCombFrameSite, Nat.ne_of_gt hnpos, hn1, hsq]
    exact hflip.1 hz
  have htouchIff :=
    primeCombFrameTouched_iff_properTouched_of_nextPrime_rake hnext hflip.2.1
  have htouch : PrimeCombFrameTouched S n := htouchIff.mpr hflip.2.2.2
  rw [primeCombFrameSite_insert_of_rake_no_square S hnext.2.1
    hflip.2.1 hOldSquare hflip.2.2.1]
  simp [htouch]

/-- The next prime does not change its own prime-candidate seat. -/
theorem primeCombFrameSite_insert_nextPrime_self
    {S : Finset ℕ} {p : ℕ}
    (hnext : PrimeCombNextPrime S p) :
    primeCombFrameSite (insert p S) p = primeCombFrameSite S p := by
  classical
  have hp := hnext.1
  have hOldDiv : primeCombFrameDivisors S p = ∅ := by
    ext q
    simp only [primeCombFrameDivisors, Finset.mem_filter, Finset.notMem_empty,
      iff_false]
    intro hq
    have hqNext := hnext.2.2 q hq.1
    rcases (Nat.dvd_prime hp).mp hq.2 with hq1 | hqp
    · exact hqNext.1.ne_one hq1
    · subst q
      omega
  have hOldSquare : ¬ PrimeCombFrameSquareHit S p := by
    intro hsq
    rcases hsq with ⟨q, hqS, hq2⟩
    have hqdiv : q ∣ p := by
      rcases hq2 with ⟨k, hk⟩
      refine ⟨q * k, ?_⟩
      simpa [pow_two, Nat.mul_assoc] using hk
    have hmem : q ∈ primeCombFrameDivisors S p :=
      Finset.mem_filter.mpr ⟨hqS, hqdiv⟩
    rw [hOldDiv] at hmem
    simp at hmem
  have hpSquare : ¬ p ^ 2 ∣ p := by
    intro hp2
    have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hp2
    have hp2le : 2 ≤ p := hp.two_le
    nlinarith
  have hNewSquare : ¬ PrimeCombFrameSquareHit (insert p S) p := by
    simpa using (not_or_intro hpSquare hOldSquare)
  have hNewDiv : primeCombFrameDivisors (insert p S) p = {p} := by
    rw [primeCombFrameDivisors_insert]
    simp [hOldDiv]
  simp [primeCombFrameSite, hp.ne_zero, hp.ne_one,
    hOldSquare, hNewSquare, hOldDiv, hNewDiv]

/-- The operational Boolean-mask update is exactly insertion of the next prime
into the processed-coordinate frame. -/
theorem primeCombOperationalStepSite_eq_insert
    {S : Finset ℕ} {p n : ℕ}
    (hnext : PrimeCombNextPrime S p)
    (hnpos : 0 < n) :
    primeCombOperationalStepSite S p n =
      primeCombFrameSite (insert p S) n := by
  by_cases hpn : p ∣ n
  · by_cases hnp : n = p
    · subst n
      have hnotRake : ¬ PrimeCombFrameRake p p := by
        simp [PrimeCombFrameRake]
      have hnotKill : ¬ PrimeCombFrameKillEvent S p p := by
        intro h
        exact hnotRake h.2.1
      have hnotFlip : ¬ PrimeCombFrameFlipEvent S p p := by
        intro h
        exact hnotRake h.2.1
      simp [primeCombOperationalStepSite, hnotKill, hnotFlip,
        primeCombFrameSite_insert_nextPrime_self hnext]
    · have hpLe : p ≤ n := Nat.le_of_dvd hnpos hpn
      have hrake : PrimeCombFrameRake p n := ⟨by omega, hpn⟩
      by_cases hOldSquare : PrimeCombFrameSquareHit S n
      · have hn1 : n ≠ 1 := by omega
        have hOldZero : primeCombFrameSite S n = 0 := by
          simp [primeCombFrameSite, Nat.ne_of_gt hnpos, hn1, hOldSquare]
        have hnotAlive : ¬ PrimeCombFrameAlive S n := by
          simp [PrimeCombFrameAlive, hOldZero]
        have hnotKill : ¬ PrimeCombFrameKillEvent S p n := by
          intro h
          exact hnotAlive h.1
        have hnotFlip : ¬ PrimeCombFrameFlipEvent S p n := by
          intro h
          exact hnotAlive h.1
        have hNewSquare : PrimeCombFrameSquareHit (insert p S) n :=
          (primeCombFrameSquareHit_insert S p n).2 (Or.inr hOldSquare)
        have hNewZero : primeCombFrameSite (insert p S) n = 0 := by
          simp [primeCombFrameSite, Nat.ne_of_gt hnpos, hn1, hNewSquare]
        simp [primeCombOperationalStepSite, hnotKill, hnotFlip,
          hOldZero, hNewZero]
      · have hn1 : n ≠ 1 := by omega
        have hAlive : PrimeCombFrameAlive S n :=
          primeCombFrameSite_ne_zero_of_no_square S hnpos hn1 hOldSquare
        by_cases hpSquare : p ^ 2 ∣ n
        · have hkill : PrimeCombFrameKillEvent S p n :=
            ⟨hAlive, hrake, hpSquare⟩
          have hnotFlip := primeCombFrameKillEvent_not_flip hkill
          have hNewZero := primeCombFrameSite_insert_eq_zero_of_kill hkill
          simp [primeCombOperationalStepSite, hkill, hnotFlip, hNewZero]
        · have htouchIff :=
            primeCombFrameTouched_iff_properTouched_of_nextPrime_rake hnext hrake
          by_cases hproper : PrimeCombFrameProperTouched S n
          · have hflip : PrimeCombFrameFlipEvent S p n :=
              ⟨hAlive, hrake, hpSquare, hproper⟩
            have hnotKill : ¬ PrimeCombFrameKillEvent S p n := by
              intro h
              exact hpSquare h.2.2
            have hNew := primeCombFrameSite_insert_eq_neg_of_flip hnext hflip
            simp [primeCombOperationalStepSite, hnotKill, hflip, hNew]
          · have hfirst : PrimeCombFrameFirstHitEvent S p n :=
              ⟨hAlive, hrake, hpSquare, hproper⟩
            have hnotKill : ¬ PrimeCombFrameKillEvent S p n := by
              intro h
              exact hpSquare h.2.2
            have hnotFlip : ¬ PrimeCombFrameFlipEvent S p n := by
              intro h
              exact hproper h.2.2.2
            have hNew := primeCombFrameSite_insert_eq_self_of_firstHit hnext hfirst
            simp [primeCombOperationalStepSite, hnotKill, hnotFlip, hNew]
  · have hnotKill : ¬ PrimeCombFrameKillEvent S p n := by
      intro h
      exact hpn h.2.1.2
    have hnotFlip : ¬ PrimeCombFrameFlipEvent S p n := by
      intro h
      exact hpn h.2.1.2
    have hNew := primeCombFrameSite_insert_eq_self_of_not_dvd S hpn
    simp [primeCombOperationalStepSite, hnotKill, hnotFlip, hNew]

/-! ## Exact signed-mass accounting -/

/-- Pointwise form of the animation's delta assertion. -/
theorem primeCombOperationalStepSite_sub_eq_channels
    (S : Finset ℕ) (p n : ℕ) :
    primeCombOperationalStepSite S p n - primeCombFrameSite S n =
      -(if PrimeCombFrameKillEvent S p n then primeCombFrameSite S n else 0) -
        2 * (if PrimeCombFrameFlipEvent S p n then primeCombFrameSite S n else 0) := by
  by_cases hkill : PrimeCombFrameKillEvent S p n
  · have hnotFlip := primeCombFrameKillEvent_not_flip hkill
    simp [primeCombOperationalStepSite, hkill, hnotFlip]
  · by_cases hflip : PrimeCombFrameFlipEvent S p n
    · simp [primeCombOperationalStepSite, hkill, hflip]
      ring
    · simp [primeCombOperationalStepSite, hkill, hflip]

/-- Summing the pointwise update gives exactly the displayed identity
`Delta B = -killMass - 2*flipMass`. -/
theorem primeCombOperationalStepPrefixMass_sub_eq_channels
    (S : Finset ℕ) (p W : ℕ) :
    primeCombOperationalStepPrefixMass S p W -
        primeCombFramePrefixMass S W =
      -primeCombFrameKillMass S p W - 2 * primeCombFrameFlipMass S p W := by
  unfold primeCombOperationalStepPrefixMass primeCombFramePrefixMass
    primeCombFrameKillMass primeCombFrameFlipMass
  rw [Finset.sum_sub_distrib]
  calc
    (∑ n ∈ Finset.Icc 1 W,
        (primeCombOperationalStepSite S p n - primeCombFrameSite S n)) =
      ∑ n ∈ Finset.Icc 1 W,
        (-(if PrimeCombFrameKillEvent S p n then primeCombFrameSite S n else 0) -
          2 * (if PrimeCombFrameFlipEvent S p n then primeCombFrameSite S n else 0)) := by
        apply Finset.sum_congr rfl
        intro n _hn
        exact primeCombOperationalStepSite_sub_eq_channels S p n
    _ = - (∑ n ∈ Finset.Icc 1 W,
          if PrimeCombFrameKillEvent S p n then primeCombFrameSite S n else 0) -
        2 * (∑ n ∈ Finset.Icc 1 W,
          if PrimeCombFrameFlipEvent S p n then primeCombFrameSite S n else 0) := by
        rw [Finset.sum_sub_distrib]
        rw [Finset.sum_neg_distrib]
        rw [Finset.mul_sum]

/-- Therefore the actual next-prime frame satisfies the same signed-mass law. -/
theorem primeCombFramePrefixMass_insert_sub_eq_channels
    {S : Finset ℕ} {p W : ℕ}
    (hnext : PrimeCombNextPrime S p) :
    primeCombFramePrefixMass (insert p S) W -
        primeCombFramePrefixMass S W =
      -primeCombFrameKillMass S p W - 2 * primeCombFrameFlipMass S p W := by
  have hstep :
      primeCombOperationalStepPrefixMass S p W =
        primeCombFramePrefixMass (insert p S) W := by
    unfold primeCombOperationalStepPrefixMass primeCombFramePrefixMass
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := by
      have hn1 := (Finset.mem_Icc.mp hn).1
      omega
    exact primeCombOperationalStepSite_eq_insert hnext hnpos
  rw [← hstep]
  exact primeCombOperationalStepPrefixMass_sub_eq_channels S p W

end RHLean.Proof
