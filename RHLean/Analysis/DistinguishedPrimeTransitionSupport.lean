import Mathlib
import RHLean.Arithmetic.PrimeSquareCollisionKernel
import RHLean.Analysis.TwoABPrimeDilation

/-!
# Distinguished-prime transition support

This module records exact forced-zero laws for one distinguished large-prime
coordinate across two consecutive physical three-slot cells.

The physical six sites are

* `4*k+1`, `4*k+2`, `4*k+3`,
* `4*k+5`, `4*k+6`, `4*k+7`.

If `q > 6`, divisibility by `q` can occur at at most one of these six sites.
Consequently a fixed distinguished transport-prime fibre has no active-to-active
source/destination transition.  After retaining an arbitrary sign bit on an
active slot, the nominal `7 x 7 = 49` signed transition class contracts exactly
to the `13` states consisting of inactive-to-inactive, active-to-inactive, and
inactive-to-active transitions.

The module also records the reciprocal-fibre cofactor bound
`c <= floor((R^2-1)/q)` and its extreme fibre-one consequences.  No analytic
estimate, stochastic model, or RH-scale contraction is asserted here: these are
finite arithmetic support theorems intended to shrink the admissible operator
class for a later restricted Gram or Lyapunov argument.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-- A divisor larger than `2` can hit at most one active slot inside a physical
three-slot four-cell. -/
theorem largeDivisor_threeSlotValue_slot_unique
    (q k i j : ℕ)
    (hq : 2 < q)
    (hi : i < 3) (hj : j < 3)
    (hqi : q ∣ threeSlotValue k i)
    (hqj : q ∣ threeSlotValue k j) :
    i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hdiff : q ∣ threeSlotValue k j - threeSlotValue k i :=
      Nat.dvd_sub hqj hqi
    have hgap : threeSlotValue k j - threeSlotValue k i = j - i := by
      unfold threeSlotValue
      omega
    rw [hgap] at hdiff
    have hpos : 0 < j - i := by omega
    have hqle : q ≤ j - i := Nat.le_of_dvd hpos hdiff
    omega
  · have hdiff : q ∣ threeSlotValue k i - threeSlotValue k j :=
      Nat.dvd_sub hqi hqj
    have hgap : threeSlotValue k i - threeSlotValue k j = i - j := by
      unfold threeSlotValue
      omega
    rw [hgap] at hdiff
    have hpos : 0 < i - j := by omega
    have hqle : q ≤ i - j := Nat.le_of_dvd hpos hdiff
    omega

/-- A divisor larger than `6` cannot hit one source slot and one destination
slot in two consecutive physical three-slot cells. -/
theorem largeDivisor_current_next_threeSlot_impossible
    (q k i j : ℕ)
    (hq : 6 < q)
    (hi : i < 3) (hj : j < 3)
    (hcur : q ∣ threeSlotValue k i)
    (hnext : q ∣ threeSlotValue (k + 1) j) :
    False := by
  have hdiff : q ∣ threeSlotValue (k + 1) j - threeSlotValue k i :=
    Nat.dvd_sub hnext hcur
  have hgap :
      threeSlotValue (k + 1) j - threeSlotValue k i = 4 + j - i := by
    unfold threeSlotValue
    omega
  rw [hgap] at hdiff
  have hpos : 0 < 4 + j - i := by omega
  have hle : 4 + j - i ≤ 6 := by omega
  have hqle : q ≤ 4 + j - i := Nat.le_of_dvd hpos hdiff
  omega

/-- Any two adjacent-cell physical sites divisible by the same `q > 6` are the
same integer.  Thus one distinguished large-prime fibre has at most one active
site in the entire six-site source/destination support. -/
theorem distinguishedPrime_adjacent_site_unique
    (q k n m : ℕ)
    (hq : 6 < q)
    (hn : IsAdjacentThreeSlotSite k n)
    (hm : IsAdjacentThreeSlotSite k m)
    (hqn : q ∣ n)
    (hqm : q ∣ m) :
    n = m := by
  rcases hn with ⟨i, hi, hni | hni⟩
  · rcases hm with ⟨j, hj, hmj | hmj⟩
    · subst n
      subst m
      have hij := largeDivisor_threeSlotValue_slot_unique
        q k i j (by omega) hi hj hqn hqm
      rw [hij]
    · subst n
      subst m
      exact (largeDivisor_current_next_threeSlot_impossible
        q k i j hq hi hj hqn hqm).elim
  · rcases hm with ⟨j, hj, hmj | hmj⟩
    · subst n
      subst m
      exact (largeDivisor_current_next_threeSlot_impossible
        q k j i hq hj hi hqm hqn).elim
    · subst n
      subst m
      have hij := largeDivisor_threeSlotValue_slot_unique
        q (k + 1) i j (by omega) hi hj hqn hqm
      rw [hij]

/-- A fixed prime/divisor is active in the source physical three-slot cell. -/
def fixedPrimeSourceActive (q k : ℕ) : Prop :=
  ∃ i : ℕ, i < 3 ∧ q ∣ threeSlotValue k i

/-- A fixed prime/divisor is active in the immediately following destination
physical three-slot cell. -/
def fixedPrimeDestinationActive (q k : ℕ) : Prop :=
  ∃ j : ℕ, j < 3 ∧ q ∣ threeSlotValue (k + 1) j

/-- **Forced-zero law.**  For `q > 6`, the same distinguished prime/divisor
cannot be active in both the source and destination cells. -/
theorem fixedPrime_source_destination_not_both
    (q k : ℕ) (hq : 6 < q) :
    ¬(fixedPrimeSourceActive q k ∧ fixedPrimeDestinationActive q k) := by
  rintro ⟨⟨i, hi, hcur⟩, ⟨j, hj, hnext⟩⟩
  exact largeDivisor_current_next_threeSlot_impossible
    q k i j hq hi hj hcur hnext

/-- Signed support state for one fixed distinguished prime in one three-slot
cell. `none` means inactive; `some (i, sign)` means active in slot `i`, retaining
one arbitrary sign bit. -/
abbrev SignedPrimeHitState := Option (Fin 3 × Bool)

/-- The exact support relation forced by six-site uniqueness: at least one side
of a source/destination transition must be inactive. -/
def FixedPrimeTransitionAdmissible
    (s t : SignedPrimeHitState) : Prop :=
  s = none ∨ t = none

instance fixedPrimeTransitionAdmissibleDecidable
    (s t : SignedPrimeHitState) :
    Decidable (FixedPrimeTransitionAdmissible s t) := by
  unfold FixedPrimeTransitionAdmissible
  infer_instance

/-- Nominal signed source state count: one inactive state plus `3 * 2` active
slot/sign states. -/
theorem signedPrimeHitState_card :
    Fintype.card SignedPrimeHitState = 7 := by
  native_decide

/-- All admissible fixed-prime source/destination signed transitions. -/
def fixedPrimeAdmissibleTransitions :
    Finset (SignedPrimeHitState × SignedPrimeHitState) :=
  Finset.univ.filter fun st =>
    FixedPrimeTransitionAdmissible st.1 st.2

/-- The nominal `7 x 7 = 49` transition class has exactly `13` admissible
entries once the arithmetic active-to-active forced zero is imposed. -/
theorem fixedPrimeAdmissibleTransitions_card :
    fixedPrimeAdmissibleTransitions.card = 13 := by
  native_decide

/-- Equivalently, `36` of the `49` nominal signed entries are forced zero. -/
theorem fixedPrimeForcedZeroTransitions_card :
    Fintype.card (SignedPrimeHitState × SignedPrimeHitState) -
        fixedPrimeAdmissibleTransitions.card = 36 := by
  native_decide

/-- Source compatibility only records the arithmetic support of an active
signed label.  The sign bit is deliberately unconstrained here. -/
def SourcePrimeHitCompatible
    (q k : ℕ) : SignedPrimeHitState → Prop
  | none => True
  | some a => q ∣ threeSlotValue k a.1

/-- Destination analogue of `SourcePrimeHitCompatible`. -/
def DestinationPrimeHitCompatible
    (q k : ℕ) : SignedPrimeHitState → Prop
  | none => True
  | some a => q ∣ threeSlotValue (k + 1) a.1

/-- Every physically compatible fixed-`q` signed transition lies in the exact
`13`-entry admissible class. -/
theorem compatible_fixedPrime_transition_admissible
    (q k : ℕ) (hq : 6 < q)
    (s t : SignedPrimeHitState)
    (hs : SourcePrimeHitCompatible q k s)
    (ht : DestinationPrimeHitCompatible q k t) :
    FixedPrimeTransitionAdmissible s t := by
  rcases s with _ | ⟨i, sign⟩
  · exact Or.inl rfl
  rcases t with _ | ⟨j, sign'⟩
  · exact Or.inr rfl
  have hcur : q ∣ threeSlotValue k i := by
    simpa [SourcePrimeHitCompatible] using hs
  have hnext : q ∣ threeSlotValue (k + 1) j := by
    simpa [DestinationPrimeHitCompatible] using ht
  exact (largeDivisor_current_next_threeSlot_impossible
    q k i j hq i.isLt j.isLt hcur hnext).elim

/-- Reciprocal quotient attached to one square-root transport prime fibre. -/
def transportReciprocalFibre (R q : ℕ) : ℕ :=
  squareRootEndpoint R / q

/-- Every transport cofactor lies below its reciprocal quotient fibre. -/
theorem transportCofactor_le_reciprocalFibre
    {R q c : ℕ}
    (hq : 0 < q)
    (hprod : c * q ≤ squareRootEndpoint R) :
    c ≤ transportReciprocalFibre R q := by
  unfold transportReciprocalFibre
  exact (Nat.le_div_iff_mul_le hq).2 hprod

/-- In reciprocal fibre `1`, every positive admissible cofactor is exactly the
unit cofactor. -/
theorem transportCofactor_eq_one_of_fibre_one
    {R q c : ℕ}
    (hq : 0 < q)
    (hc : 1 ≤ c)
    (hprod : c * q ≤ squareRootEndpoint R)
    (hfibre : transportReciprocalFibre R q = 1) :
    c = 1 := by
  have hcle := transportCofactor_le_reciprocalFibre
    (R := R) (q := q) (c := c) hq hprod
  rw [hfibre] at hcle
  omega

/-- Fibre-one transport sources have Möbius sign `-1`: the source is the prime
`q` itself. -/
theorem moebius_transportProduct_eq_neg_one_of_fibre_one
    {R q c : ℕ}
    (hqPrime : q.Prime)
    (hc : 1 ≤ c)
    (hprod : c * q ≤ squareRootEndpoint R)
    (hfibre : transportReciprocalFibre R q = 1) :
    μ (c * q) = -1 := by
  have hc1 := transportCofactor_eq_one_of_fibre_one
    (R := R) (q := q) (c := c) hqPrime.pos hc hprod hfibre
  subst c
  simp [ArithmeticFunction.moebius_apply_prime hqPrime]

/-- The physical middle slot cannot occur in reciprocal fibre `1` for an odd
prime.  Thus the top prime fibre is supported only on the four outer positions
of the six-site transition. -/
theorem fibre_one_middle_threeSlot_impossible
    {R q c k : ℕ}
    (hqPrime : q.Prime)
    (hq2 : 2 < q)
    (hc : 1 ≤ c)
    (hprod : c * q ≤ squareRootEndpoint R)
    (hfibre : transportReciprocalFibre R q = 1)
    (hmiddle : c * q = threeSlotValue k 1) :
    False := by
  have hc1 := transportCofactor_eq_one_of_fibre_one
    (R := R) (q := q) (c := c) hqPrime.pos hc hprod hfibre
  subst c
  simp only [one_mul] at hmiddle
  have hqOdd : Odd q := hqPrime.odd_of_ne_two (by omega)
  rcases hqOdd with ⟨a, ha⟩
  unfold threeSlotValue at hmiddle
  omega

/-- The same fibre-one middle-slot exclusion holds in the destination cell. -/
theorem fibre_one_destination_middle_impossible
    {R q c k : ℕ}
    (hqPrime : q.Prime)
    (hq2 : 2 < q)
    (hc : 1 ≤ c)
    (hprod : c * q ≤ squareRootEndpoint R)
    (hfibre : transportReciprocalFibre R q = 1)
    (hmiddle : c * q = threeSlotValue (k + 1) 1) :
    False := by
  exact fibre_one_middle_threeSlot_impossible
    hqPrime hq2 hc hprod hfibre hmiddle

end RHLean.Analysis
