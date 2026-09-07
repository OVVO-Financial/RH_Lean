import Mathlib
import RHLean.Proof.PostRootCovarianceLcmInteriorPacking

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-! ## The owner descent is literally an LCM-wall descent

The scalar and complete-interior layers are now supplied by merged PR #597.
This file keeps only the genuinely new structural continuation: stripping the
chronological first separating prime scales the pair LCM exactly by that owner,
which turns the super-endpoint carrier into a literal first-wall-crossing
problem.  The final section records the corresponding four-corner Boolean
finite difference before any norm or multiplicity estimate is taken.
-/

private theorem lcm_prime_mul_left_of_not_dvd
    {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    Nat.lcm (p * a) b = p * Nat.lcm a b := by
  apply Nat.dvd_antisymm
  · apply (Nat.lcm_dvd_iff).2
    constructor
    · exact Nat.mul_dvd_mul_left p (Nat.dvd_lcm_left a b)
    · rcases Nat.dvd_lcm_right a b with ⟨k, hk⟩
      refine ⟨p * k, ?_⟩
      rw [hk]
      ac_rfl
  · have hpTarget : p ∣ Nat.lcm (p * a) b :=
      (show p ∣ p * a from ⟨a, rfl⟩).trans (Nat.dvd_lcm_left (p * a) b)
    have haTarget : a ∣ Nat.lcm (p * a) b :=
      (show a ∣ p * a from ⟨p, by simp [Nat.mul_comm]⟩).trans
        (Nat.dvd_lcm_left (p * a) b)
    have hbTarget : b ∣ Nat.lcm (p * a) b := Nat.dvd_lcm_right (p * a) b
    have hlcmTarget : Nat.lcm a b ∣ Nat.lcm (p * a) b :=
      (Nat.lcm_dvd_iff).2 ⟨haTarget, hbTarget⟩
    have hlcmMul : Nat.lcm a b ∣ a * b := by
      apply (Nat.lcm_dvd_iff).2
      exact ⟨⟨b, rfl⟩, ⟨a, by simp [Nat.mul_comm]⟩⟩
    have hpNotLcm : ¬ p ∣ Nat.lcm a b := by
      intro hpLcm
      have hpMul : p ∣ a * b := hpLcm.trans hlcmMul
      rcases hp.dvd_mul.mp hpMul with hpA | hpB
      · exact hpa hpA
      · exact hpb hpB
    have hcop : Nat.Coprime p (Nat.lcm a b) :=
      hp.coprime_iff_not_dvd.mpr hpNotLcm
    exact hcop.mul_dvd_of_dvd_of_dvd hpTarget hlcmTarget

/-- Stripping the chronological first separating prime divides the pair LCM by
exactly that prime. -/
theorem squarefreePairFreshPrimeOwner_lcm_eq_owner_mul_parentLcm
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n)
    (hmpos : 0 < m) (hnpos : 0 < n) :
    let p := squarefreePairFreshPrimeOwner m n
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    Nat.lcm m n = p * Nat.lcm um un := by
  let p := squarefreePairFreshPrimeOwner m n
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  change Nat.lcm m n = p * Nat.lcm um un
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hm hn hmn
  have hcube := squarefreePairFreshPrimeOwner_parentCube hm hn hmn hmpos hnpos
  change (¬ p ∣ um) ∧ (¬ p ∣ un) ∧
      ((m = p * um ∧ n = un) ∨ (m = um ∧ n = p * un)) at hcube
  rcases hcube with ⟨hpm, hpn, h | h⟩
  · rw [h.1, h.2]
    exact lcm_prime_mul_left_of_not_dvd hp hpm hpn
  · rw [h.1, h.2]
    calc
      Nat.lcm um (p * un) = Nat.lcm (p * un) um := Nat.lcm_comm _ _
      _ = p * Nat.lcm un um := lcm_prime_mul_left_of_not_dvd hp hpn hpm
      _ = p * Nat.lcm um un := by rw [Nat.lcm_comm un um]

/-- Reorienting the stripped parent does not change its LCM. -/
theorem squarefreePairFreshPrimeOrderedParent_lcm (m n : ℕ) :
    Nat.lcm (squarefreePairFreshPrimeOrderedParent m n).1
        (squarefreePairFreshPrimeOrderedParent m n).2 =
      Nat.lcm
        (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m)
        (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n) := by
  unfold squarefreePairFreshPrimeOrderedParent
  by_cases h :
      squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m <
        squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n
  · simp [h]
  · simp [h, Nat.lcm_comm]

/-- Ordered-parent form of the exact LCM scaling law. -/
theorem squarefreePairFreshPrimeOwner_lcm_eq_owner_mul_orderedParentLcm
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n) (hmn : m ≠ n)
    (hmpos : 0 < m) (hnpos : 0 < n) :
    Nat.lcm m n =
      squarefreePairFreshPrimeOwner m n *
        Nat.lcm (squarefreePairFreshPrimeOrderedParent m n).1
          (squarefreePairFreshPrimeOrderedParent m n).2 := by
  rw [squarefreePairFreshPrimeOrderedParent_lcm]
  exact squarefreePairFreshPrimeOwner_lcm_eq_owner_mul_parentLcm
    hm hn hmn hmpos hnpos

/-- **First LCM-wall dichotomy.**  On a nonzero boundary pair, stripping the
chronological owner either stays on the super-endpoint side or crosses the wall
for the first time.  In the crossing case the child LCM is exactly the owner
prime times the admitted parent LCM. -/
theorem postRootCovarianceRemainderBoundary_owner_parent_lcm_dichotomy
    {W m n : ℕ}
    (hboundary : (m, n) ∈ postRootCovarianceRemainderBoundaryLcmCarrier W)
    (hweight : realMoebiusStep m * realMoebiusStep n ≠ 0) :
    let p := squarefreePairFreshPrimeOwner m n
    let parent := squarefreePairFreshPrimeOrderedParent m n
    (W < Nat.lcm parent.1 parent.2) ∨
      (Nat.lcm parent.1 parent.2 ≤ W ∧
        W < p * Nat.lcm parent.1 parent.2) := by
  rcases mem_postRootCovarianceRemainderBoundaryLcmCarrier.mp hboundary with
    ⟨hremainder, hchildWall⟩
  have hphysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hremainder).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hphysical with
    ⟨hm1, _hmW, hn1, _hnW, hmnlt⟩
  have hmstep : realMoebiusStep m ≠ 0 := by
    intro hmzero
    exact hweight (by rw [hmzero, zero_mul])
  have hnstep : realMoebiusStep n ≠ 0 := by
    intro hnzero
    exact hweight (by rw [hnzero, mul_zero])
  have hm : Squarefree m := squarefree_of_realMoebiusStep_ne_zero hmstep
  have hn : Squarefree n := squarefree_of_realMoebiusStep_ne_zero hnstep
  have hscale :=
    squarefreePairFreshPrimeOwner_lcm_eq_owner_mul_orderedParentLcm
      hm hn (Nat.ne_of_lt hmnlt) (by omega) (by omega)
  let p := squarefreePairFreshPrimeOwner m n
  let parent := squarefreePairFreshPrimeOrderedParent m n
  change (W < Nat.lcm parent.1 parent.2) ∨
    (Nat.lcm parent.1 parent.2 ≤ W ∧
      W < p * Nat.lcm parent.1 parent.2)
  by_cases hparent : W < Nat.lcm parent.1 parent.2
  · exact Or.inl hparent
  · right
    have hle : Nat.lcm parent.1 parent.2 ≤ W := Nat.le_of_not_gt hparent
    refine ⟨hle, ?_⟩
    rw [← hscale]
    exact hchildWall

/-! ## Exact four-corner finite difference at the LCM wall -/

/-- Real indicator for the literal super-endpoint LCM wall. -/
def superLcmIndicator (W m n : ℕ) : ℝ :=
  if W < Nat.lcm m n then 1 else 0

private theorem lcm_prime_mul_right_of_not_dvd
    {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    Nat.lcm a (p * b) = p * Nat.lcm a b := by
  calc
    Nat.lcm a (p * b) = Nat.lcm (p * b) a := Nat.lcm_comm _ _
    _ = p * Nat.lcm b a := lcm_prime_mul_left_of_not_dvd hp hpb hpa
    _ = p * Nat.lcm a b := by rw [Nat.lcm_comm b a]

/-- **Exact one-prime LCM wall stencil.**  For a prime fresh to both parent
coordinates, the three non-base corners have common LCM `p*lcm(a,b)`.  The
complete four-corner indicator derivative therefore vanishes everywhere except
at the literal first crossing `lcm(a,b) ≤ W < p*lcm(a,b)`, where it is `-1`. -/
theorem superLcmIndicator_fourCorner_eq_firstFailure
    {W p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    superLcmIndicator W a b -
        superLcmIndicator W (p * a) b -
        superLcmIndicator W a (p * b) +
        superLcmIndicator W (p * a) (p * b) =
      if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b then -1 else 0 := by
  have hleft := lcm_prime_mul_left_of_not_dvd hp hpa hpb
  have hright := lcm_prime_mul_right_of_not_dvd hp hpa hpb
  have hboth : Nat.lcm (p * a) (p * b) = p * Nat.lcm a b := by
    rw [Nat.lcm_mul_left]
  unfold superLcmIndicator
  rw [hleft, hright, hboth]
  have hle : Nat.lcm a b ≤ p * Nat.lcm a b := by
    calc
      Nat.lcm a b = 1 * Nat.lcm a b := by simp
      _ ≤ p * Nat.lcm a b := Nat.mul_le_mul_right _ hp.one_le
  by_cases hbase : W < Nat.lcm a b
  · have hupper : W < p * Nat.lcm a b := hbase.trans_le hle
    simp [hbase, hupper]
  · have hbaseLe : Nat.lcm a b ≤ W := Nat.le_of_not_gt hbase
    by_cases hupper : W < p * Nat.lcm a b
    · simp [hbase, hbaseLe, hupper]
    · simp [hbase, hupper]

/-- **Möbius-weighted first-failure stencil.**  Fresh-prime sign reversal turns
the four physical pair corners into the Boolean derivative above.  Thus a full
Euler square contributes exactly zero away from the first LCM wall and exactly
minus its old pair weight on that wall. -/
theorem realMoebiusSuperLcmFourCorner_eq_firstFailure
    {W p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    (realMoebiusStep a * realMoebiusStep b) * superLcmIndicator W a b +
      (realMoebiusStep (p * a) * realMoebiusStep b) *
        superLcmIndicator W (p * a) b +
      (realMoebiusStep a * realMoebiusStep (p * b)) *
        superLcmIndicator W a (p * b) +
      (realMoebiusStep (p * a) * realMoebiusStep (p * b)) *
        superLcmIndicator W (p * a) (p * b) =
      if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b then
        -(realMoebiusStep a * realMoebiusStep b)
      else 0 := by
  rw [realMoebiusStep_mul_prime_eq_neg hp hpa,
    realMoebiusStep_mul_prime_eq_neg hp hpb]
  have hwall := superLcmIndicator_fourCorner_eq_firstFailure
    (W := W) hp hpa hpb
  by_cases hcross : Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b
  · rw [if_pos hcross] at hwall ⊢
    linear_combination (realMoebiusStep a * realMoebiusStep b) * hwall
  · rw [if_neg hcross] at hwall ⊢
    linear_combination (realMoebiusStep a * realMoebiusStep b) * hwall

end RHLean.Proof
