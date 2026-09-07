import Mathlib
import RHLean.Proof.PostRootCovarianceLcmInteriorPacking

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-- Stripping a prime-family coordinate always produces a divisor of the
original physical site. -/
private theorem lcmBoundary_squarefreePrimeFamilyParent_dvd
    (p n : ℕ) : squarefreePrimeFamilyParent p n ∣ n := by
  unfold squarefreePrimeFamilyParent
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    exact ⟨p, (Nat.div_mul_cancel hpn).symm⟩
  · simp [hpn]

/-- **Strict LCM descent under first-separation stripping.**

For a distinct positive squarefree pair, stripping its chronological first
separating prime from both endpoints strictly lowers the pair LCM.  The proof
is purely divisibility-theoretic: both parents divide their children, while the
owner prime divides the child LCM and, by squarefreeness, divides neither
stripped parent and hence not their LCM. -/
theorem squarefreePairFreshPrimeParent_lcm_lt
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (hmn : m ≠ n) (hmpos : 0 < m) (hnpos : 0 < n) :
    let p := squarefreePairFreshPrimeOwner m n
    Nat.lcm (squarefreePrimeFamilyParent p m)
        (squarefreePrimeFamilyParent p n) < Nat.lcm m n := by
  let p := squarefreePairFreshPrimeOwner m n
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hm hn hmn
  have humdvd : um ∣ m := by
    dsimp [um]
    exact lcmBoundary_squarefreePrimeFamilyParent_dvd p m
  have hundvd : un ∣ n := by
    dsimp [un]
    exact lcmBoundary_squarefreePrimeFamilyParent_dvd p n
  have hparentDvd : Nat.lcm um un ∣ Nat.lcm m n :=
    Nat.lcm_dvd
      (humdvd.trans (Nat.dvd_lcm_left m n))
      (hundvd.trans (Nat.dvd_lcm_right m n))
  have hpChild : p ∣ Nat.lcm m n := by
    apply (hp.dvd_lcm).2
    rcases squarefreePairFreshPrimeOwner_dvd_xor hm hn hmn hmpos hnpos with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hpUm : ¬ p ∣ um := by
    dsimp [um]
    exact squarefreePrimeFamilyParent_not_dvd hp hm
  have hpUn : ¬ p ∣ un := by
    dsimp [un]
    exact squarefreePrimeFamilyParent_not_dvd hp hn
  have hpParent : ¬ p ∣ Nat.lcm um un :=
    hp.not_dvd_lcm hpUm hpUn
  have hne : Nat.lcm um un ≠ Nat.lcm m n := by
    intro heq
    apply hpParent
    rw [heq]
    exact hpChild
  have hchildPos : 0 < Nat.lcm m n := Nat.lcm_pos hmpos hnpos
  exact Nat.lt_of_dvd_of_ne hchildPos hparentDvd hne

/-- Reorienting the stripped endpoints does not change their LCM, so the exact
ordered owner-parent used by the #593 descent also lowers LCM strictly. -/
theorem squarefreePairFreshPrimeOrderedParent_lcm_lt
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (hmn : m ≠ n) (hmpos : 0 < m) (hnpos : 0 < n) :
    Nat.lcm (squarefreePairFreshPrimeOrderedParent m n).1
        (squarefreePairFreshPrimeOrderedParent m n).2 < Nat.lcm m n := by
  let p := squarefreePairFreshPrimeOwner m n
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  have hlt := squarefreePairFreshPrimeParent_lcm_lt hm hn hmn hmpos hnpos
  dsimp only at hlt
  unfold squarefreePairFreshPrimeOrderedParent
  dsimp only
  by_cases h : um < un
  · rw [if_pos h]
    simpa [p, um, un] using hlt
  · rw [if_neg h]
    simpa [p, um, un, Nat.lcm_comm] using hlt

/-- **Boundary descent / first-crossing dichotomy.**  Every nonzero recursive
post-root boundary pair strips to the same remainder carrier with opposite
weight and strictly smaller LCM.  It either remains above the LCM wall, or the
ordered parent is the first step at or below that wall. -/
theorem postRootCovarianceRemainderBoundary_recursive_owner_lcm_descent
    {W m n : ℕ}
    (hboundary : (m, n) ∈ postRootCovarianceRemainderBoundaryLcmCarrier W)
    (hrecursive : (m, n) ∈ postRootCovarianceRemainderRecursivePairCarrier W)
    (hweight : realMoebiusStep m * realMoebiusStep n ≠ 0) :
    let parent := squarefreePairFreshPrimeOrderedParent m n
    parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W ∧
      Nat.lcm parent.1 parent.2 < Nat.lcm m n ∧
      (W < Nat.lcm parent.1 parent.2 ∨
        Nat.lcm parent.1 parent.2 ≤ W) ∧
      realMoebiusStep m * realMoebiusStep n =
        -(realMoebiusStep parent.1 * realMoebiusStep parent.2) := by
  let parent := squarefreePairFreshPrimeOrderedParent m n
  have hdesc := postRootCovarianceRemainderRecursivePair_owner_descent
    hrecursive hweight
  have hm0 : realMoebiusStep m ≠ 0 := by
    intro hmz
    exact hweight (by rw [hmz, zero_mul])
  have hn0 : realMoebiusStep n ≠ 0 := by
    intro hnz
    exact hweight (by rw [hnz, mul_zero])
  have hm : Squarefree m := squarefree_of_realMoebiusStep_ne_zero hm0
  have hn : Squarefree n := squarefree_of_realMoebiusStep_ne_zero hn0
  have hphysical :=
    (mem_postRootCovarianceRemainderBoundaryLcmCarrier.mp hboundary).1
  have hbase :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hphysical).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hbase with
    ⟨hm1, _hmW, hn1, _hnW, hmnlt⟩
  have hlcm := squarefreePairFreshPrimeOrderedParent_lcm_lt
    hm hn (Nat.ne_of_lt hmnlt) (by omega) (by omega)
  dsimp only [parent]
  refine ⟨hdesc.1, hlcm, ?_, hdesc.2.2.2⟩
  omega

end RHLean.Proof
