import Mathlib
import «research.CANONICAL_ROUGH_Q2_TAIL_REDUCTION»
import RHLean.Proof.EndpointCubeAnalyticClosure
import RHLean.Analysis.PrimeWheelRunOthelloBoundary

/-!
# q² daughter energy in first-separation Gram currency

The linear q² reassembly already identifies each daughter amplitude with the
literal Mertens value at

  Y_q = floor((R^2 - 1) / q^2).

For the remaining signed Stokes/covariance problem we need the corresponding
bilinear object before any square is estimated.  This file performs only that
currency conversion.

Every off-diagonal Möbius pair below Y_q is assigned to its unique
chronological fresh-prime owner.  Summing those owner fibres gives the literal
positive-lag covariance at Y_q.  The classical Green--Kubo identity then yields

  M(Y_q)^2 = diagonal(Y_q) + 2 * sum_p Gram(q,p).

Thus the entire first-owner daughter Gram is already paid by the genuine q²
Mertens daughter energy, with no ownerwise norm, support count, or independence
assumption.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Off-diagonal Möbius covariance of one q² daughter carried by one unique
fresh-prime owner. -/
def lowOwnerQ2DaughterFirstOwnerGram (R q p : ℕ) : ℝ :=
  let Y := rawQ2ChildCutoff R q
  ∑ n ∈ Finset.range (Y + 1),
    ∑ m ∈ Finset.range n,
      if IsSquarefreePairFreshPrimeOwner p m n then
        realMoebiusStep m * realMoebiusStep n
      else 0

/-- **Arbitrary-cutoff first-owner Fubini.**

At the literal daughter cutoff, summing the unique fresh-prime owner fibres is
exactly the full positive-lag Möbius covariance. -/
theorem sum_lowOwnerQ2DaughterFirstOwnerGram_eq_positiveLag
    (R q : ℕ) :
    (∑ p ∈ primesUpTo (rawQ2ChildCutoff R q),
      lowOwnerQ2DaughterFirstOwnerGram R q p) =
      realMertensPositiveLagPairSum (rawQ2ChildCutoff R q + 1) := by
  let Y := rawQ2ChildCutoff R q
  have hpair :
      (∑ n ∈ Finset.range (Y + 1),
        ∑ m ∈ Finset.range n,
          realMoebiusStep m * realMoebiusStep n) =
      ∑ n ∈ Finset.range (Y + 1),
        ∑ m ∈ Finset.range n,
          squarefreePairFreshPrimeOwnerExpansion Y m n := by
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    have hmn : m < n := Finset.mem_range.mp hm
    have hnY : n ≤ Y := by
      have hnlt : n < Y + 1 := Finset.mem_range.mp hn
      omega
    rw [squarefreePairFreshPrimeOwnerExpansion_eq_pairWeight hmn hnY]
  rw [realMertensPositiveLagPairSum_eq_doubleSum]
  change
    (∑ p ∈ primesUpTo Y,
      ∑ n ∈ Finset.range (Y + 1),
        ∑ m ∈ Finset.range n,
          if IsSquarefreePairFreshPrimeOwner p m n then
            realMoebiusStep m * realMoebiusStep n
          else 0) =
      ∑ n ∈ Finset.range (Y + 1),
        ∑ m ∈ Finset.range n,
          realMoebiusStep m * realMoebiusStep n
  rw [hpair]
  unfold squarefreePairFreshPrimeOwnerExpansion
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.sum_comm]
  rfl

private theorem rawQ2ChildEnergyReal_eq_realMertensLength_sq
    (R q : ℕ) :
    rawQ2ChildEnergyReal R q =
      realMertensLength (rawQ2ChildCutoff R q + 1) ^ 2 := by
  let Y := rawQ2ChildCutoff R q
  have hInt :
      ‖RHLean.Analysis.mertensSummatory Y‖ ^ 2 =
        ((mertensSummatoryInt Y : ℤ) : ℝ) ^ 2 := by
    rw [← mertensSummatoryInt_cast Y, Complex.norm_intCast]
    exact sq_abs (((mertensSummatoryInt Y : ℤ) : ℝ))
  have hReal :=
    norm_mertensSummatory_sq_eq_realMertensLength_sq Y
  unfold rawQ2ChildEnergyReal
  change
    ((mertensSummatoryInt Y : ℤ) : ℝ) ^ 2 =
      realMertensLength (Y + 1) ^ 2
  calc
    ((mertensSummatoryInt Y : ℤ) : ℝ) ^ 2 =
        ‖RHLean.Analysis.mertensSummatory Y‖ ^ 2 := hInt.symm
    _ = realMertensLength (Y + 1) ^ 2 := hReal

/-- **Exact daughter Green--Kubo / first-owner decomposition.**

This is the desired bilinear q² currency: no square of a signature sum is
introduced. -/
theorem rawQ2ChildEnergyReal_eq_diagonal_add_two_firstOwnerGram
    (R q : ℕ) :
    rawQ2ChildEnergyReal R q =
      realMertensDiagonal (rawQ2ChildCutoff R q + 1) +
        2 * (∑ p ∈ primesUpTo (rawQ2ChildCutoff R q),
          lowOwnerQ2DaughterFirstOwnerGram R q p) := by
  rw [rawQ2ChildEnergyReal_eq_realMertensLength_sq]
  rw [realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum]
  rw [sum_lowOwnerQ2DaughterFirstOwnerGram_eq_positiveLag]

/-- The signed daughter first-owner Gram costs at most the literal daughter
energy; the omitted squarefree diagonal is nonnegative and therefore helps. -/
theorem two_mul_sum_lowOwnerQ2DaughterFirstOwnerGram_le_childEnergy
    (R q : ℕ) :
    2 * (∑ p ∈ primesUpTo (rawQ2ChildCutoff R q),
      lowOwnerQ2DaughterFirstOwnerGram R q p) ≤
        rawQ2ChildEnergyReal R q := by
  rw [rawQ2ChildEnergyReal_eq_diagonal_add_two_firstOwnerGram]
  have hdiag :
      0 ≤ realMertensDiagonal (rawQ2ChildCutoff R q + 1) :=
    realMertensDiagonal_nonneg _
  linarith

/-- Global low-q² off-diagonal daughter Gram, retaining the unique chronological
first owner inside each genuine Mertens daughter. -/
def lowOwnerQ2DaughterFirstOwnerGramEnergy (R : ℕ) : ℝ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    2 * (∑ p ∈ primesUpTo (rawQ2ChildCutoff R q),
      lowOwnerQ2DaughterFirstOwnerGram R q p)

/-- **Global bilinear q² budget.**

The exact first-separation daughter Gram is already dominated by the recursive
Mertens energy used by the existing CORR-4 consumer. -/
theorem lowOwnerQ2DaughterFirstOwnerGramEnergy_le_lowQ2DaughterEnergy
    (R : ℕ) :
    lowOwnerQ2DaughterFirstOwnerGramEnergy R ≤
      canonicalRoughLowQ2DaughterEnergy R := by
  unfold lowOwnerQ2DaughterFirstOwnerGramEnergy
    canonicalRoughLowQ2DaughterEnergy
  apply Finset.sum_le_sum
  intro q _hq
  exact two_mul_sum_lowOwnerQ2DaughterFirstOwnerGram_le_childEnergy R q

/-- Exact global decomposition: the recursive q² Mertens energy is its
squarefree daughter diagonal plus the bilinear first-owner Gram. -/
theorem canonicalRoughLowQ2DaughterEnergy_eq_diagonal_add_firstOwnerGram
    (R : ℕ) :
    canonicalRoughLowQ2DaughterEnergy R =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        realMertensDiagonal (rawQ2ChildCutoff R q + 1)) +
      lowOwnerQ2DaughterFirstOwnerGramEnergy R := by
  unfold canonicalRoughLowQ2DaughterEnergy
    lowOwnerQ2DaughterFirstOwnerGramEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  exact rawQ2ChildEnergyReal_eq_diagonal_add_two_firstOwnerGram R q

end RHLean.Proof
