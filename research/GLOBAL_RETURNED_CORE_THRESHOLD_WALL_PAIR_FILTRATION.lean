import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_MERTENS_WALL_ZERO_TARGET_GRAM»
import «research.GLOBAL_RETURNED_CORE_ARBITRARY_PRIME_FILTRATION»

/-!
# Prime-signature filtration on one threshold Mertens wall

For a prime wall owner `p` and cutoff `y`, the physical threshold wall

  W(p,y) = { n : 1 <= n <= y, p ∤ n, y < p*n }

already has signed Mobius mass `M(y)`.  This file puts the repository's
order-independent revealed-prime filtration directly on that finite wall.

At the empty revealed set the ordered wall-pair energy is exactly the target-zero
wall Gram, hence exactly `M(y)^2`.  Revealing a fresh prime `r` splits that
energy *exactly* into same-branch continuation plus the signed r-crossing packet.

This is the missing bookkeeping bridge needed to let the descending raw-parent
chronology spend one literal daughter wall energy once, instead of estimating
one norm per owner.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Ordered wall pairs indistinguishable on the revealed prime set. -/
def lowOwnerThresholdWallRevealedPairCarrier
    (p y : ℕ) (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerThresholdMertensCrossingCarrier p y).product
      (lowOwnerThresholdMertensCrossingCarrier p y)).filter fun mn =>
    lowOwnerRevealedPrimeSignature S mn.1 =
      lowOwnerRevealedPrimeSignature S mn.2

/-- Wall pairs which still agree after revealing the fresh coordinate `r`. -/
def lowOwnerThresholdWallRevealedSameBranchPairCarrier
    (p y : ℕ) (S : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerThresholdMertensCrossingCarrier p y).product
      (lowOwnerThresholdMertensCrossingCarrier p y)).filter fun mn =>
    lowOwnerRevealedPrimeSignature S mn.1 =
        lowOwnerRevealedPrimeSignature S mn.2 ∧
      (r ∣ mn.1 ↔ r ∣ mn.2)

/-- Wall pairs separated for the first time by the fresh coordinate `r`. -/
def lowOwnerThresholdWallRevealedCrossPairCarrier
    (p y : ℕ) (S : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerThresholdMertensCrossingCarrier p y).product
      (lowOwnerThresholdMertensCrossingCarrier p y)).filter fun mn =>
    lowOwnerRevealedPrimeSignature S mn.1 =
        lowOwnerRevealedPrimeSignature S mn.2 ∧
      ((r ∣ mn.1 ∧ ¬ r ∣ mn.2) ∨ (r ∣ mn.2 ∧ ¬ r ∣ mn.1))

/-- Signed ordered pair energy of the threshold wall at one revealed state. -/
def lowOwnerThresholdWallRevealedPairEnergy
    (p y : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ mn ∈ lowOwnerThresholdWallRevealedPairCarrier p y S,
    realMoebiusStep mn.1 * realMoebiusStep mn.2

/-- Signed wall-pair mass exposed by revealing one fresh prime. -/
def lowOwnerThresholdWallRevealedCrossPairMass
    (p y : ℕ) (S : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ mn ∈ lowOwnerThresholdWallRevealedCrossPairCarrier p y S r,
    realMoebiusStep mn.1 * realMoebiusStep mn.2

private theorem thresholdWall_mem_pos
    {p y n : ℕ}
    (hn : n ∈ lowOwnerThresholdMertensCrossingCarrier p y) :
    0 < n := by
  have hIcc := (Finset.mem_filter.mp hn).1
  have h1 := (Finset.mem_Icc.mp hIcc).1
  omega

/-- Revealing a fresh prime turns the old wall carrier into its same-branch
part exactly. -/
theorem lowOwnerThresholdWallRevealedPairCarrier_insert_eq_sameBranch
    {p y : ℕ} {S : Finset ℕ} {r : ℕ}
    (hr : r.Prime) (hrS : r ∉ S) :
    lowOwnerThresholdWallRevealedPairCarrier p y (insert r S) =
      lowOwnerThresholdWallRevealedSameBranchPairCarrier p y S r := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hprod, hsig⟩
    rcases Finset.mem_product.mp hprod with ⟨hmWall, hnWall⟩
    have hmPos := thresholdWall_mem_pos hmWall
    have hnPos := thresholdWall_mem_pos hnWall
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmWall, hnWall⟩,
        (lowOwnerRevealedPrimeSignature_insert_eq_iff
          hr hrS hmPos hnPos).1 hsig⟩
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hprod, hdata⟩
    rcases Finset.mem_product.mp hprod with ⟨hmWall, hnWall⟩
    have hmPos := thresholdWall_mem_pos hmWall
    have hnPos := thresholdWall_mem_pos hnWall
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmWall, hnWall⟩,
        (lowOwnerRevealedPrimeSignature_insert_eq_iff
          hr hrS hmPos hnPos).2 hdata⟩

/-- The same-branch and newly-separated wall packets are disjoint. -/
theorem lowOwnerThresholdWallRevealedSameBranch_disjoint_cross
    (p y : ℕ) (S : Finset ℕ) (r : ℕ) :
    Disjoint
      (lowOwnerThresholdWallRevealedSameBranchPairCarrier p y S r)
      (lowOwnerThresholdWallRevealedCrossPairCarrier p y S r) := by
  rw [Finset.disjoint_left]
  intro mn hsame hcross
  have hs := (Finset.mem_filter.mp hsame).2.2
  have hc := (Finset.mem_filter.mp hcross).2.2
  rcases hc with hc | hc
  · exact hc.2 (hs.mp hc.1)
  · exact hc.2 (hs.mpr hc.1)

/-- Before revealing `r`, every wall pair either remains on the same branch
or is separated by `r`. -/
theorem lowOwnerThresholdWallRevealedPairCarrier_eq_sameBranch_union_cross
    (p y : ℕ) (S : Finset ℕ) (r : ℕ) :
    lowOwnerThresholdWallRevealedPairCarrier p y S =
      lowOwnerThresholdWallRevealedSameBranchPairCarrier p y S r ∪
        lowOwnerThresholdWallRevealedCrossPairCarrier p y S r := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hprod, hsig⟩
    by_cases hrm : r ∣ m
    · by_cases hrn : r ∣ n
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr
            ⟨hprod, ⟨hsig, by simp [hrm, hrn]⟩⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨hprod, ⟨hsig, Or.inl ⟨hrm, hrn⟩⟩⟩)
    · by_cases hrn : r ∣ n
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨hprod, ⟨hsig, Or.inr ⟨hrn, hrm⟩⟩⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr
            ⟨hprod, ⟨hsig, by simp [hrm, hrn]⟩⟩)
  · intro hmn
    rcases Finset.mem_union.mp hmn with hsame | hcross
    · rcases Finset.mem_filter.mp hsame with ⟨hprod, hdata⟩
      exact Finset.mem_filter.mpr ⟨hprod, hdata.1⟩
    · rcases Finset.mem_filter.mp hcross with ⟨hprod, hdata⟩
      exact Finset.mem_filter.mpr ⟨hprod, hdata.1⟩

/-- **Exact one-prime wall-energy telescope.** -/
theorem lowOwnerThresholdWallRevealedPairEnergy_eq_insert_add_cross
    {p y : ℕ} {S : Finset ℕ} {r : ℕ}
    (hr : r.Prime) (hrS : r ∉ S) :
    lowOwnerThresholdWallRevealedPairEnergy p y S =
      lowOwnerThresholdWallRevealedPairEnergy p y (insert r S) +
        lowOwnerThresholdWallRevealedCrossPairMass p y S r := by
  unfold lowOwnerThresholdWallRevealedPairEnergy
    lowOwnerThresholdWallRevealedCrossPairMass
  rw [lowOwnerThresholdWallRevealedPairCarrier_eq_sameBranch_union_cross,
    Finset.sum_union
      (lowOwnerThresholdWallRevealedSameBranch_disjoint_cross p y S r),
    lowOwnerThresholdWallRevealedPairCarrier_insert_eq_sameBranch hr hrS]

/-- With no revealed primes, the wall carrier is its full Cartesian square. -/
theorem lowOwnerThresholdWallRevealedPairCarrier_empty
    (p y : ℕ) :
    lowOwnerThresholdWallRevealedPairCarrier p y ∅ =
      (lowOwnerThresholdMertensCrossingCarrier p y).product
        (lowOwnerThresholdMertensCrossingCarrier p y) := by
  simp [lowOwnerThresholdWallRevealedPairCarrier,
    lowOwnerRevealedPrimeSignature]

/-- **The unrevealed wall energy is exactly the target-zero wall Gram.** -/
theorem lowOwnerThresholdWallRevealedPairEnergy_empty_eq_zeroTargetGram
    (p y : ℕ) :
    lowOwnerThresholdWallRevealedPairEnergy p y ∅ =
      lowOwnerThresholdMertensWallZeroTargetGram p y := by
  let W := lowOwnerThresholdMertensCrossingCarrier p y
  have hprod :
      (∑ mn ∈ W.product W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) =
        (∑ n ∈ W, realMoebiusStep n) ^ 2 := by
    calc
      (∑ mn ∈ W.product W,
          realMoebiusStep mn.1 * realMoebiusStep mn.2) =
        ∑ m ∈ W, ∑ n ∈ W,
          realMoebiusStep m * realMoebiusStep n := by
            simpa only using
              (Finset.sum_product
                (s := W) (t := W)
                (f := fun mn : ℕ × ℕ =>
                  realMoebiusStep mn.1 * realMoebiusStep mn.2))
      _ = (∑ m ∈ W, realMoebiusStep m) *
          (∑ n ∈ W, realMoebiusStep n) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro m _hm
            rw [Finset.mul_sum]
      _ = (∑ n ∈ W, realMoebiusStep n) ^ 2 := by ring
  have hgram :
      lowOwnerThresholdMertensWallZeroTargetGram p y =
        (∑ n ∈ W, realMoebiusStep n) ^ 2 := by
    unfold lowOwnerThresholdMertensWallZeroTargetGram
    rw [← zeroTarget_globalGram_reassembly]
  unfold lowOwnerThresholdWallRevealedPairEnergy
  rw [lowOwnerThresholdWallRevealedPairCarrier_empty]
  change
    (∑ mn ∈ W.product W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      lowOwnerThresholdMertensWallZeroTargetGram p y
  rw [hprod, hgram]

/-- At a q^2 daughter cutoff, the unrevealed wall filtration starts from the
literal recursive daughter energy, independently of the exposing wall owner. -/
theorem lowOwnerQ2ThresholdWallRevealedPairEnergy_empty_eq_childEnergy
    {R q p : ℕ} (hp : p.Prime) :
    lowOwnerThresholdWallRevealedPairEnergy
        p (rawQ2ChildCutoff R q) ∅ =
      rawQ2ChildEnergyReal R q := by
  rw [lowOwnerThresholdWallRevealedPairEnergy_empty_eq_zeroTargetGram]
  exact lowOwnerQ2ThresholdWallZeroTargetGram_eq_childEnergy hp

end RHLean.Proof
