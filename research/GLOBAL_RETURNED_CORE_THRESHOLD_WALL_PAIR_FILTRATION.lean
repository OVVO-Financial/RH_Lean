import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_MERTENS_WALL_ZERO_TARGET_GRAM»
import «research.GLOBAL_RETURNED_CORE_ARBITRARY_PRIME_FILTRATION»
import «research.GLOBAL_RETURNED_CORE_DESCENDING_PAIR_OWNER»

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


/-- Diagonal wall pairs, used to identify the fully revealed endpoint. -/
def lowOwnerThresholdWallDiagonalPairCarrier
    (p y : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerThresholdMertensCrossingCarrier p y).image (fun n => (n, n))

/-- Every diagonal wall pair survives every revealed coordinate set. -/
theorem lowOwnerThresholdWallDiagonalPairCarrier_subset_revealed
    (p y : ℕ) (S : Finset ℕ) :
    lowOwnerThresholdWallDiagonalPairCarrier p y ⊆
      lowOwnerThresholdWallRevealedPairCarrier p y S := by
  intro mn hmn
  rcases Finset.mem_image.mp hmn with ⟨n, hn, rfl⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hn, hn⟩, rfl⟩

/-- After all primes up to the wall cutoff have been revealed, every
off-diagonal surviving pair has zero Mobius weight. -/
theorem lowOwnerThresholdWall_fullReveal_offDiagonal_zero
    {p y : ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈
      lowOwnerThresholdWallRevealedPairCarrier p y (primesUpTo y))
    (hne : mn.1 ≠ mn.2) :
    realMoebiusStep mn.1 * realMoebiusStep mn.2 = 0 := by
  rcases mn with ⟨m, n⟩
  by_contra hnon
  have hm0 : realMoebiusStep m ≠ 0 := by
    intro hm
    exact hnon (by rw [hm, zero_mul])
  have hn0 : realMoebiusStep n ≠ 0 := by
    intro hn
    exact hnon (by rw [hn, mul_zero])
  have hmsq : Squarefree m := squarefree_of_realMoebiusStep_ne_zero hm0
  have hnsq : Squarefree n := squarefree_of_realMoebiusStep_ne_zero hn0
  rcases Finset.mem_filter.mp hmn with ⟨hprod, hsig⟩
  rcases Finset.mem_product.mp hprod with ⟨hmWall, hnWall⟩
  have hmIcc := (Finset.mem_filter.mp hmWall).1
  have hnIcc := (Finset.mem_filter.mp hnWall).1
  have hmLe : m ≤ y := (Finset.mem_Icc.mp hmIcc).2
  have hnLe : n ≤ y := (Finset.mem_Icc.mp hnIcc).2
  have hmSig :
      lowOwnerRevealedPrimeSignature (primesUpTo y) m =
        squarefreePrimeFace m := by
    unfold lowOwnerRevealedPrimeSignature
    exact Finset.inter_eq_left.mpr
      (squarefreePrimeFace_subset_primesUpTo hmsq hmLe)
  have hnSig :
      lowOwnerRevealedPrimeSignature (primesUpTo y) n =
        squarefreePrimeFace n := by
    unfold lowOwnerRevealedPrimeSignature
    exact Finset.inter_eq_left.mpr
      (squarefreePrimeFace_subset_primesUpTo hnsq hnLe)
  rw [hmSig, hnSig] at hsig
  have hmnEq : m = n := by
    calc
      m = primeFaceProduct (squarefreePrimeFace m) :=
        (primeFaceProduct_squarefreePrimeFace hmsq).symm
      _ = primeFaceProduct (squarefreePrimeFace n) := by rw [hsig]
      _ = n := primeFaceProduct_squarefreePrimeFace hnsq
  exact hne hmnEq

/-- Sum on the diagonal pair carrier is the literal squarefree diagonal. -/
theorem sum_lowOwnerThresholdWallDiagonalPairCarrier_eq
    (p y : ℕ) :
    (∑ mn ∈ lowOwnerThresholdWallDiagonalPairCarrier p y,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      ∑ n ∈ lowOwnerThresholdMertensCrossingCarrier p y,
        realMoebiusStep n ^ 2 := by
  unfold lowOwnerThresholdWallDiagonalPairCarrier
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _hn
    ring
  · intro a _ha b _hb hab
    exact congrArg Prod.fst hab

/-- **Fully revealed wall energy is exactly diagonal.**

Thus every off-diagonal contribution of one threshold Mertens wall is exhausted
by the fresh-prime crossing packets; no positive off-diagonal terminal remains. -/
theorem lowOwnerThresholdWallRevealedPairEnergy_full_eq_diagonal
    (p y : ℕ) :
    lowOwnerThresholdWallRevealedPairEnergy p y (primesUpTo y) =
      ∑ n ∈ lowOwnerThresholdMertensCrossingCarrier p y,
        realMoebiusStep n ^ 2 := by
  let D := lowOwnerThresholdWallDiagonalPairCarrier p y
  let P := lowOwnerThresholdWallRevealedPairCarrier p y (primesUpTo y)
  have hsub : D ⊆ P := by
    exact lowOwnerThresholdWallDiagonalPairCarrier_subset_revealed
      p y (primesUpTo y)
  have hzero :
      ∀ mn ∈ P, mn ∉ D →
        realMoebiusStep mn.1 * realMoebiusStep mn.2 = 0 := by
    intro mn hmn hnot
    have hne : mn.1 ≠ mn.2 := by
      intro heq
      apply hnot
      rcases mn with ⟨m, n⟩
      dsimp only at heq ⊢
      subst n
      have hprod := (Finset.mem_filter.mp hmn).1
      have hmWall := (Finset.mem_product.mp hprod).1
      exact Finset.mem_image.mpr ⟨m, hmWall, rfl⟩
    exact lowOwnerThresholdWall_fullReveal_offDiagonal_zero hmn hne
  have hs :
      (∑ mn ∈ D,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      ∑ mn ∈ P,
        realMoebiusStep mn.1 * realMoebiusStep mn.2 :=
    Finset.sum_subset hsub hzero
  unfold lowOwnerThresholdWallRevealedPairEnergy
  change (∑ mn ∈ P,
    realMoebiusStep mn.1 * realMoebiusStep mn.2) = _
  rw [← hs]
  simpa [D] using
    sum_lowOwnerThresholdWallDiagonalPairCarrier_eq p y


/-! ## Descending chronology interface -/

/-- The threshold-wall filtration can be run on the *same* descending revealed
state as the raw-parent/Stokes chronology.  This is deliberately parameterized
by the root clock `R`, even when the wall cutoff is a lower q^2 daughter
endpoint, so the two carrier descriptions use literally the same state. -/
theorem lowOwnerThresholdWallRevealedPairEnergy_descending_step
    {R p y r : ℕ} (hr : r.Prime) :
    lowOwnerThresholdWallRevealedPairEnergy p y
        (lowOwnerRevealedPrimesAbove R r) =
      lowOwnerThresholdWallRevealedPairEnergy p y
          (insert r (lowOwnerRevealedPrimesAbove R r)) +
        lowOwnerThresholdWallRevealedCrossPairMass p y
          (lowOwnerRevealedPrimesAbove R r) r := by
  exact lowOwnerThresholdWallRevealedPairEnergy_eq_insert_add_cross
    hr (owner_not_mem_lowOwnerRevealedPrimesAbove R r)

/-- Difference form of the same descending step.  This is the form that can be
summed through the raw-parent owner chronology without an ownerwise norm: the
current signed wall crossing is exactly the drop in the surviving wall energy. -/
theorem lowOwnerThresholdWallRevealedCrossPairMass_descending_eq_energyDrop
    {R p y r : ℕ} (hr : r.Prime) :
    lowOwnerThresholdWallRevealedCrossPairMass p y
        (lowOwnerRevealedPrimesAbove R r) r =
      lowOwnerThresholdWallRevealedPairEnergy p y
          (lowOwnerRevealedPrimesAbove R r) -
        lowOwnerThresholdWallRevealedPairEnergy p y
          (insert r (lowOwnerRevealedPrimesAbove R r)) := by
  have h :=
    lowOwnerThresholdWallRevealedPairEnergy_descending_step
      (R := R) (p := p) (y := y) hr
  linarith

/-- q^2-daughter specialization in the exact root-clock chronology used by the
Stokes descent.  No estimate occurs here. -/
theorem lowOwnerQ2ThresholdWallRevealedPairEnergy_descending_step
    {R q p r : ℕ} (hr : r.Prime) :
    lowOwnerThresholdWallRevealedPairEnergy p (rawQ2ChildCutoff R q)
        (lowOwnerRevealedPrimesAbove R r) =
      lowOwnerThresholdWallRevealedPairEnergy p (rawQ2ChildCutoff R q)
          (insert r (lowOwnerRevealedPrimesAbove R r)) +
        lowOwnerThresholdWallRevealedCrossPairMass p
          (rawQ2ChildCutoff R q) (lowOwnerRevealedPrimesAbove R r) r := by
  exact lowOwnerThresholdWallRevealedPairEnergy_descending_step
    (R := R) (p := p) (y := rawQ2ChildCutoff R q) hr


end RHLean.Proof
