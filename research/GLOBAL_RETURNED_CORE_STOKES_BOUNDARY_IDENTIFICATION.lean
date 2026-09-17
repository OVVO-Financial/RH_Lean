import Mathlib
import «research.GLOBAL_RETURNED_CORE_CANONICAL_SIGNED_STOKES»
import «research.GLOBAL_RETURNED_CORE_POLARIZATION_UNIQUE_OWNER_FUBINI»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_INCIDENCE_KERNEL»

/-!
# Physical identification of the signed Stokes boundary

This file remains entirely before every positive-energy gate.

The generic weighted Othello/Stokes theorem books two escape faces at one pair
coordinate.  On a product carrier those faces are exactly products of the
one-dimensional Othello escape/interior sets.  For the actual first-owner base
fibre and every larger prime `r`, the one-dimensional escape set has a literal
physical description:

  n is in the cell, r does not divide n, and X_R < r*n.

Thus the first escape face is not a new error population: it is precisely the
Dirichlet clock clip of the fresh `r` edge.  Equivalently the endpoint threshold
crossing at `X_R` is active.  The signs and the scalar weights are unchanged.

The product-factorization lemmas are stated for arbitrary finite carriers so
that the same exact bookkeeping can be iterated.  No norm, square, Carleson,
Schur, inherited-energy, `2/9`, or `4/9` statement is imported or used.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Literal Dirichlet clip face of a larger fresh owner on one p-free base
cell.  The edge starts on the physical clock and its r-child leaves it. -/
def lowOwnerFirstOwnerStokesDirichletClipFace
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (lowOwnerFirstOwnerBaseFiber R p sig).filter fun n =>
    ¬ r ∣ n ∧ squareRootEndpoint R < r * n

@[simp] theorem mem_lowOwnerFirstOwnerStokesDirichletClipFace
    {R p r n : ℕ} {sig : Finset ℕ} :
    n ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig r ↔
      n ∈ lowOwnerFirstOwnerBaseFiber R p sig ∧
        ¬ r ∣ n ∧ squareRootEndpoint R < r * n :=
  Finset.mem_filter

/-- Multiplying a p-free cell site by a fresh larger prime stays in the same
cell whenever the new site remains on the physical clock. -/
theorem lowOwnerFirstOwner_mul_larger_prime_mem_same_base_of_le
    {R p r n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hrn : ¬ r ∣ n)
    (hn : n ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hupper : r * n ≤ squareRootEndpoint R) :
    r * n ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
  rcases Finset.mem_filter.mp hn with ⟨hnCar, hnData⟩
  rcases Finset.mem_filter.mp hnCar with ⟨hnIcc, hmuN⟩
  have hnPos : 0 < n := by
    omega
  have hrnPos : 0 < r * n := Nat.mul_pos hr.pos hnPos
  have hmuRN : realMoebiusStep (r * n) ≠ 0 := by
    rw [realMoebiusStep_mul_prime_eq_neg hr hrn]
    exact neg_ne_zero.mpr hmuN
  have hrnCar : r * n ∈ lowOwnerNonzeroMobiusCarrier R := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hupper⟩, hmuRN⟩
  have hsig : squarefreeLowerPrimeSignature p (r * n) = sig := by
    rw [squarefreeLowerPrimeSignature_mul_larger_prime hr hpr hnPos, hnData.1]
  have hpnotr : ¬ p ∣ r := by
    intro hdiv
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hdiv
    omega
  have hpfree : ¬ p ∣ r * n := by
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with h | h
    · exact hpnotr h
    · exact hnData.2 h
  exact Finset.mem_filter.mpr ⟨hrnCar, ⟨hsig, hpfree⟩⟩

/-- On the squarefree first-owner base fibre, stripping a present larger prime
is exactly the Othello mate and remains in the same cell. -/
theorem lowOwnerFirstOwner_toggle_of_dvd_mem_same_base
    {R p r n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hn : n ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hrn : r ∣ n) :
    primeCarrierToggle r n ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
  have hnCar := (Finset.mem_filter.mp hn).1
  have hnSq := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).1
  have hrsq : ¬ r ^ 2 ∣ n := by
    intro hsq
    exact (Nat.squarefree_iff_prime_squarefree.mp hnSq r hr)
      (by simpa [pow_two] using hsq)
  have hparent := lowOwnerFirstOwner_primeParent_mem_same_base hp hr hpr hn
  have hparentEq : squarefreePrimeFamilyParent r n = n / r := by
    simp [squarefreePrimeFamilyParent, hrn]
  rw [primeCarrierToggle_of_dvd hrn hrsq]
  simpa [hparentEq] using hparent

/-- **No hidden one-dimensional escape class at the base cell.**

For a larger prime `r`, the Othello escape set is exactly the fresh r-edge whose
child crosses the physical Dirichlet endpoint.  A present r-factor always strips
back into the same base cell, and a missing r-factor stays in the same cell
whenever `r*n <= X_R`. -/
theorem lowOwnerFirstOwner_primeEscapePart_eq_dirichletClipFace
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    primeEscapePart r (lowOwnerFirstOwnerBaseFiber R p sig) =
      lowOwnerFirstOwnerStokesDirichletClipFace R p sig r := by
  ext n
  constructor
  · intro hesc
    rcases mem_primeEscapePart.mp hesc with ⟨hn, hout⟩
    by_cases hrn : r ∣ n
    · exact False.elim
        (hout (lowOwnerFirstOwner_toggle_of_dvd_mem_same_base
          hp hr hpr hn hrn))
    · have hclip : squareRootEndpoint R < r * n := by
        by_contra hnot
        have hle : r * n ≤ squareRootEndpoint R := Nat.le_of_not_gt hnot
        have hmul := lowOwnerFirstOwner_mul_larger_prime_mem_same_base_of_le
          hp hr hpr hrn hn hle
        apply hout
        rw [primeCarrierToggle_of_not_dvd hrn]
        simpa [Nat.mul_comm] using hmul
      exact mem_lowOwnerFirstOwnerStokesDirichletClipFace.mpr
        ⟨hn, hrn, hclip⟩
  · intro hclip
    rcases mem_lowOwnerFirstOwnerStokesDirichletClipFace.mp hclip with
      ⟨hn, hrn, hupper⟩
    apply mem_primeEscapePart.mpr
    refine ⟨hn, ?_⟩
    rw [primeCarrierToggle_of_not_dvd hrn]
    intro hmate
    have hcar := (Finset.mem_filter.mp hmate).1
    have hIcc := (Finset.mem_filter.mp hcar).1
    have hle : n * r ≤ squareRootEndpoint R := (Finset.mem_Icc.mp hIcc).2
    have : r * n ≤ squareRootEndpoint R := by simpa [Nat.mul_comm] using hle
    omega

/-- The same physical clip is exactly the endpoint threshold crossing of the
fresh `r` edge. -/
theorem lowOwnerFirstOwner_dirichletClipFace_thresholdCrossing_eq_one
    {R p r n : ℕ} {sig : Finset ℕ}
    (hn : n ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig r) :
    lowOwnerThresholdCrossingIndicator r n (squareRootEndpoint R) = 1 := by
  rcases mem_lowOwnerFirstOwnerStokesDirichletClipFace.mp hn with
    ⟨hbase, _hrn, hclip⟩
  have hcar := (Finset.mem_filter.mp hbase).1
  have hIcc := (Finset.mem_filter.mp hcar).1
  unfold lowOwnerThresholdCrossingIndicator
  simp [Finset.mem_Icc.mp hIcc |>.2, hclip]

/-! ## Exact product-carrier factorization of pair escape faces -/

/-- Left pair escape on a product carrier is exactly one one-dimensional escape
face times the untouched right carrier. -/
theorem pairPrimeLeftEscapePart_product
    (r : ℕ) (A B : Finset ℕ) :
    pairPrimeLeftEscapePart r (A.product B) =
      (primeEscapePart r A).product B := by
  ext mn
  rcases mn with ⟨a, b⟩
  simp [pairPrimeLeftEscapePart, weightedOthelloEscapePart,
    pairPrimeCarrierToggleLeft, primeEscapePart]

/-- Left pair interior factors coordinatewise on a product carrier. -/
theorem pairPrimeLeftInteriorPart_product
    (r : ℕ) (A B : Finset ℕ) :
    pairPrimeLeftInteriorPart r (A.product B) =
      (primeInteriorPart r A).product B := by
  ext mn
  rcases mn with ⟨a, b⟩
  simp [pairPrimeLeftInteriorPart, weightedOthelloInteriorPart,
    pairPrimeCarrierToggleLeft, primeInteriorPart]

/-- After the left coordinate is paired, the right escape face is the left
interior times the one-dimensional right escape face. -/
theorem pairPrimeRightEscapeAfterLeft_product
    (r : ℕ) (A B : Finset ℕ) :
    pairPrimeRightEscapeAfterLeft r (A.product B) =
      (primeInteriorPart r A).product (primeEscapePart r B) := by
  ext mn
  rcases mn with ⟨a, b⟩
  simp [pairPrimeRightEscapeAfterLeft, pairPrimeLeftInteriorPart,
    weightedOthelloEscapePart, weightedOthelloInteriorPart,
    pairPrimeCarrierToggleLeft, pairPrimeCarrierToggleRight,
    primeEscapePart, primeInteriorPart]

/-- The complete two-coordinate interior is the product of the two
one-dimensional interiors. -/
theorem pairPrimeTwoCoordinateInterior_product
    (r : ℕ) (A B : Finset ℕ) :
    pairPrimeTwoCoordinateInterior r (A.product B) =
      (primeInteriorPart r A).product (primeInteriorPart r B) := by
  ext mn
  rcases mn with ⟨a, b⟩
  simp [pairPrimeTwoCoordinateInterior, pairPrimeLeftInteriorPart,
    weightedOthelloInteriorPart, pairPrimeCarrierToggleLeft,
    pairPrimeCarrierToggleRight, primeInteriorPart]

/-- Specialized left Stokes face: same sites and same signs, now on the named
Dirichlet clip carrier. -/
theorem lowOwnerFirstOwner_pairLeftEscape_eq_dirichletClip_product
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    pairPrimeLeftEscapePart r
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig) =
      (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r).product
        (lowOwnerFirstOwnerBaseFiber R p sig) := by
  unfold lowOwnerFirstOwnerSignedCellPairCarrier
  rw [pairPrimeLeftEscapePart_product,
    lowOwnerFirstOwner_primeEscapePart_eq_dirichletClipFace hp hr hpr]

/-- Specialized right Stokes face after left pairing. -/
theorem lowOwnerFirstOwner_pairRightEscape_eq_interior_product_dirichletClip
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    pairPrimeRightEscapeAfterLeft r
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig) =
      (primeInteriorPart r (lowOwnerFirstOwnerBaseFiber R p sig)).product
        (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r) := by
  unfold lowOwnerFirstOwnerSignedCellPairCarrier
  rw [pairPrimeRightEscapeAfterLeft_product,
    lowOwnerFirstOwner_primeEscapePart_eq_dirichletClipFace hp hr hpr]

/-- The first Stokes boundary step on an actual signed cell is literally the two
Dirichlet clip faces, with the generic Othello signs and scalar weights left
unchanged.  This is an identity, not a bound. -/
theorem lowOwnerFirstOwner_pairBoundaryStep_eq_dirichletClipFaces
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (f : ℕ × ℕ → ℝ) :
    pairWeightedStokesBoundaryStep r
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig) f =
      (∑ mn ∈
          (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r).product
            (lowOwnerFirstOwnerBaseFiber R p sig),
          othelloRealMoebiusPair mn * f mn) +
        (1 / 2 : ℝ) *
          ∑ mn ∈
            (primeInteriorPart r
              (lowOwnerFirstOwnerBaseFiber R p sig)).product
              (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r),
            othelloRealMoebiusPair mn *
              (f mn - f (pairPrimeCarrierToggleLeft r mn)) := by
  unfold pairWeightedStokesBoundaryStep
  rw [lowOwnerFirstOwner_pairLeftEscape_eq_dirichletClip_product hp hr hpr,
    lowOwnerFirstOwner_pairRightEscape_eq_interior_product_dirichletClip
      hp hr hpr]

end RHLean.Proof
