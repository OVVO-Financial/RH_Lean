import Mathlib
import «research.GLOBAL_RETURNED_CORE_CANONICAL_SIGNED_STOKES»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_INCIDENCE_KERNEL»

/-!
# Physical identification of the signed Stokes boundary

This file remains entirely before every positive-energy gate.

The generic weighted Othello/Stokes theorem books two escape faces at one pair
coordinate. On a product carrier those faces are exactly products of the
one-dimensional Othello escape/interior sets. For the actual first-owner base
fibre and every larger prime `r`, the one-dimensional escape set has a literal
physical description:

  n is in the cell, r does not divide n, and X_R < r*n.

Thus the first escape face is not a new error population: it is precisely the
Dirichlet clock clip of the fresh `r` edge. Equivalently the endpoint threshold
crossing at `X_R` is active. The signs and scalar weights are unchanged.

After earlier owners have been peeled, a later escape may occur because a
higher Boolean corner leaves the clock. This file names that exact class as a
`higher-corner Dirichlet clip` and proves recursively that every such escape
terminates at one literal base-cell Dirichlet clip. The accumulated Stokes
boundary is then rewritten exactly as the corresponding signed physical clip
ledger.

The escaped endpoint is also assigned its exact nearest completed-square
coordinate. The square-block midpoint determines the orientation, the physical
stray distance is at most the square-block half-radius `floor(sqrt x)`, and for
any positive finite-wheel conductor the residual distance is the literal
remainder modulo that conductor. These are deterministic boundary-geometry
facts, not energy estimates.

No norm, square, Carleson, Schur, inherited-energy, `2/9`, or `4/9` statement is
imported or used.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Literal Dirichlet clip face of a larger fresh owner on one p-free base
cell. The edge starts on the physical clock and its r-child leaves it. -/
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
  have hnOne : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
  have hnPos : 0 < n := Nat.succ_le_iff.mp hnOne
  have hmuRN : realMoebiusStep (r * n) ≠ 0 := by
    rw [realMoebiusStep_mul_prime_eq_neg hr hrn]
    exact neg_ne_zero.mpr hmuN
  have hrnCar : r * n ∈ lowOwnerNonzeroMobiusCarrier R := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨Nat.succ_le_iff.mpr (Nat.mul_pos hr.pos hnPos), hupper⟩,
        hmuRN⟩
  have hsig : squarefreeLowerPrimeSignature p (r * n) = sig := by
    rw [squarefreeLowerPrimeSignature_mul_larger_prime hr hpr hnPos, hnData.1]
  have hpnotr : ¬ p ∣ r := by
    intro hdiv
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hdiv
    exact (ne_of_lt hpr) heq
  have hpfree : ¬ p ∣ r * n := by
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with h | h
    · exact hpnotr h
    · exact hnData.2 h
  exact Finset.mem_filter.mpr ⟨hrnCar, ⟨hsig, hpfree⟩⟩

/-- Dividing out a present larger prime from a squarefree p-free cell site stays
in the same base cell. -/
theorem lowOwnerFirstOwner_div_larger_prime_mem_same_base
    {R p r n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hn : n ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hrn : r ∣ n) :
    n / r ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
  rcases Finset.mem_filter.mp hn with ⟨hnCar, hnData⟩
  rcases Finset.mem_filter.mp hnCar with ⟨hnIcc, hmuN⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with
    ⟨hnSq, hnPos⟩
  let u := n / r
  have huPos : 0 < u := by
    dsimp [u]
    exact Nat.div_pos (Nat.le_of_dvd hnPos hrn) hr.pos
  have heq : r * u = n := by
    dsimp [u]
    exact Nat.mul_div_cancel' hrn
  have huX : u ≤ squareRootEndpoint R := by
    have hun : u ≤ n := by
      dsimp [u]
      exact Nat.div_le_self n r
    exact hun.trans (Finset.mem_Icc.mp hnIcc).2
  have hrnotu : ¬ r ∣ u := by
    intro hru
    apply (Nat.squarefree_iff_prime_squarefree.mp hnSq r hr)
    rcases hru with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      n = r * u := heq.symm
      _ = r * (r * k) := by rw [hk]
      _ = r ^ 2 * k := by simp [pow_two, Nat.mul_assoc]
  have hmuU : realMoebiusStep u ≠ 0 := by
    have hsign := realMoebiusStep_mul_prime_eq_neg hr hrnotu
    intro hz
    apply hmuN
    rw [← heq, hsign, hz, neg_zero]
  have huCar : u ∈ lowOwnerNonzeroMobiusCarrier R := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, huX⟩, hmuU⟩
  have hsigU : squarefreeLowerPrimeSignature p u = sig := by
    have hlower := squarefreeLowerPrimeSignature_mul_larger_prime
      (p := p) (r := r) (a := u) hr hpr huPos
    calc
      squarefreeLowerPrimeSignature p u =
          squarefreeLowerPrimeSignature p (r * u) := hlower.symm
      _ = squarefreeLowerPrimeSignature p n := by rw [heq]
      _ = sig := hnData.1
  have hpFreeU : ¬ p ∣ u := by
    intro hpu
    rcases hpu with ⟨k, hk⟩
    apply hnData.2
    refine ⟨r * k, ?_⟩
    calc
      n = r * u := heq.symm
      _ = r * (p * k) := by rw [hk]
      _ = p * (r * k) := by ring
  exact Finset.mem_filter.mpr ⟨huCar, ⟨hsigU, hpFreeU⟩⟩

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
  rw [primeCarrierToggle_of_dvd hrn hrsq]
  exact lowOwnerFirstOwner_div_larger_prime_mem_same_base
    hp hr hpr hn hrn

/-- **No hidden one-dimensional escape class at the base cell.** -/
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
    have hle' : r * n ≤ squareRootEndpoint R := by
      simpa [Nat.mul_comm] using hle
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
  have hnX : n ≤ squareRootEndpoint R := (Finset.mem_Icc.mp hIcc).2
  unfold lowOwnerThresholdCrossingIndicator
  simp [hnX, hclip]

/-! ## Exact nearest-square endpoint coordinate of a clip child -/

/-- Canonical completed-square endpoint nearest to an arbitrary integer `x`.
The midpoint of the square block is the half-integer between the two cases. -/
def lowOwnerStokesNearestSquareEndpoint (x : ℕ) : ℕ :=
  let s := Nat.sqrt x
  if x < s ^ 2 + s then squareRootEndpoint s
  else squareRootEndpoint (s + 1)

/-- Exact physical distance from `x` to its selected completed-square endpoint. -/
def lowOwnerStokesNearestSquareDistance (x : ℕ) : ℕ :=
  let s := Nat.sqrt x
  if x < s ^ 2 + s then x - squareRootEndpoint s
  else squareRootEndpoint (s + 1) - x

/-- The square-block midpoint determines the lower-endpoint orientation. -/
theorem lowOwnerStokesNearestSquareEndpoint_eq_lower
    {x : ℕ}
    (hmid : x < (Nat.sqrt x) ^ 2 + Nat.sqrt x) :
    lowOwnerStokesNearestSquareEndpoint x =
      squareRootEndpoint (Nat.sqrt x) := by
  simp [lowOwnerStokesNearestSquareEndpoint, hmid]

/-- At or above the midpoint switch, the upper completed-square endpoint is
selected. -/
theorem lowOwnerStokesNearestSquareEndpoint_eq_upper
    {x : ℕ}
    (hmid : (Nat.sqrt x) ^ 2 + Nat.sqrt x ≤ x) :
    lowOwnerStokesNearestSquareEndpoint x =
      squareRootEndpoint (Nat.sqrt x + 1) := by
  simp [lowOwnerStokesNearestSquareEndpoint, Nat.not_lt.mpr hmid]

/-- Exact orientation-and-distance dichotomy for an arbitrary physical
endpoint. -/
theorem lowOwnerStokesNearestSquareEndpoint_cases (x : ℕ) :
    (x < (Nat.sqrt x) ^ 2 + Nat.sqrt x ∧
      lowOwnerStokesNearestSquareEndpoint x =
        squareRootEndpoint (Nat.sqrt x) ∧
      lowOwnerStokesNearestSquareDistance x =
        x - squareRootEndpoint (Nat.sqrt x)) ∨
    ((Nat.sqrt x) ^ 2 + Nat.sqrt x ≤ x ∧
      lowOwnerStokesNearestSquareEndpoint x =
        squareRootEndpoint (Nat.sqrt x + 1) ∧
      lowOwnerStokesNearestSquareDistance x =
        squareRootEndpoint (Nat.sqrt x + 1) - x) := by
  by_cases hmid : x < (Nat.sqrt x) ^ 2 + Nat.sqrt x
  · left
    exact ⟨hmid,
      by simp [lowOwnerStokesNearestSquareEndpoint, hmid],
      by simp [lowOwnerStokesNearestSquareDistance, hmid]⟩
  · right
    have hmid' : (Nat.sqrt x) ^ 2 + Nat.sqrt x ≤ x :=
      Nat.le_of_not_gt hmid
    exact ⟨hmid',
      by simp [lowOwnerStokesNearestSquareEndpoint, hmid],
      by simp [lowOwnerStokesNearestSquareDistance, hmid]⟩

/-- **Deterministic stray-radius theorem.** The unfinished physical interval
between `x` and its nearest completed-square endpoint has length at most the
square-block half-radius `floor(sqrt x)`. -/
theorem lowOwnerStokesNearestSquareDistance_le_sqrt (x : ℕ) :
    lowOwnerStokesNearestSquareDistance x ≤ Nat.sqrt x := by
  let s := Nat.sqrt x
  have hs2 : s ^ 2 ≤ x := by
    simpa [s] using Nat.sqrt_le' x
  have hxlt : x < (s + 1) ^ 2 := by
    simpa [s] using Nat.lt_succ_sqrt' x
  by_cases hmid : x < s ^ 2 + s
  · have hdist :
        lowOwnerStokesNearestSquareDistance x =
          x - squareRootEndpoint s := by
      simp [lowOwnerStokesNearestSquareDistance, s, hmid]
    rw [hdist]
    have hgap : x - squareRootEndpoint s ≤ s := by
      unfold squareRootEndpoint
      omega
    simpa [s] using hgap
  · have hmid' : s ^ 2 + s ≤ x := Nat.le_of_not_gt hmid
    have hdist :
        lowOwnerStokesNearestSquareDistance x =
          squareRootEndpoint (s + 1) - x := by
      simp [lowOwnerStokesNearestSquareDistance, s, hmid]
    rw [hdist]
    have hsquare : (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 := by ring
    have hgap : squareRootEndpoint (s + 1) - x ≤ s := by
      unfold squareRootEndpoint
      rw [hsquare]
      omega
    simpa [s] using hgap

/-- Residual endpoint distance at an arbitrary positive finite-wheel conductor.
This remains an exact coordinate, not a magnitude estimate. -/
def lowOwnerStokesResidualEndpointDistance (x conductor : ℕ) : ℕ :=
  lowOwnerStokesNearestSquareDistance x % conductor

/-- A nonzero-frequency wheel state has fewer than `conductor` possible residual
endpoint distances. -/
theorem lowOwnerStokesResidualEndpointDistance_lt
    {x conductor : ℕ} (hc : 0 < conductor) :
    lowOwnerStokesResidualEndpointDistance x conductor < conductor := by
  exact Nat.mod_lt _ hc

/-- A literal Stokes clip child therefore carries an explicit square endpoint
coordinate and lies within its deterministic square-block half-radius. -/
theorem lowOwnerFirstOwner_dirichletClip_has_bounded_squareEndpointDistance
    {R p r n : ℕ} {sig : Finset ℕ}
    (hn : n ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig r) :
    squareRootEndpoint R < r * n ∧
      lowOwnerStokesNearestSquareDistance (r * n) ≤ Nat.sqrt (r * n) := by
  rcases mem_lowOwnerFirstOwnerStokesDirichletClipFace.mp hn with
    ⟨_hbase, _hrn, hclip⟩
  exact ⟨hclip, lowOwnerStokesNearestSquareDistance_le_sqrt (r * n)⟩

/-- The same clip child has an exact finite residual-distance coordinate at any
positive wheel conductor. -/
theorem lowOwnerFirstOwner_dirichletClip_residualEndpointDistance_lt
    {R p r n conductor : ℕ} {sig : Finset ℕ}
    (hn : n ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig r)
    (hc : 0 < conductor) :
    squareRootEndpoint R < r * n ∧
      lowOwnerStokesResidualEndpointDistance (r * n) conductor < conductor := by
  rcases mem_lowOwnerFirstOwnerStokesDirichletClipFace.mp hn with
    ⟨_hbase, _hrn, hclip⟩
  exact ⟨hclip, lowOwnerStokesResidualEndpointDistance_lt hc⟩

/-! ## Exact product-carrier factorization of pair escape faces -/

theorem pairPrimeLeftEscapePart_product
    (r : ℕ) (A B : Finset ℕ) :
    pairPrimeLeftEscapePart r (A.product B) =
      (primeEscapePart r A).product B := by
  ext mn
  rcases mn with ⟨a, b⟩
  simp [pairPrimeLeftEscapePart, weightedOthelloEscapePart,
    pairPrimeCarrierToggleLeft, primeEscapePart]
  aesop

theorem pairPrimeLeftInteriorPart_product
    (r : ℕ) (A B : Finset ℕ) :
    pairPrimeLeftInteriorPart r (A.product B) =
      (primeInteriorPart r A).product B := by
  ext mn
  rcases mn with ⟨a, b⟩
  simp [pairPrimeLeftInteriorPart, weightedOthelloInteriorPart,
    pairPrimeCarrierToggleLeft, primeInteriorPart]
  aesop

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
  aesop

theorem pairPrimeTwoCoordinateInterior_product
    (r : ℕ) (A B : Finset ℕ) :
    pairPrimeTwoCoordinateInterior r (A.product B) =
      (primeInteriorPart r A).product (primeInteriorPart r B) := by
  ext mn
  rcases mn with ⟨a, b⟩
  simp [pairPrimeTwoCoordinateInterior, pairPrimeLeftInteriorPart,
    weightedOthelloInteriorPart, pairPrimeCarrierToggleLeft,
    pairPrimeCarrierToggleRight, primeInteriorPart]
  aesop

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

/-! ## Accumulated escape faces are higher-corner Dirichlet clips -/

def stokesReversedInterior : List ℕ → Finset ℕ → Finset ℕ
  | [], B => B
  | q :: qs, B => primeInteriorPart q (stokesReversedInterior qs B)

def stokesPhysicalClipWitness
    (B : Finset ℕ) : List ℕ → ℕ → ℕ → Prop
  | [], r, n => n ∈ B ∧ primeCarrierToggle r n ∉ B
  | q :: qs, r, n =>
      n ∈ primeInteriorPart q (stokesReversedInterior qs B) ∧
        (stokesPhysicalClipWitness B qs r n ∨
          stokesPhysicalClipWitness B qs q (primeCarrierToggle r n))

theorem stokesPhysicalClipWitness_mem
    (B : Finset ℕ) :
    ∀ (qs : List ℕ) (r n : ℕ),
      stokesPhysicalClipWitness B qs r n →
        n ∈ stokesReversedInterior qs B := by
  intro qs
  cases qs with
  | nil =>
      intro r n h
      exact h.1
  | cons q qs =>
      intro r n h
      exact h.1

theorem mem_primeEscapePart_stokesReversedInterior_iff_clipWitness
    (B : Finset ℕ) :
    ∀ (qs : List ℕ) (r n : ℕ),
      n ∈ primeEscapePart r (stokesReversedInterior qs B) ↔
        stokesPhysicalClipWitness B qs r n := by
  intro qs
  induction qs with
  | nil =>
      intro r n
      simp [stokesReversedInterior, stokesPhysicalClipWitness,
        mem_primeEscapePart]
  | cons q qs ih =>
      intro r n
      let A := stokesReversedInterior qs B
      change n ∈ primeEscapePart r (primeInteriorPart q A) ↔
        n ∈ primeInteriorPart q A ∧
          (stokesPhysicalClipWitness B qs r n ∨
            stokesPhysicalClipWitness B qs q (primeCarrierToggle r n))
      constructor
      · intro hesc
        rcases mem_primeEscapePart.mp hesc with ⟨hnInt, hmateNotInt⟩
        refine ⟨hnInt, ?_⟩
        by_cases hmateA : primeCarrierToggle r n ∈ A
        · right
          apply (ih q (primeCarrierToggle r n)).mp
          apply mem_primeEscapePart.mpr
          refine ⟨hmateA, ?_⟩
          intro hqmateA
          exact hmateNotInt
            (mem_primeInteriorPart.mpr ⟨hmateA, hqmateA⟩)
        · left
          apply (ih r n).mp
          apply mem_primeEscapePart.mpr
          exact ⟨(mem_primeInteriorPart.mp hnInt).1, hmateA⟩
      · rintro ⟨hnInt, hdirect | hinherited⟩
        · have hescA := (ih r n).mpr hdirect
          have hmateNotA := (mem_primeEscapePart.mp hescA).2
          apply mem_primeEscapePart.mpr
          refine ⟨hnInt, ?_⟩
          intro hmateInt
          exact hmateNotA (mem_primeInteriorPart.mp hmateInt).1
        · have hescQ :=
            (ih q (primeCarrierToggle r n)).mpr hinherited
          have hqdata := mem_primeEscapePart.mp hescQ
          apply mem_primeEscapePart.mpr
          refine ⟨hnInt, ?_⟩
          intro hmateInt
          exact hqdata.2 (mem_primeInteriorPart.mp hmateInt).2

theorem stokesPhysicalClipWitness_exists_baseEscape
    (B : Finset ℕ) :
    ∀ (qs : List ℕ) (r n : ℕ),
      stokesPhysicalClipWitness B qs r n →
        ∃ t m, t ∈ r :: qs ∧ m ∈ primeEscapePart t B := by
  intro qs
  induction qs with
  | nil =>
      intro r n h
      exact ⟨r, n, by simp, mem_primeEscapePart.mpr h⟩
  | cons q qs ih =>
      intro r n h
      rcases h with ⟨_hnInt, hdirect | hinherited⟩
      · rcases ih r n hdirect with ⟨t, m, ht, hm⟩
        refine ⟨t, m, ?_, hm⟩
        simp only [List.mem_cons] at ht ⊢
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ht)
      · rcases ih q (primeCarrierToggle r n) hinherited with
          ⟨t, m, ht, hm⟩
        refine ⟨t, m, ?_, hm⟩
        simp only [List.mem_cons] at ht ⊢
        exact Or.inr ht

def lowOwnerFirstOwnerStokesHigherCornerClipFace
    (R p : ℕ) (sig : Finset ℕ) (qs : List ℕ) (r : ℕ) : Finset ℕ :=
  (stokesReversedInterior qs (lowOwnerFirstOwnerBaseFiber R p sig)).filter
    fun n => stokesPhysicalClipWitness
      (lowOwnerFirstOwnerBaseFiber R p sig) qs r n

theorem lowOwnerFirstOwner_primeEscapePart_reversedInterior_eq_higherCornerClip
    (R p : ℕ) (sig : Finset ℕ) (qs : List ℕ) (r : ℕ) :
    primeEscapePart r
        (stokesReversedInterior qs (lowOwnerFirstOwnerBaseFiber R p sig)) =
      lowOwnerFirstOwnerStokesHigherCornerClipFace R p sig qs r := by
  ext n
  rw [mem_primeEscapePart_stokesReversedInterior_iff_clipWitness]
  constructor
  · intro hw
    exact Finset.mem_filter.mpr
      ⟨stokesPhysicalClipWitness_mem
        (lowOwnerFirstOwnerBaseFiber R p sig) qs r n hw, hw⟩
  · intro hn
    exact (Finset.mem_filter.mp hn).2

theorem lowOwnerFirstOwner_higherCornerClip_has_dirichletClipLeaf
    {R p r n : ℕ} {sig : Finset ℕ} {qs : List ℕ}
    (hp : p.Prime)
    (howners : ∀ t ∈ r :: qs, t.Prime ∧ p < t)
    (hn : n ∈ lowOwnerFirstOwnerStokesHigherCornerClipFace R p sig qs r) :
    ∃ t m, t ∈ r :: qs ∧
      m ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig t := by
  have hwit : stokesPhysicalClipWitness
      (lowOwnerFirstOwnerBaseFiber R p sig) qs r n :=
    (Finset.mem_filter.mp hn).2
  rcases stokesPhysicalClipWitness_exists_baseEscape
      (lowOwnerFirstOwnerBaseFiber R p sig) qs r n hwit with
    ⟨t, m, ht, hm⟩
  have htData := howners t ht
  refine ⟨t, m, ht, ?_⟩
  rw [← lowOwnerFirstOwner_primeEscapePart_eq_dirichletClipFace
    hp htData.1 htData.2]
  exact hm

/-- Every accumulated higher-corner clip therefore inherits an explicit base
clip whose escaped child has deterministic nearest-square radius. -/
theorem lowOwnerFirstOwner_higherCornerClip_has_bounded_squareEndpointLeaf
    {R p r n : ℕ} {sig : Finset ℕ} {qs : List ℕ}
    (hp : p.Prime)
    (howners : ∀ t ∈ r :: qs, t.Prime ∧ p < t)
    (hn : n ∈ lowOwnerFirstOwnerStokesHigherCornerClipFace R p sig qs r) :
    ∃ t m, t ∈ r :: qs ∧
      m ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig t ∧
      squareRootEndpoint R < t * m ∧
      lowOwnerStokesNearestSquareDistance (t * m) ≤ Nat.sqrt (t * m) := by
  rcases lowOwnerFirstOwner_higherCornerClip_has_dirichletClipLeaf
      hp howners hn with ⟨t, m, ht, hm⟩
  have hgeom :=
    lowOwnerFirstOwner_dirichletClip_has_bounded_squareEndpointDistance hm
  exact ⟨t, m, ht, hm, hgeom.1, hgeom.2⟩

theorem lowOwnerZeroFrequencyMobiusWeight_sub_toggle_eq_signedCrossing
    {R r n : ℕ} (hr : r.Prime) (hnSq : Squarefree n) :
    lowOwnerZeroFrequencyMobiusWeight R n -
        lowOwnerZeroFrequencyMobiusWeight R (primeCarrierToggle r n) =
      if r ∣ n then
        -(lowOwnerDaughterCrossingWeight R r (n / r) -
          lowOwnerRootCrossingIndicator R r (n / r))
      else
        lowOwnerDaughterCrossingWeight R r n -
          lowOwnerRootCrossingIndicator R r n := by
  by_cases hrn : r ∣ n
  · have hrsq : ¬ r ^ 2 ∣ n := by
      intro hsq
      exact (Nat.squarefree_iff_prime_squarefree.mp hnSq r hr)
        (by simpa [pow_two] using hsq)
    rw [if_pos hrn, primeCarrierToggle_of_dvd hrn hrsq]
    have heq : r * (n / r) = n := Nat.mul_div_cancel' hrn
    have h := lowOwnerZeroFrequencyMobiusWeight_sub_mul
      (R := R) (p := r) (n := n / r) hr.one_le
    rw [heq] at h
    linarith
  · rw [if_neg hrn, primeCarrierToggle_of_not_dvd hrn]
    simpa [Nat.mul_comm] using
      (lowOwnerZeroFrequencyMobiusWeight_sub_mul
        (R := R) (p := r) (n := n) hr.one_le)

/-! ## Exact value of the accumulated physical clip ledger -/

theorem lowOwnerFirstOwner_pairLeftEscape_reversedInterior_eq_higherCornerClip
    (R p : ℕ) (sig : Finset ℕ) (qs : List ℕ) (r : ℕ) :
    pairPrimeLeftEscapePart r
        ((stokesReversedInterior qs
          (lowOwnerFirstOwnerBaseFiber R p sig)).product
         (stokesReversedInterior qs
          (lowOwnerFirstOwnerBaseFiber R p sig))) =
      (lowOwnerFirstOwnerStokesHigherCornerClipFace R p sig qs r).product
        (stokesReversedInterior qs
          (lowOwnerFirstOwnerBaseFiber R p sig)) := by
  rw [pairPrimeLeftEscapePart_product,
    lowOwnerFirstOwner_primeEscapePart_reversedInterior_eq_higherCornerClip]

theorem lowOwnerFirstOwner_pairRightEscape_reversedInterior_eq_higherCornerClip
    (R p : ℕ) (sig : Finset ℕ) (qs : List ℕ) (r : ℕ) :
    pairPrimeRightEscapeAfterLeft r
        ((stokesReversedInterior qs
          (lowOwnerFirstOwnerBaseFiber R p sig)).product
         (stokesReversedInterior qs
          (lowOwnerFirstOwnerBaseFiber R p sig))) =
      (primeInteriorPart r
        (stokesReversedInterior qs
          (lowOwnerFirstOwnerBaseFiber R p sig))).product
        (lowOwnerFirstOwnerStokesHigherCornerClipFace R p sig qs r) := by
  rw [pairPrimeRightEscapeAfterLeft_product,
    lowOwnerFirstOwner_primeEscapePart_reversedInterior_eq_higherCornerClip]

def lowOwnerFirstOwnerStokesHigherCornerBoundaryStep
    (R p : ℕ) (sig : Finset ℕ) (qs : List ℕ) (r : ℕ)
    (f : ℕ × ℕ → ℝ) : ℝ :=
  let A := stokesReversedInterior qs (lowOwnerFirstOwnerBaseFiber R p sig)
  let E := lowOwnerFirstOwnerStokesHigherCornerClipFace R p sig qs r
  (∑ mn ∈ E.product A, othelloRealMoebiusPair mn * f mn) +
    (1 / 2 : ℝ) *
      ∑ mn ∈ (primeInteriorPart r A).product E,
        othelloRealMoebiusPair mn *
          (f mn - f (pairPrimeCarrierToggleLeft r mn))

theorem lowOwnerFirstOwner_pairBoundaryStep_reversedInterior_eq_higherCorner
    (R p : ℕ) (sig : Finset ℕ) (qs : List ℕ) (r : ℕ)
    (f : ℕ × ℕ → ℝ) :
    pairWeightedStokesBoundaryStep r
        ((stokesReversedInterior qs
          (lowOwnerFirstOwnerBaseFiber R p sig)).product
         (stokesReversedInterior qs
          (lowOwnerFirstOwnerBaseFiber R p sig))) f =
      lowOwnerFirstOwnerStokesHigherCornerBoundaryStep R p sig qs r f := by
  unfold pairWeightedStokesBoundaryStep
    lowOwnerFirstOwnerStokesHigherCornerBoundaryStep
  rw [lowOwnerFirstOwner_pairLeftEscape_reversedInterior_eq_higherCornerClip,
    lowOwnerFirstOwner_pairRightEscape_reversedInterior_eq_higherCornerClip]

def lowOwnerFirstOwnerPhysicalStokesBoundaryFrom
    (R p : ℕ) (sig : Finset ℕ) :
    List ℕ → List ℕ → (ℕ × ℕ → ℝ) → ℝ
  | _doneRev, [], _f => 0
  | doneRev, r :: rs, f =>
      lowOwnerFirstOwnerStokesHigherCornerBoundaryStep
          R p sig doneRev r f +
        (1 / 4 : ℝ) *
          lowOwnerFirstOwnerPhysicalStokesBoundaryFrom R p sig
            (r :: doneRev) rs (pairPrimeMixedDifference r f)

theorem iteratedPairWeightedStokesBoundary_eq_physicalClipLedger :
    ∀ (R p : ℕ) (sig : Finset ℕ) (doneRev ps : List ℕ)
      (f : ℕ × ℕ → ℝ),
      iteratedPairWeightedStokesBoundary ps
          ((stokesReversedInterior doneRev
            (lowOwnerFirstOwnerBaseFiber R p sig)).product
           (stokesReversedInterior doneRev
            (lowOwnerFirstOwnerBaseFiber R p sig))) f =
        lowOwnerFirstOwnerPhysicalStokesBoundaryFrom
          R p sig doneRev ps f := by
  intro R p sig doneRev ps
  induction ps generalizing doneRev with
  | nil =>
      intro f
      simp [iteratedPairWeightedStokesBoundary,
        lowOwnerFirstOwnerPhysicalStokesBoundaryFrom]
  | cons r rs ih =>
      intro f
      rw [iteratedPairWeightedStokesBoundary,
        lowOwnerFirstOwnerPhysicalStokesBoundaryFrom,
        lowOwnerFirstOwner_pairBoundaryStep_reversedInterior_eq_higherCorner,
        pairPrimeTwoCoordinateInterior_product]
      change
        lowOwnerFirstOwnerStokesHigherCornerBoundaryStep
            R p sig doneRev r f +
          (1 / 4 : ℝ) *
            iteratedPairWeightedStokesBoundary rs
              ((stokesReversedInterior (r :: doneRev)
                (lowOwnerFirstOwnerBaseFiber R p sig)).product
               (stokesReversedInterior (r :: doneRev)
                (lowOwnerFirstOwnerBaseFiber R p sig)))
              (pairPrimeMixedDifference r f) =
        lowOwnerFirstOwnerStokesHigherCornerBoundaryStep
            R p sig doneRev r f +
          (1 / 4 : ℝ) *
            lowOwnerFirstOwnerPhysicalStokesBoundaryFrom
              R p sig (r :: doneRev) rs (pairPrimeMixedDifference r f)
      rw [ih (doneRev := r :: doneRev)
        (f := pairPrimeMixedDifference r f)]

def lowOwnerFirstOwnerCanonicalStokesClipBoundary
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  lowOwnerFirstOwnerPhysicalStokesBoundaryFrom R p sig []
    (lowOwnerFirstOwnerCanonicalStokesSchedule R p)
    (lowOwnerFirstOwnerDirichletPolarizationScalar R p)

theorem lowOwnerFirstOwnerCanonicalStokesBoundary_eq_clipBoundary
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerCanonicalStokesBoundary R p sig =
      lowOwnerFirstOwnerCanonicalStokesClipBoundary R p sig := by
  unfold lowOwnerFirstOwnerCanonicalStokesBoundary
    lowOwnerFirstOwnerCanonicalStokesClipBoundary
    lowOwnerFirstOwnerSignedCellPairCarrier
  exact iteratedPairWeightedStokesBoundary_eq_physicalClipLedger
    R p sig [] (lowOwnerFirstOwnerCanonicalStokesSchedule R p)
      (lowOwnerFirstOwnerDirichletPolarizationScalar R p)

def lowOwnerCanonicalSignedStokesClipBoundary (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCanonicalStokesClipBoundary R p sig

theorem lowOwnerCanonicalSignedStokesBoundary_eq_clipBoundary
    (R : ℕ) :
    lowOwnerCanonicalSignedStokesBoundary R =
      lowOwnerCanonicalSignedStokesClipBoundary R := by
  unfold lowOwnerCanonicalSignedStokesBoundary
    lowOwnerCanonicalSignedStokesClipBoundary
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro sig _hsig
  exact lowOwnerFirstOwnerCanonicalStokesBoundary_eq_clipBoundary R p sig

end RHLean.Proof
