import Mathlib
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_CONTINUATION_LEDGER»
import «research.GLOBAL_RETURNED_CORE_ADMITTED_POSITIVE_OWNER_FUBINI»

/-!
# VF centered greatest-owner continuation partition

This file performs the missing finite carrier bookkeeping needed by the raw
zero-target rank telescope.

For one positive-lag greatest-owner fibre, the existing theorem
`lowOwnerFirstOwnerGreatestOwnerPositivePair_namedContinuation` gives six
possible destinations:

1. a complete post-root family already at the current endpoint;
2. an equal stripped parent (immediate nonpositive terminal);
3. a companion-clipped exit;
4. a complete post-root family at the lower endpoint;
5. an existing lower-endpoint terminal pair;
6. a genuinely recursive lower-rank parent.

The definitions below turn that pointwise disjunction into a priority partition.
No estimate, absolute value, reciprocal-energy promotion, or analytic hypothesis
is introduced.  The final theorem identifies every element of the remaining
sector with the existing recursive lower-rank alternative.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Greatest-owner pairs already belonging to a complete post-root family at
the current endpoint. -/
def lowOwnerFirstOwnerGreatestOwnerCurrentFamilyPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r).filter fun mn =>
    mn ∈ postRootPrimePhysicalPairUnion (squareRootEndpoint R)

/-- Remainder after removing current-endpoint complete families. -/
def lowOwnerFirstOwnerGreatestOwnerAfterCurrentFamilyPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r).filter fun mn =>
    mn ∉ postRootPrimePhysicalPairUnion (squareRootEndpoint R)

/-- Immediate equal-parent terminals after the current complete families are
removed. -/
def lowOwnerFirstOwnerGreatestOwnerEqualParentPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerAfterCurrentFamilyPairFiber R p sig r).filter
    fun mn => SquarefreePairPrimeParentsEqual r mn

/-- Remainder after the equal-parent terminal sector. -/
def lowOwnerFirstOwnerGreatestOwnerAfterEqualParentPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerAfterCurrentFamilyPairFiber R p sig r).filter
    fun mn => ¬ SquarefreePairPrimeParentsEqual r mn

/-- Genuine companion-clipped exits after current complete families and
equal-parent terminals are removed. -/
def lowOwnerFirstOwnerGreatestOwnerClippedPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerAfterEqualParentPairFiber R p sig r).filter
    fun mn =>
      squareRootEndpoint R <
        r * (squarefreePairPrimeOrderedParent r mn.1 mn.2).2

/-- Remainder after the clipped exit. -/
def lowOwnerFirstOwnerGreatestOwnerAfterClippedPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerAfterEqualParentPairFiber R p sig r).filter
    fun mn =>
      ¬ squareRootEndpoint R <
        r * (squarefreePairPrimeOrderedParent r mn.1 mn.2).2

/-- Complete post-root family reached at the lower endpoint after stripping the
greatest fresh owner. -/
def lowOwnerFirstOwnerGreatestOwnerLowerFamilyPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerAfterClippedPairFiber R p sig r).filter
    fun mn =>
      squarefreePairPrimeOrderedParent r mn.1 mn.2 ∈
        postRootPrimePhysicalPairUnion (squareRootEndpoint R / r)

/-- Remainder after lower-endpoint complete families. -/
def lowOwnerFirstOwnerGreatestOwnerAfterLowerFamilyPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerAfterClippedPairFiber R p sig r).filter
    fun mn =>
      squarefreePairPrimeOrderedParent r mn.1 mn.2 ∉
        postRootPrimePhysicalPairUnion (squareRootEndpoint R / r)

/-- Existing nonpositive terminal pair at the lower endpoint. -/
def lowOwnerFirstOwnerGreatestOwnerLowerTerminalPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerAfterLowerFamilyPairFiber R p sig r).filter
    fun mn =>
      squarefreePairPrimeOrderedParent r mn.1 mn.2 ∈
        postRootCovarianceRemainderTerminalPairCarrier
          (squareRootEndpoint R / r)

/-- Final priority remainder.  The theorem below proves that every member is
literally the already-defined recursive lower-rank continuation. -/
def lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerAfterLowerFamilyPairFiber R p sig r).filter
    fun mn =>
      squarefreePairPrimeOrderedParent r mn.1 mn.2 ∉
        postRootCovarianceRemainderTerminalPairCarrier
          (squareRootEndpoint R / r)

private theorem sum_eq_filter_add_filter_not
    {α : Type*} [DecidableEq α]
    (s : Finset α) (P : α → Prop) [DecidablePred P] (f : α → ℝ) :
    (∑ x ∈ s, f x) =
      (∑ x ∈ s.filter P, f x) +
        ∑ x ∈ s.filter (fun x => ¬ P x), f x := by
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := s) (p := P) (f := f)).symm

/-- **Exact six-sector signed Fubini.**

Every greatest-owner positive fibre is split in the chronological priority
order current-family / equal-parent / clipped / lower-family / lower-terminal /
recursive remainder.  The identity is valid for an arbitrary signed pair
weight. -/
theorem sum_lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_eq_sixContinuationSectors
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r,
        f mn) =
      (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerCurrentFamilyPairFiber
          R p sig r, f mn) +
      (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerEqualParentPairFiber
          R p sig r, f mn) +
      (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerClippedPairFiber
          R p sig r, f mn) +
      (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerLowerFamilyPairFiber
          R p sig r, f mn) +
      (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerLowerTerminalPairFiber
          R p sig r, f mn) +
      (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
          R p sig r, f mn) := by
  let F :=
    lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r
  let P0 : ℕ × ℕ → Prop := fun mn =>
    mn ∈ postRootPrimePhysicalPairUnion (squareRootEndpoint R)
  let P1 : ℕ × ℕ → Prop := fun mn =>
    SquarefreePairPrimeParentsEqual r mn
  let P2 : ℕ × ℕ → Prop := fun mn =>
    squareRootEndpoint R <
      r * (squarefreePairPrimeOrderedParent r mn.1 mn.2).2
  let P3 : ℕ × ℕ → Prop := fun mn =>
    squarefreePairPrimeOrderedParent r mn.1 mn.2 ∈
      postRootPrimePhysicalPairUnion (squareRootEndpoint R / r)
  let P4 : ℕ × ℕ → Prop := fun mn =>
    squarefreePairPrimeOrderedParent r mn.1 mn.2 ∈
      postRootCovarianceRemainderTerminalPairCarrier
        (squareRootEndpoint R / r)
  have h0 := sum_eq_filter_add_filter_not F P0 f
  have h1 := sum_eq_filter_add_filter_not (F.filter (fun mn => ¬ P0 mn)) P1 f
  have h2 := sum_eq_filter_add_filter_not
    ((F.filter (fun mn => ¬ P0 mn)).filter (fun mn => ¬ P1 mn)) P2 f
  have h3 := sum_eq_filter_add_filter_not
    (((F.filter (fun mn => ¬ P0 mn)).filter (fun mn => ¬ P1 mn)).filter
      (fun mn => ¬ P2 mn)) P3 f
  have h4 := sum_eq_filter_add_filter_not
    ((((F.filter (fun mn => ¬ P0 mn)).filter (fun mn => ¬ P1 mn)).filter
      (fun mn => ¬ P2 mn)).filter (fun mn => ¬ P3 mn)) P4 f
  change
    (∑ mn ∈ F, f mn) =
      (∑ mn ∈ F.filter P0, f mn) +
      (∑ mn ∈ (F.filter (fun mn => ¬ P0 mn)).filter P1, f mn) +
      (∑ mn ∈
        ((F.filter (fun mn => ¬ P0 mn)).filter (fun mn => ¬ P1 mn)).filter P2,
        f mn) +
      (∑ mn ∈
        (((F.filter (fun mn => ¬ P0 mn)).filter (fun mn => ¬ P1 mn)).filter
          (fun mn => ¬ P2 mn)).filter P3, f mn) +
      (∑ mn ∈
        ((((F.filter (fun mn => ¬ P0 mn)).filter (fun mn => ¬ P1 mn)).filter
          (fun mn => ¬ P2 mn)).filter (fun mn => ¬ P3 mn)).filter P4, f mn) +
      (∑ mn ∈
        ((((F.filter (fun mn => ¬ P0 mn)).filter (fun mn => ¬ P1 mn)).filter
          (fun mn => ¬ P2 mn)).filter (fun mn => ¬ P3 mn)).filter
          (fun mn => ¬ P4 mn), f mn)
  calc
    (∑ mn ∈ F, f mn) =
        (∑ mn ∈ F.filter P0, f mn) +
          ∑ mn ∈ F.filter (fun mn => ¬ P0 mn), f mn := h0
    _ =
        (∑ mn ∈ F.filter P0, f mn) +
          ((∑ mn ∈ (F.filter (fun mn => ¬ P0 mn)).filter P1, f mn) +
            ∑ mn ∈ (F.filter (fun mn => ¬ P0 mn)).filter
              (fun mn => ¬ P1 mn), f mn) := by rw [h1]
    _ =
        (∑ mn ∈ F.filter P0, f mn) +
          (∑ mn ∈ (F.filter (fun mn => ¬ P0 mn)).filter P1, f mn) +
          ((∑ mn ∈
              ((F.filter (fun mn => ¬ P0 mn)).filter
                (fun mn => ¬ P1 mn)).filter P2, f mn) +
            ∑ mn ∈
              ((F.filter (fun mn => ¬ P0 mn)).filter
                (fun mn => ¬ P1 mn)).filter (fun mn => ¬ P2 mn), f mn) := by
          rw [h2]
          ring
    _ =
        (∑ mn ∈ F.filter P0, f mn) +
          (∑ mn ∈ (F.filter (fun mn => ¬ P0 mn)).filter P1, f mn) +
          (∑ mn ∈
            ((F.filter (fun mn => ¬ P0 mn)).filter
              (fun mn => ¬ P1 mn)).filter P2, f mn) +
          ((∑ mn ∈
              (((F.filter (fun mn => ¬ P0 mn)).filter
                (fun mn => ¬ P1 mn)).filter
                (fun mn => ¬ P2 mn)).filter P3, f mn) +
            ∑ mn ∈
              (((F.filter (fun mn => ¬ P0 mn)).filter
                (fun mn => ¬ P1 mn)).filter
                (fun mn => ¬ P2 mn)).filter (fun mn => ¬ P3 mn), f mn) := by
          rw [h3]
          ring
    _ =
        (∑ mn ∈ F.filter P0, f mn) +
          (∑ mn ∈ (F.filter (fun mn => ¬ P0 mn)).filter P1, f mn) +
          (∑ mn ∈
            ((F.filter (fun mn => ¬ P0 mn)).filter
              (fun mn => ¬ P1 mn)).filter P2, f mn) +
          (∑ mn ∈
            (((F.filter (fun mn => ¬ P0 mn)).filter
              (fun mn => ¬ P1 mn)).filter
              (fun mn => ¬ P2 mn)).filter P3, f mn) +
          ((∑ mn ∈
              ((((F.filter (fun mn => ¬ P0 mn)).filter
                (fun mn => ¬ P1 mn)).filter
                (fun mn => ¬ P2 mn)).filter
                (fun mn => ¬ P3 mn)).filter P4, f mn) +
            ∑ mn ∈
              ((((F.filter (fun mn => ¬ P0 mn)).filter
                (fun mn => ¬ P1 mn)).filter
                (fun mn => ¬ P2 mn)).filter
                (fun mn => ¬ P3 mn)).filter (fun mn => ¬ P4 mn), f mn) := by
          rw [h4]
          ring
    _ = _ := by ring

/-- **The priority remainder is exactly the recursive lower-rank class.**

No extra continuation population survives the six-sector split. -/
theorem lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber_data
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
        R p sig r) :
    let W := squareRootEndpoint R
    let parent := squarefreePairPrimeOrderedParent r m n
    parent ∈ postRootCovarianceRemainderRecursivePairCarrier (W / r) ∧
      (squarefreePairFreshPrimeSet parent.1 parent.2).card + 1 =
        (squarefreePairFreshPrimeSet m n).card ∧
      ∀ q ∈ squarefreePairFreshPrimeSet parent.1 parent.2, q < r := by
  have h5 := Finset.mem_filter.mp hmn
  have h4rest := Finset.mem_filter.mp h5.1
  have h3rest := Finset.mem_filter.mp h4rest.1
  have h2rest := Finset.mem_filter.mp h3rest.1
  have h1rest := Finset.mem_filter.mp h2rest.1
  have hbase := h1rest.1
  have hnotCurrent := h1rest.2
  have hnotEqual := h2rest.2
  have hnotClipped := h3rest.2
  have hnotLowerFamily := h4rest.2
  have hnotLowerTerminal := h5.2
  have hcont :=
    lowOwnerFirstOwnerGreatestOwnerPositivePair_namedContinuation hp hbase
  dsimp only at hcont ⊢
  rcases hcont with hcurrent | hequal | hclipped | hlowerFamily |
      hlowerTerminal | hrecursive
  · exact (hnotCurrent hcurrent).elim
  · exact (hnotEqual hequal).elim
  · exact (hnotClipped hclipped).elim
  · exact (hnotLowerFamily hlowerFamily).elim
  · exact (hnotLowerTerminal hlowerTerminal).elim
  · exact hrecursive


/-! ## No-persistence capacitor ledger

The direct survivor machinery has already removed persistent admitted/interior
mass before this continuation partition is used.  The Dirichlet polarization
ledger supplies the exact remaining split:

* the rank-zero diagonal is nonrecursive;
* the mixed clipped sector is literal boundary mass;
* the admitted positive-lag sector is partitioned uniquely by greatest owner;
* within each greatest-owner fibre, the six-sector identity above leaves only
  sector six as genuinely recursive.

The definitions below merely package those existing equalities.  No estimate,
norm, absolute value, or new cancellation hypothesis is introduced.
-/

/-- Sectors one through five in one greatest-owner fibre, in the exact
Dirichlet-polarization weight carried by the existing signed cell telescope. -/
def lowOwnerFirstOwnerGreatestOwnerNoPersistenceSafeDirichletMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerCurrentFamilyPairFiber
      R p sig r, lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerEqualParentPairFiber
      R p sig r, lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerClippedPairFiber
      R p sig r, lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerLowerFamilyPairFiber
      R p sig r, lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerLowerTerminalPairFiber
      R p sig r, lowOwnerFirstOwnerDirichletPolarizationAtom R p mn)

/-- Sector six in one greatest-owner fibre, with exactly the same signed
Dirichlet-polarization weight as the parent cell telescope. -/
def lowOwnerFirstOwnerGreatestOwnerSectorSixDirichletMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
      R p sig r, lowOwnerFirstOwnerDirichletPolarizationAtom R p mn

/-- **One-fibre no-persistence split.**

The whole positive greatest-owner fibre is exactly sectors one through five
plus sector six.  This is the six-sector Fubini specialized to the signed
Dirichlet weight; no inequality has yet been used. -/
theorem sum_lowOwnerFirstOwnerGreatestOwnerPositive_dirichlet_eq_safe_add_sectorSix
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) =
      lowOwnerFirstOwnerGreatestOwnerNoPersistenceSafeDirichletMass
          R p sig r +
        lowOwnerFirstOwnerGreatestOwnerSectorSixDirichletMass
          R p sig r := by
  rw [sum_lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_eq_sixContinuationSectors]
  rfl

/-- Aggregate sectors one through five over the unique greatest-owner
partition of one admitted positive-lag first-owner/signature cell. -/
def lowOwnerFirstOwnerAdmittedPositiveNoPersistenceSafeDirichletMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
    lowOwnerFirstOwnerGreatestOwnerNoPersistenceSafeDirichletMass R p sig r

/-- Aggregate sector-six mass over the same unique greatest-owner partition. -/
def lowOwnerFirstOwnerAdmittedPositiveSectorSixDirichletMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
    lowOwnerFirstOwnerGreatestOwnerSectorSixDirichletMass R p sig r

/-- **Admitted positive-lag mass = no-persistence sectors + sector six.**

Unique greatest-owner Fubini is performed before the six-sector split, so no
owner label or multiplicity is discarded. -/
theorem sum_lowOwnerFirstOwnerAdmittedPositive_dirichlet_eq_safe_add_sectorSix
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ mn ∈ lowOwnerFirstOwnerAdmittedPositivePairCarrier R p sig,
        lowOwnerFirstOwnerDirichletPolarizationAtom R p mn) =
      lowOwnerFirstOwnerAdmittedPositiveNoPersistenceSafeDirichletMass R p sig +
        lowOwnerFirstOwnerAdmittedPositiveSectorSixDirichletMass R p sig := by
  rw [sum_lowOwnerFirstOwnerAdmittedPositive_eq_sum_greatestOwnerFibers
    hp (lowOwnerFirstOwnerDirichletPolarizationAtom R p)]
  unfold lowOwnerFirstOwnerAdmittedPositiveNoPersistenceSafeDirichletMass
    lowOwnerFirstOwnerAdmittedPositiveSectorSixDirichletMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  exact
    sum_lowOwnerFirstOwnerGreatestOwnerPositive_dirichlet_eq_safe_add_sectorSix
      R p sig r

/-- The nonrecursive part of one complete signed cell after all already-proved
no-persistence reductions: rank-zero diagonal, mixed clipped boundary, and
twice sectors one through five of the admitted positive-lag population. -/
def lowOwnerFirstOwnerNoPersistenceSafeDirichletMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
      lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, a)) +
    lowOwnerFirstOwnerClippedMixedPolarizationMass R p sig +
    2 * lowOwnerFirstOwnerAdmittedPositiveNoPersistenceSafeDirichletMass
      R p sig

/-- The only genuinely recursive contribution to one complete signed cell:
twice the positive-lag sector-six mass. -/
def lowOwnerFirstOwnerSectorSixRecursiveDirichletMass
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  2 * lowOwnerFirstOwnerAdmittedPositiveSectorSixDirichletMass R p sig

/-- **Exact no-persistence capacitor identity.**

After the repository's already-proved interior cancellation and boundary
polarization, the entire signed cell telescope is exactly

  safe sectors + sector six.

The safe side consists only of the nonpositive rank-zero diagonal, the mixed
clipped boundary, and continuation sectors one through five.  Every remaining
recursive contribution is literally sector six. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_noPersistenceSafe_add_sectorSix
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      lowOwnerFirstOwnerNoPersistenceSafeDirichletMass R p sig +
        lowOwnerFirstOwnerSectorSixRecursiveDirichletMass R p sig := by
  rw [lowOwnerFirstOwnerSignedCellTelescope_eq_admitted_add_clippedMixed hp]
  rw [lowOwnerFirstOwnerAdmittedPolarizationMass_eq_diag_add_two_positive]
  rw [sum_lowOwnerFirstOwnerAdmittedPositive_dirichlet_eq_safe_add_sectorSix hp]
  unfold lowOwnerFirstOwnerNoPersistenceSafeDirichletMass
    lowOwnerFirstOwnerSectorSixRecursiveDirichletMass
  ring

end RHLean.Proof
