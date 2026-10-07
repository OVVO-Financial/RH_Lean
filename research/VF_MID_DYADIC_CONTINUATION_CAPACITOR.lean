import Mathlib
import «research.VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE»
import «research.VF_MID_FAN_ESCAPE_CAPACITY_BILLS»

/-!
# VF dyadic continuation capacitor

This file globalizes the #903 six-sector greatest-owner continuation identity
over an actual contiguous dyadic square-root run `[A,B)`.

No new carrier is introduced.  The outer indices are exactly the existing
global owner indices at each endpoint scale:

* `R ∈ Finset.Ico A B`;
* `p ∈ primesUpTo (squareRootEndpoint R)`;
* `sig ∈ lowOwnerFirstOwnerSignatureSet R p`;
* `r ∈ lowOwnerRevealedPrimesAbove R p`.

Inside each `(R,p,sig,r)` fibre, sectors 1--5 are grouped as the local
"capacitor" or safe mass and sector 6 is retained literally as the recursive
continuation mass.  Because the local theorem is an exact signed Fubini
identity for an arbitrary weight, the run-level statement is also an exact
signed identity before any absolute value is taken.

This is the mechanical bridge needed by the capacity-bounce lemmas:

  totalRunMass = safeRunMass + recursiveRunMass.

Consequently, if the recursive run mass is assumed to stay in `[-H,H]`, the
safe mass is forced into the rigid window

  totalRunMass - H <= safeRunMass <= totalRunMass + H.

The theorem does not yet identify the total run mass with the first-bad VF
escape bill, nor does it yet regroup the recursive sector into contiguous
lower child runs.  Those are the two remaining source/reassembly splices.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Arbitrary signed weight on one greatest-owner pair in one endpoint cell. -/
abbrev VFMidContinuationRunPairWeight :=
  ℕ → ℕ → Finset ℕ → ℕ → (ℕ × ℕ) → ℝ

/-- Positive greatest-owner fibre mass for an arbitrary signed weight. -/
def lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : VFMidContinuationRunPairWeight) : ℝ :=
  ∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r,
    f R p sig r mn

/-- Sectors 1--5 of the #903 continuation partition, still at one
greatest-owner fibre and with exact signs retained. -/
def lowOwnerFirstOwnerGreatestOwnerSafeContinuationFiberMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : VFMidContinuationRunPairWeight) : ℝ :=
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerCurrentFamilyPairFiber R p sig r,
      f R p sig r mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerEqualParentPairFiber R p sig r,
      f R p sig r mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerClippedPairFiber R p sig r,
      f R p sig r mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerLowerFamilyPairFiber R p sig r,
      f R p sig r mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerLowerTerminalPairFiber R p sig r,
      f R p sig r mn)

/-- Sector 6 of the #903 continuation partition, retained as the unresolved
recursive continuation mass. -/
def lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationFiberMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : VFMidContinuationRunPairWeight) : ℝ :=
  ∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
      R p sig r,
    f R p sig r mn

/-- **Local capacitor equality.**

This is exactly the six-sector theorem with sectors 1--5 grouped and sector 6
left separate. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass_eq_safe_add_recursive
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : VFMidContinuationRunPairWeight) :
    lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass R p sig r f =
      lowOwnerFirstOwnerGreatestOwnerSafeContinuationFiberMass R p sig r f +
        lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationFiberMass
          R p sig r f := by
  unfold lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass
    lowOwnerFirstOwnerGreatestOwnerSafeContinuationFiberMass
    lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationFiberMass
  rw [sum_lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_eq_sixContinuationSectors]
  ring

/-- Full positive greatest-owner mass over the contiguous endpoint run
`[A,B)`, using exactly the repository's existing first-owner/signature/owner
index sets at each scale. -/
def lowOwnerDyadicGreatestOwnerPositiveRunMass
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
          lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass R p sig r f

/-- Run-level capacitor mass: exact signed sum of continuation sectors 1--5. -/
def lowOwnerDyadicGreatestOwnerSafeContinuationRunMass
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
          lowOwnerFirstOwnerGreatestOwnerSafeContinuationFiberMass
            R p sig r f

/-- Run-level unresolved recursive mass: exact signed sum of sector 6. -/
def lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
          lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationFiberMass
            R p sig r f

/-- **Globalized six-sector Fubini on a complete dyadic run.**

The full positive greatest-owner run mass is exactly sectors 1--5 plus the
recursive sixth sector.  No norm or estimate occurs. -/
theorem lowOwnerDyadicGreatestOwnerPositiveRunMass_eq_safe_add_recursive
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) :
    lowOwnerDyadicGreatestOwnerPositiveRunMass A B f =
      lowOwnerDyadicGreatestOwnerSafeContinuationRunMass A B f +
        lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass A B f := by
  unfold lowOwnerDyadicGreatestOwnerPositiveRunMass
    lowOwnerDyadicGreatestOwnerSafeContinuationRunMass
    lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass
  simp_rw [lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass_eq_safe_add_recursive]
  simp only [Finset.sum_add_distrib]

/-- **Run-level capacitor window.**

If the complete recursive sixth sector of the run is not supercritical, then
the exact signed mass of sectors 1--5 is trapped in the rigid `±H` window
around the total run mass. -/
theorem lowOwnerDyadicGreatestOwnerSafeContinuationRunMass_mem_totalWindow
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) (H : ℝ)
    (hrec :
      |lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass A B f| ≤ H) :
    lowOwnerDyadicGreatestOwnerPositiveRunMass A B f - H ≤
        lowOwnerDyadicGreatestOwnerSafeContinuationRunMass A B f ∧
      lowOwnerDyadicGreatestOwnerSafeContinuationRunMass A B f ≤
        lowOwnerDyadicGreatestOwnerPositiveRunMass A B f + H := by
  exact vfMidSafeMass_mem_parentWindow_of_recursive_abs_le
    (lowOwnerDyadicGreatestOwnerPositiveRunMass_eq_safe_add_recursive A B f)
    hrec

/-- **Positive-side run tripwire.**

Any upper bound on sectors 1--5 which lies more than `H` below the exact
total run mass forces the recursive sixth sector to be positively
supercritical. -/
theorem lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass_gt_of_safeCapacity
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) (cap H : ℝ)
    (hsafe :
      lowOwnerDyadicGreatestOwnerSafeContinuationRunMass A B f ≤ cap)
    (hexcess :
      cap + H < lowOwnerDyadicGreatestOwnerPositiveRunMass A B f) :
    H <
      lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass A B f := by
  exact vfMidRecursiveResidual_gt_of_safeCapacity
    (lowOwnerDyadicGreatestOwnerPositiveRunMass_eq_safe_add_recursive A B f)
    hsafe hexcess

/-- **Negative-side run tripwire.**

Any lower bound on sectors 1--5 which lies more than `H` above the exact
total run mass forces the recursive sixth sector to be negatively
supercritical. -/
theorem lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass_lt_neg_of_safeFloor
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) (floorMass H : ℝ)
    (hsafe :
      floorMass ≤ lowOwnerDyadicGreatestOwnerSafeContinuationRunMass A B f)
    (hover :
      lowOwnerDyadicGreatestOwnerPositiveRunMass A B f + H < floorMass) :
    lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass A B f < -H := by
  exact vfMidRecursiveResidual_lt_neg_of_safeFloor
    (lowOwnerDyadicGreatestOwnerPositiveRunMass_eq_safe_add_recursive A B f)
    hsafe hover

/-! ## Canonical Dirichlet-polarization specialization

The local six-sector continuation is used by the existing owner Fubini in the
Dirichlet polarization currency.  These aliases freeze that actual weight so a
later source theorem cannot silently change currencies. -/

/-- Existing signed pair weight, lifted to the full run index type. -/
def vfMidContinuationDirichletPairWeight :
    VFMidContinuationRunPairWeight :=
  fun R p _sig _r mn =>
    lowOwnerFirstOwnerDirichletPolarizationAtom R p mn

def vfMidDyadicGreatestOwnerPositiveDirichletRunMass
    (A B : ℕ) : ℝ :=
  lowOwnerDyadicGreatestOwnerPositiveRunMass
    A B vfMidContinuationDirichletPairWeight

def vfMidDyadicGreatestOwnerSafeDirichletRunMass
    (A B : ℕ) : ℝ :=
  lowOwnerDyadicGreatestOwnerSafeContinuationRunMass
    A B vfMidContinuationDirichletPairWeight

def vfMidDyadicGreatestOwnerRecursiveDirichletRunMass
    (A B : ℕ) : ℝ :=
  lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass
    A B vfMidContinuationDirichletPairWeight

theorem vfMidDyadicGreatestOwnerPositiveDirichletRunMass_eq_safe_add_recursive
    (A B : ℕ) :
    vfMidDyadicGreatestOwnerPositiveDirichletRunMass A B =
      vfMidDyadicGreatestOwnerSafeDirichletRunMass A B +
        vfMidDyadicGreatestOwnerRecursiveDirichletRunMass A B := by
  exact lowOwnerDyadicGreatestOwnerPositiveRunMass_eq_safe_add_recursive
    A B vfMidContinuationDirichletPairWeight


/-! ## Native sector-six parent reassembly

The sixth sector is pair-valued, so it is reassembled first in its own native
Möbius-pair currency.  This avoids an invalid identification with the scalar
VF child carrier.  Every recursive child is mapped to its stripped ordered
greatest-owner parent, exact sign reversal is retained, and duplicate parents
are counted with their literal multiplicity. -/

/-- Raw Möbius pair weight lifted to the run index type. -/
def vfMidContinuationMoebiusPairWeight :
    VFMidContinuationRunPairWeight :=
  fun _R _p _sig _r mn =>
    realMoebiusStep mn.1 * realMoebiusStep mn.2

/-- Every sector-six child is still a member of the original positive
greatest-owner fibre. -/
theorem lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber_mem_positive
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
        R p sig r) :
    (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r := by
  have h5 := Finset.mem_filter.mp hmn
  have h4rest := Finset.mem_filter.mp h5.1
  have h3rest := Finset.mem_filter.mp h4rest.1
  have h2rest := Finset.mem_filter.mp h3rest.1
  have h1rest := Finset.mem_filter.mp h2rest.1
  exact h1rest.1

/-- Exact greatest-owner Möbius sign reversal on one sector-six child. -/
theorem lowOwnerFirstOwnerGreatestOwnerRecursiveContinuation_moebiusWeight_eq_neg_parent
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
        R p sig r) :
    realMoebiusStep m * realMoebiusStep n =
      -(realMoebiusStep
          (squarefreePairPrimeOrderedParent r m n).1 *
        realMoebiusStep
          (squarefreePairPrimeOrderedParent r m n).2) := by
  have hpos :=
    lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber_mem_positive
      hmn
  have hrData :=
    lowOwnerFirstOwnerGreatestOwnerPositivePair_owner_data hp hpos
  have hcross :=
    lowOwnerFirstOwnerGreatestOwnerPositivePair_mem_descendingCross hp hpos
  have hdesc :=
    descendingGreatestOwner_reciprocal_descent hrData.1 hcross
  dsimp only at hdesc
  have hsign := hdesc.2.1
  unfold squarefreePairPrimeOrderedParent
  dsimp only
  split_ifs <;> simpa [mul_comm] using hsign

/-- Stripped ordered parents actually reached by sector six in one fibre. -/
def lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
    R p sig r).image
      (fun mn => squarefreePairPrimeOrderedParent r mn.1 mn.2)

/-- Exact multiplicity of sector-six children which strip to one ordered
parent. -/
def lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentMultiplicity
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (parent : ℕ × ℕ) : ℕ :=
  ((lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
      R p sig r).filter
    (fun mn =>
      squarefreePairPrimeOrderedParent r mn.1 mn.2 = parent)).card

/-- Every reached parent is literally in the lower recursive pair carrier
already identified by #903. -/
theorem lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet_data
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet
        R p sig r) :
    parent ∈ postRootCovarianceRemainderRecursivePairCarrier
      (squareRootEndpoint R / r) := by
  rcases Finset.mem_image.mp hparent with
    ⟨mn, hmn, hmap⟩
  rcases mn with ⟨m, n⟩
  have hdata :=
    lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber_data
      hp hmn
  dsimp only at hdata
  rw [← hmap]
  exact hdata.1

/-- **Exact sector-six parent Fubini with multiplicity.**

The unresolved recursive mass is the negative of the stripped-parent mass,
with every duplicate parent retained through its exact child multiplicity. -/
theorem sum_lowOwnerFirstOwnerGreatestOwnerRecursiveContinuation_moebius_eq_neg_parentMultiplicity
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    (∑ mn ∈
      lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
        R p sig r,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      -∑ parent ∈
        lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet
          R p sig r,
        (lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentMultiplicity
          R p sig r parent : ℝ) *
          (realMoebiusStep parent.1 * realMoebiusStep parent.2) := by
  let S :=
    lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
      R p sig r
  let P : ℕ × ℕ → ℕ × ℕ :=
    fun mn => squarefreePairPrimeOrderedParent r mn.1 mn.2
  let w : ℕ × ℕ → ℝ :=
    fun mn => realMoebiusStep mn.1 * realMoebiusStep mn.2
  have hsign :
      (∑ mn ∈ S, w mn) =
        -(∑ mn ∈ S, w (P mn)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro mn hmn
    rcases mn with ⟨m, n⟩
    exact
      lowOwnerFirstOwnerGreatestOwnerRecursiveContinuation_moebiusWeight_eq_neg_parent
        hp hmn
  have hmaps : ∀ mn ∈ S,
      P mn ∈
        lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet
          R p sig r := by
    intro mn hmn
    exact Finset.mem_image.mpr ⟨mn, hmn, rfl⟩
  have hfiber :
      (∑ parent ∈
        lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet
          R p sig r,
        (lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentMultiplicity
          R p sig r parent : ℝ) * w parent) =
        ∑ mn ∈ S, w (P mn) := by
    calc
      (∑ parent ∈
          lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet
            R p sig r,
          (lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentMultiplicity
            R p sig r parent : ℝ) * w parent) =
        ∑ parent ∈
          lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet
            R p sig r,
          ∑ _mn ∈ S with P _mn = parent, w parent := by
            apply Finset.sum_congr rfl
            intro parent _hparent
            simp [lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentMultiplicity,
              S, P, nsmul_eq_mul]
      _ = ∑ mn ∈ S, w (P mn) :=
        Finset.sum_fiberwise_of_maps_to'
          (s := S)
          (t :=
            lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet
              R p sig r)
          (g := P) hmaps w
  change (∑ mn ∈ S, w mn) =
    -∑ parent ∈
      lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet
        R p sig r,
      (lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentMultiplicity
        R p sig r parent : ℝ) * w parent
  rw [hsign, hfiber]

/-- Run-level stripped-parent mass with exact sector-six multiplicities. -/
def vfMidDyadicGreatestOwnerRecursiveMoebiusParentRunMass
    (A B : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
          ∑ parent ∈
            lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentSet
              R p sig r,
            (lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationParentMultiplicity
              R p sig r parent : ℝ) *
              (realMoebiusStep parent.1 * realMoebiusStep parent.2)

/-- Run-level sector six is exactly the negative stripped-parent ledger.
This is the first genuine reassembly of the recursive remainder before child
blocks are regrouped. -/
theorem vfMidDyadicGreatestOwnerRecursiveMoebiusRunMass_eq_neg_parentRunMass
    (A B : ℕ) :
    lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass
        A B vfMidContinuationMoebiusPairWeight =
      -vfMidDyadicGreatestOwnerRecursiveMoebiusParentRunMass A B := by
  unfold lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass
    lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationFiberMass
    vfMidContinuationMoebiusPairWeight
    vfMidDyadicGreatestOwnerRecursiveMoebiusParentRunMass
  apply Finset.sum_congr rfl
  intro R _hR
  apply Finset.sum_congr rfl
  intro p hpMem
  have hpPrime : p.Prime := (mem_primesUpTo.mp hpMem).1
  apply Finset.sum_congr rfl
  intro sig _hsig
  apply Finset.sum_congr rfl
  intro r _hr
  exact
    sum_lowOwnerFirstOwnerGreatestOwnerRecursiveContinuation_moebius_eq_neg_parentMultiplicity
      hpPrime


end RHLean.Proof
