import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_BOUNDARY_IDENTIFICATION»
import «research.GLOBAL_RETURNED_CORE_STOKES_TERMINAL_FRAME_API»

/-!
# Simultaneous physical-core support of the Stokes clip

The remaining Stokes clip must be studied after the owner chronology has been
removed. This file works directly on the common nonzero Mobius carrier
1 <= n <= X_R.

For one active prime toggle, the already-compiled Stokes identity says that the
finite difference of the simultaneous zero-frequency weight is exactly a
threshold-crossing defect. We package that pointwise defect, define the
physical cores on which some active prime sees a nonzero defect, and prove:

* every squarefree physical core outside that fracture carrier has exact zero
  toggle difference for every active prime;
* the fracture carrier is a literal subset of the square clock and hence has
  cardinality at most R^2.

No magnitude is taken over prime owners and no owner-count factor appears.
The remaining quantitative task is to identify the fully iterated mixed
Boolean-cube coefficient carried by each fractured core.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open StokesTerminalFrame

attribute [local instance] Classical.propDecidable

/-- Exact signed threshold defect seen by toggling prime r at a squarefree
physical core n. -/
def lowOwnerStokesToggleCrossingDefect
    (R r n : ℕ) : ℝ :=
  if r ∣ n then
    -(lowOwnerDaughterCrossingWeight R r (n / r) -
      lowOwnerRootCrossingIndicator R r (n / r))
  else
    lowOwnerDaughterCrossingWeight R r n -
      lowOwnerRootCrossingIndicator R r n

/-- On the actual squarefree physical carrier, the toggle finite difference is
literally the signed threshold defect. -/
theorem lowOwnerZeroFrequencyMobiusWeight_sub_toggle_eq_toggleCrossingDefect
    {R r n : ℕ}
    (hr : r.Prime)
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R) :
    lowOwnerZeroFrequencyMobiusWeight R n -
        lowOwnerZeroFrequencyMobiusWeight R (primeCarrierToggle r n) =
      lowOwnerStokesToggleCrossingDefect R r n := by
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hn with
    ⟨hnSq, _hnPos⟩
  simpa [lowOwnerStokesToggleCrossingDefect] using
    (lowOwnerZeroFrequencyMobiusWeight_sub_toggle_eq_signedCrossing
      (R := R) (r := r) (n := n) hr hnSq)

/-- Endpoint correction omitted by the unextended threshold defect.  It is
present exactly when the Othello toggle leaves the physical Dirichlet clock. -/
def lowOwnerStokesToggleEndpointEscapeCorrection
    (R r n : ℕ) : ℝ :=
  if squareRootEndpoint R < primeCarrierToggle r n then
    lowOwnerZeroFrequencyMobiusWeight R (primeCarrierToggle r n)
  else 0

/-- **Exact physical Stokes toggle dictionary.**

On a physical squarefree core, the toggle difference of the actual
Dirichlet-extended Stokes base coefficient is the previously identified
threshold-crossing defect plus the literal endpoint escape correction.  This
is the missing endpoint term when the toggled corner lies beyond `X_R`. -/
theorem lowOwnerStokesBaseToggleDifference_eq_crossing_add_endpointEscape
    {R r n : ℕ}
    (hr : r.Prime)
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R) :
    lowOwnerStokesToggleDifference r
        (lowOwnerDirichletBaseCoefficient R) n =
      lowOwnerStokesToggleCrossingDefect R r n +
        lowOwnerStokesToggleEndpointEscapeCorrection R r n := by
  have hnIcc := (Finset.mem_filter.mp hn).1
  have hnLe : n ≤ squareRootEndpoint R := (Finset.mem_Icc.mp hnIcc).2
  have hcross :=
    lowOwnerZeroFrequencyMobiusWeight_sub_toggle_eq_toggleCrossingDefect
      (R := R) (r := r) (n := n) hr hn
  unfold lowOwnerStokesToggleDifference lowOwnerDirichletBaseCoefficient
  rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le hnLe]
  by_cases htoggle :
      primeCarrierToggle r n ≤ squareRootEndpoint R
  · rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le htoggle]
    have hnot :
        ¬ squareRootEndpoint R < primeCarrierToggle r n :=
      Nat.not_lt_of_ge htoggle
    simp [lowOwnerStokesToggleEndpointEscapeCorrection, hnot]
    exact hcross
  · have hout :
        squareRootEndpoint R < primeCarrierToggle r n :=
      Nat.lt_of_not_ge htoggle
    rw [lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hout]
    simp [lowOwnerStokesToggleEndpointEscapeCorrection, hout]
    linarith

/-- The genuine physical fracture carrier for the Stokes base coordinate.
Unlike `lowOwnerStokesFracturedCoreCarrier`, this carrier sees Dirichlet
endpoint exits as well as threshold crossings. -/
def lowOwnerStokesPhysicalFracturedCoreCarrier (R : ℕ) : Finset ℕ :=
  (lowOwnerNonzeroMobiusCarrier R).filter fun n =>
    ∃ r ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerStokesToggleDifference r
        (lowOwnerDirichletBaseCoefficient R) n ≠ 0

theorem lowOwnerStokesPhysicalFracturedCoreCarrier_subset_nonzeroCarrier
    (R : ℕ) :
    lowOwnerStokesPhysicalFracturedCoreCarrier R ⊆
      lowOwnerNonzeroMobiusCarrier R := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

theorem lowOwnerStokesPhysicalFracturedCoreCarrier_subset_clock
    (R : ℕ) :
    lowOwnerStokesPhysicalFracturedCoreCarrier R ⊆
      Finset.Icc 1 (squareRootEndpoint R) := by
  intro n hn
  have hnCar :=
    lowOwnerStokesPhysicalFracturedCoreCarrier_subset_nonzeroCarrier R hn
  exact (Finset.mem_filter.mp hnCar).1

/-- Off the corrected fracture carrier, the actual Dirichlet Stokes toggle
difference vanishes for every active physical prime. -/
theorem physical_clip_toggle_difference_eq_zero_of_not_fractured
    {R r n : ℕ}
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hr : r ∈ primesUpTo (squareRootEndpoint R))
    (hnfract : n ∉ lowOwnerStokesPhysicalFracturedCoreCarrier R) :
    lowOwnerStokesToggleDifference r
        (lowOwnerDirichletBaseCoefficient R) n = 0 := by
  by_contra hne
  apply hnfract
  exact Finset.mem_filter.mpr
    ⟨hn, ⟨r, hr, hne⟩⟩

/-- The corrected physical fracture support is still bounded by the square
clock, with no owner multiplicity. -/
theorem card_lowOwnerStokesPhysicalFracturedCoreCarrier_le_R_sq
    (R : ℕ) :
    (lowOwnerStokesPhysicalFracturedCoreCarrier R).card ≤ R ^ 2 := by
  have hcard :=
    Finset.card_le_card
      (lowOwnerStokesPhysicalFracturedCoreCarrier_subset_clock R)
  have hendpoint :
      (lowOwnerStokesPhysicalFracturedCoreCarrier R).card ≤
        squareRootEndpoint R := by
    simpa [Nat.card_Icc] using hcard
  exact hendpoint.trans (by
    unfold squareRootEndpoint
    omega)

/-- Physical squarefree cores at which at least one active prime toggle sees a
nonzero threshold defect.  This is the threshold-only carrier retained for the
exact crossing dictionary above; the actual Stokes carrier is
`lowOwnerStokesPhysicalFracturedCoreCarrier`. -/
def lowOwnerStokesFracturedCoreCarrier (R : ℕ) : Finset ℕ :=
  (lowOwnerNonzeroMobiusCarrier R).filter fun n =>
    ∃ r ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerStokesToggleCrossingDefect R r n ≠ 0

theorem lowOwnerStokesFracturedCoreCarrier_subset_nonzeroCarrier
    (R : ℕ) :
    lowOwnerStokesFracturedCoreCarrier R ⊆
      lowOwnerNonzeroMobiusCarrier R := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

theorem lowOwnerStokesFracturedCoreCarrier_subset_clock
    (R : ℕ) :
    lowOwnerStokesFracturedCoreCarrier R ⊆
      Finset.Icc 1 (squareRootEndpoint R) := by
  intro n hn
  have hnCar :=
    lowOwnerStokesFracturedCoreCarrier_subset_nonzeroCarrier R hn
  exact (Finset.mem_filter.mp hnCar).1

theorem mem_lowOwnerStokesFracturedCoreCarrier_iff
    {R n : ℕ} :
    n ∈ lowOwnerStokesFracturedCoreCarrier R ↔
      n ∈ lowOwnerNonzeroMobiusCarrier R ∧
        ∃ r ∈ primesUpTo (squareRootEndpoint R),
          lowOwnerStokesToggleCrossingDefect R r n ≠ 0 := by
  simp [lowOwnerStokesFracturedCoreCarrier]

/-- Exact interior annihilation at first finite-difference level. -/
theorem clip_toggle_difference_eq_zero_of_not_fractured
    {R r n : ℕ}
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hr : r ∈ primesUpTo (squareRootEndpoint R))
    (hnfract : n ∉ lowOwnerStokesFracturedCoreCarrier R) :
    lowOwnerZeroFrequencyMobiusWeight R n -
        lowOwnerZeroFrequencyMobiusWeight R (primeCarrierToggle r n) = 0 := by
  have hrPrime : r.Prime := (mem_primesUpTo.mp hr).1
  rw [lowOwnerZeroFrequencyMobiusWeight_sub_toggle_eq_toggleCrossingDefect
    hrPrime hn]
  by_contra hne
  apply hnfract
  exact Finset.mem_filter.mpr
    ⟨hn, ⟨r, hr, hne⟩⟩

/-- Equivalently, every active prime threshold defect vanishes off the fracture
carrier. -/
theorem toggleCrossingDefect_eq_zero_of_not_fractured
    {R r n : ℕ}
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hr : r ∈ primesUpTo (squareRootEndpoint R))
    (hnfract : n ∉ lowOwnerStokesFracturedCoreCarrier R) :
    lowOwnerStokesToggleCrossingDefect R r n = 0 := by
  have hrPrime : r.Prime := (mem_primesUpTo.mp hr).1
  have h :=
    clip_toggle_difference_eq_zero_of_not_fractured
      (R := R) (r := r) (n := n) hn hr hnfract
  rwa [lowOwnerZeroFrequencyMobiusWeight_sub_toggle_eq_toggleCrossingDefect
    hrPrime hn] at h

/-- The sum of all active-prime first differences at one unfractured physical
core is exactly zero. -/
theorem sum_toggleCrossingDefect_eq_zero_of_not_fractured
    {R n : ℕ}
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hnfract : n ∉ lowOwnerStokesFracturedCoreCarrier R) :
    (∑ r ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerStokesToggleCrossingDefect R r n) = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  exact toggleCrossingDefect_eq_zero_of_not_fractured hn hr hnfract

/-- The geometric fracture support is automatically at most the size of the
square clock. -/
theorem card_lowOwnerStokesFracturedCoreCarrier_le_endpoint
    (R : ℕ) :
    (lowOwnerStokesFracturedCoreCarrier R).card ≤ squareRootEndpoint R := by
  have hcard :=
    Finset.card_le_card
      (lowOwnerStokesFracturedCoreCarrier_subset_clock R)
  simpa [Nat.card_Icc] using hcard

/-- Boundary area bound. Since X_R = R^2 - 1, the simultaneous fracture
carrier contains at most R^2 physical cores. -/
theorem card_fractured_clip_boundary_le_R_sq
    (R : ℕ) :
    (lowOwnerStokesFracturedCoreCarrier R).card ≤ R ^ 2 := by
  exact (card_lowOwnerStokesFracturedCoreCarrier_le_endpoint R).trans
    (by
      unfold squareRootEndpoint
      omega)

/-- Every fractured site is squarefree and positive. -/
theorem lowOwnerStokesFracturedCoreCarrier_squarefree_pos
    {R n : ℕ}
    (hn : n ∈ lowOwnerStokesFracturedCoreCarrier R) :
    Squarefree n ∧ 0 < n := by
  exact lowOwnerNonzeroMobiusCarrier_squarefree_pos
    (lowOwnerStokesFracturedCoreCarrier_subset_nonzeroCarrier R hn)


/-! ## DAG collapse to the two actual Stokes toggle coordinates -/

/-- **Nonterminal schedules start with the global top two physical primes.**

For an active first owner other than the largest and second-largest physical
owners, the canonical descending Stokes schedule begins with exactly those two
owners.  Thus, after the terminal classification, no third prime coordinate can
enter the physical clip boundary before the two-step interior has already
vanished. -/
theorem lowOwnerCanonicalStokesSchedule_eq_top_second_cons_of_lower_owner
    {R p : ℕ} (hR : 56 ≤ R)
    (hpMem : p ∈ primesUpTo (squareRootEndpoint R))
    (hpTop : p ≠ topPrime R hR)
    (hpSecond : p ≠ secondPrime R hR) :
    ∃ rest : List ℕ,
      lowOwnerFirstOwnerCanonicalStokesSchedule R p =
        topPrime R hR :: secondPrime R hR :: rest := by
  let t := topPrime R hR
  let u := secondPrime R hR
  have htMem : t ∈ primesUpTo (squareRootEndpoint R) := by
    simpa [t] using topPrime_mem hR
  have huErase :
      u ∈ (primesUpTo (squareRootEndpoint R)).erase t := by
    simpa [u, t] using secondPrime_mem_erase hR
  have huMem : u ∈ primesUpTo (squareRootEndpoint R) :=
    (Finset.mem_erase.mp huErase).2
  have hut : u ≠ t := (Finset.mem_erase.mp huErase).1
  have hptLe : p ≤ t := by
    simpa [t] using
      Finset.le_max' (primesUpTo (squareRootEndpoint R)) p hpMem
  have hpt : p < t := by
    have hne : p ≠ t := by simpa [t] using hpTop
    omega
  have hpErase :
      p ∈ (primesUpTo (squareRootEndpoint R)).erase t := by
    exact Finset.mem_erase.mpr ⟨by simpa [t] using hpTop, hpMem⟩
  have hpuLe : p ≤ u := by
    simpa [u, t] using
      Finset.le_max'
        ((primesUpTo (squareRootEndpoint R)).erase t) p hpErase
  have hpu : p < u := by
    have hne : p ≠ u := by simpa [u] using hpSecond
    omega
  have htFull :
      t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2 htMem
  have huFull :
      u ∈ squareRootCanonicalRoughDescendingPrimeSchedule R := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2 huMem
  have htSched :
      t ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using
      (show t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ p < t
        from ⟨htFull, hpt⟩)
  have huSched :
      u ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using
      (show u ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ p < u
        from ⟨huFull, hpu⟩)
  have hmem :
      ∀ q ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p,
        q ∈ primesUpTo (squareRootEndpoint R) := by
    intro q hq
    have hqData :
        q ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ p < q := by
      simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using hq
    unfold squareRootCanonicalRoughDescendingPrimeSchedule at hqData
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).1 hqData.1
  have hsorted := lowOwnerFirstOwnerCanonicalStokesSchedule_sorted R p
  have hnodup := lowOwnerFirstOwnerCanonicalStokesSchedule_nodup R p
  generalize hsched :
      lowOwnerFirstOwnerCanonicalStokesSchedule R p = ps at
      htSched huSched hmem hsorted hnodup
  cases ps with
  | nil =>
      simp at htSched
  | cons a tail =>
      have haMem : a ∈ primesUpTo (squareRootEndpoint R) :=
        hmem a (by simp)
      have haLeT : a ≤ t :=
        Finset.le_max' (primesUpTo (squareRootEndpoint R)) a haMem
      have haGeT : t ≤ a := by
        simp only [List.mem_cons] at htSched
        rcases htSched with hat | htTail
        · simpa [hat]
        · exact (List.pairwise_cons.mp hsorted).1 t htTail
      have ha : a = t := by omega
      subst a
      have htailNodup : (t :: tail).Nodup := hnodup
      have htNotTail : t ∉ tail := (List.nodup_cons.mp htailNodup).1
      have huTail : u ∈ tail := by
        simp only [List.mem_cons] at huSched
        rcases huSched with hutEq | huTail
        · exact False.elim (hut hutEq)
        · exact huTail
      cases tail with
      | nil =>
          simp at huTail
      | cons b rest =>
          have hbMem : b ∈ primesUpTo (squareRootEndpoint R) :=
            hmem b (by simp)
          have hbNeT : b ≠ t := by
            intro hbt
            apply htNotTail
            simp [hbt]
          have hbErase :
              b ∈ (primesUpTo (squareRootEndpoint R)).erase t :=
            Finset.mem_erase.mpr ⟨hbNeT, hbMem⟩
          have hbLeU : b ≤ u := by
            simpa [u, t] using
              Finset.le_max'
                ((primesUpTo (squareRootEndpoint R)).erase t) b hbErase
          have htailSorted : List.Sorted (fun x y : ℕ => x ≥ y) (b :: rest) :=
            (List.pairwise_cons.mp hsorted).2
          have hbGeU : u ≤ b := by
            simp only [List.mem_cons] at huTail
            rcases huTail with hub | huRest
            · simpa [hub]
            · exact (List.pairwise_cons.mp htailSorted).1 u huRest
          have hb : b = u := by omega
          subst b
          exact ⟨rest, rfl⟩


/-- Exact local clip normal form after the DAG collapse to the two largest
physical owner coordinates. -/
def lowOwnerFirstOwnerTopTwoStokesClipNormalForm
    (R : ℕ) (hR : 56 ≤ R) (p : ℕ) (sig : Finset ℕ) : ℝ :=
  let C := lowOwnerFirstOwnerSignedCellPairCarrier R p sig
  let f := lowOwnerFirstOwnerDirichletPolarizationScalar R p
  if p = topPrime R hR then
    0
  else
    pairWeightedStokesBoundaryStep (topPrime R hR) C f +
      (if p = secondPrime R hR then
        0
      else
        (1 / 4 : ℝ) *
          pairWeightedStokesBoundaryStep (secondPrime R hR)
            (pairPrimeTwoCoordinateInterior (topPrime R hR) C)
            (pairPrimeMixedDifference (topPrime R hR) f))

/-- **Exact local top-two reduction.**

Every physical first-owner cell has only the two global top prime coordinates
in its clip ledger.  The largest first owner has empty schedule; the
second-largest has only the top coordinate; every lower first owner starts with
the top two coordinates, after which the complete two-coordinate interior is
already empty. -/
theorem lowOwnerFirstOwnerCanonicalStokesClipBoundary_eq_topTwoNormalForm
    {R p : ℕ} (hR : 56 ≤ R)
    (hpMem : p ∈ primesUpTo (squareRootEndpoint R))
    (sig : Finset ℕ) :
    lowOwnerFirstOwnerCanonicalStokesClipBoundary R p sig =
      lowOwnerFirstOwnerTopTwoStokesClipNormalForm R hR p sig := by
  by_cases hpTop : p = topPrime R hR
  · subst p
    simp [lowOwnerFirstOwnerTopTwoStokesClipNormalForm,
      lowOwnerFirstOwnerCanonicalStokesClipBoundary,
      topPrime_schedule_eq_nil hR,
      lowOwnerFirstOwnerPhysicalStokesBoundaryFrom]
  · by_cases hpSecond : p = secondPrime R hR
    · subst p
      rw [← lowOwnerFirstOwnerCanonicalStokesBoundary_eq_clipBoundary]
      unfold lowOwnerFirstOwnerCanonicalStokesBoundary
      rw [secondPrime_schedule_eq_single_top hR]
      simp [iteratedPairWeightedStokesBoundary,
        lowOwnerFirstOwnerTopTwoStokesClipNormalForm,
        hpTop]
    · obtain ⟨rest, hrest⟩ :=
        lowOwnerCanonicalStokesSchedule_eq_top_second_cons_of_lower_owner
          hR hpMem hpTop hpSecond
      have htwo :=
        lowOwnerFirstOwnerCanonicalStokesClipBoundary_eq_twoSteps_of_twoOwners
          (R := R) (p := p)
          (q := topPrime R hR) (s := secondPrime R hR)
          (sig := sig) (rest := rest) (by omega) hrest
      simpa [lowOwnerFirstOwnerTopTwoStokesClipNormalForm,
        hpTop, hpSecond] using htwo

/-- Globally assembled top-two physical clip normal form. -/
def lowOwnerCanonicalTopTwoStokesClipNormalForm
    (R : ℕ) (hR : 56 ≤ R) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerTopTwoStokesClipNormalForm R hR p sig

/-- **Global DAG reduction.**  The complete physical Stokes clip is exactly the
globally assembled two-toggle normal form.  No ownerwise norm, absolute value,
or prime-counting multiplicity is introduced. -/
theorem lowOwnerCanonicalSignedStokesClipBoundary_eq_topTwoNormalForm
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesClipBoundary R =
      lowOwnerCanonicalTopTwoStokesClipNormalForm R hR := by
  unfold lowOwnerCanonicalSignedStokesClipBoundary
    lowOwnerCanonicalTopTwoStokesClipNormalForm
  apply Finset.sum_congr rfl
  intro p hpMem
  apply Finset.sum_congr rfl
  intro sig _hsig
  exact
    lowOwnerFirstOwnerCanonicalStokesClipBoundary_eq_topTwoNormalForm
      hR hpMem sig

/-- The genuinely remaining quantitative statement after exact DAG reduction:
bound one globally assembled two-toggle signed ledger at root scale. -/
def LowOwnerTopTwoStokesClipRootBound (A : ℝ) : Prop :=
  ∀ (R : ℕ) (hR : 56 ≤ R),
    lowOwnerCanonicalTopTwoStokesClipNormalForm R hR ≤
      A * (R : ℝ) ^ 2

/-- A root bound on the top-two normal form is literally a root bound on the
physical clip; no additional arithmetic estimate is needed to pass between
them. -/
theorem lowOwnerCanonicalSignedStokesClipBoundary_le_root_sq_of_topTwoBound
    {A : ℝ} (hA : LowOwnerTopTwoStokesClipRootBound A)
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesClipBoundary R ≤
      A * (R : ℝ) ^ 2 := by
  rw [lowOwnerCanonicalSignedStokesClipBoundary_eq_topTwoNormalForm hR]
  exact hA R hR

end RHLean.Proof
