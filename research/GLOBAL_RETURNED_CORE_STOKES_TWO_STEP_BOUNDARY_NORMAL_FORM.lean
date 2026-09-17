import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_TERMINAL_CLASSIFICATION»

/-!
# Two-step normal form of the final signed Stokes boundary

The terminal-classification theorem already proves that the first canonical
remaining owner lies above half the physical clock and that the complete
interior after the first two distinct owners is empty.

This file records the corresponding statement for the accumulated boundary,
not just the residual: once the second interior is empty, every later boundary
step is literally zero.  Hence a cell with at least two remaining owners has an
exact boundary consisting of only

  step(q) + 1/4 * step(s after q).

No estimate is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- An empty carrier produces no later Stokes boundary, for any remaining
schedule and scalar weight. -/
theorem iteratedPairWeightedStokesBoundary_empty :
    ∀ (ps : List ℕ) (f : ℕ × ℕ → ℝ),
      iteratedPairWeightedStokesBoundary ps ∅ f = 0 := by
  intro ps
  induction ps with
  | nil =>
      intro f
      simp [iteratedPairWeightedStokesBoundary]
  | cons q qs ih =>
      intro f
      simp [iteratedPairWeightedStokesBoundary,
        pairWeightedStokesBoundaryStep,
        pairPrimeLeftEscapePart, pairPrimeRightEscapeAfterLeft,
        pairPrimeLeftInteriorPart, weightedOthelloEscapePart,
        weightedOthelloInteriorPart, ih]

/-- **Exact two-step boundary normal form.**

If the canonical remaining-owner schedule begins `q,s`, then for `R ≥ 2` the
entire canonical cell boundary is the first boundary step plus one quarter of
the second boundary step.  Every later term is zero by exact carrier emptiness. -/
theorem lowOwnerFirstOwnerCanonicalStokesBoundary_eq_twoSteps_of_twoOwners
    {R p q s : ℕ} {sig : Finset ℕ} {rest : List ℕ}
    (hR : 2 ≤ R)
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: s :: rest) :
    lowOwnerFirstOwnerCanonicalStokesBoundary R p sig =
      pairWeightedStokesBoundaryStep q
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p) +
      (1 / 4 : ℝ) *
        pairWeightedStokesBoundaryStep s
          (pairPrimeTwoCoordinateInterior q
            (lowOwnerFirstOwnerSignedCellPairCarrier R p sig))
          (pairPrimeMixedDifference q
            (lowOwnerFirstOwnerDirichletPolarizationScalar R p)) := by
  have hqMem : q ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    rw [hps]
    simp
  have hsMem : s ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    rw [hps]
    simp
  have hqPrime := lowOwnerFirstOwnerCanonicalStokesSchedule_prime R p q hqMem
  have hsPrime := lowOwnerFirstOwnerCanonicalStokesSchedule_prime R p s hsMem
  have hqTop :=
    lowOwnerFirstOwnerCanonicalStokesSchedule_head_gt_half
      hR (show lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: (s :: rest)
        from hps)
  have hqne := lowOwnerFirstOwnerCanonicalStokesSchedule_first_two_ne hps
  have hcarrier :=
    lowOwnerFirstOwner_twoPrimePairInterior_eq_empty_of_top
      (R := R) (p := p) (q := q) (s := s) (sig := sig)
      hqPrime hsPrime hqne hqTop
  unfold lowOwnerFirstOwnerCanonicalStokesBoundary
  rw [hps]
  simp only [iteratedPairWeightedStokesBoundary]
  rw [hcarrier, iteratedPairWeightedStokesBoundary_empty]
  ring

/-- The physically identified clip ledger has the same exact two-step form. -/
theorem lowOwnerFirstOwnerCanonicalStokesClipBoundary_eq_twoSteps_of_twoOwners
    {R p q s : ℕ} {sig : Finset ℕ} {rest : List ℕ}
    (hR : 2 ≤ R)
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: s :: rest) :
    lowOwnerFirstOwnerCanonicalStokesClipBoundary R p sig =
      pairWeightedStokesBoundaryStep q
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p) +
      (1 / 4 : ℝ) *
        pairWeightedStokesBoundaryStep s
          (pairPrimeTwoCoordinateInterior q
            (lowOwnerFirstOwnerSignedCellPairCarrier R p sig))
          (pairPrimeMixedDifference q
            (lowOwnerFirstOwnerDirichletPolarizationScalar R p)) := by
  rw [← lowOwnerFirstOwnerCanonicalStokesBoundary_eq_clipBoundary]
  exact lowOwnerFirstOwnerCanonicalStokesBoundary_eq_twoSteps_of_twoOwners
    hR hps

/-- For two or more remaining owners the top-terminal contribution itself is
zero, so the full cell contribution is exactly the same two boundary steps. -/
theorem lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary_eq_zero_of_twoOwners
    {R p q s : ℕ} {sig : Finset ℕ} {rest : List ℕ}
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: s :: rest) :
    lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig = 0 := by
  simp [lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary, hps]

/-! ## Exact top-half orbit collapse

The first remaining owner in every nonempty canonical schedule is above half of
the physical clock.  On such a coordinate there is no large complete orbit to
estimate: a one-dimensional interior point can only be `1` or the top prime
itself.  The pair interior therefore contains at most four states.
-/

/-- **Top-half one-coordinate orbit collapse.**  On any positive carrier
bounded by `X`, a prime coordinate above `X/2` can have interior states only at
`1` and at the prime itself. -/
theorem primeInteriorPart_subset_one_insert_prime_of_top
    {B : Finset ℕ} {X q : ℕ}
    (hB : ∀ n ∈ B, 0 < n ∧ n ≤ X)
    (hq : q.Prime) (hqTop : X / 2 < q) :
    primeInteriorPart q B ⊆ ({1, q} : Finset ℕ) := by
  intro n hn
  rcases mem_primeInteriorPart.mp hn with ⟨hnB, hmateB⟩
  have hnData := hB n hnB
  have h2q : X < 2 * q := by omega
  by_cases hqn : q ∣ n
  · rcases hqn with ⟨k, hk⟩
    have hkPos : 0 < k := by
      by_contra hnot
      have hk0 : k = 0 := by omega
      rw [hk0] at hk
      simp at hk
      omega
    have hqkLt : q * k < q * 2 := by
      have h : n < 2 * q := hnData.2.trans_lt h2q
      rw [hk] at h
      simpa [Nat.mul_comm] using h
    have hkLt : k < 2 :=
      (Nat.mul_lt_mul_left hq.pos).mp hqkLt
    have hk1 : k = 1 := by omega
    rw [hk, hk1]
    simp
  · rw [primeCarrierToggle_of_not_dvd hqn] at hmateB
    have hmateData := hB (n * q) hmateB
    have hqnLt : q * n < q * 2 := by
      have h : n * q < 2 * q := hmateData.2.trans_lt h2q
      simpa [Nat.mul_comm] using h
    have hnLt : n < 2 :=
      (Nat.mul_lt_mul_left hq.pos).mp hqnLt
    have hn1 : n = 1 := by omega
    rw [hn1]
    simp

/-- The top-half collapse on the literal first-owner base carrier. -/
theorem lowOwnerFirstOwner_topPrimeInterior_subset_one_insert_prime
    {R p q : ℕ} {sig : Finset ℕ}
    (hq : q.Prime)
    (hqTop : squareRootEndpoint R / 2 < q) :
    primeInteriorPart q (lowOwnerFirstOwnerBaseFiber R p sig) ⊆
      ({1, q} : Finset ℕ) := by
  exact primeInteriorPart_subset_one_insert_prime_of_top
    (fun n hn => lowOwnerFirstOwnerBaseFiber_pos_le_endpoint hn)
    hq hqTop

/-- Consequently one top-half first-owner cell has at most two surviving
one-coordinate states. -/
theorem card_lowOwnerFirstOwner_topPrimeInterior_le_two
    {R p q : ℕ} {sig : Finset ℕ}
    (hq : q.Prime)
    (hqTop : squareRootEndpoint R / 2 < q) :
    (primeInteriorPart q (lowOwnerFirstOwnerBaseFiber R p sig)).card ≤ 2 := by
  have hsub :=
    lowOwnerFirstOwner_topPrimeInterior_subset_one_insert_prime
      (R := R) (p := p) (q := q) (sig := sig) hq hqTop
  have htwo : (({1, q} : Finset ℕ).card) ≤ 2 := by
    have h := Finset.card_insert_le 1 ({q} : Finset ℕ)
    simpa using h
  exact (Finset.card_le_card hsub).trans htwo

/-- **Top-half pair collapse.**  After the first canonical Stokes peel, the
complete two-coordinate interior of any first-owner/signature cell has at most
four states. -/
theorem card_lowOwnerFirstOwner_topPrimePairInterior_le_four
    {R p q : ℕ} {sig : Finset ℕ}
    (hq : q.Prime)
    (hqTop : squareRootEndpoint R / 2 < q) :
    (pairPrimeTwoCoordinateInterior q
      (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)).card ≤ 4 := by
  unfold lowOwnerFirstOwnerSignedCellPairCarrier
  rw [pairPrimeTwoCoordinateInterior_product]
  let A := primeInteriorPart q (lowOwnerFirstOwnerBaseFiber R p sig)
  have hcard : A.card ≤ 2 := by
    dsimp [A]
    exact card_lowOwnerFirstOwner_topPrimeInterior_le_two
      (R := R) (p := p) (q := q) (sig := sig) hq hqTop
  calc
    (A.product A).card = A.card * A.card := Finset.card_product _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul hcard hcard
    _ = 4 := by norm_num

end RHLean.Proof
