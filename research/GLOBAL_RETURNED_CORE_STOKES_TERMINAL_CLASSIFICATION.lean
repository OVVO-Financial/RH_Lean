import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_BOUNDARY_IDENTIFICATION»

/-!
# Exact classification of the terminal signed Stokes residual

This file is the second algebraic layer of the signed-first route.

There is still no norm, square, Carleson estimate, Schur estimate, inherited
energy, `2/9`, or `4/9` argument here.

The key geometric fact is exact.  If a finite physical carrier lies in
`[1,X]`, and it is complete under two distinct prime toggles `q,s`, then one of
the four Boolean corners is divisible by `q*s`.  Hence no such complete
2-face can exist when `X < q*s`.  In particular, if `q > X/2` and `s` is any
distinct prime, the two-prime complete interior is empty.

The canonical Stokes schedule is all primes above the first owner `p`, in the
repository's descending chronology.  By Bertrand its first entry, whenever the
schedule is nonempty, lies above `X/2`.  Consequently every cell whose schedule
contains at least two owners has zero terminal residual *by exact carrier
emptiness*.  The only surviving terminal strata are the schedule lengths zero
and one.  They are retained as a signed terminal-boundary ledger; they are not
estimated or declared small.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A member of a first-owner base cell is positive and lies on the physical
clock. -/
theorem lowOwnerFirstOwnerBaseFiber_pos_le_endpoint
    {R p n : ℕ} {sig : Finset ℕ}
    (hn : n ∈ lowOwnerFirstOwnerBaseFiber R p sig) :
    0 < n ∧ n ≤ squareRootEndpoint R := by
  have hnCar := (Finset.mem_filter.mp hn).1
  have hnIcc := (Finset.mem_filter.mp hnCar).1
  exact ⟨(Finset.mem_Icc.mp hnIcc).1, (Finset.mem_Icc.mp hnIcc).2⟩

/-- **Two-prime complete-face obstruction.**

For any positive finite carrier bounded by `X`, a complete `q`-then-`s`
interior for two distinct primes forces a carrier point divisible by `q*s`.
Therefore the complete two-prime interior is empty whenever `X < q*s`.

This is a carrier identity.  No weight or magnitude is used. -/
theorem primeInteriorPart_primeInteriorPart_eq_empty_of_product_gt
    {B : Finset ℕ} {X q s : ℕ}
    (hB : ∀ n ∈ B, 0 < n ∧ n ≤ X)
    (hq : q.Prime) (hs : s.Prime) (hqs : q ≠ s)
    (hprod : X < q * s) :
    primeInteriorPart s (primeInteriorPart q B) = ∅ := by
  ext n
  simp only [Finset.mem_empty, iff_false]
  intro hn
  have hnOuter := mem_primeInteriorPart.mp hn
  have hnInner := mem_primeInteriorPart.mp hnOuter.1
  have hsInner := mem_primeInteriorPart.mp hnOuter.2
  have hcop : q.Coprime s := by
    rw [hq.coprime_iff_not_dvd]
    intro hqd
    exact hqs ((Nat.prime_dvd_prime_iff_eq hq hs).mp hqd)
  have hnoCorner : ∀ {m : ℕ}, m ∈ B → q * s ∣ m → False := by
    intro m hm hdvd
    have hmData := hB m hm
    have hle : q * s ≤ m := Nat.le_of_dvd hmData.1 hdvd
    omega
  by_cases hqn : q ∣ n
  · by_cases hsn : s ∣ n
    · exact hnoCorner hnInner.1
        (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hqn hsn)
    · have hmB : n * s ∈ B := by
        have h := hsInner.1
        rw [primeCarrierToggle_of_not_dvd hsn] at h
        exact h
      rcases hqn with ⟨k, hk⟩
      apply hnoCorner hmB
      refine ⟨k, ?_⟩
      rw [hk]
      ring
  · by_cases hsn : s ∣ n
    · have hmB : n * q ∈ B := by
        have h := hnInner.2
        rw [primeCarrierToggle_of_not_dvd hqn] at h
        exact h
      rcases hsn with ⟨k, hk⟩
      apply hnoCorner hmB
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    · have hqns : ¬ q ∣ n * s := by
        intro hdiv
        rcases hq.dvd_mul.mp hdiv with hdiv | hdiv
        · exact hqn hdiv
        · exact hqs ((Nat.prime_dvd_prime_iff_eq hq hs).mp hdiv)
      have hmB : (n * s) * q ∈ B := by
        have h := hsInner.2
        rw [primeCarrierToggle_of_not_dvd hsn] at h
        rw [primeCarrierToggle_of_not_dvd hqns] at h
        exact h
      apply hnoCorner hmB
      refine ⟨n, ?_⟩
      ring

/-- On an actual first-owner cell, any two distinct primes whose product exceeds
the clock endpoint have no complete two-prime interior. -/
theorem lowOwnerFirstOwner_twoPrimeInterior_eq_empty_of_product_gt
    {R p q s : ℕ} {sig : Finset ℕ}
    (hq : q.Prime) (hs : s.Prime) (hqs : q ≠ s)
    (hprod : squareRootEndpoint R < q * s) :
    primeInteriorPart s
        (primeInteriorPart q (lowOwnerFirstOwnerBaseFiber R p sig)) = ∅ := by
  exact primeInteriorPart_primeInteriorPart_eq_empty_of_product_gt
    (fun n hn => lowOwnerFirstOwnerBaseFiber_pos_le_endpoint hn)
    hq hs hqs hprod

/-- The `> X/2` form requested by the terminal Stokes geometry. -/
theorem lowOwnerFirstOwner_twoPrimeInterior_eq_empty_of_top
    {R p q s : ℕ} {sig : Finset ℕ}
    (hq : q.Prime) (hs : s.Prime) (hqs : q ≠ s)
    (hqTop : squareRootEndpoint R / 2 < q) :
    primeInteriorPart s
        (primeInteriorPart q (lowOwnerFirstOwnerBaseFiber R p sig)) = ∅ := by
  have h2q : squareRootEndpoint R < 2 * q := by omega
  have h2le : 2 * q ≤ s * q := Nat.mul_le_mul_right q hs.two_le
  have hprod : squareRootEndpoint R < q * s := by
    calc
      squareRootEndpoint R < 2 * q := h2q
      _ ≤ s * q := h2le
      _ = q * s := by ring
  exact lowOwnerFirstOwner_twoPrimeInterior_eq_empty_of_product_gt
    hq hs hqs hprod

/-- The same obstruction on the actual signed pair carrier: after two complete
pair-coordinate peels the carrier is empty. -/
theorem lowOwnerFirstOwner_twoPrimePairInterior_eq_empty_of_top
    {R p q s : ℕ} {sig : Finset ℕ}
    (hq : q.Prime) (hs : s.Prime) (hqs : q ≠ s)
    (hqTop : squareRootEndpoint R / 2 < q) :
    pairPrimeTwoCoordinateInterior s
        (pairPrimeTwoCoordinateInterior q
          (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)) = ∅ := by
  unfold lowOwnerFirstOwnerSignedCellPairCarrier
  rw [pairPrimeTwoCoordinateInterior_product]
  rw [pairPrimeTwoCoordinateInterior_product]
  rw [lowOwnerFirstOwner_twoPrimeInterior_eq_empty_of_top
    (sig := sig) hq hs hqs hqTop]
  simp

@[simp] theorem pairPrimeTwoCoordinateInterior_empty (q : ℕ) :
    pairPrimeTwoCoordinateInterior q (∅ : Finset (ℕ × ℕ)) = ∅ := by
  ext mn
  simp [pairPrimeTwoCoordinateInterior, pairPrimeLeftInteriorPart,
    weightedOthelloInteriorPart]

/-- Once the pair carrier is empty, every later exact Stokes residual is zero. -/
theorem iteratedPairWeightedStokesResidual_empty :
    ∀ (ps : List ℕ) (f : ℕ × ℕ → ℝ),
      iteratedPairWeightedStokesResidual ps ∅ f = 0 := by
  intro ps
  induction ps with
  | nil =>
      intro f
      simp [iteratedPairWeightedStokesResidual, pairWeightedStokesMass]
  | cons q qs ih =>
      intro f
      simp [iteratedPairWeightedStokesResidual,
        pairPrimeTwoCoordinateInterior_empty, ih]

/-- The canonical cell schedule remains descending after filtering to owners
larger than the first owner. -/
theorem lowOwnerFirstOwnerCanonicalStokesSchedule_sorted
    (R p : ℕ) :
    List.Sorted (fun a b : ℕ => a ≥ b)
      (lowOwnerFirstOwnerCanonicalStokesSchedule R p) := by
  have hfull :
      List.Sorted (fun a b : ℕ => a ≥ b)
        (squareRootCanonicalRoughDescendingPrimeSchedule R) := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule
    exact Finset.sort_sorted (· ≥ ·) _
  unfold lowOwnerFirstOwnerCanonicalStokesSchedule
  exact hfull.filter _

/-- The canonical filtered schedule has no duplicate prime coordinates. -/
theorem lowOwnerFirstOwnerCanonicalStokesSchedule_nodup
    (R p : ℕ) :
    (lowOwnerFirstOwnerCanonicalStokesSchedule R p).Nodup := by
  have hfull :
      (squareRootCanonicalRoughDescendingPrimeSchedule R).Nodup := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule
    exact Finset.sort_nodup _ _
  unfold lowOwnerFirstOwnerCanonicalStokesSchedule
  exact hfull.filter _

/-- **The first canonical remaining owner is a top-half prime.**

For `R ≥ 2`, Bertrand supplies a prime in `(X_R/2,X_R]`.  If the first owner
`p` is below that prime, descending chronology puts the schedule head above it;
if `p` is already above it, every remaining owner is above it. -/
theorem lowOwnerFirstOwnerCanonicalStokesSchedule_head_gt_half
    {R p q : ℕ} {qs : List ℕ}
    (hR : 2 ≤ R)
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: qs) :
    squareRootEndpoint R / 2 < q := by
  have hpow : R ^ 2 = R * R := by ring
  have hge : 2 * 2 ≤ R * R := Nat.mul_le_mul hR hR
  have hX : 3 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hhalf : squareRootEndpoint R / 2 ≠ 0 := by omega
  obtain ⟨t, htPrime, htLow, htHigh⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (squareRootEndpoint R / 2) hhalf
  have htX : t ≤ squareRootEndpoint R := by omega
  have hqMem : q ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    rw [hps]
    simp
  have hqData :
      q ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ p < q := by
    simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using hqMem
  by_cases hpt : p < t
  · have htFull : t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R := by
      unfold squareRootCanonicalRoughDescendingPrimeSchedule
      exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2
        (mem_primesUpTo_of_prime_le htPrime htX)
    have htSched : t ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
      have htData :
          t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ p < t :=
        ⟨htFull, hpt⟩
      simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using htData
    have hsorted := lowOwnerFirstOwnerCanonicalStokesSchedule_sorted R p
    rw [hps] at hsorted htSched
    simp only [List.mem_cons] at htSched
    rcases htSched with rfl | htTail
    · exact htLow
    · have hqt : q ≥ t := (List.pairwise_cons.mp hsorted).1 t htTail
      omega
  · have htp : t ≤ p := Nat.le_of_not_gt hpt
    omega

/-- The first two entries of a canonical schedule are distinct. -/
theorem lowOwnerFirstOwnerCanonicalStokesSchedule_first_two_ne
    {R p q s : ℕ} {rest : List ℕ}
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: s :: rest) :
    q ≠ s := by
  have hnodup := lowOwnerFirstOwnerCanonicalStokesSchedule_nodup R p
  rw [hps] at hnodup
  intro hqs
  subst s
  exact (List.nodup_cons.mp hnodup).1 (by simp)

/-- **Terminal bulk vanishes once two owners remain.**

This is not an estimate: after the first two canonical peels the actual pair
carrier is empty because the first prime is above half the clock and the second
prime is distinct. -/
theorem lowOwnerFirstOwnerCanonicalStokesResidual_eq_zero_of_twoOwners
    {R p q s : ℕ} {sig : Finset ℕ} {rest : List ℕ}
    (hR : 2 ≤ R)
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: s :: rest) :
    lowOwnerFirstOwnerCanonicalStokesResidual R p sig = 0 := by
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
      (sig := sig) hqPrime hsPrime hqne hqTop
  unfold lowOwnerFirstOwnerCanonicalStokesResidual
  rw [hps]
  simp only [iteratedPairWeightedStokesResidual]
  rw [hcarrier]
  rw [iteratedPairWeightedStokesResidual_empty]
  ring

/-- Signed terminal ledger containing exactly the zero-owner and one-owner
strata.  The one-owner term is retained with its exact quarter multiplicity and
mixed finite difference; no magnitude is taken. -/
def lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  match lowOwnerFirstOwnerCanonicalStokesSchedule R p with
  | [] =>
      pairWeightedStokesMass
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p)
  | [q] =>
      (1 / 4 : ℝ) *
        pairWeightedStokesMass
          (pairPrimeTwoCoordinateInterior q
            (lowOwnerFirstOwnerSignedCellPairCarrier R p sig))
          (pairPrimeMixedDifference q
            (lowOwnerFirstOwnerDirichletPolarizationScalar R p))
  | _ => 0

/-- **Exact terminal classification.**  For `R ≥ 2`, the canonical Stokes
residual is supported only on the zero-owner and one-owner top terminal strata.
Every schedule of length at least two has identically zero residual. -/
theorem lowOwnerFirstOwnerCanonicalStokesResidual_eq_topTerminalBoundary
    {R p : ℕ} {sig : Finset ℕ} (hR : 2 ≤ R) :
    lowOwnerFirstOwnerCanonicalStokesResidual R p sig =
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig := by
  generalize hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = ps
  cases ps with
  | nil =>
      simp [lowOwnerFirstOwnerCanonicalStokesResidual,
        lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary,
        hps, iteratedPairWeightedStokesResidual]
  | cons q qs =>
      cases qs with
      | nil =>
          simp [lowOwnerFirstOwnerCanonicalStokesResidual,
            lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary,
            hps, iteratedPairWeightedStokesResidual]
      | cons s rest =>
          have hz :=
            lowOwnerFirstOwnerCanonicalStokesResidual_eq_zero_of_twoOwners
              (sig := sig) hR hps
          simpa [lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary, hps]
            using hz

/-- Global signed terminal-boundary ledger. -/
def lowOwnerCanonicalSignedStokesTopTerminalBoundary (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig

/-- The global terminal residual is exactly the explicit top terminal boundary
ledger. -/
theorem lowOwnerCanonicalSignedStokesResidual_eq_topTerminalBoundary
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerCanonicalSignedStokesResidual R =
      lowOwnerCanonicalSignedStokesTopTerminalBoundary R := by
  unfold lowOwnerCanonicalSignedStokesResidual
    lowOwnerCanonicalSignedStokesTopTerminalBoundary
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro sig _hsig
  exact lowOwnerFirstOwnerCanonicalStokesResidual_eq_topTerminalBoundary
    (sig := sig) hR

/-- Final all-signed boundary ledger after the terminal interior has been
classified and moved to the boundary side. -/
def lowOwnerCanonicalSignedStokesFinalBoundary (R : ℕ) : ℝ :=
  lowOwnerCanonicalSignedStokesClipBoundary R +
    lowOwnerCanonicalSignedStokesTopTerminalBoundary R

/-- **Signed Stokes all the way to the boundary.**

For `R ≥ 2`, the original returned-core signed target is exactly one explicit
physical boundary ledger: higher-corner Dirichlet clips plus the zero/one-owner
top terminal strata.  This theorem still contains no inequality. -/
theorem sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) =
      lowOwnerCanonicalSignedStokesFinalBoundary R := by
  rw [sum_lowOwnerFirstOwnerSignedCellTelescope_eq_canonicalBoundary_add_residual,
    lowOwnerCanonicalSignedStokesBoundary_eq_clipBoundary,
    lowOwnerCanonicalSignedStokesResidual_eq_topTerminalBoundary hR]
  rfl

end RHLean.Proof
