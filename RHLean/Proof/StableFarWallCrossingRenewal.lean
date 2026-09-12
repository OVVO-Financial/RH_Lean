import RHLean.Proof.StableFarWallOwnedCensus
import RHLean.Proof.StableFarPrimeWallTransport

/-!
# Crossing survivors are genuine lower-cofactor stable-wall occurrences

After the exact census of #672, a strict `q^2` crossing is represented by a
true product `(q, d*p)`, where `p` is the original far prime and `d` is the
cofactor left after stripping the fresh low prime `q`.

This file records the next signed-reassembly fact without taking a norm:
forgetting the stripped owner does not create an artificial arithmetic object.
The lower state `(d,p)` is itself a literal member of the original stable far
wall, and its native physical weight is the opposite of the crossing product's
Möbius weight.

The owner tag is deliberately retained in the sum.  Different crossing owners
may descend to the same lower stable-wall state, so no injectivity across owners
is asserted or used.  This is the renewal form needed for any subsequent
frontier cancellation: every surviving crossing is an actual signed return to
the same physical wall, with exact multiplicity.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open FrozenCofactorTopBottom LowWheelCanonicalDowncrossOwnership

attribute [local instance] Classical.propDecidable

/-- The stable-wall state reached after forgetting only the crossing owner tag. -/
def lowWheelFarPrimeCrossingStableState
    (x : ℕ × ℕ) : LowWheelFullTaggedPhysicalState :=
  (∅, (canonicalCofactor x.2, canonicalLargestPrimeFactor x.2))

/-- Every strict crossing product returns to a literal state of the original
stable far wall.  No owner multiplicity is forgotten by this membership
statement. -/
theorem lowWheelFarPrimeCrossingStableState_mem
    {R : ℕ} (hR : 2 ≤ R) {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    lowWheelFarPrimeCrossingStableState x ∈ stableFarWallCarrier R := by
  rcases Finset.mem_image.mp hx with ⟨t, htCross, rfl⟩
  have ht : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp htCross).1
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hq, hqR, hd1, hp, hpR, hdsq, hdq, hcut⟩
  have hcoords := lowWheelFarPrimeProduct_coordinates ht
  have hlpf :
      canonicalLargestPrimeFactor (t.2.1 * t.2.2) = t.2.2 := by
    simpa [lowWheelFarPrimeProductKey] using hcoords.1
  have hcofactor :
      canonicalCofactor (t.2.1 * t.2.2) = t.2.1 := by
    simpa [lowWheelFarPrimeProductKey] using hcoords.2
  have hq1 : 1 ≤ t.1 := hq.one_le
  have hdpCut : t.2.1 * t.2.2 ≤ squareRootEndpoint R := by
    have hle : t.2.1 * t.2.2 ≤ t.1 * (t.2.1 * t.2.2) := by
      simpa using Nat.mul_le_mul_right (t.2.1 * t.2.2) hq1
    exact hle.trans (by simpa [Nat.mul_assoc] using hcut)
  have hRpos : 0 < R := by omega
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hne
  have hpGeR : R ≤ t.2.2 := by omega
  have hdR : t.2.1 < R := by
    by_contra hnot
    have hRd : R ≤ t.2.1 := Nat.le_of_not_gt hnot
    have hR2 : R * R ≤ t.2.1 * t.2.2 := Nat.mul_le_mul hRd hpGeR
    exact (Nat.not_lt_of_ge (hR2.trans hdpCut)) hXlt
  apply (mem_stableFarWallCarrier_iff_primeInsertion hR).2
  change
    (∅ : Finset ℕ) = ∅ ∧
      (canonicalLargestPrimeFactor (t.2.1 * t.2.2)).Prime ∧
      R + 8 ≤ canonicalLargestPrimeFactor (t.2.1 * t.2.2) ∧
      canonicalLargestPrimeFactor (t.2.1 * t.2.2) ≤ squareRootEndpoint R ∧
      canonicalCofactor (t.2.1 * t.2.2) ∈ Finset.Ico 1 R ∧
      Squarefree (canonicalCofactor (t.2.1 * t.2.2)) ∧
      canonicalCofactor (t.2.1 * t.2.2) *
          canonicalLargestPrimeFactor (t.2.1 * t.2.2) ≤ squareRootEndpoint R
  rw [hlpf, hcofactor]
  refine ⟨rfl, hp, hpR, ?_, Finset.mem_Ico.mpr ⟨hd1, hdR⟩, hdsq, hdpCut⟩
  have hle : t.2.2 ≤ t.2.1 * t.2.2 := by
    simpa using Nat.mul_le_mul_right t.2.2 hd1
  exact hle.trans hdpCut

/-- Pointwise renewal sign: the returned stable-wall occurrence has exactly the
opposite weight of the crossing product. -/
theorem lowWheelFarPrimeCrossingStableState_weight_eq_neg_product
    {R : ℕ} (hR : 2 ≤ R) {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) :
    lowWheelFullTaggedPhysicalWeight
        (lowWheelFarPrimeCrossingStableState x) =
      -canonicalMoebiusWeight x.2 := by
  have hmem := lowWheelFarPrimeCrossingStableState_mem hR hx
  have hweight := stableFarWall_singleInsertion_weight hR hmem
  have hxgt : 1 < x.2 := by
    rcases Finset.mem_image.mp hx with ⟨t, htCross, htx⟩
    have ht := (Finset.mem_filter.mp htCross).1
    have hfar := (lowWheelFarPrimeProduct_geometry ht).2.1
    have hfarx : R + 8 ≤ x.2 := by
      simpa [htx] using hfar
    omega
  have hprod := canonicalCofactor_mul_largestPrimeFactor hxgt
  unfold lowWheelFarPrimeCrossingStableState at hweight
  rw [hprod] at hweight
  exact hweight

/-- **Exact crossing-renewal mass identity.**  Every crossing survivor is the
negative of a genuine lower stable-wall occurrence.  The sum is still indexed
by the tagged crossing carrier, so repeated owners landing on the same lower
state remain repeated occurrences rather than being silently collapsed. -/
theorem lowWheelFarPrimeCrossingProductMass_eq_neg_stableRenewalMass
    {R : ℕ} (hR : 2 ≤ R) :
    (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        canonicalMoebiusWeight x.2) =
      -∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [lowWheelFarPrimeCrossingStableState_weight_eq_neg_product hR hx]
  ring

/-- The descended triples may be regrouped by every possible prime owner below
`R` without losing an occurrence.  This is finite Fubini only. -/
theorem lowWheelFarPrimeQ2DescendedMass_eq_ownerFibers (R : ℕ) :
    lowWheelFarPrimeQ2DescendedMass R =
      ∑ q ∈ primesUpTo (R - 1),
        ∑ t ∈ lowWheelFarPrimeQ2DescendedOwnerTriples R q,
          canonicalMoebiusWeight t.2.1 := by
  let S := lowWheelFarPrimeQ2DescendedTriples R
  let O := primesUpTo (R - 1)
  let owner : ℕ × (ℕ × ℕ) → ℕ := Prod.fst
  have hmaps : ∀ t ∈ S, owner t ∈ O := by
    intro t ht
    have hdata := lowWheelFarPrimeLowCofactorTriple_data
      (Finset.mem_filter.mp ht).1
    exact mem_primesUpTo.mpr ⟨hdata.1, Nat.le_pred_of_lt hdata.2.1⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := O) (g := owner) hmaps
    (fun t => canonicalMoebiusWeight t.2.1)
  have hraw :
      (∑ t ∈ S, canonicalMoebiusWeight t.2.1) =
        ∑ q ∈ O,
          ∑ t ∈ S with owner t = q,
            canonicalMoebiusWeight t.2.1 := hfiber.symm
  unfold lowWheelFarPrimeQ2DescendedMass
  change (∑ t ∈ S, canonicalMoebiusWeight t.2.1) =
    ∑ q ∈ O,
      ∑ t ∈ lowWheelFarPrimeQ2DescendedOwnerTriples R q,
        canonicalMoebiusWeight t.2.1
  rw [hraw]
  apply Finset.sum_congr rfl
  intro q hq
  rfl

/-- **Global descended-child identification.**  The complete stripped descended
mass is exactly the sum of the literal far-prime high-transport slices at every
q² child cutoff. -/
theorem lowWheelFarPrimeQ2DescendedMass_eq_sum_childFarSlices (R : ℕ) :
    lowWheelFarPrimeQ2DescendedMass R =
      ∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1 := by
  rw [lowWheelFarPrimeQ2DescendedMass_eq_ownerFibers R]
  apply Finset.sum_congr rfl
  intro q hq
  have hdata := mem_primesUpTo.mp hq
  have hRpos : 0 < R := by
    have := hdata.1.two_le
    omega
  have hqR : q < R := Nat.lt_of_le_pred hRpos hdata.2
  exact lowWheelFarPrimeQ2DescendedOwner_mass_eq_childFarSlice hdata.1 hqR

/-- Reattaching the original far prime reverses the child-far sign, so the true
descended product packet is the negative of the global child high-transport
slice sum. -/
theorem lowWheelFarPrimeDescendedProductMass_eq_neg_sum_childFarSlices
    (R : ℕ) :
    (∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R,
        canonicalMoebiusWeight x.2) =
      -∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1 := by
  have hprod := lowWheelFarPrimeQ2DescendedMass_eq_neg_productMass R
  have hchild := lowWheelFarPrimeQ2DescendedMass_eq_sum_childFarSlices R
  rw [hchild] at hprod
  have hneg := congrArg Neg.neg hprod
  simpa using hneg.symm

/-- The four-term #672 boundary in renewal form: all strict crossing mass is now
shown on the literal stable far wall, while the already-owned terminal product
population remains explicit.  This is still a signed identity, not an estimate. -/
theorem lowWheelFarWall_remainingBoundary_eq_neg_stableRenewal_sub_terminal
    {R : ℕ} (hR : 2 ≤ R) :
    lowWheelFarPrimeUnitFaceMass R - lowWheelFarPrimeQ2CrossingMass R -
        lowWheelCanonicalRepeatedTerminalInternalMateLedger R -
        lowWheelFrozenCofactorTopImageLedger R =
      -(∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
          lowWheelFullTaggedPhysicalWeight
            (lowWheelFarPrimeCrossingStableState x)) -
        ∑ n ∈ lowWheelFarWallTerminalProducts R,
          canonicalMoebiusWeight n := by
  rw [lowWheelFarWall_remainingBoundary_eq_signed_products R,
    lowWheelFarPrimeCrossingProductMass_eq_neg_stableRenewalMass hR]

/-- **Complete post-#672 residual in renewal normal form.**  The old hard far
residual is now the genuine descended q² product packet minus the literal
stable-wall renewal occurrences minus the terminal product carrier.  Every
crossing-owner multiplicity is still present in the middle sum, and no norm has
been taken. -/
theorem lowWheelFrozenTopFarResidual_eq_descended_sub_stableRenewal_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      (∑ x ∈ lowWheelFarPrimeDescendedProductCarrier R,
        canonicalMoebiusWeight x.2) -
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x)) -
      ∑ n ∈ lowWheelFarWallTerminalProducts R,
        canonicalMoebiusWeight n := by
  rw [lowWheelFrozenTopFarResidual_eq_descended_add_crossing_sub_terminal R hR,
    lowWheelFarPrimeCrossingProductMass_eq_neg_stableRenewalMass (by omega)]
  ring

/-- The same hard residual with its descended term rewritten ownerwise as the
literal lower-scale child far-transport slices from #671. -/
theorem lowWheelFrozenTopFarResidual_eq_neg_childFarSlices_sub_stableRenewal_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      -(∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) -
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x)) -
      ∑ n ∈ lowWheelFarWallTerminalProducts R,
        canonicalMoebiusWeight n := by
  rw [lowWheelFrozenTopFarResidual_eq_descended_sub_stableRenewal_sub_terminal R hR,
    lowWheelFarPrimeDescendedProductMass_eq_neg_sum_childFarSlices R]

/-! ## Frequency-weighted crossing renewal -/

/-- **Pointwise q² transfer symbol.**  For any completely multiplicative
complex frequency `χ`, a strict crossing at owner `q=x.1` and lower product
`n=x.2` carries the second-contact frequency `χ(q² n)`.  Renewal returns to the
same lower state with the opposite Möbius weight, so the parent contribution is
exactly the renewed lower contribution multiplied by `-χ(q)^2`.

This theorem is deliberately abstract in `χ`: it applies to Mellin/Perron
characters once their multiplicativity is supplied, but it uses only the exact
physical crossing carrier and the already-proved renewal sign. -/
theorem lowWheelFarPrimeCrossing_frequency_q2_factor
    {R : ℕ} (hR : 2 ≤ R) {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R)
    (χ : ℕ → ℂ)
    (hmul : ∀ a b : ℕ, χ (a * b) = χ a * χ b) :
    canonicalMoebiusWeight x.2 * χ (x.1 * x.1 * x.2) =
      -(χ x.1) ^ 2 *
        (lowWheelFullTaggedPhysicalWeight
            (lowWheelFarPrimeCrossingStableState x) * χ x.2) := by
  have hsign :=
    lowWheelFarPrimeCrossingStableState_weight_eq_neg_product hR hx
  have hfreq1 := hmul (x.1 * x.1) x.2
  have hfreq2 := hmul x.1 x.1
  rw [hfreq1, hfreq2, hsign]
  ring

/-- **Global frequency-weighted crossing-renewal identity.**  The owner tag is
kept in the summation, hence every crossing multiplicity survives exactly.
The only spectral multiplier introduced by a second `q` insertion is the
explicit square `χ(q)^2`; no norm, triangle inequality, or owner collapse is
used. -/
theorem lowWheelFarPrimeCrossing_frequency_q2_sum
    {R : ℕ} (hR : 2 ≤ R)
    (χ : ℕ → ℂ)
    (hmul : ∀ a b : ℕ, χ (a * b) = χ a * χ b) :
    (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        canonicalMoebiusWeight x.2 * χ (x.1 * x.1 * x.2)) =
      -∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        (χ x.1) ^ 2 *
          (lowWheelFullTaggedPhysicalWeight
              (lowWheelFarPrimeCrossingStableState x) * χ x.2) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have h := lowWheelFarPrimeCrossing_frequency_q2_factor hR hx χ hmul
  calc
    canonicalMoebiusWeight x.2 * χ (x.1 * x.1 * x.2) =
        -(χ x.1) ^ 2 *
          (lowWheelFullTaggedPhysicalWeight
              (lowWheelFarPrimeCrossingStableState x) * χ x.2) := h
    _ = -((χ x.1) ^ 2 *
          (lowWheelFullTaggedPhysicalWeight
              (lowWheelFarPrimeCrossingStableState x) * χ x.2)) := by ring

/-! ### Mellin/Perron specialization -/

/-- The finite Mellin character `n ↦ n^{-s}`, extended by zero at `n=0` so it
is a total function on naturals. -/
noncomputable def lowWheelMellinFrequency (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (n : ℂ) ^ (-s)

/-- The zero-extended Mellin character remains completely multiplicative. -/
theorem lowWheelMellinFrequency_mul (s : ℂ) (a b : ℕ) :
    lowWheelMellinFrequency s (a * b) =
      lowWheelMellinFrequency s a * lowWheelMellinFrequency s b := by
  by_cases ha : a = 0
  · subst a
    simp [lowWheelMellinFrequency]
  by_cases hb : b = 0
  · subst b
    simp [lowWheelMellinFrequency]
  have hab : a * b ≠ 0 := Nat.mul_ne_zero ha hb
  simp only [lowWheelMellinFrequency, ha, hb, hab, if_false]
  have hcp := @Complex.mul_cpow_ofReal_nonneg
    (a := (a : ℝ)) (b := (b : ℝ)) (r := -s)
    (Nat.cast_nonneg a) (Nat.cast_nonneg b)
  push_cast at hcp ⊢
  simpa [Nat.cast_mul] using hcp

/-- Pointwise crossing-renewal identity for the literal Mellin/Perron
character `n^{-s}`. -/
theorem lowWheelFarPrimeCrossing_mellin_q2_factor
    {R : ℕ} (hR : 2 ≤ R) {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) (s : ℂ) :
    canonicalMoebiusWeight x.2 *
        lowWheelMellinFrequency s (x.1 * x.1 * x.2) =
      -(lowWheelMellinFrequency s x.1) ^ 2 *
        (lowWheelFullTaggedPhysicalWeight
            (lowWheelFarPrimeCrossingStableState x) *
          lowWheelMellinFrequency s x.2) := by
  exact lowWheelFarPrimeCrossing_frequency_q2_factor hR hx
    (lowWheelMellinFrequency s) (lowWheelMellinFrequency_mul s)

/-- Global crossing-renewal identity on the Mellin/Perron character. -/
theorem lowWheelFarPrimeCrossing_mellin_q2_sum
    {R : ℕ} (hR : 2 ≤ R) (s : ℂ) :
    (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        canonicalMoebiusWeight x.2 *
          lowWheelMellinFrequency s (x.1 * x.1 * x.2)) =
      -∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        (lowWheelMellinFrequency s x.1) ^ 2 *
          (lowWheelFullTaggedPhysicalWeight
              (lowWheelFarPrimeCrossingStableState x) *
            lowWheelMellinFrequency s x.2) := by
  exact lowWheelFarPrimeCrossing_frequency_q2_sum hR
    (lowWheelMellinFrequency s) (lowWheelMellinFrequency_mul s)

/-- Standard critical-line Mellin parameter `1/2 + it`. -/
noncomputable def lowWheelCriticalMellinParameter (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- On the critical line, one Mellin insertion has radial size `q^{-1/2}`. -/
theorem lowWheelMellinFrequency_norm_critical
    {q : ℕ} (hq : 0 < q) (t : ℝ) :
    ‖lowWheelMellinFrequency (lowWheelCriticalMellinParameter t) q‖ =
      Real.rpow (q : ℝ) (-(1 / 2 : ℝ)) := by
  simp [lowWheelMellinFrequency, hq.ne',
    Complex.norm_natCast_cpow_of_pos hq, lowWheelCriticalMellinParameter]

/-- Therefore the exact second-contact multiplier has radial size `1/q`. -/
theorem lowWheelMellinFrequency_sq_norm_critical
    {q : ℕ} (hq : 0 < q) (t : ℝ) :
    ‖(lowWheelMellinFrequency (lowWheelCriticalMellinParameter t) q) ^ 2‖ =
      1 / (q : ℝ) := by
  rw [norm_pow, lowWheelMellinFrequency_norm_critical hq t]
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  calc
    (Real.rpow (q : ℝ) (-(1 / 2 : ℝ))) ^ 2 =
        Real.rpow (Real.rpow (q : ℝ) (-(1 / 2 : ℝ))) (2 : ℝ) := by
          exact
            (Real.rpow_natCast (Real.rpow (q : ℝ) (-(1 / 2 : ℝ))) 2).symm
    _ = Real.rpow (q : ℝ) ((-(1 / 2 : ℝ)) * 2) :=
      (Real.rpow_mul hq0 (-(1 / 2 : ℝ)) (2 : ℝ)).symm
    _ = ((q : ℝ))⁻¹ := by
      simpa only using (Real.rpow_neg_one (q : ℝ))
    _ = 1 / (q : ℝ) := by rw [one_div]

/-- The phase-normalized critical-line renewal symbol.  Multiplying the raw
`-q^{-2s}` symbol by `q` strips its radial `1/q` factor and leaves a unit
complex phase. -/
noncomputable def lowWheelCriticalRenewalPhase (q : ℕ) (t : ℝ) : ℂ :=
  -((q : ℂ) *
    (lowWheelMellinFrequency (lowWheelCriticalMellinParameter t) q) ^ 2)

/-- The normalized renewal symbol lies exactly on the unit circle. -/
theorem lowWheelCriticalRenewalPhase_norm
    {q : ℕ} (hq : 0 < q) (t : ℝ) :
    ‖lowWheelCriticalRenewalPhase q t‖ = 1 := by
  rw [lowWheelCriticalRenewalPhase, norm_neg, norm_mul,
    Complex.norm_natCast, lowWheelMellinFrequency_sq_norm_critical hq t]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

/-- Exact radial-phase decomposition of the critical-line second-contact
multiplier: `-q^{-2s} = q^{-1} * phase_q(t)`, with the phase normalized above. -/
theorem lowWheelCriticalRenewalMultiplier_eq_inv_mul_phase
    {q : ℕ} (hq : 0 < q) (t : ℝ) :
    -(lowWheelMellinFrequency (lowWheelCriticalMellinParameter t) q) ^ 2 =
      ((q : ℂ)⁻¹) * lowWheelCriticalRenewalPhase q t := by
  unfold lowWheelCriticalRenewalPhase
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp [hqC]

/-- Every actual crossing owner has the critical-line radial factor `1/q`.
This specializes the abstract symbol to the physical carrier itself. -/
theorem lowWheelFarPrimeCrossing_critical_multiplier_norm
    {R : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ lowWheelFarPrimeCrossingProductCarrier R) (t : ℝ) :
    ‖(lowWheelMellinFrequency (lowWheelCriticalMellinParameter t) x.1) ^ 2‖ =
      1 / (x.1 : ℝ) := by
  rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
  have hu0 : u ∈ lowWheelFarPrimeLowCofactorTriples R :=
    (Finset.mem_filter.mp hu).1
  have hqpos : 0 < u.1 := (lowWheelFarPrimeLowCofactorTriple_data hu0).1.pos
  exact lowWheelMellinFrequency_sq_norm_critical hqpos t

end RHLean.Proof