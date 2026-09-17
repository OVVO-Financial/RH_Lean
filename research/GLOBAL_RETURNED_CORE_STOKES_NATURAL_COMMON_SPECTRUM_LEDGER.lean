import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_NATURAL_CORRECTED_CONDUCTOR_PACKET»
import «research.GLOBAL_RETURNED_CORE_STOKES_ALL_ENDPOINT_MERTENS_LEDGER»

/-!
# Exact common spectrum on the natural Stokes torus

For `R >= 56`, the natural square-sensitive modulus `P_R` already contains the
entire physical clock.  This file therefore performs the conductor grouping of
the *actual* periodic-raw-minus-smooth Stokes field directly on `P_R`.

The endpoint Mertens gap

  M(R-1) - M(X_R) - sum_q M(Y_q)/q

is represented as one signed sum of corrected natural-conductor packets.  The
full conductor-conductor Gram is then just the square of that exact signed sum.
No conductor is dropped and no inequality appears here.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

attribute [local instance] Classical.propDecidable

/-- One frequency atom of the periodic raw spectrum on the natural torus. -/
def lowOwnerStokesNaturalPeriodicRawSpectralAtom
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ)
    (r : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus) : ℂ :=
  ((((lowOwnerStokesNaturalWheelSystem R hR).modulus : ℂ)⁻¹) *
    lowOwnerStokesNaturalPeriodicRawSpectrum R hR r) *
      (lowOwnerStokesNaturalWheelSystem R hR).prefixWindowSpectrum x (-r)

/-- One frequency atom of the pinned smooth correction on the natural torus. -/
def lowOwnerStokesNaturalPeriodicSmoothSpectralAtom
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ)
    (r : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus) : ℂ :=
  ((((lowOwnerStokesNaturalWheelSystem R hR).modulus : ℂ)⁻¹) *
    (lowOwnerStokesNaturalWheelSystem R hR).smoothCoreBlockSpectrum r) *
      (lowOwnerStokesNaturalWheelSystem R hR).prefixWindowSpectrum x (-r)

/-- One frequency atom of the actual corrected natural Stokes spectrum. -/
def lowOwnerStokesNaturalPeriodicJointSpectralAtom
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ)
    (r : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus) : ℂ :=
  ((((lowOwnerStokesNaturalWheelSystem R hR).modulus : ℂ)⁻¹) *
    lowOwnerStokesNaturalPeriodicRawJointSpectrum R hR r) *
      (lowOwnerStokesNaturalWheelSystem R hR).prefixWindowSpectrum x (-r)

/-- Raw and smooth remain coupled frequency by frequency. -/
theorem lowOwnerStokesNaturalPeriodicJointSpectralAtom_eq_raw_sub_two_smooth
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ)
    (r : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus) :
    lowOwnerStokesNaturalPeriodicJointSpectralAtom R hR x r =
      lowOwnerStokesNaturalPeriodicRawSpectralAtom R hR x r -
        2 * lowOwnerStokesNaturalPeriodicSmoothSpectralAtom R hR x r := by
  unfold lowOwnerStokesNaturalPeriodicJointSpectralAtom
    lowOwnerStokesNaturalPeriodicRawSpectralAtom
    lowOwnerStokesNaturalPeriodicSmoothSpectralAtom
  rw [lowOwnerStokesNaturalPeriodicRawJointSpectrum_eq_raw_sub_two_smooth]
  ring

/-- One reduced-conductor shell of the actual corrected natural spectrum. -/
def lowOwnerStokesNaturalPeriodicJointConductorResponse
    (R : ℕ) (hR : 56 ≤ R) (x c : ℕ) : ℂ :=
  ∑ r : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus,
    if c = reducedAdditiveConductor r then
      lowOwnerStokesNaturalPeriodicJointSpectralAtom R hR x r
    else 0

/-- The shell definition is exactly the corrected response already exposed by
`GLOBAL_RETURNED_CORE_STOKES_NATURAL_CORRECTED_CONDUCTOR_PACKET`. -/
theorem lowOwnerStokesNaturalPeriodicJointConductorResponse_eq_corrected
    (R : ℕ) (hR : 56 ≤ R) (x c : ℕ) :
    lowOwnerStokesNaturalPeriodicJointConductorResponse R hR x c =
      lowOwnerStokesNaturalPeriodicCorrectedConductorResponse R hR x c := by
  classical
  unfold lowOwnerStokesNaturalPeriodicJointConductorResponse
    lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
    lowOwnerStokesNaturalPeriodicRawConductorResponse
    primeWheelSmoothConductorResponse
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hc : c = reducedAdditiveConductor r
  · simp only [hc, if_true]
    exact lowOwnerStokesNaturalPeriodicJointSpectralAtom_eq_raw_sub_two_smooth
      R hR x r
  · simp [hc]

/-- The complete natural periodic spectral prefix is the sum of its frequency
atoms. -/
theorem lowOwnerStokesNaturalPeriodicRawSpectralPrefix_eq_sum_atoms
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ) :
    lowOwnerStokesNaturalPeriodicRawSpectralPrefix R hR x =
      ∑ r : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus,
        lowOwnerStokesNaturalPeriodicJointSpectralAtom R hR x r := by
  unfold lowOwnerStokesNaturalPeriodicRawSpectralPrefix
    finiteTorusSpectralPairing
    lowOwnerStokesNaturalPeriodicJointSpectralAtom
    lowOwnerStokesNaturalPeriodicRawJointSpectrum
    PrimeWheelFiniteSystem.prefixWindowSpectrum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- Exact partition of the natural periodic Stokes prefix by reduced additive
conductor. -/
theorem lowOwnerStokesNaturalPeriodicRawSpectralPrefix_eq_sum_conductorResponses
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ) :
    lowOwnerStokesNaturalPeriodicRawSpectralPrefix R hR x =
      ∑ c ∈ Finset.range
          ((lowOwnerStokesNaturalWheelSystem R hR).modulus + 1),
        lowOwnerStokesNaturalPeriodicCorrectedConductorResponse R hR x c := by
  classical
  rw [lowOwnerStokesNaturalPeriodicRawSpectralPrefix_eq_sum_atoms]
  rw [← Finset.sum_congr rfl (fun c _hc =>
    lowOwnerStokesNaturalPeriodicJointConductorResponse_eq_corrected
      R hR x c)]
  unfold lowOwnerStokesNaturalPeriodicJointConductorResponse
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  have hcond :
      reducedAdditiveConductor r ≤
        (lowOwnerStokesNaturalWheelSystem R hR).modulus := by
    unfold reducedAdditiveConductor
    split_ifs
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (lowOwnerStokesNaturalWheelSystem R hR).modulus_pos)
    · exact Nat.div_le_self _ _
  have hmem :
      reducedAdditiveConductor r ∈
        Finset.range ((lowOwnerStokesNaturalWheelSystem R hR).modulus + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcond)
  simp [hmem]

/-- A genuine LOW q^2 daughter cutoff is positive. -/
theorem natural_rawQ2ChildCutoff_pos_of_mem_lowQ2Owners
    {R q : ℕ} (hR : 56 ≤ R)
    (hq : q ∈ canonicalRoughLowQ2Owners R) :
    0 < rawQ2ChildCutoff R q := by
  have hdata := Finset.mem_sdiff.mp hq
  have hbase := hdata.1
  have hnotHigh := hdata.2
  have hqMem : q ∈ primesUpTo (R - 1) := (Finset.mem_erase.mp hbase).2
  have hqPrime : q.Prime := (mem_primesUpTo.mp hqMem).1
  have hq2pos : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
  have hlow : q * q < R := by
    by_contra hnot
    have hhigh : R ≤ q * q := Nat.le_of_not_gt hnot
    apply hnotHigh
    exact Finset.mem_filter.mpr ⟨hbase, hhigh⟩
  have hRleX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hRR : R + 1 ≤ R * R := by nlinarith
    rw [pow_two]
    omega
  have hq2leX : q * q ≤ squareRootEndpoint R :=
    (Nat.le_of_lt hlow).trans hRleX
  unfold rawQ2ChildCutoff
  exact Nat.div_pos hq2leX hq2pos

/-- Every literal LOW daughter cutoff remains inside the physical clock. -/
theorem natural_rawQ2ChildCutoff_le_squareRootEndpoint
    (R q : ℕ) :
    rawQ2ChildCutoff R q ≤ squareRootEndpoint R := by
  unfold rawQ2ChildCutoff
  exact Nat.div_le_self _ _

/-- Every positive physical Mertens prefix is the sum of the corrected natural
conductor responses. -/
theorem mertensSummatory_eq_sum_naturalCorrectedConductorResponses
    {R x : ℕ} (hR : 56 ≤ R)
    (hxpos : 0 < x) (hx : x ≤ squareRootEndpoint R) :
    mertensSummatory x =
      ∑ c ∈ Finset.range
          ((lowOwnerStokesNaturalWheelSystem R hR).modulus + 1),
        lowOwnerStokesNaturalPeriodicCorrectedConductorResponse R hR x c := by
  rw [← lowOwnerStokesNaturalPeriodicRawSpectralPrefix_eq_mertensSummatory
    hR hxpos hx]
  exact lowOwnerStokesNaturalPeriodicRawSpectralPrefix_eq_sum_conductorResponses
    R hR x

/-- One reduced-conductor component of the exact all-endpoint Stokes gap on the
natural torus. -/
def lowOwnerStokesNaturalEndpointConductorComponent
    (R : ℕ) (hR : 56 ≤ R) (c : ℕ) : ℂ :=
  lowOwnerStokesNaturalPeriodicCorrectedConductorResponse R hR (R - 1) c -
    lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
      R hR (squareRootEndpoint R) c -
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℂ)) *
          lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
            R hR (rawQ2ChildCutoff R q) c

/-- **Exact natural-spectrum decomposition of the physical Stokes endpoint
gap.**  All endpoints use the same corrected spectrum on `P_R`. -/
theorem lowOwnerStokesAllEndpointMertensGap_eq_sum_naturalConductorComponents
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesAllEndpointMertensGap R =
      ∑ c ∈ Finset.range
          ((lowOwnerStokesNaturalWheelSystem R hR).modulus + 1),
        lowOwnerStokesNaturalEndpointConductorComponent R hR c := by
  let W := lowOwnerStokesNaturalWheelSystem R hR
  let C : Finset ℕ := Finset.range (W.modulus + 1)
  have hRm1pos : 0 < R - 1 := by omega
  have hRm1le : R - 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hRR : R ≤ R * R := by nlinarith
    rw [pow_two]
    omega
  have hXpos : 0 < squareRootEndpoint R :=
    squareRootEndpoint_pos_of_two_le (by omega)
  have hroot := mertensSummatory_eq_sum_naturalCorrectedConductorResponses
    hR hRm1pos hRm1le
  have hfull := mertensSummatory_eq_sum_naturalCorrectedConductorResponses
    hR hXpos (le_refl (squareRootEndpoint R))
  have hdaughter :
      lowOwnerReciprocalMertensEndpointSum R =
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) *
            (∑ c ∈ C,
              lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
                R hR (rawQ2ChildCutoff R q) c) := by
    unfold lowOwnerReciprocalMertensEndpointSum
    apply Finset.sum_congr rfl
    intro q hq
    rw [mertensSummatory_eq_sum_naturalCorrectedConductorResponses
      hR
      (natural_rawQ2ChildCutoff_pos_of_mem_lowQ2Owners hR hq)
      (natural_rawQ2ChildCutoff_le_squareRootEndpoint R q)]
  have hswap :
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℂ)) *
          (∑ c ∈ C,
            lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
              R hR (rawQ2ChildCutoff R q) c)) =
      ∑ c ∈ C,
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) *
            lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
              R hR (rawQ2ChildCutoff R q) c := by
    calc
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℂ)) *
          (∑ c ∈ C,
            lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
              R hR (rawQ2ChildCutoff R q) c)) =
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          ∑ c ∈ C,
            (1 / (q : ℂ)) *
              lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
                R hR (rawQ2ChildCutoff R q) c := by
          apply Finset.sum_congr rfl
          intro q _hq
          rw [Finset.mul_sum]
      _ = ∑ c ∈ C,
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) *
            lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
              R hR (rawQ2ChildCutoff R q) c := by
          exact Finset.sum_comm
  unfold lowOwnerStokesAllEndpointMertensGap
  rw [hroot, hfull, hdaughter, hswap]
  change
    (∑ c ∈ C,
      lowOwnerStokesNaturalPeriodicCorrectedConductorResponse R hR (R - 1) c) -
      (∑ c ∈ C,
        lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
          R hR (squareRootEndpoint R) c) -
      (∑ c ∈ C,
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) *
            lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
              R hR (rawQ2ChildCutoff R q) c) =
      ∑ c ∈ C,
        (lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
            R hR (R - 1) c -
          lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
            R hR (squareRootEndpoint R) c -
          ∑ q ∈ canonicalRoughLowQ2Owners R,
            (1 / (q : ℂ)) *
              lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
                R hR (rawQ2ChildCutoff R q) c)
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]

/-- Full natural conductor-conductor Gram block of the physical endpoint gap. -/
def lowOwnerStokesNaturalEndpointConductorGramBlock
    (R : ℕ) (hR : 56 ≤ R) (c c' : ℕ) : ℂ :=
  lowOwnerStokesNaturalEndpointConductorComponent R hR c *
    conj (lowOwnerStokesNaturalEndpointConductorComponent R hR c')

/-- The complete natural-conductor Gram; no off-diagonal block is discarded. -/
def lowOwnerStokesNaturalEndpointConductorGramEnergy
    (R : ℕ) (hR : 56 ≤ R) : ℂ :=
  let W := lowOwnerStokesNaturalWheelSystem R hR
  ∑ c ∈ Finset.range (W.modulus + 1),
    ∑ c' ∈ Finset.range (W.modulus + 1),
      lowOwnerStokesNaturalEndpointConductorGramBlock R hR c c'

/-- **Exact full Gram identity on the natural Stokes torus.** -/
theorem lowOwnerStokesNaturalEndpointConductorGramEnergy_eq_gap_mul_conj
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesNaturalEndpointConductorGramEnergy R hR =
      lowOwnerStokesAllEndpointMertensGap R *
        conj (lowOwnerStokesAllEndpointMertensGap R) := by
  let W := lowOwnerStokesNaturalWheelSystem R hR
  let C : Finset ℕ := Finset.range (W.modulus + 1)
  have hsum :=
    lowOwnerStokesAllEndpointMertensGap_eq_sum_naturalConductorComponents hR
  change
    (∑ c ∈ C,
      ∑ c' ∈ C,
        lowOwnerStokesNaturalEndpointConductorComponent R hR c *
          conj (lowOwnerStokesNaturalEndpointConductorComponent R hR c')) =
      lowOwnerStokesAllEndpointMertensGap R *
        conj (lowOwnerStokesAllEndpointMertensGap R)
  rw [hsum]
  rw [map_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [Finset.mul_sum]

end RHLean.Proof
