import Mathlib
import «research.LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE»
import «research.LOW_OWNER_PHYSICAL_CENSUS_CORRELATION»

/-!
# Zero-frequency AMP remainder in the q-owner physical coordinate

The chronological Stokes split is useful for exposing the reciprocal Euler
drop, but its memory coordinate is indexed by the fresh chronology prime `p`.
The AMP normalization defect itself is naturally indexed by the q^2 daughter
owner `q`.  This file removes that bookkeeping split completely.

For `R >= 56`, the exact zero-frequency AMP remainder is

  physicalFarCensus_R - reciprocalQ2MertensColumn_R - rootCorrection_R.

Thus the remaining proof can stay in the q-owner/returned-child coordinate
where the reciprocal Fubini and reciprocal-square congestion theorems live.
No norm or estimate is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The non-root q-owner AMP memory packet: literal signed physical far census
minus the genuine reciprocal q^2 Mertens daughter column. -/
def lowOwnerPhysicalQMemoryCensus (R : ℕ) : ℂ :=
  lowOwnerPhysicalFarCensus R - lowOwnerReciprocalMertensColumn R

/-- **q-owner normal form of the AMP remainder.**  This is the exact physical
census coordinate, not the chronological p-memory decomposition. -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_qMemory_sub_root
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      lowOwnerPhysicalQMemoryCensus R - frozenTopFarRoughRootCorrection R := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_correlation_sub_reciprocalColumn
      R hR,
    squareRootCanonicalRoughCorrelation_eq_physicalFarCensus_sub_root R hR]
  unfold lowOwnerPhysicalQMemoryCensus
  ring

/-- Expand the q-memory packet only into the already-signed physical census
populations.  In particular, no ownerwise norm is taken. -/
theorem lowOwnerPhysicalQMemoryCensus_eq_signed_populations (R : ℕ) :
    lowOwnerPhysicalQMemoryCensus R =
      -lowOwnerChildFarCensus R - lowOwnerReciprocalMertensColumn R -
      ownerTwoChildFarCensus R - stableFarRenewalColumn R -
      stableFarTerminalProductColumn R := by
  unfold lowOwnerPhysicalQMemoryCensus lowOwnerPhysicalFarCensus
  ring

/-- One low q^2 owner correction at zero frequency is literally its negative
child-far slice minus its reciprocal raw Mertens daughter. -/
theorem lowOwnerAmplitudeTransportCorrection_zero_eq_neg_childFar_sub_reciprocal
    {R q : ℕ} (hq : q ∈ primesUpTo (R - 1)) :
    lowOwnerAmplitudeTransportCorrection R q 0 =
      -(∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) -
        ((1 : ℂ) / (q : ℂ)) * lowOwnerRawMertensAmplitude R q := by
  have hqpos : 0 < q := (mem_primesUpTo.mp hq).1.pos
  rw [lowOwnerAmplitudeTransportCorrection_eq_neg_childFar_sub_critical hq 0,
    stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase 0 hqpos]
  simp

/-- Summing the preceding identity over the actual low q^2 owner schedule gives
exactly the low child-far census plus the reciprocal daughter column. -/
theorem sum_lowOwnerAmplitudeTransportCorrection_zero_eq_neg_childFar_sub_reciprocal
    (R : ℕ) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      lowOwnerAmplitudeTransportCorrection R q 0) =
      -lowOwnerChildFarCensus R - lowOwnerReciprocalMertensColumn R := by
  unfold lowOwnerChildFarCensus lowOwnerReciprocalMertensColumn
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hprime : q ∈ primesUpTo (R - 1) :=
    (Finset.mem_erase.mp (Finset.sdiff_subset hq)).2
  rw [lowOwnerAmplitudeTransportCorrection_zero_eq_neg_childFar_sub_reciprocal
    hprime]

/-- Full expanded zero-frequency remainder, with the q-owner normalization
memory visible before the owner-two / renewal / terminal / root populations. -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_signed_qMemory_populations
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      -lowOwnerChildFarCensus R - lowOwnerReciprocalMertensColumn R -
      ownerTwoChildFarCensus R - stableFarRenewalColumn R -
      stableFarTerminalProductColumn R - frozenTopFarRoughRootCorrection R := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_qMemory_sub_root R hR,
    lowOwnerPhysicalQMemoryCensus_eq_signed_populations]

end RHLean.Proof
