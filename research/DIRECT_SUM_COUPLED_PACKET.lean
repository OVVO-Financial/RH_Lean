import Mathlib
import «research.DIRECT_SUM_LOW_FRESHNESS_ABEL»

/-!
# Coupled direct-sum scalar packet

This module records the architectural correction forced by the large-root
numerics: the dyadic wavelet aggregate and coherent aggregate must be added as
scalars before any terminal norm is taken.

Everything below is deterministic packaging or a named open proposition.  No
coupled dispersion estimate and no FAR-4 budget estimate is proved here.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The scalar PNT packet after high/low coupling inside each dyadic channel and
before the reconstruction remainder is added. -/
def directSumCoupledPNTPacket (R : ℕ) : ℂ :=
  directSumDyadicWavelet R + directSumDyadicCoherent R

/-- Honest coefficient energy attached to the coupled scalar PNT packet.  The
coefficient spaces remain a direct sum; only their scalar outputs are coupled. -/
def directSumCoupledPNTPacketEnergy (R : ℕ) : ℝ :=
  directSumDyadicWaveletEnergy R + directSumDyadicCoherentEnergy R

/-- Full scalar packet, including the exact reconstruction remainder. -/
def directSumCoupledFarPacket (R : ℕ) : ℂ :=
  directSumCoupledPNTPacket R + directSumDyadicFarRemainder R

/-- The coupled PNT packet is exactly the previously compiled high+low PNT
error.  This is only commutativity of the coherent/wavelet split. -/
theorem directSumCoupledPNTPacket_eq_PNTError (R : ℕ) :
    directSumCoupledPNTPacket R =
      primeSievePNTError R (squareRootEndpoint R) + directSumLowPNTError R := by
  rw [directSumPNTError_eq_coherent_add_wavelet]
  unfold directSumCoupledPNTPacket
  ring

/-- Exact reconstruction of the compiled FAR residual with no triangle or
Cauchy step. -/
theorem directSumCoupledFarPacket_eq_frozenTopFarResidual (R : ℕ) :
    directSumCoupledFarPacket R = lowWheelFrozenTopFarResidual R := by
  unfold directSumCoupledFarPacket directSumCoupledPNTPacket
  rw [directSumDyadicFar_reconstruction]
  ring

/-- **Open coupled dispersion target.**

This is the coefficient-energy statement measured by the numerical ratio
`kappa_R = |W_R + C_R|^2 / (E_W(R) + E_C(R))`.  It intentionally keeps the
wavelet and coherent scalar aggregates coupled before squaring. -/
def DirectSumCoupledPacketDispersionBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ R : ℕ, 56 ≤ R →
        ‖directSumCoupledPNTPacket R‖ ^ 2 ≤
          D * Real.rpow (squareRootEndpoint R : ℝ) ε *
            directSumCoupledPNTPacketEnergy R

/-- **Open fixed-scale absorption target for the coupled packet.**

Given a global coupled-dispersion coefficient at one exponent, this statement
asks for a fixed FAR-4 constant while preserving the exact scalar cancellation
between the PNT packet and reconstruction remainder.  In particular, it does
*not* replace `|W+C+Rem|^2` by a sum of three separate squares. -/
def DirectSumCoupledPacketFarFourBudgetStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 ≤ D →
    (∀ R : ℕ, 56 ≤ R →
      ‖directSumCoupledPNTPacket R‖ ^ 2 ≤
        D * Real.rpow (squareRootEndpoint R : ℝ) ε *
          directSumCoupledPNTPacketEnergy R) →
    ∃ CF : ℝ, 0 ≤ CF ∧
      ∀ R : ℕ, ∀ K : ℝ,
        56 ≤ R →
        LowerMertensCriticalEnvelope R K →
        ‖directSumCoupledPNTPacket R + directSumDyadicFarRemainder R‖ ^ 2 ≤
          4 * farFourOddQ2DaughterEnergy R + CF * (R : ℝ) ^ 2 * K

/-- **Lossless deterministic terminal bridge.**

The only analytic hypotheses are the named coupled dispersion statement and
its fixed-scale absorption statement.  The proof itself never separates the
wavelet, coherent, and remainder scalars before taking the terminal norm. -/
theorem farFour_of_coupledPacketDispersion
    (hD : DirectSumCoupledPacketDispersionBoundedStatement)
    (hB : DirectSumCoupledPacketFarFourBudgetStatement) :
    FrozenTopFarFourEnergyStatement := by
  have hε : (0 : ℝ) < 1 := by norm_num
  obtain ⟨D, hD0, hDb⟩ := hD 1 hε
  obtain ⟨CF, hCF, hBb⟩ := hB 1 hε D hD0 hDb
  refine ⟨CF, hCF, ?_⟩
  intro R K hR hK
  have h := hBb R K hR hK
  rw [← directSumCoupledFarPacket_eq_frozenTopFarResidual R]
  simpa [directSumCoupledFarPacket] using h

end RHLean.Proof
