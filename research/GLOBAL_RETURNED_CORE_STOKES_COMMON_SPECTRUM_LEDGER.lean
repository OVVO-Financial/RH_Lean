import Mathlib
import RHLean.Analysis.PrimeWheelConductorGram
import «research.GLOBAL_RETURNED_CORE_STOKES_ARBITRARY_CLOCK_WHEEL»
import «research.GLOBAL_RETURNED_CORE_STOKES_ALL_ENDPOINT_MERTENS_LEDGER»

/-!
# One common corrected spectrum for the complete Stokes endpoint gap

This file is still identity-only.

For `R >= 2`, the arbitrary-clock wheel from the preceding file carries one
corrected joint spectrum on the whole physical clock `(0,X_R]`.  The root
prefix `R-1`, the full endpoint `X_R`, and every genuine LOW q^2 daughter
endpoint therefore differ only by their finite prefix windows.

We group that *same* corrected spectrum by reduced additive conductor and form
one conductor component of the actual Stokes endpoint gap

  M(R-1) - M(X_R) - sum_q M(Y_q)/q.

The resulting exact theorem is

  H_R = sum_c H_{R,c},

with no conductor dropped.  A second exact theorem expands the associated
complex Gram as the full double conductor sum, retaining every diagonal and
off-diagonal block.  No frame estimate, triangle inequality, endpoint shell
bound, or conductor-one cancellation is used here.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

attribute [local instance] Classical.propDecidable

/-- A genuine LOW q^2 daughter cutoff is positive. -/
theorem rawQ2ChildCutoff_pos_of_mem_lowQ2Owners
    {R q : ℕ} (hR : 2 ≤ R)
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

/-- Every literal LOW daughter cutoff stays on the common physical clock. -/
theorem rawQ2ChildCutoff_le_squareRootEndpoint
    (R q : ℕ) :
    rawQ2ChildCutoff R q ≤ squareRootEndpoint R := by
  unfold rawQ2ChildCutoff
  exact Nat.div_le_self _ _

/-- One reduced-conductor component of the exact all-endpoint Stokes gap. -/
def lowOwnerStokesEndpointConductorComponent
    (R : ℕ) (hR : 2 ≤ R) (c : ℕ) : ℂ :=
  let W := lowOwnerStokesWheelSystem R hR
  primeWheelConductorComponent W (R - 1) c -
    primeWheelConductorComponent W (squareRootEndpoint R) c -
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℂ)) *
          primeWheelConductorComponent W (rawQ2ChildCutoff R q) c

/-- Full conductor-conductor Gram block of the Stokes endpoint gap. -/
def lowOwnerStokesEndpointConductorGramBlock
    (R : ℕ) (hR : 2 ≤ R) (c c' : ℕ) : ℂ :=
  lowOwnerStokesEndpointConductorComponent R hR c *
    conj (lowOwnerStokesEndpointConductorComponent R hR c')

/-- Complete conductor Gram energy of the endpoint gap; no cross block is
removed. -/
def lowOwnerStokesEndpointConductorGramEnergy
    (R : ℕ) (hR : 2 ≤ R) : ℂ :=
  let W := lowOwnerStokesWheelSystem R hR
  ∑ c ∈ Finset.range (W.modulus + 1),
    ∑ c' ∈ Finset.range (W.modulus + 1),
      lowOwnerStokesEndpointConductorGramBlock R hR c c'

/-- The reciprocal LOW daughter endpoint column is represented by prefix
windows of the same corrected joint spectrum. -/
theorem lowOwnerReciprocalMertensEndpointSum_eq_commonSpectrum
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerReciprocalMertensEndpointSum R =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℂ)) *
          (lowOwnerStokesWheelSystem R hR).spectralPrefix
            (rawQ2ChildCutoff R q) := by
  unfold lowOwnerReciprocalMertensEndpointSum
  apply Finset.sum_congr rfl
  intro q hq
  rw [lowOwnerStokesWheel_spectralPrefix_eq_mertensSummatory
    hR
    (rawQ2ChildCutoff_pos_of_mem_lowQ2Owners hR hq)
    (rawQ2ChildCutoff_le_squareRootEndpoint R q)]

/-- **Exact common-spectrum conductor decomposition of the actual Stokes
endpoint gap.** -/
theorem lowOwnerStokesAllEndpointMertensGap_eq_sum_conductorComponents
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerStokesAllEndpointMertensGap R =
      ∑ c ∈ Finset.range
          ((lowOwnerStokesWheelSystem R hR).modulus + 1),
        lowOwnerStokesEndpointConductorComponent R hR c := by
  let W := lowOwnerStokesWheelSystem R hR
  let C : Finset ℕ := Finset.range (W.modulus + 1)
  have hRm1pos : 0 < R - 1 := by omega
  have hRm1le : R - 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hRR : R ≤ R * R := by nlinarith
    rw [pow_two]
    omega
  have hXpos : 0 < squareRootEndpoint R :=
    squareRootEndpoint_pos_of_two_le hR
  have hroot : W.spectralPrefix (R - 1) = mertensSummatory (R - 1) := by
    dsimp [W]
    exact lowOwnerStokesWheel_spectralPrefix_eq_mertensSummatory hR hRm1pos hRm1le
  have hfull : W.spectralPrefix (squareRootEndpoint R) =
      mertensSummatory (squareRootEndpoint R) := by
    dsimp [W]
    exact lowOwnerStokesWheel_spectralPrefix_eq_mertensSummatory
      hR hXpos le_rfl
  have hdaughter :
      lowOwnerReciprocalMertensEndpointSum R =
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) * W.spectralPrefix (rawQ2ChildCutoff R q) := by
    dsimp [W]
    exact lowOwnerReciprocalMertensEndpointSum_eq_commonSpectrum hR
  have hswap :
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℂ)) *
          (∑ c ∈ C,
            primeWheelConductorComponent W (rawQ2ChildCutoff R q) c)) =
      ∑ c ∈ C,
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) *
            primeWheelConductorComponent W (rawQ2ChildCutoff R q) c := by
    calc
      (∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) *
            (∑ c ∈ C,
              primeWheelConductorComponent W (rawQ2ChildCutoff R q) c)) =
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          ∑ c ∈ C,
            (1 / (q : ℂ)) *
              primeWheelConductorComponent W (rawQ2ChildCutoff R q) c := by
          apply Finset.sum_congr rfl
          intro q _hq
          rw [Finset.mul_sum]
      _ = ∑ c ∈ C,
          ∑ q ∈ canonicalRoughLowQ2Owners R,
            (1 / (q : ℂ)) *
              primeWheelConductorComponent W (rawQ2ChildCutoff R q) c := by
          exact Finset.sum_comm
  unfold lowOwnerStokesAllEndpointMertensGap
  rw [← hroot, ← hfull, hdaughter]
  rw [spectralPrefix_eq_sum_conductorComponents,
    spectralPrefix_eq_sum_conductorComponents]
  simp_rw [spectralPrefix_eq_sum_conductorComponents]
  change
    (∑ c ∈ C, primeWheelConductorComponent W (R - 1) c) -
        (∑ c ∈ C,
          primeWheelConductorComponent W (squareRootEndpoint R) c) -
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) *
            ∑ c ∈ C,
              primeWheelConductorComponent W (rawQ2ChildCutoff R q) c) =
      ∑ c ∈ C,
        (primeWheelConductorComponent W (R - 1) c -
          primeWheelConductorComponent W (squareRootEndpoint R) c -
          ∑ q ∈ canonicalRoughLowQ2Owners R,
            (1 / (q : ℂ)) *
              primeWheelConductorComponent W (rawQ2ChildCutoff R q) c)
  rw [hswap]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]

/-- **Full conductor Gram identity for the Stokes endpoint gap.**  This is the
legal object on which any later completed-period alignment estimate must act. -/
theorem lowOwnerStokesEndpointConductorGramEnergy_eq_gap_mul_conj
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerStokesEndpointConductorGramEnergy R hR =
      lowOwnerStokesAllEndpointMertensGap R *
        conj (lowOwnerStokesAllEndpointMertensGap R) := by
  let W := lowOwnerStokesWheelSystem R hR
  let C : Finset ℕ := Finset.range (W.modulus + 1)
  have hsum := lowOwnerStokesAllEndpointMertensGap_eq_sum_conductorComponents hR
  change
    (∑ c ∈ C,
      ∑ c' ∈ C,
        lowOwnerStokesEndpointConductorComponent R hR c *
          conj (lowOwnerStokesEndpointConductorComponent R hR c')) =
      lowOwnerStokesAllEndpointMertensGap R *
        conj (lowOwnerStokesAllEndpointMertensGap R)
  rw [hsum]
  rw [map_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [Finset.mul_sum]

end RHLean.Proof
