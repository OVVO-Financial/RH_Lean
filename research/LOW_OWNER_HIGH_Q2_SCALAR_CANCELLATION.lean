import Mathlib
import «research.CANONICAL_ROUGH_Q2_TAIL_REDUCTION»
import RHLean.Proof.PostRootPartnerLogAlignment

/-!
# Exact scalar cancellation of the nonrecursive q^2 owner tail

PR #706 proves that every odd q^2 owner with `q^2 >= R` has daughter cutoff

  Y_q = floor((R^2-1)/q^2) < R.

At the signed scalar-synthesis level one can say more.  Since `Y_q < R`, the
far-prime portion of that owner's high-transport column is empty: no prime
`p > R+7` can also satisfy `p <= Y_q`.  Hence the near high-transport is the
entire high-transport column.  The already-compiled prime coboundary

  High_q = Go_q - M(Y_q)

then gives the exact cancellation

  M(Y_q) + NearHigh_q - Go_q = 0.

The same empty far-prime range kills the q^2-or-deeper intermediate-prime tower.
Thus the full q-indexed synthesis atom

  M(Y_q) + NearHigh_q - IntermediateTower_q - Go_q

vanishes pointwise for every odd owner with `q^2 >= R`.

The final theorem rewrites the whole frozen/top/far carrier as a sum of these
atoms over only the genuinely recursive odd owners `q^2 < R`, plus owner two,
minus the stable-far renewal and terminal product columns.  No norm is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A high q^2 owner has no far-prime high-transport population at all. -/
theorem q2DaughterFarHighTransport_eq_zero_of_mem_highQ2Owners
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ canonicalRoughHighQ2Owners R) :
    q2DaughterFarHighTransport R q = 0 := by
  have hY : rawQ2ChildCutoff R q < R :=
    rawQ2ChildCutoff_lt_parent_of_mem_highQ2Owners hR hq
  have hempty :
      frozenPrimeUniverseHighPrimeSet (R + 7)
          (squareRootEndpoint R / (q * q)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    have hpLower : R + 7 < p := hpData.2.1
    have hpUpper : p ≤ squareRootEndpoint R / (q * q) := hpData.2.2
    have hY' : squareRootEndpoint R / (q * q) < R := by
      simpa [rawQ2ChildCutoff] using hY
    omega
  unfold q2DaughterFarHighTransport
  rw [hempty]
  simp

/-- The q^2-or-deeper intermediate-prime tower has the same empty outer-prime
schedule on a high owner. -/
theorem q2DaughterFarIntermediatePrimeTower_eq_zero_of_mem_highQ2Owners
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ canonicalRoughHighQ2Owners R) :
    q2DaughterFarIntermediatePrimeTower R q = 0 := by
  have hY : rawQ2ChildCutoff R q < R :=
    rawQ2ChildCutoff_lt_parent_of_mem_highQ2Owners hR hq
  have hempty :
      frozenPrimeUniverseHighPrimeSet (R + 7)
          (squareRootEndpoint R / (q * q)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    have hpLower : R + 7 < p := hpData.2.1
    have hpUpper : p ≤ squareRootEndpoint R / (q * q) := hpData.2.2
    have hY' : squareRootEndpoint R / (q * q) < R := by
      simpa [rawQ2ChildCutoff] using hY
    omega
  unfold q2DaughterFarIntermediatePrimeTower
  rw [hempty]
  simp

/-- Therefore `near` is the whole high-transport column for every high q^2
owner. -/
theorem q2DaughterNearHighTransport_eq_highTransport_of_mem_highQ2Owners
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ canonicalRoughHighQ2Owners R) :
    q2DaughterNearHighTransport R q =
      q2DaughterHighTransport q (squareRootEndpoint R) := by
  unfold q2DaughterNearHighTransport
  rw [q2DaughterFarHighTransport_eq_zero_of_mem_highQ2Owners hR hq]
  ring

/-- **Exact high-owner scalar cancellation.**  The q^2 Mertens daughter,
near high-transport, and Go source cancel identically on every odd owner with
`q^2 >= R`.  No lower-envelope estimate and no norm is used. -/
theorem highQ2Owner_mertens_add_near_sub_go_eq_zero
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ canonicalRoughHighQ2Owners R) :
    (((mertensSummatoryInt (squareRootEndpoint R / (q * q)) : ℤ) : ℂ)) +
        (((q2DaughterNearHighTransport R q : ℤ) : ℂ)) -
        (((squareRootLowPrimeGoWallSquareResidual q
          (squareRootEndpoint R) : ℤ) : ℂ)) = 0 := by
  have hbase := (Finset.mem_filter.mp hq).1
  have hqPrime := (mem_primesUpTo.mp (Finset.mem_erase.mp hbase).2).1
  have hnear :=
    q2DaughterNearHighTransport_eq_highTransport_of_mem_highQ2Owners hR hq
  have hcob := q2DaughterHighTransport_eq_go_sub_mertens_all
    (q := q) (X := squareRootEndpoint R) hqPrime
  rw [hnear, hcob]
  push_cast
  ring

/-- One complete q-indexed scalar atom in the corrected ownerwise synthesis. -/
def farFourQ2OwnerSynthesisAtom (R q : ℕ) : ℂ :=
  (((mertensSummatoryInt (squareRootEndpoint R / (q * q)) : ℤ) : ℂ)) +
    (((q2DaughterNearHighTransport R q : ℤ) : ℂ)) -
    (((q2DaughterFarIntermediatePrimeTower R q : ℤ) : ℂ)) -
    (((squareRootLowPrimeGoWallSquareResidual q
      (squareRootEndpoint R) : ℤ) : ℂ))

/-- Every nonrecursive odd q^2 owner has zero complete scalar synthesis atom. -/
theorem farFourQ2OwnerSynthesisAtom_eq_zero_of_mem_highQ2Owners
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ canonicalRoughHighQ2Owners R) :
    farFourQ2OwnerSynthesisAtom R q = 0 := by
  have hmain := highQ2Owner_mertens_add_near_sub_go_eq_zero hR hq
  have htower :=
    q2DaughterFarIntermediatePrimeTower_eq_zero_of_mem_highQ2Owners hR hq
  unfold farFourQ2OwnerSynthesisAtom
  rw [htower]
  norm_num
  exact hmain

/-- The complete nonrecursive odd-owner scalar tail is therefore zero before
energy. -/
theorem sum_highQ2Owner_synthesisAtom_eq_zero
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ q ∈ canonicalRoughHighQ2Owners R,
      farFourQ2OwnerSynthesisAtom R q) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  exact farFourQ2OwnerSynthesisAtom_eq_zero_of_mem_highQ2Owners hR hq

/-- Before any owner split, the exact frozen/top/far carrier is the sum of the
complete q-indexed atoms minus the two genuinely first-power chronology columns. -/
theorem lowWheelFrozenTopFarResidual_eq_sum_q2OwnerAtoms_sub_renewal_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      (∑ q ∈ primesUpTo (R - 1), farFourQ2OwnerSynthesisAtom R q) -
        stableFarRenewalColumn R - stableFarTerminalProductColumn R := by
  rw [lowWheelFrozenTopFarResidual_eq_mertensColumn_add_ownerwiseError R hR]
  unfold squareEndpointQ2MertensColumn farFourAllPrimeOwnerwiseSynthesisError
    squareEndpointQ2NearHighTransportColumn
    squareEndpointQ2IntermediatePrimeTower squareEndpointQ2GoColumn
    farFourQ2OwnerSynthesisAtom
  push_cast
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- Odd owners split exactly into the recursive low sector and the cancelled
nonrecursive high sector. -/
theorem sum_odd_q2OwnerAtoms_eq_low_add_high (R : ℕ) :
    (∑ q ∈ (primesUpTo (R - 1)).erase 2,
      farFourQ2OwnerSynthesisAtom R q) =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        farFourQ2OwnerSynthesisAtom R q) +
      (∑ q ∈ canonicalRoughHighQ2Owners R,
        farFourQ2OwnerSynthesisAtom R q) := by
  have hsub := canonicalRoughHighQ2Owners_subset_oddOwners R
  have hs := Finset.sum_sdiff hsub
    (f := fun q => farFourQ2OwnerSynthesisAtom R q)
  simpa [canonicalRoughLowQ2Owners] using hs.symm

/-- **Low-owner signed normal form.**  At every square endpoint `R >= 56`, all
odd owners with `q^2 >= R` disappear algebraically.  The entire hard scalar is
therefore the genuinely recursive low-owner synthesis packet plus owner two,
minus stable-far renewal and terminal products.  This is strictly pre-energy. -/
theorem lowWheelFrozenTopFarResidual_eq_lowQ2Atoms_add_two_sub_renewal_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        farFourQ2OwnerSynthesisAtom R q) +
      farFourQ2OwnerSynthesisAtom R 2 -
      stableFarRenewalColumn R - stableFarTerminalProductColumn R := by
  have htwo : 2 ∈ primesUpTo (R - 1) :=
    mem_primesUpTo.mpr ⟨Nat.prime_two, by omega⟩
  have hall :=
    lowWheelFrozenTopFarResidual_eq_sum_q2OwnerAtoms_sub_renewal_sub_terminal
      R hR
  have herase := Finset.sum_erase_add
    (s := primesUpTo (R - 1))
    (f := fun q => farFourQ2OwnerSynthesisAtom R q) htwo
  have hsplit := sum_odd_q2OwnerAtoms_eq_low_add_high R
  have hhigh := sum_highQ2Owner_synthesisAtom_eq_zero R (by omega)
  rw [herase, hsplit, hhigh, add_zero] at hall
  exact hall

end RHLean.Proof
