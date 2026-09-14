import Mathlib
import «research.LOW_OWNER_HIGH_Q2_SCALAR_CANCELLATION»

/-!
# LOW-A owner atoms are the physical child-far slices

The corrected q-indexed synthesis atom is

  A_q = M(X/q^2) + NearHigh_q - IntermediateTower_q - Go_q.

For every scheduled prime q<R, the exact coboundary and far-base transport
identities imply

  A_q = -FarBase_q.

The compiled ownerwise common-base bridge then identifies `FarBase_q` with the
literal q^2 child-far slice.  Thus the scalar left after all q-indexed Euler
cancellations is not an isolated Mertens daughter and not a Stokes increment:
it is exactly the signed physical far slice.  Any LOW-A estimate must therefore
keep these slices coupled to stable-far renewal and terminal products.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- One complete owner synthesis atom is exactly the negative common-q far-base
column. -/
theorem farFourQ2OwnerSynthesisAtom_eq_neg_farBase
    {R q : ℕ} (hqmem : q ∈ primesUpTo (R - 1)) :
    farFourQ2OwnerSynthesisAtom R q =
      -(((q2DaughterFarBaseColumn R q : ℤ) : ℂ)) := by
  have hqData := mem_primesUpTo.mp hqmem
  have hqPrime := hqData.1
  have hqR : q < R := by
    have hq2 := hqPrime.two_le
    omega
  have hcob := q2DaughterHighTransport_eq_go_sub_mertens_all
    (q := q) (X := squareRootEndpoint R) hqPrime
  have hfar := q2DaughterFarHighTransport_eq_base_sub_intermediatePrimeTower
    (R := R) (q := q) hqR
  unfold farFourQ2OwnerSynthesisAtom q2DaughterNearHighTransport
  rw [hcob, hfar]
  push_cast
  ring

/-- **Physical owner atom.**  The same scalar is the negative literal child-far
slice mass on the q^2 daughter. -/
theorem farFourQ2OwnerSynthesisAtom_eq_neg_childFarSlice
    {R q : ℕ} (hqmem : q ∈ primesUpTo (R - 1)) :
    farFourQ2OwnerSynthesisAtom R q =
      -(∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) := by
  rw [farFourQ2OwnerSynthesisAtom_eq_neg_farBase hqmem,
    q2DaughterFarBaseColumn_cast_eq_childFarSliceMass
      (mem_primesUpTo.mp hqmem).1]

/-- The entire low-owner scalar packet is therefore a signed sum of physical
child-far slices, with no per-owner energy estimate inserted. -/
theorem sum_lowQ2OwnerSynthesisAtoms_eq_neg_childFarSlices
    (R : ℕ) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        farFourQ2OwnerSynthesisAtom R q) =
      -(∑ q ∈ canonicalRoughLowQ2Owners R,
          ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
            canonicalMoebiusWeight dp.1) := by
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        farFourQ2OwnerSynthesisAtom R q) =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        -(∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
            canonicalMoebiusWeight dp.1) := by
          apply Finset.sum_congr rfl
          intro q hq
          have hodd : q ∈ (primesUpTo (R - 1)).erase 2 := by
            exact (Finset.mem_sdiff.mp hq).1
          exact farFourQ2OwnerSynthesisAtom_eq_neg_childFarSlice
            (Finset.mem_erase.mp hodd).2
    _ = -(∑ q ∈ canonicalRoughLowQ2Owners R,
          ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
            canonicalMoebiusWeight dp.1) := by
          rw [Finset.sum_neg_distrib]

end RHLean.Proof
