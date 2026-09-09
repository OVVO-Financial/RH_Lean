import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoSecondContactSources

/-!
# Global signed second-contact contraction

The first global Go reassembly already removes the old-owner multiplicity: every
square residual is transported to one arithmetic child `m`, whose canonical
largest prime recovers its owner.  The compiled half-scale bound keeps the child
itself and uses only `P⁺(m) >= 2`.

For the next descent, strip that canonical owner *after* the global reassembly.
If `q = P⁺(m)` and `c = canonicalCofactor m`, then the exact owner contact is

`q * m = q^2 * c <= X`.

Since every owner is prime, `q^2 >= 4`.  Thus the canonical parent lies at the
strict quarter scale `c <= X/4`.  This is a genuine scale gain on one common
signed carrier; no ownerwise norm or triangle inequality is used.  The price is
that the parent map is not injective: several fresh owners can have the same
canonical cofactor.  Subsequent declarations will keep that owner multiplicity
as an exact signed fibre rather than discard it by absolute values.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Canonical parents of the globally reassembled second-contact source set. -/
def squareRootLowPrimeGoSecondContactParentCofactors
    (Q : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (squareRootLowPrimeGoSecondContactSources Q X).image canonicalCofactor

/-- **Quarter-scale canonical-parent descent.**  Removing the unique largest
prime from a globally reassembled second-contact child gains a full factor
four: `q*m <= X`, `m=q*c`, and `q>=2` give `4*c <= X`. -/
theorem squareRootLowPrimeGoSecondContactSource_canonicalCofactor_le_quarterScale
    {Q : Finset ℕ} {X m : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime)
    (hm : m ∈ squareRootLowPrimeGoSecondContactSources Q X) :
    canonicalCofactor m ≤ X / 4 := by
  rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
  have hqPrime := hprime q hqQ
  have hcoords :=
    squareRootLowPrimeGoWallSquareResidualChild_coordinates hqPrime hmq
  have hcontact :=
    squareRootLowPrimeGoWallSquareResidualChild_owner_mul_le hqPrime hmq
  have hq2 : q * (q * canonicalCofactor m) ≤ X := by
    rw [hcoords.2]
    exact hcontact
  have hfourqq : 4 ≤ q * q := by
    nlinarith [hqPrime.two_le]
  have hfour :
      4 * canonicalCofactor m ≤ q * (q * canonicalCofactor m) := by
    have h := Nat.mul_le_mul_right (canonicalCofactor m) hfourqq
    simpa [Nat.mul_assoc] using h
  have h4X : 4 * canonicalCofactor m ≤ X := hfour.trans hq2
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (4 : ℕ))).2
  simpa [Nat.mul_comm] using h4X

/-- A second-contact child has a positive canonical parent. -/
theorem squareRootLowPrimeGoSecondContactSource_canonicalCofactor_pos
    {Q : Finset ℕ} {X m : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime)
    (hm : m ∈ squareRootLowPrimeGoSecondContactSources Q X) :
    0 < canonicalCofactor m := by
  rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
  have hqPrime := hprime q hqQ
  have hcoords :=
    squareRootLowPrimeGoWallSquareResidualChild_coordinates hqPrime hmq
  rcases mem_squareRootLowPrimeGoWallSquareResidualChildren.mp hmq with
    ⟨u, hu, hchild⟩
  have huPos : 0 < primeFaceProduct u :=
    primeFaceProduct_pos_of_mem_powerset
      (mem_squareRootLowPrimeGoWallSquareResidualFaces.mp hu).1
  have hmPos : 0 < m := by
    rw [← hchild]
    exact Nat.mul_pos hqPrime.pos huPos
  by_contra hnot
  have hc0 : canonicalCofactor m = 0 := Nat.eq_zero_of_not_pos hnot
  rw [hc0, Nat.mul_zero] at hcoords
  omega

/-- The whole canonical-parent image therefore lives in one quarter-scale
interval.  This is a support theorem on the globally reassembled carrier, not a
sum of bounds over old owners. -/
theorem squareRootLowPrimeGoSecondContactParentCofactors_subset_quarterScale
    {Q : Finset ℕ} {X : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime) :
    squareRootLowPrimeGoSecondContactParentCofactors Q X ⊆
      Finset.Icc 1 (X / 4) := by
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨m, hm, rfl⟩
  exact Finset.mem_Icc.mpr
    ⟨squareRootLowPrimeGoSecondContactSource_canonicalCofactor_pos hprime hm,
      squareRootLowPrimeGoSecondContactSource_canonicalCofactor_le_quarterScale
        hprime hm⟩

/-- In particular there are at most `X/4` distinct canonical parents.  No claim
is made here that the parent map is injective; the exact owner fibre is the next
object to cancel. -/
theorem squareRootLowPrimeGoSecondContactParentCofactors_card_le_quarterScale
    {Q : Finset ℕ} {X : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime) :
    (squareRootLowPrimeGoSecondContactParentCofactors Q X).card ≤ X / 4 := by
  calc
    (squareRootLowPrimeGoSecondContactParentCofactors Q X).card ≤
        (Finset.Icc 1 (X / 4)).card :=
      Finset.card_le_card
        (squareRootLowPrimeGoSecondContactParentCofactors_subset_quarterScale
          hprime)
    _ = X / 4 := by simp

end RHLean.Proof
