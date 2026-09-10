import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SquareRootLowPrimeGoSecondContactSources

/-!
# Canonical one-dimensional carrier for all Go second-contact daughters

After all prime owners are reassembled, the `q^2` Go daughters are not an
abstract family of overlapping scalar channels.  They form one arithmetic set.
For the complete prime schedule through `X`, a squarefree integer `m > 1`
belongs to that set exactly when its canonical largest prime can make one more
contact below the parent cutoff:

`P+(m) * m <= X`.

The already-proved half-scale theorem then gives `m <= X/2`.  This file records
the converse and packages the whole residual cascade as one ordinary Mobius sum
on that canonical triangular carrier.  No norm or cancellation estimate is
asserted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- The owner-free canonical description of the complete second-contact source
population. -/
def squareRootLowPrimeCanonicalSecondContactSources (X : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (X / 2)).filter fun m =>
    Squarefree m ∧ canonicalLargestPrimeFactor m * m ≤ X

/-- A concrete Go second-contact child is squarefree. -/
theorem squareRootLowPrimeGoSecondContactSource_squarefree
    {Q : Finset ℕ} {X m : ℕ}
    (hprime : ∀ q ∈ Q, q.Prime)
    (hm : m ∈ squareRootLowPrimeGoSecondContactSources Q X) :
    Squarefree m := by
  rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
  have hq := hprime q hqQ
  rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage hq] at hmq
  rcases Finset.mem_image.mp hmq with ⟨c, hc, rfl⟩
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hc with
    ⟨hc1, _hcB, hcsq, hcrough⟩
  have hqNot : ¬ q ∣ c := by
    intro hqd
    by_cases hcEq : c = 1
    · subst c
      exact hq.not_dvd_one hqd
    · have hcgt : 1 < c := by omega
      have hle := prime_dvd_le_canonicalLargestPrimeFactor hcgt hq hqd
      omega
  have hcop : Nat.Coprime q c := (hq.coprime_iff_not_dvd).2 hqNot
  exact (Nat.squarefree_mul hcop).2 ⟨hq.squarefree, hcsq⟩

/-- **Exact canonical carrier identification.**  Summing over every prime owner
through `X`, the disjoint `q^2` daughter population is precisely the squarefree
integers whose canonical largest prime can make one further multiplicative
contact below `X`. -/
theorem squareRootLowPrimeGoSecondContactSources_primesUpTo_eq_canonical
    (X : ℕ) :
    squareRootLowPrimeGoSecondContactSources (primesUpTo X) X =
      squareRootLowPrimeCanonicalSecondContactSources X := by
  ext m
  constructor
  · intro hm
    have hprime : ∀ q ∈ primesUpTo X, q.Prime := by
      intro q hq
      exact (mem_primesUpTo.mp hq).1
    have hhalf := squareRootLowPrimeGoSecondContactSources_subset_halfScale
      (Q := primesUpTo X) (X := X) hprime hm
    have howner := squareRootLowPrimeGoSecondContactSource_owner_exists
      (Q := primesUpTo X) (X := X) hprime hm
    have hsq := squareRootLowPrimeGoSecondContactSource_squarefree hprime hm
    have hmTwo : 2 ≤ m := by
      rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
      have hq := (mem_primesUpTo.mp hqQ).1
      rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage hq] at hmq
      rcases Finset.mem_image.mp hmq with ⟨c, hc, hmc⟩
      have hc1 := (mem_squareRootLowPrimeGoSmoothCofactors.mp hc).1
      rw [← hmc]
      nlinarith [hq.two_le]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hmTwo, (Finset.mem_Icc.mp hhalf).2⟩,
      hsq, howner.2⟩
  · intro hm
    rcases Finset.mem_filter.mp hm with ⟨hmIcc, hsq, hcontact⟩
    have hmgt : 1 < m := by omega
    let q := canonicalLargestPrimeFactor m
    let c := canonicalCofactor m
    have hdata : CanonicalSourceData q c := by
      simpa [q, c] using canonicalSourceData_of_squarefree hsq hmgt
    rcases hdata with ⟨hq, hc1, hcsq, _hcop, hdom⟩
    have hprod : q * c = m := by
      simpa [q, c, Nat.mul_comm] using
        canonicalCofactor_mul_largestPrimeFactor hmgt
    have hqX : q ≤ X := by
      have hqm : q ≤ q * m := by
        exact Nat.le_mul_of_pos_right q (by omega)
      exact hqm.trans hcontact
    have hqMem : q ∈ primesUpTo X := mem_primesUpTo.mpr ⟨hq, hqX⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hqMem, ?_⟩
    rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage hq]
    apply Finset.mem_image.mpr
    refine ⟨c, ?_, hprod⟩
    apply mem_squareRootLowPrimeGoSmoothCofactors.mpr
    refine ⟨hc1, ?_, hcsq, ?_⟩
    · apply (Nat.le_div_iff_mul_le (Nat.mul_pos hq.pos hq.pos)).2
      rw [show c * (q * q) = q * (q * c) by ring, hprod]
      exact hcontact
    · by_cases hcEq : c = 1
      · subst c
        simp [canonicalLargestPrimeFactor, hq.one_lt]
      · have hcgt : 1 < c := by omega
        exact hdom _ (canonicalLargestPrimeFactor_prime hcgt)
          (canonicalLargestPrimeFactor_dvd hcgt)

/-- The full square-residual cascade is therefore one signed Mobius sum on the
canonical triangular carrier.  This is the owner-free form of the remaining
cross-owner quantitative problem. -/
theorem squareRootLowPrimeGoWallSquareResidualTotal_primesUpTo_eq_canonicalMobiusSum
    (X : ℕ) :
    squareRootLowPrimeGoWallSquareResidualTotal (primesUpTo X) X =
      -∑ m ∈ squareRootLowPrimeCanonicalSecondContactSources X, μ m := by
  have hprime : ∀ q ∈ primesUpTo X, q.Prime := by
    intro q hq
    exact (mem_primesUpTo.mp hq).1
  rw [squareRootLowPrimeGoWallSquareResidualTotal_eq_neg_sourceMobiusSum hprime,
    squareRootLowPrimeGoSecondContactSources_primesUpTo_eq_canonical]

end RHLean.Proof