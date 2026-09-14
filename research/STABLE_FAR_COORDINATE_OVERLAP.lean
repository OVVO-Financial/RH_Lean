import «research.STABLE_FAR_OWNED_SMOOTH_SHELL_COMPLETION»
import RHLean.Proof.LowWheelCanonicalDefectReduction
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence
import RHLean.Analysis.PrimeSieveCollapseIdentity
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity

/-!
# Stable-far / canonical-defect coordinate overlap

PR #694 identifies the owned stable-far terminal products with the complete
squarefree `R`-smooth shell `(R,R^2)`.  The older canonical involution has an
apparently different fixed-state coordinate, but its face geometry is the same
open/closed product shell.  This file tests and records that overlap exactly,
before any norm is taken.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Boolean-face realization of the smooth square shell. -/
def lowWheelFrozenTopFarSmoothShellFaces (R : ℕ) : Finset (Finset ℕ) :=
  frozenPrimeUniverseWindowFaces (primesUpTo R) R (squareRootEndpoint R)

/-- Prime-face product is injective on the smooth shell faces. -/
theorem lowWheelFrozenTopFarSmoothShellFaces_product_injOn (R : ℕ) :
    Set.InjOn primeFaceProduct (lowWheelFrozenTopFarSmoothShellFaces R : Set (Finset ℕ)) := by
  intro t ht u hu hprod
  have htPow := (mem_frozenPrimeUniverseWindowFaces.mp ht).1
  have huPow := (mem_frozenPrimeUniverseWindowFaces.mp hu).1
  have htSub := Finset.mem_powerset.mp htPow
  have huSub := Finset.mem_powerset.mp huPow
  exact (primeFaceProduct_eq_iff
    (fun p hp => prime_of_mem_primesUpTo (htSub hp))
    (fun p hp => prime_of_mem_primesUpTo (huSub hp))).mp hprod

/-- The Boolean-face shell and #694's integer smooth shell are literally the
same finite population under prime-face product. -/
theorem lowWheelFrozenTopFarSmoothShellFaces_image_eq_smoothShell
    (R : ℕ) (hR : 2 ≤ R) :
    (lowWheelFrozenTopFarSmoothShellFaces R).image primeFaceProduct =
      lowWheelFrozenTopFarSmoothShell R := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨t, ht, rfl⟩
    rcases mem_frozenPrimeUniverseWindowFaces.mp ht with ⟨htPow, hlow, hupp⟩
    have htSub := Finset.mem_powerset.mp htPow
    have hprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact prime_of_mem_primesUpTo (htSub hp)
    have hmu := moebius_primeFaceProduct_eq_booleanCubeSign t hprime
    have hmuNe : μ (primeFaceProduct t) ≠ 0 := by
      rw [hmu]
      simp [booleanCubeSign]
    have hsq : Squarefree (primeFaceProduct t) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
    have hltR2 : primeFaceProduct t < R ^ 2 := by
      have hXlt : squareRootEndpoint R < R ^ 2 := by
        unfold squareRootEndpoint
        have hpos : 0 < R ^ 2 := by positivity
        exact Nat.pred_lt (Nat.ne_of_gt hpos)
      exact hupp.trans_lt hXlt
    have hprodPos : 0 < primeFaceProduct t :=
      primeFaceProduct_pos_of_mem_powerset htPow
    have hlpf : canonicalLargestPrimeFactor (primeFaceProduct t) ≤ R := by
      apply (canonicalLargestPrimeFactor_le_iff_forall_primeFactors_le
        (by omega : 1 ≤ R) hprodPos).2
      intro p hpFactors
      have hpData := Nat.mem_primeFactors.mp hpFactors
      have hpPrime : p.Prime := hpData.1
      have hpDiv : p ∣ primeFaceProduct t := hpData.2.1
      have hpDivProd : p ∣ t.prod id := by
        simpa [primeFaceProduct] using hpDiv
      rcases (Prime.dvd_finset_prod_iff hpPrime.prime id).mp hpDivProd with
        ⟨q, hqt, hpq⟩
      have hqPrime := hprime q hqt
      rcases hqPrime.eq_one_or_self_of_dvd p hpq with hpOne | hpEq
      · exact (hpPrime.ne_one hpOne).elim
      · subst p
        exact (mem_primesUpTo.mp (htSub hqt)).2
    exact mem_lowWheelFrozenTopFarSmoothShell.mpr ⟨hlow, hltR2, hsq, hlpf⟩
  · intro hn
    rcases mem_lowWheelFrozenTopFarSmoothShell.mp hn with
      ⟨hlow, hupp, hsq, hlpf⟩
    let t := squarefreePrimeFace n
    have hnPos : 0 < n := by omega
    have htSub : t ⊆ primesUpTo R := by
      intro p hp
      have hpLe : p ≤ R :=
        (canonicalLargestPrimeFactor_le_iff_forall_primeFactors_le
          (by omega : 1 ≤ R) hnPos).1 hlpf p hp
      exact mem_primesUpTo.mpr ⟨(Nat.mem_primeFactors.mp hp).1, hpLe⟩
    have hprod : primeFaceProduct t = n :=
      primeFaceProduct_squarefreePrimeFace hsq
    apply Finset.mem_image.mpr
    refine ⟨t, ?_, hprod⟩
    apply mem_frozenPrimeUniverseWindowFaces.mpr
    refine ⟨Finset.mem_powerset.mpr htSub, ?_, ?_⟩
    · simpa [hprod] using hlow
    · rw [hprod]
      unfold squareRootEndpoint
      exact Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hupp)

/-- The Möbius mass of #694's smooth terminal shell is the ordinary frozen
window mass on the old canonical low-wheel faces. -/
theorem lowWheelFrozenTopFarSmoothShell_mass_eq_window
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ lowWheelFrozenTopFarSmoothShell R, canonicalMoebiusWeight n) =
      ((frozenPrimeUniverseWindowMass (primesUpTo R) R
        (squareRootEndpoint R) : ℤ) : ℂ) := by
  rw [← lowWheelFrozenTopFarSmoothShellFaces_image_eq_smoothShell R hR]
  unfold lowWheelFrozenTopFarSmoothShellFaces frozenPrimeUniverseWindowMass
  rw [Finset.sum_image]
  · push_cast
    apply Finset.sum_congr rfl
    intro t ht
    have htPow := (mem_frozenPrimeUniverseWindowFaces.mp ht).1
    have htSub := Finset.mem_powerset.mp htPow
    have hmu := moebius_primeFaceProduct_eq_booleanCubeSign t
      (fun p hp => prime_of_mem_primesUpTo (htSub hp))
    simp [canonicalMoebiusWeight, hmu]
  · intro a ha b hb hab
    exact lowWheelFrozenTopFarSmoothShellFaces_product_injOn R ha hb hab

/-- **First cross-coordinate collapse.**  The newly saturated stable-far smooth
terminal shell is exactly the old canonical fixed-state ledger. -/
theorem lowWheelFrozenTopFarSmoothShell_mass_eq_fixedLedger
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ lowWheelFrozenTopFarSmoothShell R, canonicalMoebiusWeight n) =
      lowWheelCanonicalFixedLedger R := by
  rw [lowWheelFrozenTopFarSmoothShell_mass_eq_window R hR]
  rw [frozenPrimeUniverseWindowMass_eq_sub]
  · rw [lowWheelCanonicalFixedLedger_eq_frozenDifference R hR]
    push_cast
  · have hquad : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega

/-- The #694 owned terminal products therefore carry exactly the canonical
fixed-state mass. -/
theorem lowWheelFrozenTopFarOwnedProducts_mass_eq_fixedLedger
    (R : ℕ) (hR : 56 ≤ R) :
    (∑ n ∈ lowWheelFrozenTopFarOwnedProducts R, canonicalMoebiusWeight n) =
      lowWheelCanonicalFixedLedger R := by
  rw [lowWheelFrozenTopFarOwnedProducts_eq_smoothShell R hR]
  exact lowWheelFrozenTopFarSmoothShell_mass_eq_fixedLedger R (by omega)

/-- The two old stable-far owned images are the fixed sector of the canonical
involution. -/
theorem lowWheelInternalMate_add_topImage_eq_fixedLedger
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelCanonicalRepeatedTerminalInternalMateLedger R +
        lowWheelFrozenCofactorTopImageLedger R =
      lowWheelCanonicalFixedLedger R := by
  rw [lowWheelInternalMate_add_topImage_eq_ownedProductMass R,
    lowWheelFrozenTopFarOwnedProducts_mass_eq_fixedLedger R hR]

/-- Hence the owned terminal mass is also full transport minus the canonical
defect, using the original canonical involution itself. -/
theorem lowWheelFrozenTopFarOwnedProducts_mass_eq_transport_sub_defect
    (R : ℕ) (hR : 56 ≤ R) :
    (∑ n ∈ lowWheelFrozenTopFarOwnedProducts R, canonicalMoebiusWeight n) =
      squareRootTransportCofactorFirst R - lowWheelCanonicalDefectLedger R := by
  rw [lowWheelFrozenTopFarOwnedProducts_mass_eq_fixedLedger R hR,
    squareRootTransportCofactorFirst_eq_canonicalPhysicalLedger R (by omega),
    lowWheelCanonicalPhysicalLedger_eq_fixed_add_defect]
  ring

end RHLean.Proof
