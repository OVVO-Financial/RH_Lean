import Mathlib
import RHLean.Arithmetic.PrimeWheelCorrectedLocalFlip

noncomputable section

open scoped BigOperators

namespace RHLean.Arithmetic

/-!
# Fixed-point square kills for the corrected prime-wheel collision field

The physical collision involution leaves three slot labels fixed.  The useful
arithmetic fact is stronger than a cardinality bound: whenever a fixed physical
site carries a square hit from one selected prime coordinate, the complete
corrected `raw - 2 * smoothCore` field vanishes at that site exactly.

This removes the fixed-point contribution from the finite-frontier pairing
identity.  After a physical sign-reversing realization has been supplied for
the nonfixed labels, the entire collision frontier is therefore reduced to the
explicit mate-crosses-cutoff defect.
-/

/-- A square hit from any selected prime coordinate kills the complete seeded
prime comb. -/
theorem seededPrimeComb_eq_zero_of_square_hit
    (S : Finset ℕ) (p n : ℕ)
    (hpS : p ∈ S) (hsq : p ^ 2 ∣ n) :
    seededPrimeComb S n = 0 := by
  classical
  have hlocal : localPrimeComb p n = 0 := by
    simp [localPrimeComb, hsq]
  have hprod :=
    Finset.mul_prod_erase S (fun q => localPrimeComb q n) hpS
  unfold seededPrimeComb
  rw [← hprod, hlocal]
  simp

/-- The smooth-core contribution also vanishes at a selected-prime square hit,
because its only possible nonzero value is the already-killed seeded comb. -/
theorem primeWheelSmoothCoreSite_eq_zero_of_square_hit
    (S : Finset ℕ) (upper p n : ℕ)
    (hpS : p ∈ S) (hsq : p ^ 2 ∣ n) :
    primeWheelSmoothCoreSite S upper n = 0 := by
  have hseed := seededPrimeComb_eq_zero_of_square_hit S p n hpS hsq
  simp [primeWheelSmoothCoreSite, hseed]

/-- **Exact square-kill law for the corrected field.**  The signed
`raw - 2 * smoothCore` site is zero whenever one selected prime square divides
the site. -/
theorem correctedPrimeWheelSite_eq_zero_of_square_hit
    (S : Finset ℕ) (upper p n : ℕ)
    (hpS : p ∈ S) (hsq : p ^ 2 ∣ n) :
    correctedPrimeWheelSite S upper n = 0 := by
  have hseed := seededPrimeComb_eq_zero_of_square_hit S p n hpS hsq
  have hcore :=
    primeWheelSmoothCoreSite_eq_zero_of_square_hit S upper p n hpS hsq
  simp [correctedPrimeWheelSite, hseed, hcore]

/-- A fixed physical collision label has zero corrected weight as soon as its
site realization forces a square hit from a selected prime coordinate. -/
theorem correctedCollisionSiteWeight_eq_zero_of_fixed_square_hit
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (hfixedSquare : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s = s → p ^ 2 ∣ site s) :
    ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s = s →
      correctedCollisionSiteWeight S upper site s = 0 := by
  intro s hs
  unfold correctedCollisionSiteWeight
  exact correctedPrimeWheelSite_eq_zero_of_square_hit
    S upper p (site s) hpS (hfixedSquare s hs)

/-- The entire fixed-label part of an arbitrary collision frontier vanishes
under the physical square-hit hypothesis. -/
theorem sum_correctedCollisionSiteWeight_fixedPart_eq_zero
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (hfixedSquare : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s = s → p ^ 2 ∣ site s)
    (F : Finset TwoPrimeCollisionState) :
    (∑ s ∈ collisionInvolutionFixedPart F,
      correctedCollisionSiteWeight S upper site s) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro s hs
  have hfix := (Finset.mem_filter.mp hs).2
  exact correctedCollisionSiteWeight_eq_zero_of_fixed_square_hit
    S upper p site hpS hfixedSquare s hfix

/-- **Fixed-point-free physical frontier reduction.**  Once the nonfixed
physical labels satisfy the actual corrected-field sign law and the fixed labels
carry a selected-prime square hit, the full incomplete CRT frontier equals only
the explicit mate-crosses-cutoff defect. -/
theorem sum_correctedCollisionSiteWeight_prefix_eq_defect
    (S : Finset ℕ) (upper p q K : ℕ)
    (hcop : Nat.Coprime (p ^ 2) (q ^ 2))
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (hupper : ∀ s : TwoPrimeCollisionState, site s ≤ upper)
    (hstate : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      localPrimeExponentState p
          (site (collisionExponentStateInvolution s)) =
        primeCombExponentFlip (localPrimeExponentState p (site s)))
    (hother : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      ∀ r ∈ S, r ≠ p →
        localPrimeComb r (site (collisionExponentStateInvolution s)) =
          localPrimeComb r (site s))
    (hsmooth : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s ≠ s →
      (IsPrimeWheelSmooth S
          (site (collisionExponentStateInvolution s)) ↔
        IsPrimeWheelSmooth S (site s)))
    (hfixedSquare : ∀ s : TwoPrimeCollisionState,
      collisionExponentStateInvolution s = s → p ^ 2 ∣ site s) :
    (∑ s ∈ collisionExponentStatePrefixFrontier p q K hcop,
        correctedCollisionSiteWeight S upper site s) =
      ∑ s ∈ collisionInvolutionDefectPart
          (collisionExponentStatePrefixFrontier p q K hcop),
        correctedCollisionSiteWeight S upper site s := by
  rw [sum_correctedCollisionSiteWeight_prefix_eq_fixed_add_defect
    S upper p q K hcop site hpS hupper hstate hother hsmooth]
  rw [sum_correctedCollisionSiteWeight_fixedPart_eq_zero
    S upper p site hpS hfixedSquare
    (collisionExponentStatePrefixFrontier p q K hcop)]
  simp

end RHLean.Arithmetic
