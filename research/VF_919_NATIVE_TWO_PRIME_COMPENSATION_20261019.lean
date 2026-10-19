import «research.VF_MID_919_OAI_PHASE_ALIGNED_OWNER_COMPENSATION»
import «research.VF_MID_919_OAI_SIGNED_SIXTH_POWER_INLET»

/-!
# Native double-prime compensated owner source, retaining the physical weights

This formalizes the TWO distinct-prime interactions on the actual RH_Lean
first-owner AMP source. There are no imports from OAI's Hecke, moments or
nonvanishing libraries. Each occurrence is evaluated at its actual physical
site; the native daughter/root crossing weights, Mobius signs, and full
complex character phases are kept.

These are exact equations at every admissible p-free/q-free physical parent.
They are not a substitute for an analytic two-prime fourth-moment bound or
an assertion that OAI's holomorphic probe is equal to the VF source.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Actual two-prime marked source: first compensate the p child, then
compensate its q-translated counterpart at the SAME physical site weights.
The inverse row phase is only used on a nonvanishing row. -/
def vf919TwoPrimeAlignedPhysicalSite
    (R p q : ℕ) (chi : ℕ → ℂ) (a : ℕ) : ℂ :=
  vf919CharacterAlignedSite R p chi a +
    (chi q)⁻¹ * vf919CharacterAlignedSite R p chi (q * a)

/-- Unconditional four-occurrence expansion. A phase is not silently
cancelled; there are literally four source sites with their own weights. -/
theorem vf919TwoPrimeAlignedPhysicalSite_fourTerms
    (R p q a : ℕ) (chi : ℕ → ℂ) :
    vf919TwoPrimeAlignedPhysicalSite R p q chi a =
      vf919CharacterMobiusSite R chi a +
        (chi p)⁻¹ * vf919CharacterMobiusSite R chi (p * a) +
        (chi q)⁻¹ * vf919CharacterMobiusSite R chi (q * a) +
        ((chi p)⁻¹ * (chi q)⁻¹) *
          vf919CharacterMobiusSite R chi (p * (q * a)) := by
  unfold vf919TwoPrimeAlignedPhysicalSite vf919CharacterAlignedSite
  ring

/-- The true double-prime finite difference of the original crossing
functions, rather than a replacement smooth weight or a constant profile. -/
def vf919TwoPrimePhysicalCurvature (R p q a : ℕ) : ℝ :=
  ((lowOwnerDaughterCrossingWeight R p a -
      lowOwnerRootCrossingIndicator R p a) -
    (lowOwnerDaughterCrossingWeight R p (q * a) -
      lowOwnerRootCrossingIndicator R p (q * a))) *
    realMoebiusStep a

/-- Genuine TWO-prime sign-reversal and character compensation. This is the
native source-level analogue of the finite selected-slot cancellation:
no Euler-character moment is assumed. -/
theorem vf919TwoPrimeAlignedPhysicalSite_eq_curvature
    {R p q a : ℕ} (chi : ℕ → ℂ)
    (hp : p.Prime) (hq : q.Prime)
    (hpa : ¬ p ∣ a) (hqa : ¬ q ∣ a) (hpqa : ¬ p ∣ q * a)
    (hchip : chi p ≠ 0) (hchiq : chi q ≠ 0)
    (hmul : ∀ m n : ℕ, chi (m * n) = chi m * chi n) :
    vf919TwoPrimeAlignedPhysicalSite R p q chi a =
      (vf919TwoPrimePhysicalCurvature R p q a : ℂ) * chi a := by
  have hfirst :
      vf919CharacterAlignedSite R p chi a =
        vf919ParentTwistedCompensatedSite R p chi a :=
    vf919CharacterAlignedSite_eq_parentTwisted chi hp hpa hchip (hmul p a)
  have hsecond :
      vf919CharacterAlignedSite R p chi (q * a) =
        vf919ParentTwistedCompensatedSite R p chi (q * a) :=
    vf919CharacterAlignedSite_eq_parentTwisted chi hp hpqa hchip (hmul p (q * a))
  unfold vf919TwoPrimeAlignedPhysicalSite
  rw [hfirst, hsecond]
  unfold vf919ParentTwistedCompensatedSite
    lowOwnerFirstOwnerCompensatedSite vf919TwoPrimePhysicalCurvature
  rw [hmul q a, realMoebiusStep_mul_prime_eq_neg hq hqa]
  push_cast
  field_simp [hchiq]
  ring

/-- A nonunit q-row has NO inverse cancellation. This zero-extension is
distinct from the good-row identity and retains the first p-compensation. -/
theorem vf919TwoPrimeAlignedPhysicalSite_zero_q_phase
    (R p q a : ℕ) (chi : ℕ → ℂ) (hq : chi q = 0) :
    vf919TwoPrimeAlignedPhysicalSite R p q chi a =
      vf919CharacterAlignedSite R p chi a := by
  simp [vf919TwoPrimeAlignedPhysicalSite, hq]

/-- The one-character (principal) specialization is exactly the complete
four-site signed Mobius source, with no independent site-by-site norms. -/
theorem vf919TwoPrimeAlignedPhysicalSite_principal
    (R p q a : ℕ) :
    vf919TwoPrimeAlignedPhysicalSite R p q (fun _ => 1) a =
      ((lowOwnerZeroFrequencyMobiusSite R a +
        lowOwnerZeroFrequencyMobiusSite R (p * a) +
        lowOwnerZeroFrequencyMobiusSite R (q * a) +
        lowOwnerZeroFrequencyMobiusSite R (p * (q * a)) : ℝ) : ℂ) := by
  rw [vf919TwoPrimeAlignedPhysicalSite_fourTerms]
  simp [vf919CharacterMobiusSite]

/-- The FULL finite double-prime source from genuine physical sites. -/
def vf919TwoPrimePhysicalPopulation (R p q : ℕ)
    (chi : ℕ → ℂ) (parents : Finset ℕ) : ℂ :=
  ∑ a ∈ parents, vf919TwoPrimeAlignedPhysicalSite R p q chi a

/-- Source-to-curvature identification for any genuine admissible parent
population. All moving native weights are retained before summation. -/
theorem vf919TwoPrimePhysicalPopulation_eq_curvature
    {R p q : ℕ} (chi : ℕ → ℂ) (parents : Finset ℕ)
    (hp : p.Prime) (hq : q.Prime)
    (hfree : ∀ a ∈ parents, ¬ p ∣ a ∧ ¬ q ∣ a ∧ ¬ p ∣ q * a)
    (hchip : chi p ≠ 0) (hchiq : chi q ≠ 0)
    (hmul : ∀ m n : ℕ, chi (m * n) = chi m * chi n) :
    vf919TwoPrimePhysicalPopulation R p q chi parents =
      ∑ a ∈ parents, (vf919TwoPrimePhysicalCurvature R p q a : ℂ) * chi a := by
  unfold vf919TwoPrimePhysicalPopulation
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨hpa, hqa, hpqa⟩ := hfree a ha
  exact vf919TwoPrimeAlignedPhysicalSite_eq_curvature chi hp hq
    hpa hqa hpqa hchip hchiq hmul

/-- The entire COMPLEX norm square, with every off-diagonal and same-owner
term, without Cauchy/absolute values on source occurrences. -/
theorem vf919TwoPrimePhysicalPopulation_fullHermitianGram
    (R p q : ℕ) (chi : ℕ → ℂ) (parents : Finset ℕ) :
    ‖vf919TwoPrimePhysicalPopulation R p q chi parents‖ ^ 2 =
      ∑ a ∈ parents, ∑ b ∈ parents,
        (vf919TwoPrimeAlignedPhysicalSite R p q chi a *
          star (vf919TwoPrimeAlignedPhysicalSite R p q chi b)).re := by
  unfold vf919TwoPrimePhysicalPopulation
  exact vf919FiniteHermitianGram parents _

/-- Unlike the scalar Fermat projection, this native two-prime full
character cell has an exactly norm-preserving two-real coordinate image. -/
theorem vf919TwoPrimePhysicalPopulation_realPairEnergy
    (R p q : ℕ) (chi : ℕ → ℂ) (parents : Finset ℕ) :
    stableFarRealPairNormalizedEnergy
      (stableFarComplexToRealPair
        (vf919TwoPrimePhysicalPopulation R p q chi parents)) =
    ‖vf919TwoPrimePhysicalPopulation R p q chi parents‖ ^ 2 := by
  exact stableFarRealPairNormalizedEnergy_complexToRealPair _

#print axioms vf919TwoPrimeAlignedPhysicalSite_fourTerms
#print axioms vf919TwoPrimeAlignedPhysicalSite_eq_curvature
#print axioms vf919TwoPrimeAlignedPhysicalSite_principal
#print axioms vf919TwoPrimePhysicalPopulation_eq_curvature
#print axioms vf919TwoPrimePhysicalPopulation_fullHermitianGram
#print axioms vf919TwoPrimePhysicalPopulation_realPairEnergy

end RHLean.Proof
