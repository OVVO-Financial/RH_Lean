import OAI.NumberTheory.DirichletL.Detector.CompensationActual

/-!
# True Eisenstein ideals AND actual OpenAI continued compensation
# on the ORIGINAL RH_Lean half-open sharp square-block physical weight

This Lean 4.34.1 file uses, without axioms:
  * ActualEisensteinCubic.O and its REAL Ideals I : Ideal O,
  * the ideal Möbius coefficient UniqueFactorizationMonoid.moebius I,
  * individual rational character cofactors d with χ_-3(d),
  * physical integer site n = d * Ideal.absNorm I,
  * the original mask [R^2 <= n < (R+1)^2],
  * the genuine distinct PrimeIdeal P and HeckeFamily.Character η,
  * the actual OpenAI idealMarkedLocalFactor and
    idealCompensatedRatio_eq_continued (physical 5.13c),
  * selected and unselected factors with complete returned terms.

No term is norm-grouped before its ideal / prime-ideal labels and
phase are applied. Distinct ideals with the same norm are separate
summands and EVERY signed product survives.

This proves exact algebraic transfer of OAI's local compensated factors
to ORIGINAL square-block source weights. The OAI smooth theta/Poisson
probe and sharp owner sum are NOT asserted to be equal: proving a
uniform analytic estimate for this exact sharp weighted source requires
a separate inversion/test-function estimate, not an axiom or a result
of multiplying a pre-proved local identity.
-/

noncomputable section
open scoped BigOperators
namespace OAI
namespace SevenEighths.ProbePhysical

open ActualEisensteinCubic ProbeLocal
open ShortDraftHeckeBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- REAL original Möbius source of one Eisenstein ideal I, with
    the original rational cofactor character and square-block indicator.
    I is NOT replaced by a norm-first scalar ideal count. -/
def rhleanActualIdealSharpSquareSite
    (R d : ℕ) (I : Id) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) *
    chiMinusThree d *
      (if R ^ 2 ≤ d * Ideal.absNorm I ∧
          d * Ideal.absNorm I < (R + 1) ^ 2 then (1 : ℂ) else 0)

/-- Literal selected minus rescaled OAI local factor at a good PRIME IDEAL,
    with exactly the same η phase and zero-mask handling as the upstream
    physical detector. -/
def rhleanActualCompensatedLocalFactor
    (η : HeckeFamily.Character) (P : PrimeIdeal)
    (x w z B q : ℂ) : ℂ :=
  B * idealMarkedLocalFactor η P x w z /
    idealHighLocalFactor η P.val x w z - q

/-- The full OAI continued local ratio, using its ACTUAL prime ideal,
    physical marked ratio, and normalizing holomorphic local correction. -/
def rhleanActualContinuedLocalFactor
    (η : HeckeFamily.Character) (P : PrimeIdeal)
    (x w z B q : ℂ) : ℂ :=
  compensatedReplacement
    (ProbeEuler.coordV (Ideal.absNorm P.val) z)
    (ProbeEuler.coordW (Ideal.absNorm P.val) 1 w)
    (ProbeEuler.coordD (Ideal.absNorm P.val)
       (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) B q /
    idealClosedCorrection η P x w z

/-- An actual prime-ideal slot: exact OAI compensation on a PHYSICAL
    square-block owner occurrence. No 3-adic surrogate and no invented
    phase, even when 2 different ideals have the same rational norm. -/
theorem rhlean_actual_marked_rescaled_sharp_at_ideal
    (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val ∉ S)
    (x w z B q : ℂ)
    (hx : 3 / 2 < x.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re)
    (R d : ℕ) (I : Id) :
    rhleanActualIdealSharpSquareSite R d I *
      rhleanActualCompensatedLocalFactor η P x w z B q =
    rhleanActualIdealSharpSquareSite R d I *
      rhleanActualContinuedLocalFactor η P x w z B q := by
  unfold rhleanActualCompensatedLocalFactor
    rhleanActualContinuedLocalFactor
  rw [idealCompensatedRatio_eq_continued S hS η P hP
    x w z B q hx hw hz]

/-- All good prime ideals are retained SEPARATELY in their finite subset
    amplifier product. This is not a single norm-only Fourier phase. -/
theorem rhlean_actual_sharp_good_prime_slots_term_by_term
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S)
    (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal → ℂ)
    (hx : 3 / 2 < x.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re)
    (R d : ℕ) (I : Id) :
    rhleanActualIdealSharpSquareSite R d I *
      (∏ P ∈ T, rhleanActualCompensatedLocalFactor
        η P x w z (B P) (q P)) =
    rhleanActualIdealSharpSquareSite R d I *
      (∏ P ∈ T, rhleanActualContinuedLocalFactor
        η P x w z (B P) (q P)) := by
  congr 1
  apply Finset.prod_congr rfl
  intro P hP
  unfold rhleanActualCompensatedLocalFactor
    rhleanActualContinuedLocalFactor
  exact idealCompensatedRatio_eq_continued
    S hS η P (hT P hP) x w z (B P) (q P) hx hw hz

/-- ALL original actual ideals and ALL cofactor sites d are admitted
    with their actual complex signed weights. The compensated source
    is not substituted for the original Mobius covariance by fiat. -/
def rhleanActualSharpCompensatedIdealSource
    (R : ℕ) (ds : Finset ℕ) (is : Finset Id)
    (T : Finset PrimeIdeal) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal → ℂ) : ℂ :=
  ∑ I ∈ is, ∑ d ∈ ds,
    rhleanActualIdealSharpSquareSite R d I *
      (∏ P ∈ T, rhleanActualCompensatedLocalFactor
        η P x w z (B P) (q P))

def rhleanActualSharpContinuedIdealSource
    (R : ℕ) (ds : Finset ℕ) (is : Finset Id)
    (T : Finset PrimeIdeal) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal → ℂ) : ℂ :=
  ∑ I ∈ is, ∑ d ∈ ds,
    rhleanActualIdealSharpSquareSite R d I *
      (∏ P ∈ T, rhleanActualContinuedLocalFactor
        η P x w z (B P) (q P))

/-- FIRST GLOBAL PHYSICAL IDENTITY: actual OAI compensated Hecke
    prime-factor operator on actual ideal-labelled sharp Mobius sites,
    no collapsed norm, no omitted cross term, all complex phases. -/
theorem rhlean_actual_sharp_compensated_all_ideal_sources
    (S : Finset Id) (hS : SourceExclusions S)
    (ds : Finset ℕ) (is : Finset Id)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S)
    (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal → ℂ)
    (hx : 3 / 2 < x.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re)
    (R : ℕ) :
    rhleanActualSharpCompensatedIdealSource R ds is T η x w z B q =
      rhleanActualSharpContinuedIdealSource R ds is T η x w z B q := by
  unfold rhleanActualSharpCompensatedIdealSource
    rhleanActualSharpContinuedIdealSource
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro d _
  exact rhlean_actual_sharp_good_prime_slots_term_by_term
    S hS T hT η x w z B q hx hw hz R d I

/-- The COMPLETE original signed ideal-pair Gram is maintained after
    compensation. No Cauchy, absolute value, or decorrelation assumption. -/
theorem rhlean_actual_sharp_compensated_full_ideal_pair_gram
    (S : Finset Id) (hS : SourceExclusions S)
    (ds : Finset ℕ) (is : Finset Id)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S)
    (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal → ℂ)
    (hx : 3 / 2 < x.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re)
    (R : ℕ) :
    ‖rhleanActualSharpCompensatedIdealSource R ds is T η x w z B q‖ ^ 2 =
      ‖rhleanActualSharpContinuedIdealSource R ds is T η x w z B q‖ ^ 2 := by
  rw [rhlean_actual_sharp_compensated_all_ideal_sources
    S hS ds is T hT η x w z B q hx hw hz R]

#print axioms rhlean_actual_marked_rescaled_sharp_at_ideal
#print axioms rhlean_actual_sharp_good_prime_slots_term_by_term
#print axioms rhlean_actual_sharp_compensated_all_ideal_sources
#print axioms rhlean_actual_sharp_compensated_full_ideal_pair_gram

end SevenEighths.ProbePhysical
end OAI
