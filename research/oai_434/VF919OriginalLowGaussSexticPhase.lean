import OAI.NumberTheory.DirichletL.Moments.Unequal
import OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier

/-!
# True original LOW Gaussian coefficient: primitive sextic phase, not a model

The native original low physical source has
  sexticGauss(primaryGenerator s, -m)
at each ideal s, with m running over actual Eisenstein numerator
lattice sites of norm ~ Q = norm(C.generator)*X*Y.

At a supported GOOD prime ideal s=(p), the Gauss coefficient is
a constant depending on p multiplied by the EXACT inverse sextic
character evaluated at -m. That is an algebraic source identification,
NOT a probabilistic assumption or a power-saving hypothesis.

This holds for genuinely PRIME s. The full low numerator source has
composite s, principal sixth-power ideals, and an m-dependent inverse
L-function B(sigma,m); none are erased by this lemma.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.LowSignedSixthCompletion

open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open ConcretePrimeRowBridge CanonicalQuadraticSieve CanonicalRowCompletion
open SevenEighths.CenteredMomentCanonical
open SevenEighths.CenteredMomentFourier
open SevenEighths.CenteredMomentSupportedCorrelation

local notation "O" => ActualEisensteinCubic.O

/-- The actual original sextic character at a good prime is EXACTLY
the primitive supportedModulusCharacter in the Gaussian low source. -/
theorem actual_low_prime_supportedChar_eq_sextic
    (p : O) (hp : Supported (Ideal.span {p}))
    [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) :
    supportedModulusCharacter p hp =
      actualSextic (Ideal.span {p}) hg := by
  apply MulChar.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [supportedModulusCharacter_mk, idealRowHom_prime _ _ hg]

/-- Original low prime sextic, with exact OAI GaussSum normalization.
The normalized oscillatory dependence on m is precisely the inverse
true sextic phase. Zero divisors remain zero, not arbitrary unit phases. -/
theorem actual_low_gauss_prime_phase_exact
    (p : O) (hp : Supported (Ideal.span {p}))
    [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (m : O) :
    ProbePhysical.sexticGauss p (supported_element_ne_zero p hp) (-m) =
      (if Ideal.Quotient.mk (Ideal.span {p}) (-m) = 0 then 0 else
        (actualSextic (Ideal.span {p}) hg
          (Ideal.Quotient.mk (Ideal.span {p}) (-m)))⁻¹ *
          ProbePhysical.sexticGauss p (supported_element_ne_zero p hp) 1) := by
  let χ := supportedModulusCharacter p hp
  have hχeq : χ = actualSextic (Ideal.span {p}) hg :=
    actual_low_prime_supportedChar_eq_sextic p hp hg
  have hχ : χ ≠ 1 := by
    intro he
    have horder := actualSextic_order_six (Ideal.span {p}) hg hchar
    rw [← hχeq, he, orderOf_one] at horder
    norm_num at horder
  let hp0 := supported_element_ne_zero p hp
  letI : Finite (Residue p) := finite_quotient_span hp0
  letI : Fintype (Residue p) := Fintype.ofFinite _
  letI : Field (Residue p) := Ideal.Quotient.field _
  let ψ := quotientTrace p hp0
  have ht := ShortDraftFiniteGaussFourier.gauss_transform χ ψ hχ
    (Ideal.Quotient.mk (Ideal.span {p}) (-m))
  have hgt :
      residueGauss p hp0 χ (Ideal.Quotient.mk (Ideal.span {p}) (-m)) =
        (if Ideal.Quotient.mk (Ideal.span {p}) (-m) = 0 then 0 else
          (χ (Ideal.Quotient.mk (Ideal.span {p}) (-m)))⁻¹ *
            residueGauss p hp0 χ 1) := by
    simpa only [residueGauss, tsum_fintype, gaussSum, map_one, one_mul, ψ] using ht
  calc
    ProbePhysical.sexticGauss p hp0 (-m) =
        residueGauss p hp0 χ (Ideal.Quotient.mk (Ideal.span {p}) (-m)) := by
      exact (residueGauss_supported_mk p hp (-m)).symm
    _ = _ := by
      rw [hgt]
      rw [residueGauss_supported_mk p hp 1]
      rw [hχeq]

#print axioms actual_low_prime_supportedChar_eq_sextic
#print axioms actual_low_gauss_prime_phase_exact

end SevenEighths.LowSignedSixthCompletion
end OAI
