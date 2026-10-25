import OAI.NumberTheory.DirichletL.Detector.Sextic

/-!
# Source-local sextic parity gates for the OAI low-Gaussian numerator

These statements specialize the ORIGINAL exact order-six theorem.
They certify only the local nonprincipal/principal classification, not a
Fourier coefficient bound, physical Poisson estimate, global low-detector
saving, Mertens exponent improvement, or RH.
-/

namespace OAI
noncomputable section

namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

/-- At a good I-column prime (I squarefree), 1+3v never vanishes mod 6. -/
theorem lowColumn_one_plus_three_nonprincipal
    (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2)
    (v : ℕ) :
    actualSextic P hg ^ (1 + 3 * v) ≠ 1 := by
  intro h
  have hd := (actualSextic_pow_eq_one_iff P hg hc (1 + 3 * v)).mp h
  omega

/-- At a noncolliding outer prime, -1+3v = 5+3v (mod 6) is nonprincipal. -/
theorem lowOuter_five_plus_three_nonprincipal
    (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2)
    (v : ℕ) :
    actualSextic P hg ^ (5 + 3 * v) ≠ 1 := by
  intro h
  have hd := (actualSextic_pow_eq_one_iff P hg hc (5 + 3 * v)).mp h
  omega

/-- J has odd valuation: the cubed sextic factor remains nonprincipal. -/
theorem lowJ_odd_quadratic_nonprincipal
    (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2)
    (v : ℕ) :
    actualSextic P hg ^ (3 * (2 * v + 1)) ≠ 1 := by
  intro h
  have hd := (actualSextic_pow_eq_one_iff P hg hc (3 * (2 * v + 1))).mp h
  omega

/-- J has even valuation: the cubed sextic factor is principal. -/
theorem lowJ_even_principal
    (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2)
    (v : ℕ) :
    actualSextic P hg ^ (3 * (2 * v)) = 1 := by
  apply (actualSextic_pow_eq_one_iff P hg hc (3 * (2 * v))).mpr
  refine ⟨v, ?_⟩
  omega

/-- A genuine s|I collision with odd J-valuation remains nonprincipal. -/
theorem lowCollision_odd_nonprincipal
    (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2)
    (v : ℕ) :
    actualSextic P hg ^ (3 * (2 * v + 1)) ≠ 1 :=
  lowJ_odd_quadratic_nonprincipal P hg hc v

/-- A genuine s|I collision with even J-valuation becomes principal. -/
theorem lowCollision_even_principal
    (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2)
    (v : ℕ) :
    actualSextic P hg ^ (3 * (2 * v)) = 1 :=
  lowJ_even_principal P hg hc v

#print axioms lowColumn_one_plus_three_nonprincipal
#print axioms lowOuter_five_plus_three_nonprincipal
#print axioms lowJ_odd_quadratic_nonprincipal
#print axioms lowJ_even_principal

end SevenEighths.ProbePrimePower
end
end OAI
