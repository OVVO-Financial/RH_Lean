import OAI.NumberTheory.DirichletL.CubicSieve.Poisson
import OAI.NumberTheory.DirichletL.Detector.Sextic

/-!
# Original low-Gaussian good-column primitive CRT component

The original fixed-source m-character contains the low inverse sextic
phase at the good prime s and an I-column sextic factor multiplied by
the cubic J-factor. At every good prime dividing a squarefree column I,
its residual exponent is 1 + 3*v_p(J), which is NEVER divisible by 6.

This file kernel-certifies the corresponding nonprincipality statements
and applies the original OpenAI finite CRT Gauss norm theorem to a family
of good prime factors with low-slot exponent 5 and column exponents
1+3*v_p(J). It does NOT claim the full calibrated source factorization
or the uniform physical nonzero-frequency Poisson estimate.
-/

namespace OAI
noncomputable section
namespace SevenEighths.ProbePhysical

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

/-- Even if the I-column prime divides J, the combined local
    I*J^3 character is nonprincipal: exponent 1 or 4 modulo 6. -/
theorem lowColumnOnePlusThree_not_six_dvd (e : ℕ) :
    ¬ 6 ∣ (1 + 3 * e) := by
  omega

/-- The actual original order-six local character remains nonprincipal
    on every admitted squarefree I-column prime, including I/J overlap. -/
theorem lowColumnActualSextic_nonprincipal
    (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P)
    (hc : ringChar (O ⧸ P) ≠ 2)
    (e : ℕ) :
    actualSextic P hg ^ (1 + 3 * e) ≠ 1 := by
  intro h
  have hd := (SevenEighths.ProbePrimePower.actualSextic_pow_eq_one_iff
    P hg hc (1 + 3 * e)).mp h
  exact (lowColumnOnePlusThree_not_six_dvd e) hd

/-- The inverse sextic low-slot phase is nonprincipal at a good prime. -/
theorem lowSlotInverseActualSextic_nonprincipal
    (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P)
    (hc : ringChar (O ⧸ P) ≠ 2) :
    actualSextic P hg ^ 5 ≠ 1 := by
  intro h
  have hd := (SevenEighths.ProbePrimePower.actualSextic_pow_eq_one_iff
    P hg hc 5).mp h
  norm_num at hd

/-- Original OpenAI finite CRT Gauss norm applies to all the good
    low-slot/column prime factors jointly. The remaining calibration
    and J-only factors, and physical Poisson, still require a source
    adapter and are NOT included in this theorem. -/
theorem lowGoodColumnCRTGauss_norm
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (isLowSlot : ι → Bool)
    (eJ : ι → ℕ) :
    ‖SevenEighths.CubicSieve.canonicalGaussSum P hcop hgood
       (fun i => if isLowSlot i then 5 else 1 + 3 * eJ i)‖ =
      ‖eisEmbedding (SevenEighths.CubicSieve.finitePrimeModulus P)‖ := by
  apply SevenEighths.CubicSieve.norm_canonicalGaussSum_of_nontrivial
    P hcop hgood (fun i => if isLowSlot i then 5 else 1 + 3 * eJ i)
  intro i
  cases h : isLowSlot i
  · simpa [h] using lowColumnActualSextic_nonprincipal
      (P i) (hgood i) (hchar i) (eJ i)
  · simpa [h] using lowSlotInverseActualSextic_nonprincipal
      (P i) (hgood i) (hchar i)

#print axioms lowColumnOnePlusThree_not_six_dvd
#print axioms lowColumnActualSextic_nonprincipal
#print axioms lowSlotInverseActualSextic_nonprincipal
#print axioms lowGoodColumnCRTGauss_norm

end SevenEighths.ProbePhysical
end
end OAI
