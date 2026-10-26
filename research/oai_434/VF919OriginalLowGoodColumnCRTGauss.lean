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

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
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
    ‖canonicalGaussSum P hcop hgood
       (fun i => if isLowSlot i then 5 else 1 + 3 * eJ i)‖ =
      ‖eisEmbedding (finitePrimeModulus P)‖ := by
  apply SevenEighths.CubicSieve.norm_canonicalGaussSum_of_nontrivial
    P hcop hgood (fun i => if isLowSlot i then 5 else 1 + 3 * eJ i)
  intro i
  cases h : isLowSlot i
  · simpa [h] using lowColumnActualSextic_nonprincipal
      (P i) (hgood i) (hchar i) (eJ i)
  · simpa [h] using lowSlotInverseActualSextic_nonprincipal
      (P i) (hgood i) (hchar i)


/-- Exact squarefree collision factorization at the marked low prime:
    the quotient column remains squarefree and coprime to the slot. -/
theorem lowSquarefreeCollision_split (s I : Ideal O)
    (hI : Squarefree I) (hs : s ∣ I) :
    ∃ I' : Ideal O, I = s * I' ∧ IsRelPrime s I' ∧ Squarefree I' := by
  obtain ⟨I', hfac⟩ := hs
  have hsf : Squarefree (s * I') := hfac ▸ hI
  obtain ⟨hrel, _, hI'⟩ := squarefree_mul_iff.mp hsf
  exact ⟨I', hfac, hrel, hI'⟩

/-- Ideal norms retain the exact q factor after the collision split. -/
theorem lowSquarefreeCollision_norm (s I I' : Ideal O)
    (hfac : I = s * I') :
    Ideal.absNorm I = Ideal.absNorm s * Ideal.absNorm I' := by
  rw [hfac]
  exact map_mul Ideal.absNorm s I'

/-- At a colliding low prime the total sextic exponent is 3*v_s(J). -/
theorem lowCollisionResidualExponent (v : ℕ) :
    (5 + (1 + 3 * v)) % 6 = (3 * v) % 6 := by
  omega

/-- In the Gaussian bulk s does not divide J; hence at v_s(J)=0
    the s-phase is PRINCIPAL on units. Calibration is still present. -/
theorem lowCollisionPrincipal_at_zero :
    (5 + (1 + 3 * 0)) % 6 = 0 := by
  norm_num


/-- No s/J collision is possible once the actual prime-ideal norm of J
    is strictly below the slot prime-ideal norm. The physical
    exponent ledger must establish this inequality for each source
    scale; it may fail after selected-slot compensation rescales Y. -/
theorem lowCollision_no_J_of_norm_lt (s J : Ideal O)
    (hJ : J ≠ 0)
    (hnorm : Ideal.absNorm J < Ideal.absNorm s) :
    ¬ s ∣ J := by
  intro hd
  have hdNorm : Ideal.absNorm s ∣ Ideal.absNorm J :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hd)
  have hJpos : 0 < Ideal.absNorm J :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  exact (Nat.not_le_of_gt hnorm) (Nat.le_of_dvd hJpos hdNorm)

#print axioms lowColumnOnePlusThree_not_six_dvd
#print axioms lowColumnActualSextic_nonprincipal
#print axioms lowSlotInverseActualSextic_nonprincipal
#print axioms lowGoodColumnCRTGauss_norm
#print axioms lowSquarefreeCollision_split
#print axioms lowSquarefreeCollision_norm
#print axioms lowCollisionResidualExponent
#print axioms lowCollisionPrincipal_at_zero
#print axioms lowCollision_no_J_of_norm_lt

end SevenEighths.ProbePhysical
end
end OAI
