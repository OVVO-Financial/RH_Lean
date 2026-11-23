import RHLean.Analysis.AlpogeNativeQuadraticRoot
import RHLean.Geometry.NativeThetaHarmonicPolynomials

/-!
# The actual native host supplies the theta-polynomial signature

The conjugate embedding rows are separated by the constructed native square
root of -d. The resulting leading-minor polynomial is nonzero, integral,
harmonic, invariant under the required row shifts and of the exact prescribed
degree. Its coefficient norm is bounded at every embedding of the independent
coefficient field K. Thus K can remain the original geometric Y.d.c₂.F.

This supplies an actual harmonic-polynomial input, not yet a theta section or
the short spanning family of cusp sections. The latter still requires the
geometric short-value evaluation, canonical connection and theta density.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Development/AbelianVarietyTheory/Proofs/UnitaryExistence/
ExistsLastEntryPosNotLastPos.lean, ThetaClaimsCompare.not_inPsi_conjugate
and exists_harmA_ne_zero; the coefficient estimate follows the explicit
minor-product estimate in ExistsBlockProductMemIntegralHarmonic.lean.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField

namespace RHLean.Geometry

open RHLean.Analysis

/-- A complex embedding of the same actual native fixed field, oriented by
the original positive imaginary quadratic root whenever its square is -d. -/
def nativeDyadicThetaEmbedding (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    alpogeNativeHostField e q d →+* ℂ := by
  classical
  let τ : alpogeNativeHostField e q d →+* ℂ := Classical.choice inferInstance
  exact if τ (alpogeNativeSqrtD e q d) = Complex.I * (Real.sqrt d : ℂ) then τ
    else ComplexEmbedding.conjugate τ

/-- The chosen embedding has the SAME orientation as the original raw-host
CM type. It is constructed by conjugating an embedding when necessary. -/
theorem nativeDyadicThetaEmbedding_sqrtD
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hd4 : d % 4 = 3) :
    nativeDyadicThetaEmbedding e q d (alpogeNativeSqrtD e q d) =
      Complex.I * (Real.sqrt d : ℂ) := by
  classical
  let τ : alpogeNativeHostField e q d →+* ℂ := Classical.choice inferInstance
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), Complex.ofReal_natCast]
  have hroot : τ (alpogeNativeSqrtD e q d) = Complex.I * (Real.sqrt d : ℂ) ∨
      τ (alpogeNativeSqrtD e q d) = -(Complex.I * (Real.sqrt d : ℂ)) := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [← map_pow, alpogeNativeSqrtD_sq e q d hd4, map_neg, map_natCast,
      mul_pow, Complex.I_sq, hs, neg_one_mul]
  change (if τ (alpogeNativeSqrtD e q d) = Complex.I * (Real.sqrt d : ℂ)
    then τ else ComplexEmbedding.conjugate τ) (alpogeNativeSqrtD e q d) = _
  split_ifs with h
  · exact h
  · rw [ComplexEmbedding.conjugate_coe_eq, hroot.resolve_left h]
    simp

/-- The source's positive embedding rows, using the actual constructed root. -/
def nativeDyadicThetaPositive (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (τ : alpogeNativeHostField e q d →+* ℂ) : Prop :=
  τ (alpogeNativeSqrtD e q d) =
    nativeDyadicThetaEmbedding e q d (alpogeNativeSqrtD e q d)

theorem nativeDyadicThetaPositive_iff
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hd4 : d % 4 = 3)
    (τ : alpogeNativeHostField e q d →+* ℂ) :
    nativeDyadicThetaPositive e q d τ ↔
      τ (alpogeNativeSqrtD e q d) = Complex.I * (Real.sqrt d : ℂ) := by
  unfold nativeDyadicThetaPositive
  rw [nativeDyadicThetaEmbedding_sqrtD e q d hd4]

/-- Conjugation cannot preserve the chosen square-root value, because its
square is the strictly negative real number -d. -/
theorem nativeDyadicThetaPositive_conjugate_not
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hd4 : d % 4 = 3)
    (τ : alpogeNativeHostField e q d →+* ℂ)
    (h : nativeDyadicThetaPositive e q d τ) :
    ¬ nativeDyadicThetaPositive e q d (ComplexEmbedding.conjugate τ) := by
  intro h'
  change τ (alpogeNativeSqrtD e q d) =
    nativeDyadicThetaEmbedding e q d (alpogeNativeSqrtD e q d) at h
  change ComplexEmbedding.conjugate τ (alpogeNativeSqrtD e q d) =
    nativeDyadicThetaEmbedding e q d (alpogeNativeSqrtD e q d) at h'
  rw [ComplexEmbedding.conjugate_coe_eq, h] at h'
  have him : (nativeDyadicThetaEmbedding e q d (alpogeNativeSqrtD e q d)).im = 0 :=
    Complex.conj_eq_iff_im.mp h'
  have hsquare :
      (nativeDyadicThetaEmbedding e q d (alpogeNativeSqrtD e q d)) ^ 2 = -(d : ℂ) := by
    rw [← map_pow, alpogeNativeSqrtD_sq e q d hd4, map_neg, map_natCast]
  have hre := congrArg Complex.re hsquare
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re,
    Complex.natCast_re] at hre
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Fact.out : d.Prime).pos
  nlinarith [mul_self_nonneg
    (nativeDyadicThetaEmbedding e q d (alpogeNativeSqrtD e q d)).re]

/-- The exact p/q row signature determined by the constructed root. -/
def nativeDyadicThetaRows (e q d pplus pminus : ℕ)
    [Fact q.Prime] [Fact d.Prime]
    (τ : alpogeNativeHostField e q d →+* ℂ) : ℕ :=
  open Classical in
  if nativeDyadicThetaPositive e q d τ then pplus else pminus

/-- Construct the actual native-host harmonic polynomial over the original
independent coefficient field, retaining every embedding and its degree cost.
No polynomial, harmonicity, integral coefficient or norm witness is supplied. -/
theorem nativeExists_host_short_integral_harmonic_polynomial
    (e q d pplus pminus n : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hd4 : d % 4 = 3) (hn : pplus + pminus ≤ n)
    (K : Type) [Field K] [NumberField K]
    (a : (alpogeNativeHostField e q d →+* ℂ) → ℕ → ℕ)
    (ha : ∀ τ, Antitone
      (fun i : Fin (nativeDyadicThetaRows e q d pplus pminus τ) => a τ i)) :
    let r := nativeDyadicThetaRows e q d pplus pminus
    let D := ∑ τ, ∑ i : Fin (r τ), a τ i
    ∃ P : MvPolynomial (NativeTheta.Letter (alpogeNativeHostField e q d →+* ℂ) r n) K,
      P ∈ NativeTheta.HaO r n K (integralClosure ℤ K).toSubring
        ComplexEmbedding.conjugate (nativeDyadicThetaPositive e q d) a ∧
      P ≠ 0 ∧ P.IsHomogeneous D ∧ P.totalDegree = D ∧
      (∀ σ : K →+* ℂ, ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤
        ((pplus + pminus : ℕ) : ℝ) ^ D) ∧
      NativeTheta.CoeffNorm.allEmbeddingNorm P ≤
        Real.sqrt (Module.finrank ℚ K) * ((pplus + pminus : ℕ) : ℝ) ^ D := by
  classical
  let r := nativeDyadicThetaRows e q d pplus pminus
  obtain ⟨P, hP, hne, hhom, hdeg, hemb⟩ :=
    NativeTheta.exists_short_integral_harmonic_of_signature K
      (integralClosure ℤ K).toSubring r ComplexEmbedding.conjugate
      (nativeDyadicThetaPositive e q d) pplus pminus n hn (fun _ => rfl)
      (nativeDyadicThetaPositive_conjugate_not e q d hd4) a ha
  exact ⟨P, hP, hne, hhom, hdeg, hemb,
    NativeTheta.CoeffNorm.allEmbeddingNorm_le_of_l1Bound P
      (((pplus + pminus : ℕ) : ℝ) ^ (∑ τ, ∑ i : Fin (r τ), a τ i))
      (pow_nonneg (Nat.cast_nonneg _) _) hemb⟩

end RHLean.Geometry

end
