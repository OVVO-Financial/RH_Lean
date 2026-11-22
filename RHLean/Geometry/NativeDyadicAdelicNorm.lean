import RHLean.Geometry.NativeAdicQuadraticNorm
import RHLean.Analysis.AlpogeThin.NativeDyadicHostCore
import RHLean.Analysis.AlpogeNativeIntegralQuadraticRoot

/-!
# An actual finite-adelic norm-minus-one element on the native host

This reconstructs the global part of
`Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean` by Levent
Alpöge (with Claude), from `CocoSgt/riemann-hypothesis-lean` at source commit
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

Both quadratic roots are the already constructed Gauss roots in the SAME
native fixed field. At primes away from d the integral local d-norm equation
is solved directly. At primes above d the q-norm equation is solved and
transported by the actual real ratio sqrt(-q)/sqrt(-d). The resulting local
coordinates are integral away from the finite set of primes dividing d, so
they define genuine elements of the original finite-adele restricted product.

The final tensor element is explicit. Its norm under the scalar extension
of the actual host conjugation is -1, and hence it is a unit. Neither that
norm equation, an adelic element, nor a Hermitian isometry is an input.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeDyadicAdelicNorm

open NumberField IsDedekindDomain HeightOneSpectrum Filter
open RHLean.Analysis RHLean.Analysis.AlpogeThin Formalism.FrobeniusOrbits
open scoped TensorProduct

def quarterPlusOne (n : ℕ) : ℤ := ((n : ℤ) + 1) / 4

theorem quarterPlusOne_spec (n : ℕ) (hn : n % 4 = 3) :
    4 * quarterPlusOne n = (n : ℤ) + 1 := by
  unfold quarterPlusOne
  have h : (4 : ℤ) ∣ (n : ℤ) + 1 := by omega
  exact Int.mul_ediv_cancel' h

section Host

variable (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]

local notation "E" => alpogeNativeHostField e q d
local notation "F" => maximalRealSubfield E
local notation "Af" => FiniteAdeleRing (𝓞 F) F

theorem conj_sqrtQ (hH : HostHyp q d) :
    alpogeNativeHostConj e q d (alpogeNativeSqrtQ e q d) =
      -alpogeNativeSqrtQ e q d := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  rw [alpogeNativeSqrtQ_galois_apply e q d (by omega) (by omega) (by omega),
    alpogeNativeHostGalEquiv_conj e q d (by omega) (by omega) (by omega)
      (by omega) (by omega)]
  norm_num [alpogeNativeCconj]

theorem conj_sqrtD (hH : HostHyp q d) :
    alpogeNativeHostConj e q d (alpogeNativeSqrtD e q d) =
      -alpogeNativeSqrtD e q d := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  exact alpogeNativeHostConj_sqrtD e q d (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem mem_real_iff (he : 2 ≤ e) (hH : HostHyp q d) (x : E) :
    x ∈ F ↔ alpogeNativeHostConj e q d x = x := by
  have h := nativeDyadicHostRaw_mem_F e q d he hH x
  rw [nativeDyadicHostRaw_conj] at h
  exact h

/-- The original host involution as an algebra homomorphism over its actual
maximal real subfield, with the commutation law proved. -/
def conjugation (he : 2 ≤ e) (hH : HostHyp q d) : E →ₐ[F] E :=
  { (alpogeNativeHostConj e q d).toRingHom with
    commutes' := fun x => (mem_real_iff e q d he hH (x : E)).mp x.property }

theorem conjugation_apply (he : 2 ≤ e) (hH : HostHyp q d) (x : E) :
    conjugation e q d he hH x = alpogeNativeHostConj e q d x := rfl

theorem conjugation_eq_host (he : 2 ≤ e) (hH : HostHyp q d) (x : E) :
    conjugation e q d he hH x = (nativeDyadicHostRaw e q d he hH).conj x := by
  simpa only [nativeDyadicHostRaw_conj] using (conjugation_apply e q d he hH x)

/-- The ratio of the SAME two Gauss roots lies in the actual real subfield. -/
def beta (he : 2 ≤ e) (hH : HostHyp q d) : F :=
  ⟨alpogeNativeSqrtQ e q d / alpogeNativeSqrtD e q d,
    (mem_real_iff e q d he hH _).mpr (by
      rw [map_div₀, conj_sqrtQ e q d hH, conj_sqrtD e q d hH, neg_div_neg_eq])⟩

def alpha (he : 2 ≤ e) (hH : HostHyp q d) : F :=
  (1 - beta e q d he hH) / 2

def theta : E := (1 + alpogeNativeSqrtD e q d) / 2

theorem theta_eq_integralHalfRoot (hd4 : d % 4 = 3) :
    theta e q d = (alpogeNativeIntegralHalfRoot e q d hd4 : E) := rfl

theorem theta_conj (hH : HostHyp q d) :
    alpogeNativeHostConj e q d (theta e q d) = 1 - theta e q d := by
  unfold theta
  rw [map_div₀, map_add, map_one, conj_sqrtD e q d hH, map_ofNat]
  ring

theorem theta_norm (hH : HostHyp q d) :
    theta e q d * (1 - theta e q d) = (quarterPlusOne d : E) := by
  have hdmod := hH.2.2.2.1
  have h4 := congrArg (Int.cast : ℤ → E) (quarterPlusOne_spec d (by omega))
  push_cast at h4
  have hs := alpogeNativeSqrtD_sq e q d (by omega)
  unfold theta
  linear_combination (-1 / 4 : E) * hs - (1 / 4 : E) * h4

theorem alpha_beta_linear (he : 2 ≤ e) (hH : HostHyp q d) :
    2 * alpha e q d he hH + beta e q d he hH = 1 := by
  unfold alpha
  ring

theorem alpha_beta_norm (he : 2 ≤ e) (hH : HostHyp q d) :
    alpha e q d he hH ^ 2 + alpha e q d he hH * beta e q d he hH +
        (quarterPlusOne d : F) * beta e q d he hH ^ 2 = (quarterPlusOne q : F) := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : d.Prime).ne_zero
  have key : beta e q d he hH ^ 2 * (d : F) = (q : F) := by
    apply Subtype.ext
    change (alpogeNativeSqrtQ e q d / alpogeNativeSqrtD e q d) ^ 2 * (d : E) = (q : E)
    rw [div_pow, alpogeNativeSqrtQ_sq e q d (by omega),
      alpogeNativeSqrtD_sq e q d (by omega), neg_div_neg_eq, div_mul_cancel₀ _ hd0]
  have h4d := congrArg (Int.cast : ℤ → F) (quarterPlusOne_spec d (by omega))
  have h4q := congrArg (Int.cast : ℤ → F) (quarterPlusOne_spec q (by omega))
  push_cast at h4d h4q
  unfold alpha
  linear_combination (1 / 4 : F) * key +
    (beta e q d he hH ^ 2 / 4) * h4d - (1 / 4 : F) * h4q

theorem not_both (hH : HostHyp q d) (v : HeightOneSpectrum (𝓞 F)) :
    ¬ (((d : ℤ) : 𝓞 F) ∈ v.asIdeal ∧ ((q : ℤ) : 𝓞 F) ∈ v.asIdeal) := by
  rintro ⟨hdv, hqv⟩
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hne : d ≠ q := by omega
  have hcop : IsCoprime (d : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr
      ((Nat.coprime_primes (Fact.out : d.Prime) (Fact.out : q.Prime)).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom (𝓞 F))
  simp only [eq_intCast] at hab
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hab]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hdv)
      (v.asIdeal.mul_mem_left b hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- Local solutions at every actual finite place, integral outside the exact
finite set of primes over d. The ramified d-branch is solved using q. -/
theorem local_solution (he : 2 ≤ e) (hH : HostHyp q d)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ S T : v.adicCompletion F,
      (((d : ℤ) : 𝓞 F) ∉ v.asIdeal →
        S ∈ v.adicCompletionIntegers F ∧ T ∈ v.adicCompletionIntegers F) ∧
      S * S + S * T + (quarterPlusOne d : v.adicCompletion F) * (T * T) = -1 := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hI3 : 2 * algebraMap F (v.adicCompletion F) (alpha e q d he hH) +
      algebraMap F (v.adicCompletion F) (beta e q d he hH) = 1 := by
    simpa only [map_add, map_mul, map_ofNat, map_one] using
      congrArg (algebraMap F (v.adicCompletion F)) (alpha_beta_linear e q d he hH)
  have hI4 : algebraMap F (v.adicCompletion F) (alpha e q d he hH) ^ 2 +
      algebraMap F (v.adicCompletion F) (alpha e q d he hH) *
        algebraMap F (v.adicCompletion F) (beta e q d he hH) +
      (quarterPlusOne d : v.adicCompletion F) *
        algebraMap F (v.adicCompletion F) (beta e q d he hH) ^ 2 =
      (quarterPlusOne q : v.adicCompletion F) := by
    simpa only [map_add, map_mul, map_pow, map_intCast] using
      congrArg (algebraMap F (v.adicCompletion F)) (alpha_beta_norm e q d he hH)
  by_cases hdv : ((d : ℤ) : 𝓞 F) ∈ v.asIdeal
  · have hqv : ((q : ℤ) : 𝓞 F) ∉ v.asIdeal := fun h => not_both e q d hH v ⟨hdv, h⟩
    have hc : (1 : ℤ) ^ 2 - 4 * quarterPlusOne q = -(q : ℤ) := by
      have := quarterPlusOne_spec q (by omega)
      linarith
    obtain ⟨s, t, hst⟩ := NativeAdicQuadraticNorm.numberField_adicInt_exists_norm F v
      1 (quarterPlusOne q) (by rw [hc]; simpa using hqv)
    have hst' : (s : v.adicCompletion F) ^ 2 +
        (s : v.adicCompletion F) * (t : v.adicCompletion F) +
        (quarterPlusOne q : v.adicCompletion F) * (t : v.adicCompletion F) ^ 2 = -1 := by
      have h := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hst
      push_cast at h
      simpa only [one_mul] using h
    refine ⟨(s : v.adicCompletion F) +
        algebraMap F (v.adicCompletion F) (alpha e q d he hH) * (t : v.adicCompletion F),
      algebraMap F (v.adicCompletion F) (beta e q d he hH) * (t : v.adicCompletion F),
      fun h => absurd hdv h, ?_⟩
    linear_combination hst' +
      ((s : v.adicCompletion F) * (t : v.adicCompletion F)) * hI3 +
      (t : v.adicCompletion F) ^ 2 * hI4
  · have hc : (1 : ℤ) ^ 2 - 4 * quarterPlusOne d = -(d : ℤ) := by
      have := quarterPlusOne_spec d (by omega)
      linarith
    obtain ⟨s, t, hst⟩ := NativeAdicQuadraticNorm.numberField_adicInt_exists_norm F v
      1 (quarterPlusOne d) (by rw [hc]; simpa using hdv)
    have hst' : (s : v.adicCompletion F) ^ 2 +
        (s : v.adicCompletion F) * (t : v.adicCompletion F) +
        (quarterPlusOne d : v.adicCompletion F) * (t : v.adicCompletion F) ^ 2 = -1 := by
      have h := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hst
      push_cast at h
      simpa only [one_mul] using h
    refine ⟨(s : v.adicCompletion F), (t : v.adicCompletion F),
      fun _ => ⟨s.2, t.2⟩, ?_⟩
    linear_combination hst'

theorem finite_primes_over_d :
    {v : HeightOneSpectrum (𝓞 F) | ((d : ℤ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : ((d : ℤ) : 𝓞 F) ≠ 0 :=
    Int.cast_ne_zero.mpr (by exact_mod_cast (Fact.out : d.Prime).ne_zero)
  refine (Ideal.finite_factors (I := Ideal.span {((d : ℤ) : 𝓞 F)}) ?_).subset ?_
  · rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  · intro v hv
    rw [Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv

def localS (he : 2 ≤ e) (hH : HostHyp q d) (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletion F := (local_solution e q d he hH v).choose

def localT (he : 2 ≤ e) (hH : HostHyp q d) (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletion F := (local_solution e q d he hH v).choose_spec.choose

theorem localST_spec (he : 2 ≤ e) (hH : HostHyp q d) (v : HeightOneSpectrum (𝓞 F)) :
    (((d : ℤ) : 𝓞 F) ∉ v.asIdeal →
      localS e q d he hH v ∈ v.adicCompletionIntegers F ∧
      localT e q d he hH v ∈ v.adicCompletionIntegers F) ∧
    localS e q d he hH v * localS e q d he hH v +
      localS e q d he hH v * localT e q d he hH v +
      (quarterPlusOne d : v.adicCompletion F) *
        (localT e q d he hH v * localT e q d he hH v) = -1 :=
  (local_solution e q d he hH v).choose_spec.choose_spec

def adeleS (he : 2 ≤ e) (hH : HostHyp q d) : Af :=
  ⟨fun v => localS e q d he hH v,
    Filter.eventually_cofinite.2 ((finite_primes_over_d e q d).subset (fun v hv => by
      by_contra h
      exact hv ((localST_spec e q d he hH v).1 h).1))⟩

def adeleT (he : 2 ≤ e) (hH : HostHyp q d) : Af :=
  ⟨fun v => localT e q d he hH v,
    Filter.eventually_cofinite.2 ((finite_primes_over_d e q d).subset (fun v hv => by
      by_contra h
      exact hv ((localST_spec e q d he hH v).1 h).2))⟩

theorem adele_norm_equation (he : 2 ≤ e) (hH : HostHyp q d) :
    adeleS e q d he hH * adeleS e q d he hH +
      adeleS e q d he hH * adeleT e q d he hH +
      (quarterPlusOne d : Af) * (adeleT e q d he hH * adeleT e q d he hH) = -1 := by
  refine RestrictedProduct.ext (fun v => ?_)
  change localS e q d he hH v * localS e q d he hH v +
    localS e q d he hH v * localT e q d he hH v +
    (quarterPlusOne d : v.adicCompletion F) *
      (localT e q d he hH v * localT e q d he hH v) = -1
  exact (localST_spec e q d he hH v).2

/-- Scalar extension of the SAME actual conjugation; the adele factor is fixed. -/
def tensorConjugation (he : 2 ≤ e) (hH : HostHyp q d) :
    E ⊗[F] Af →+* E ⊗[F] Af :=
  (Algebra.TensorProduct.map (conjugation e q d he hH) (AlgHom.id F Af)).toRingHom

/-- The constructed source element, with its original half-root normalization. -/
def normMinusOne (he : 2 ≤ e) (hH : HostHyp q d) : E ⊗[F] Af :=
  Algebra.TensorProduct.includeRight (adeleS e q d he hH) +
    Algebra.TensorProduct.includeLeftRingHom (theta e q d) *
      Algebra.TensorProduct.includeRight (adeleT e q d he hH)

private theorem norm_of_quad {B : Type*} [CommRing B]
    (τ : B →+* B) (s t u : B) (N : ℤ)
    (hs : τ s = s) (ht : τ t = t) (hτu : τ u = 1 - u) (hu : u * (1 - u) = N)
    (hk : s * s + s * t + (N : B) * (t * t) = -1) :
    τ (s + u * t) * (s + u * t) = -1 := by
  rw [map_add, map_mul, hs, ht, hτu]
  linear_combination hk + t * t * hu

theorem normMinusOne_spec (he : 2 ≤ e) (hH : HostHyp q d) :
    tensorConjugation e q d he hH (normMinusOne e q d he hH) *
      normMinusOne e q d he hH = -1 := by
  have hL : ∀ x : E, tensorConjugation e q d he hH
      ((Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] Af) x) =
      (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] Af)
        (conjugation e q d he hH x) := by
    intro x
    simp [tensorConjugation, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.map_tmul]
  have hR : ∀ a : Af, tensorConjugation e q d he hH
      ((Algebra.TensorProduct.includeRight : Af →ₐ[F] E ⊗[F] Af) a) =
      (Algebra.TensorProduct.includeRight : Af →ₐ[F] E ⊗[F] Af) a := by
    intro a
    simp [tensorConjugation, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul]
  have hk := congrArg
    (Algebra.TensorProduct.includeRight : Af →ₐ[F] E ⊗[F] Af).toRingHom
    (adele_norm_equation e q d he hH)
  simp only [map_add, map_mul, map_intCast, map_neg, map_one] at hk
  have hu : (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] Af)
      (theta e q d) *
      (1 - (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] Af) (theta e q d)) =
      (quarterPlusOne d : E ⊗[F] Af) := by
    simpa only [map_mul, map_sub, map_one, map_intCast] using
      congrArg (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] Af)
        (theta_norm e q d hH)
  have hτu : tensorConjugation e q d he hH
      ((Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] Af) (theta e q d)) =
      1 - (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] Af) (theta e q d) := by
    rw [hL, conjugation_apply, theta_conj e q d hH, map_sub, map_one]
  exact norm_of_quad _ _ _ _ _ (hR _) (hR _) hτu hu hk

theorem normMinusOne_isUnit (he : 2 ≤ e) (hH : HostHyp q d) :
    IsUnit (normMinusOne e q d he hH) := by
  apply isUnit_of_mul_isUnit_right
    (x := tensorConjugation e q d he hH (normMinusOne e q d he hH))
  rw [normMinusOne_spec]
  exact isUnit_one.neg

/-- The genuine finite-adelic supplier, with the element already constructed above. -/
theorem exists_adelic_neg_one (he : 2 ≤ e) (hH : HostHyp q d) :
    ∃ y : E ⊗[F] Af, tensorConjugation e q d he hH y * y = -1 :=
  ⟨normMinusOne e q d he hH, normMinusOne_spec e q d he hH⟩

end Host

end RHLean.Geometry.NativeDyadicAdelicNorm

end
