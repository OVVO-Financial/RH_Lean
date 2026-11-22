import RHLean.Geometry.NativeLocalQuadraticNorm

/-!
# Quadratic norm-minus-one solutions in actual completion integer rings

This reconstructs the local part of
`Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean` by Levent
Alpöge (with Claude), from `CocoSgt/riemann-hypothesis-lean` at source commit
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

The ring is the literal Mathlib `v.adicCompletionIntegers K`. We prove its
maximal-ideal-adic completeness, derive the Henselian property, and obtain
its finite residue field from the original quotient `R / v.asIdeal`.
The final theorem constructs the source quadratic norm-minus-one solution
at every prime not containing the quadratic discriminant. No Henselian
property, completion residue-field finiteness, or norm solution is assumed separately.

Global patching into a restricted product and the finite-adelic Hermitian
isometry remain subsequent constructions.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeAdicQuadraticNorm

open IsDedekindDomain HeightOneSpectrum IsLocalRing WithZero NumberField Filter Topology

theorem wz_lt_one_iff (γ : ℤᵐ⁰) : γ < 1 ↔ γ ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · exact iff_of_true zero_lt_one zero_le
  · rw [← WithZero.exp_log hγ, ← WithZero.exp_zero, WithZero.exp_lt_exp,
      WithZero.exp_le_exp]
    omega

theorem wz_exists_nat_lt (γ : ℤᵐ⁰) (h : γ ≠ 0) :
    ∃ N : ℕ, exp (-(N : ℤ)) < γ := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, exp m = γ := ⟨_, WithZero.exp_log h⟩
  exact ⟨m.natAbs + 1, by rw [WithZero.exp_lt_exp]; omega⟩

section Completion

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

local notation "Ov" => v.adicCompletionIntegers K
local notation "Kv" => v.adicCompletion K

theorem adicInt_integers :
    Valuation.Integers (Valued.v : Valuation Kv ℤᵐ⁰) Ov :=
  adicCompletionIntegers.integers K v

theorem adicInt_exists_unif :
    ∃ π : Ov, Valued.v (π : Kv) = exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hv : Valued.v (π : Kv) = exp (-1 : ℤ) := by
    rw [← hπ]
    exact valuedAdicCompletion_eq_valuation' (v := v) π
  have hle : Valued.v (π : Kv) ≤ 1 := by
    rw [hv]
    exact ((wz_lt_one_iff _).mpr le_rfl).le
  exact ⟨⟨(π : Kv), hle⟩, hv⟩

theorem adicInt_mem_max_iff (x : Ov) :
    x ∈ maximalIdeal Ov ↔ Valued.v (x : Kv) < 1 := by
  have hI := adicInt_integers (K := K) v
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
  exact (hI.map_le_one x).lt_iff_ne.symm

theorem adicInt_dvd_iff (x y : Ov) :
    x ∣ y ↔ Valued.v (y : Kv) ≤ Valued.v (x : Kv) :=
  (adicInt_integers (K := K) v).dvd_iff_le

theorem adicInt_max_eq_span (π : Ov) (hπ : Valued.v (π : Kv) = exp (-1 : ℤ)) :
    maximalIdeal Ov = Ideal.span {π} := by
  ext x
  rw [adicInt_mem_max_iff v x, Ideal.mem_span_singleton, adicInt_dvd_iff v π x,
    hπ, wz_lt_one_iff]

theorem adicInt_mem_pow_iff (n : ℕ) (x : Ov) :
    x ∈ (maximalIdeal Ov) ^ n ↔ Valued.v (x : Kv) ≤ exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := adicInt_exists_unif (K := K) v
  have h1 : ((π ^ n : Ov) : Kv) = (π : Kv) ^ n := rfl
  have hpow : Valued.v ((π ^ n : Ov) : Kv) = exp (-(n : ℤ)) := by
    rw [h1, map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  rw [adicInt_max_eq_span v π hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    adicInt_dvd_iff v, hpow]

theorem adicInt_eq_zero_of_forall (x : Kv)
    (h : ∀ n : ℕ, Valued.v x ≤ exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨N, hN⟩ := wz_exists_nat_lt (Valued.v x) h0
  exact absurd (h N) (not_le.mpr hN)

theorem adicCompl_isClosed_le (r : ℤᵐ⁰) :
    IsClosed {x : Kv | Valued.v x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : r < Valued.v x := not_le.mp hx
  have hx0 : Valued.v x ≠ 0 := (lt_of_le_of_lt zero_le hx').ne'
  have hmem : {y : Kv | Valued.v y = Valued.v x} ∈ 𝓝 x :=
    Valued.locally_const hx0
  filter_upwards [hmem] with y hy
  show ¬ Valued.v y ≤ r
  rw [show Valued.v y = Valued.v x from hy]
  exact not_le.mpr hx'

/-- Completeness is proved for the same valuation-subring lattice, using
the actual valuation of the complete field and the source powers of its maximal ideal. -/
theorem adicInt_isAdicComplete : IsAdicComplete (maximalIdeal Ov) Ov := by
  have key : ∀ (n : ℕ) (x y : Ov),
      x ≡ y [SMOD (maximalIdeal Ov ^ n • ⊤ : Submodule Ov Ov)] ↔
        Valued.v ((x : Kv) - y) ≤ exp (-(n : ℤ)) := by
    intro n x y
    simpa only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
      AddSubgroupClass.coe_sub] using
      (adicInt_mem_pow_iff (K := K) v n (x - y))
  have h1 : IsHausdorff (maximalIdeal Ov) Ov := by
    refine ⟨fun x hx => ?_⟩
    have h0 : (x : Kv) = 0 := adicInt_eq_zero_of_forall v _ (fun n => by
      simpa using (key n x 0).1 (hx n))
    exact Subtype.ext h0
  have h2 : IsPrecomplete (maximalIdeal Ov) Ov := by
    refine ⟨fun f hf => ?_⟩
    set g : ℕ → Kv := fun n => (f n : Kv)
    have hg : ∀ m n, m ≤ n → Valued.v (g n - g m) ≤ exp (-(m : ℤ)) := by
      intro m n hmn
      have := (key m (f m) (f n)).1 (hf hmn)
      rwa [← Valuation.map_neg, neg_sub] at this
    have hc : CauchySeq g := by
      rw [(Valued.hasBasis_uniformity Kv ℤᵐ⁰).cauchySeq_iff]
      intro γ _
      have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := fun h =>
        γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_injective
          (h.trans (map_zero _).symm))
      obtain ⟨N, hN⟩ := wz_exists_nat_lt _ hne
      refine ⟨N, fun m hm n hn => ?_⟩
      simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
      have hle : ∀ a b, N ≤ a → a ≤ b →
          Valued.v (g b - g a) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
        fun a b ha hab =>
          lt_of_le_of_lt ((hg a b hab).trans (exp_le_exp.2 (by omega))) hN
      rcases le_total m n with h | h
      · exact hle m n hm h
      · rw [← Valuation.map_neg, neg_sub]
        exact hle n m hn h
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hLmem : L ∈ Ov := by
      refine (Valued.isClosed_valuationSubring Kv).mem_of_tendsto hL
        (Eventually.of_forall ?_)
      intro n
      exact (f n).2
    refine ⟨⟨L, hLmem⟩, fun n => ?_⟩
    rw [key]
    have hcl : IsClosed {y : Kv | Valued.v (g n - y) ≤ exp (-(n : ℤ))} :=
      (adicCompl_isClosed_le v _).preimage (continuous_const.sub continuous_id)
    refine hcl.mem_of_tendsto hL ?_
    filter_upwards [eventually_ge_atTop n] with k hk
    show Valued.v (g n - g k) ≤ _
    rw [← Valuation.map_neg, neg_sub]
    exact hg n k hk
  exact { toIsHausdorff := h1, toIsPrecomplete := h2 }

@[instance] theorem adicInt_henselian : HenselianLocalRing Ov := by
  have := adicInt_isAdicComplete (K := K) v
  have : HenselianRing Ov (maximalIdeal Ov) := inferInstance
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

theorem adicCompl_val_algebraMap (y : K) :
    Valued.v (algebraMap K Kv y) = v.valuation K y :=
  valuedAdicCompletion_eq_valuation' (v := v) y

/-- Reduction of the original global integer ring onto the actual completion residue field. -/
theorem adicInt_residue_surj :
    Function.Surjective ((residue Ov).comp (algebraMap R Ov)) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  have hn : {z : Kv | Valued.v (z - x) < 1} ∈ 𝓝 (x : Kv) := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun z hz => ?_⟩
    simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding,
      Units.val_one, map_one] at hz ⊢
    exact hz
  obtain ⟨_, hz, ⟨k, rfl⟩⟩ := mem_closure_iff_nhds.1
    (denseRange_algebraMap (R := R) (K := K) (v := v) (x : Kv)) _ hn
  have hz' : Valued.v (algebraMap K Kv k - x) < 1 := hz
  have hk : v.valuation K k ≤ 1 := by
    rw [← adicCompl_val_algebraMap]
    have e : algebraMap K Kv k = (algebraMap K Kv k - x) + x := by ring
    rw [e]
    exact Valuation.map_add_le _ hz'.le x.2
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer (K := K) v hk 1
  refine ⟨a, ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  apply (Ideal.Quotient.eq).2
  rw [adicInt_mem_max_iff]
  have e1 : ((algebraMap R Ov a : Ov) : Kv) =
      algebraMap K Kv (algebraMap R K a) := rfl
  have e2 : ((algebraMap R Ov a - x : Ov) : Kv) =
      algebraMap K Kv (algebraMap R K a - k) + (algebraMap K Kv k - x) := by
    rw [map_sub, AddSubgroupClass.coe_sub, e1]
    ring
  rw [e2]
  refine Valuation.map_add_lt _ ?_ hz'
  rw [adicCompl_val_algebraMap]
  simpa using ha

theorem adicInt_residue_finite [Finite (R ⧸ v.asIdeal)] :
    Finite (ResidueField Ov) := by
  have hf : ∀ a ∈ v.asIdeal, ((residue Ov).comp (algebraMap R Ov)) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, adicInt_mem_max_iff]
    have h1 : ((algebraMap R Ov a : Ov) : Kv) =
        algebraMap K Kv (algebraMap R K a) := rfl
    rw [h1, adicCompl_val_algebraMap, valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v a).mpr ha
  exact Finite.of_surjective _
    (Ideal.Quotient.lift_surjective_of_surjective v.asIdeal hf (adicInt_residue_surj v))

theorem adicInt_isUnit_of_not_mem (r : R) (hr : r ∉ v.asIdeal) :
    IsUnit (algebraMap R Ov r) := by
  rw [(adicInt_integers (K := K) v).isUnit_iff_valuation_eq_one]
  have h1 : algebraMap Ov Kv (algebraMap R Ov r) =
      algebraMap K Kv (algebraMap R K r) := rfl
  rw [h1, adicCompl_val_algebraMap, valuation_of_algebraMap]
  exact intValuation_eq_one_iff.mpr hr

/-- The original integral norm equation, now supplied on the actual completion
without an additional Henselian-ring or finite-residue-field assumption. -/
theorem adicInt_exists_norm [Finite (R ⧸ v.asIdeal)] (T N : ℤ)
    (hD : ((T ^ 2 - 4 * N : ℤ) : R) ∉ v.asIdeal) :
    ∃ s t : Ov, s ^ 2 + (T : Ov) * s * t + (N : Ov) * t ^ 2 = -1 := by
  have := adicInt_residue_finite (K := K) v
  have hDu : IsUnit ((T : Ov) ^ 2 - 4 * (N : Ov)) := by
    have e : (T : Ov) ^ 2 - 4 * (N : Ov) =
        algebraMap R Ov ((T ^ 2 - 4 * N : ℤ) : R) := by
      calc
        (T : Ov) ^ 2 - 4 * (N : Ov) = ((T ^ 2 - 4 * N : ℤ) : Ov) := by
          simp only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]
        _ = algebraMap R Ov ((T ^ 2 - 4 * N : ℤ) : R) :=
          (map_intCast (algebraMap R Ov) (T ^ 2 - 4 * N)).symm
    rw [e]
    exact adicInt_isUnit_of_not_mem v _ hD
  exact NativeLocalQuadraticNorm.henselian_quadratic_neg_one (T : Ov) (N : Ov) hDu

end Completion

/-- For a number field, finiteness of the original residue field is supplied
by its actual nonzero prime ideal; only exclusion of the discriminant remains. -/
theorem numberField_adicInt_exists_norm
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (T N : ℤ)
    (hD : ((T ^ 2 - 4 * N : ℤ) : 𝓞 F) ∉ v.asIdeal) :
    ∃ s t : v.adicCompletionIntegers F,
      s ^ 2 + (T : v.adicCompletionIntegers F) * s * t +
        (N : v.adicCompletionIntegers F) * t ^ 2 = -1 :=
  adicInt_exists_norm (K := F) v T N hD

end RHLean.Geometry.NativeAdicQuadraticNorm

end
