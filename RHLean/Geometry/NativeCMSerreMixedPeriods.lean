import RHLean.Geometry.NativeCMSerrePolarization

/-!
# Mixed native Serre periods with both elliptic orientations

The literal positive and negative coordinate blocks are kept separate.
The positive block tensors with the original elliptic seed; the negative
block tensors with its actual conjugate seed. Conjugation on the original
elliptic quotient is proved quadratic-order linear, then tensored with the
unchanged projective coefficient module.

The resulting additive exponential has kernel exactly the already
constructed mixed period map, including every negative-coordinate
conjugation and the original finite enumeration. In particular the mixed
object is not treated as one pure-type elliptic tensor. These are analytic
point modules, with no assertion of scheme representability.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsHermFormCurve.lean`, `exists_isExp_of_isTen`, with its explicit
pure-type alternatives. The native mixed construction combines those two
analytic types using the proved literal lattice split.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical TensorProduct Pointwise ComplexConjugate

namespace RHLean.Geometry.NativeCM.EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)

/-- Conjugation is an actual quadratic-order linear equivalence between
the two analytic elliptic seeds, with their respective order actions. -/
def conjugateTorus : Torus G τ ≃ₗ[OK G] Torus G (ComplexEmbedding.conjugate τ) := by
  let f : Torus G τ →+ Torus G (ComplexEmbedding.conjugate τ) :=
    QuotientAddGroup.map (period G τ).range
      (period G (ComplexEmbedding.conjugate τ)).range
      (starRingEnd ℂ).toAddMonoidHom (by
        rintro _ ⟨a, rfl⟩
        exact ⟨a, rfl⟩)
  let g : Torus G (ComplexEmbedding.conjugate τ) →+ Torus G τ :=
    QuotientAddGroup.map (period G (ComplexEmbedding.conjugate τ)).range
      (period G τ).range (starRingEnd ℂ).toAddMonoidHom (by
        rintro _ ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        change embed G τ a = conj (conj (embed G τ a))
        simp)
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (period G τ).range x
        change QuotientAddGroup.mk' (period G τ).range (conj (conj z)) =
          QuotientAddGroup.mk' (period G τ).range z
        simp
      right_inv := by
        intro x
        obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
          (period G (ComplexEmbedding.conjugate τ)).range x
        change QuotientAddGroup.mk' (period G (ComplexEmbedding.conjugate τ)).range
            (conj (conj z)) =
          QuotientAddGroup.mk' (period G (ComplexEmbedding.conjugate τ)).range z
        simp
      map_add' := map_add f
      map_smul' := by
        intro a x
        obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective (period G τ).range x
        change QuotientAddGroup.mk' (period G (ComplexEmbedding.conjugate τ)).range
            (conj (embed G τ a * z)) =
          QuotientAddGroup.mk' (period G (ComplexEmbedding.conjugate τ)).range
            (embed G (ComplexEmbedding.conjugate τ) a * conj z)
        rw [map_mul]
        rfl }

theorem conjugateTorus_mk (z : ℂ) :
    conjugateTorus G τ (QuotientAddGroup.mk' (period G τ).range z) =
      QuotientAddGroup.mk' (period G (ComplexEmbedding.conjugate τ)).range (conj z) := rfl

/-- Conjugation changes only the actual seed factor. -/
def conjugateTensor (M : Type) [AddCommGroup M] [Module (OK G) M] :
    M ⊗[OK G] Torus G τ ≃ₗ[OK G] M ⊗[OK G] Torus G (ComplexEmbedding.conjugate τ) :=
  (conjugateTorus G τ).lTensor M

theorem conjugateTensor_tmul (M : Type) [AddCommGroup M] [Module (OK G) M]
    (x : M) (z : ℂ) :
    conjugateTensor G τ M (x ⊗ₜ[OK G] QuotientAddGroup.mk' (period G τ).range z) =
      x ⊗ₜ[OK G] QuotientAddGroup.mk'
        (period G (ComplexEmbedding.conjugate τ)).range (conj z) := by
  change (conjugateTorus G τ).toLinearMap.lTensor M
    (x ⊗ₜ[OK G] QuotientAddGroup.mk' (period G τ).range z) = _
  rw [LinearMap.lTensor_tmul]
  rfl

/-- The full original coefficient action stays on the first factor when
the elliptic orientation is changed. -/
theorem conjugateTensor_smul (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    (a : 𝓞 E) (t : M ⊗[OK G] Torus G τ) :
    conjugateTensor G τ M (a • t) = a • conjugateTensor G τ M t := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [smul_add, map_add, ht, hu]
  | tmul x z =>
    change (conjugateTorus G τ).toLinearMap.lTensor M
      ((a • x) ⊗ₜ[OK G] z) =
        (a • x) ⊗ₜ[OK G] (conjugateTorus G τ) z
    rw [LinearMap.lTensor_tmul]

end RHLean.Geometry.NativeCM.EllipticSeed

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM NativeGeometricPeriods

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E) [Algebra (OK G) ℂ]
    (hcompat : ∀ τ : cmTypeFinset H,
      embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ)

/-- The complete O_E action on raw positive embedding coordinates. -/
def rawCoefficientAction (N : ℕ) (a : 𝓞 H.E) :
    (cmTypeFinset H → Fin N → ℂ) →ₗ[ℂ] (cmTypeFinset H → Fin N → ℂ) where
  toFun v τ i := (τ : H.E →+* ℂ) (a : H.E) * v τ i
  map_add' _ _ := by
    ext τ i
    exact mul_add _ _ _
  map_smul' z _ := by
    ext τ i
    change _ * (z * _) = z * (_ * _)
    ring

theorem rawCoefficientAction_period (B : Ideal (𝓞 H.E)) (N : ℕ)
    (a : 𝓞 H.E) (x : twistedLattice H B N) :
    rawCoefficientAction H N a (purePeriodLinear H G hcompat B N x) =
      purePeriodLinear H G hcompat B N (a • x) := by
  ext τ i
  exact (map_mul (τ : H.E →+* ℂ) (a : H.E) (x.1 i)).symm

/-- The pure exponential retains the full coefficient action, including
elements outside the quadratic seed order. -/
theorem pureSerreExponential_coefficient (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (τ₀ : cmTypeFinset H) (a : 𝓞 H.E) (v : cmTypeFinset H → Fin N → ℂ) :
    pureSerreExponential H G hcompat B hB N τ₀ (rawCoefficientAction H N a v) =
      a • pureSerreExponential H G hcompat B hB N τ₀ v := by
  obtain ⟨t, rfl⟩ := (pureSerrePeriodEquiv H G hcompat B hB N).surjective v
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, ht, hu, smul_add]
  | tmul z x =>
    rw [pureSerrePeriodEquiv_tmul, map_smul, rawCoefficientAction_period,
      pureSerreExponential_period_smul, pureSerreExponential_period_smul]
    exact TensorProduct.smul_tmul' a x _

/-- The raw finite coordinate split agrees literally with the integral
split of the same inverse-ideal products. -/
def rawBlockSplit (p q : ℕ) :
    (cmTypeFinset H → Fin (p + q) → ℂ) ≃ₗ[ℂ]
      ((cmTypeFinset H → Fin p → ℂ) × (cmTypeFinset H → Fin q → ℂ)) where
  toFun u := (fun τ i => u τ (Fin.castAdd q i), fun τ i => u τ (Fin.natAdd p i))
  invFun u τ := Fin.addCases (u.1 τ) (u.2 τ)
  left_inv u := by
    funext τ i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  right_inv u := by
    apply Prod.ext <;> funext τ i <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rawBlockSplit_period (B : Ideal (𝓞 H.E)) (p q : ℕ)
    (x : twistedLattice H B (p + q)) :
    rawBlockSplit H p q (purePeriodLinear H G hcompat B (p + q) x) =
      (purePeriodLinear H G hcompat B p (twistedBlockSplit H B p q x).1,
        purePeriodLinear H G hcompat B q (twistedBlockSplit H B p q x).2) := by
  apply Prod.ext
  · funext τ i
    apply congrArg (τ : H.E →+* ℂ)
    exact (congrArg Subtype.val (twistedBlockSplit_left H B p q x i)).symm
  · funext τ i
    apply congrArg (τ : H.E →+* ℂ)
    exact (congrArg Subtype.val (twistedBlockSplit_right H B p q x i)).symm

/-- This inverse retains precisely the original negative-coordinate
conjugations and finite enumeration. -/
def mixedInputCoordinates (p q : ℕ) :
    (Fin ((cmTypeFinset H).card * (p + q)) → ℂ) ≃ₗ[ℝ]
      ((cmTypeFinset H → Fin p → ℂ) × (cmTypeFinset H → Fin q → ℂ)) :=
  (NativePeriodCoordinates.coordinates (cmTypeFinset H) (p + q) q).symm.trans
    ((rawBlockSplit H p q).restrictScalars ℝ)

omit [IsCMField H.E] [Algebra (OK G) ℂ] in
theorem mixedInputCoordinates_coordinates (p q : ℕ)
    (u : cmTypeFinset H → Fin (p + q) → ℂ) :
    mixedInputCoordinates H p q
        (NativePeriodCoordinates.coordinates (cmTypeFinset H) (p + q) q u) =
      rawBlockSplit H p q u := by
  change rawBlockSplit H p q
    ((NativePeriodCoordinates.coordinates (cmTypeFinset H) (p + q) q).symm
      (NativePeriodCoordinates.coordinates (cmTypeFinset H) (p + q) q u)) = _
  rw [LinearEquiv.symm_apply_apply]

omit [IsCMField H.E] [Algebra (OK G) ℂ] in
theorem mixedInputCoordinates_left (p q : ℕ)
    (v : Fin ((cmTypeFinset H).card * (p + q)) → ℂ)
    (τ : cmTypeFinset H) (i : Fin p) :
    (mixedInputCoordinates H p q v).1 τ i =
      v (NativePeriodCoordinates.indexEquiv (cmTypeFinset H) (p + q)
        (τ, Fin.castAdd q i)) := by
  change NativePeriodCoordinates.conjIf
    (NativePrescribedHermitian.negTail (p + q) q (Fin.castAdd q i)) _ = _
  rw [NativePrescribedHermitian.negTail_false (p + q) q (Fin.castAdd q i)
    (by simp)]
  rfl

omit [IsCMField H.E] [Algebra (OK G) ℂ] in
theorem mixedInputCoordinates_right (p q : ℕ)
    (v : Fin ((cmTypeFinset H).card * (p + q)) → ℂ)
    (τ : cmTypeFinset H) (i : Fin q) :
    (mixedInputCoordinates H p q v).2 τ i =
      conj (v (NativePeriodCoordinates.indexEquiv (cmTypeFinset H) (p + q)
        (τ, Fin.natAdd p i))) := by
  change NativePeriodCoordinates.conjIf
    (NativePrescribedHermitian.negTail (p + q) q (Fin.natAdd p i)) _ = _
  rw [NativePrescribedHermitian.negTail_true (p + q) q (Fin.natAdd p i) (by simp)]
  rfl

omit [IsCMField H.E] [Algebra (OK G) ℂ] in
/-- Ordinary complex scaling becomes conjugate scaling on precisely the
negative input block. -/
theorem mixedInputCoordinates_smul (p q : ℕ) (z : ℂ)
    (v : Fin ((cmTypeFinset H).card * (p + q)) → ℂ) :
    mixedInputCoordinates H p q (z • v) =
      (z • (mixedInputCoordinates H p q v).1,
        conj z • (mixedInputCoordinates H p q v).2) := by
  apply Prod.ext
  · funext τ i
    simp only [mixedInputCoordinates_left, Pi.smul_apply, smul_eq_mul]
  · funext τ i
    simp only [mixedInputCoordinates_right, Pi.smul_apply, smul_eq_mul, map_mul]

/-- The exact already constructed mixed period map. -/
def mixedPeriodMap (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (p q : ℕ) :
    twistedLattice H B (p + q) →+
      (Fin ((cmTypeFinset H).card * (p + q)) → ℂ) :=
  periodOfRealEquiv (twistedPeriodRealEquiv H B hB (p + q) q)

theorem mixedPeriodMap_apply (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (p q : ℕ)
    (x : twistedLattice H B (p + q)) :
    mixedPeriodMap H B hB p q x =
      NativePeriodCoordinates.coordinates (cmTypeFinset H) (p + q) q
        (purePeriodLinear H G hcompat B (p + q) x) := by
  rw [mixedPeriodMap, periodOfRealEquiv_apply, twistedPeriodRealEquiv_tmul]
  simp only [Complex.ofReal_one, one_mul]
  rfl

theorem mixedInputCoordinates_period (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (p q : ℕ)
    (x : twistedLattice H B (p + q)) :
    mixedInputCoordinates H p q (mixedPeriodMap H B hB p q x) =
      (purePeriodLinear H G hcompat B p (twistedBlockSplit H B p q x).1,
        purePeriodLinear H G hcompat B q (twistedBlockSplit H B p q x).2) := by
  rw [mixedPeriodMap_apply H G hcompat]
  change rawBlockSplit H p q
    ((NativePeriodCoordinates.coordinates (cmTypeFinset H) (p + q) q).symm
      (NativePeriodCoordinates.coordinates (cmTypeFinset H) (p + q) q
        (purePeriodLinear H G hcompat B (p + q) x))) = _
  rw [LinearEquiv.symm_apply_apply, rawBlockSplit_period]

/-- The negative factor is the conjugate elliptic seed, not the positive
seed with a discarded sign. Both factors retain the original O_E action. -/
abbrev mixedSerrePoints (B : Ideal (𝓞 H.E)) (p q : ℕ) (τ₀ : cmTypeFinset H) :=
  (twistedLattice H B p ⊗[OK G] EllipticSeed.Torus G (τ₀ : H.E →+* ℂ)) ×
    (twistedLattice H B q ⊗[OK G]
      EllipticSeed.Torus G (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ)))

def rawMixedSerreExponential (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (p q : ℕ)
    (τ₀ : cmTypeFinset H) :
    ((cmTypeFinset H → Fin p → ℂ) × (cmTypeFinset H → Fin q → ℂ)) →ₗ[OK G]
      mixedSerrePoints H G B p q τ₀ :=
  LinearMap.prodMap (pureSerreExponential H G hcompat B hB p τ₀)
    ((EllipticSeed.conjugateTensor G (τ₀ : H.E →+* ℂ)
      (twistedLattice H B q)).toLinearMap ∘ₗ
        pureSerreExponential H G hcompat B hB q τ₀)

/-- The mixed exponential is additive. There is no assertion that both
different CM characters act by one scalar on its ambient complex space. -/
def mixedSerreExponential (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (p q : ℕ)
    (τ₀ : cmTypeFinset H) :
    (Fin ((cmTypeFinset H).card * (p + q)) → ℂ) →+
      mixedSerrePoints H G B p q τ₀ :=
  (rawMixedSerreExponential H G hcompat B hB p q τ₀).toAddMonoidHom.comp
    (mixedInputCoordinates H p q).toAddEquiv.toAddMonoidHom

/-- On every period ray the two factors are the literal pure tensors
with the same complex argument in their respective actual elliptic seeds. -/
theorem mixedSerreExponential_period_smul (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (p q : ℕ)
    (τ₀ : cmTypeFinset H) (z : ℂ) (x : twistedLattice H B (p + q)) :
    mixedSerreExponential H G hcompat B hB p q τ₀
        (z • mixedPeriodMap H B hB p q x) =
      ((twistedBlockSplit H B p q x).1 ⊗ₜ[OK G]
          QuotientAddGroup.mk' (EllipticSeed.period G (τ₀ : H.E →+* ℂ)).range z,
        (twistedBlockSplit H B p q x).2 ⊗ₜ[OK G]
          QuotientAddGroup.mk' (EllipticSeed.period G
            (ComplexEmbedding.conjugate (τ₀ : H.E →+* ℂ))).range z) := by
  change rawMixedSerreExponential H G hcompat B hB p q τ₀
    (mixedInputCoordinates H p q (z • mixedPeriodMap H B hB p q x)) = _
  rw [mixedInputCoordinates_smul, mixedInputCoordinates_period H G hcompat]
  apply Prod.ext
  · exact pureSerreExponential_period_smul H G hcompat B hB p τ₀ z _
  · change EllipticSeed.conjugateTensor G (τ₀ : H.E →+* ℂ) (twistedLattice H B q)
      (pureSerreExponential H G hcompat B hB q τ₀
        (conj z • purePeriodLinear H G hcompat B q (twistedBlockSplit H B p q x).2)) = _
    rw [pureSerreExponential_period_smul, EllipticSeed.conjugateTensor_tmul]
    simp

theorem mixedSerreExponential_surjective (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (p q : ℕ)
    (τ₀ : cmTypeFinset H) :
    Function.Surjective (mixedSerreExponential H G hcompat B hB p q τ₀) := by
  intro y
  obtain ⟨u, hu⟩ := pureSerreExponential_surjective H G hcompat B hB p τ₀ y.1
  obtain ⟨v, hv⟩ := ((EllipticSeed.conjugateTensor G (τ₀ : H.E →+* ℂ)
    (twistedLattice H B q)).surjective.comp
      (pureSerreExponential_surjective H G hcompat B hB q τ₀)) y.2
  refine ⟨(mixedInputCoordinates H p q).symm (u, v), ?_⟩
  change rawMixedSerreExponential H G hcompat B hB p q τ₀
    (mixedInputCoordinates H p q ((mixedInputCoordinates H p q).symm (u, v))) = y
  rw [LinearEquiv.apply_symm_apply]
  exact Prod.ext hu hv

/-- Both exact pure kernels recombine to the original mixed period
image on the same full integral lattice. -/
theorem mixedSerreExponential_ker (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (p q : ℕ)
    (τ₀ : cmTypeFinset H) (v : Fin ((cmTypeFinset H).card * (p + q)) → ℂ) :
    mixedSerreExponential H G hcompat B hB p q τ₀ v = 0 ↔
      v ∈ (mixedPeriodMap H B hB p q).range := by
  let u := mixedInputCoordinates H p q v
  change (pureSerreExponential H G hcompat B hB p τ₀ u.1,
    EllipticSeed.conjugateTensor G (τ₀ : H.E →+* ℂ) (twistedLattice H B q)
      (pureSerreExponential H G hcompat B hB q τ₀ u.2)) = (0, 0) ↔ _
  rw [Prod.mk.injEq, LinearEquiv.map_eq_zero_iff,
    pureSerreExponential_ker, pureSerreExponential_ker]
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨(twistedBlockSplit H B p q).symm (x, y), ?_⟩
    apply (mixedInputCoordinates H p q).injective
    rw [mixedInputCoordinates_period H G hcompat]
    simp only [LinearEquiv.apply_symm_apply]
    exact Prod.ext hx hy
  · rintro ⟨x, rfl⟩
    have hu := mixedInputCoordinates_period H G hcompat B hB p q x
    exact ⟨⟨(twistedBlockSplit H B p q x).1, (congrArg Prod.fst hu).symm⟩,
      ⟨(twistedBlockSplit H B p q x).2, (congrArg Prod.snd hu).symm⟩⟩

/-- The mixed coordinate action has exactly the existing signed embedding
type: original embeddings in the positive rows and conjugates in the rest. -/
def mixedCoefficientAction (p q : ℕ) (a : 𝓞 H.E) :
    (Fin ((cmTypeFinset H).card * (p + q)) → ℂ) →ₗ[ℂ]
      (Fin ((cmTypeFinset H).card * (p + q)) → ℂ) where
  toFun v s := NativePeriodCoordinates.typeFn (cmTypeFinset H) (p + q) q s
    (a : H.E) * v s
  map_add' _ _ := by
    ext s
    exact mul_add _ _ _
  map_smul' z _ := by
    ext s
    change _ * (z * _) = z * (_ * _)
    ring

omit [IsCMField H.E] [Algebra (OK G) ℂ] in
theorem mixedInputCoordinates_coefficient (p q : ℕ) (a : 𝓞 H.E)
    (v : Fin ((cmTypeFinset H).card * (p + q)) → ℂ) :
    mixedInputCoordinates H p q (mixedCoefficientAction H p q a v) =
      (rawCoefficientAction H p a (mixedInputCoordinates H p q v).1,
        rawCoefficientAction H q a (mixedInputCoordinates H p q v).2) := by
  obtain ⟨u, rfl⟩ :=
    (NativePeriodCoordinates.coordinates (cmTypeFinset H) (p + q) q).surjective v
  have hact : mixedCoefficientAction H p q a
      (NativePeriodCoordinates.coordinates (cmTypeFinset H) (p + q) q u) =
      NativePeriodCoordinates.coordinates (cmTypeFinset H) (p + q) q
        (rawCoefficientAction H (p + q) a u) := by
    funext s
    exact (NativePeriodCoordinates.coordinates_mul (cmTypeFinset H)
      (p + q) q (a : H.E) u s).symm
  rw [hact]
  simp only [mixedInputCoordinates_coordinates]
  apply Prod.ext <;> rfl

theorem mixedSerreExponential_coefficient (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (p q : ℕ)
    (τ₀ : cmTypeFinset H) (a : 𝓞 H.E)
    (v : Fin ((cmTypeFinset H).card * (p + q)) → ℂ) :
    mixedSerreExponential H G hcompat B hB p q τ₀
        (mixedCoefficientAction H p q a v) =
      a • mixedSerreExponential H G hcompat B hB p q τ₀ v := by
  change rawMixedSerreExponential H G hcompat B hB p q τ₀
      (mixedInputCoordinates H p q (mixedCoefficientAction H p q a v)) = _
  rw [mixedInputCoordinates_coefficient]
  apply Prod.ext
  · exact pureSerreExponential_coefficient H G hcompat B hB p τ₀ a _
  · change EllipticSeed.conjugateTensor G (τ₀ : H.E →+* ℂ) (twistedLattice H B q)
      (pureSerreExponential H G hcompat B hB q τ₀
        (rawCoefficientAction H q a (mixedInputCoordinates H p q v).2)) =
      a • EllipticSeed.conjugateTensor G (τ₀ : H.E →+* ℂ) (twistedLattice H B q)
        (pureSerreExponential H G hcompat B hB q τ₀ (mixedInputCoordinates H p q v).2)
    rw [pureSerreExponential_coefficient, EllipticSeed.conjugateTensor_smul]

include hcompat in
/-- The existing prescribed period map is now the kernel of the actual
positive/conjugate-seed tensor product for every allowed original j. -/
theorem exists_prescribedMixedSerreExponential (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) (τ₀ : cmTypeFinset H) :
    ∃ ex : (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ) →+
        mixedSerrePoints H G B (k + j - 1) (m - j) τ₀,
      Function.Surjective ex ∧
      (∀ v, ex v = 0 ↔ v ∈ (prescribedPeriodMap H B hB k m j).range) ∧
      ∀ (a : 𝓞 H.E) v, ex (fun s => prescribedPeriodType H k m j s (a : H.E) * v s) =
        a • ex v := by
  have hpq : (k + j - 1) + (m - j) = k + m - 1 := by omega
  -- Abstract the dimension before transporting: the lattice, period map,
  -- source coordinates and coefficient action must all vary together.
  have transport (N : ℕ) (hN : (k + j - 1) + (m - j) = N) :
      ∃ ex : (Fin ((cmTypeFinset H).card * N) → ℂ) →+
          mixedSerrePoints H G B (k + j - 1) (m - j) τ₀,
        Function.Surjective ex ∧
        (∀ v, ex v = 0 ↔
          v ∈ (periodOfRealEquiv (twistedPeriodRealEquiv H B hB N (m - j))).range) ∧
        ∀ (a : 𝓞 H.E) v,
          ex (fun s => NativePeriodCoordinates.typeFn (cmTypeFinset H) N (m - j) s
            (a : H.E) * v s) = a • ex v := by
    subst N
    exact ⟨mixedSerreExponential H G hcompat B hB (k + j - 1) (m - j) τ₀,
      mixedSerreExponential_surjective H G hcompat B hB (k + j - 1) (m - j) τ₀,
      mixedSerreExponential_ker H G hcompat B hB (k + j - 1) (m - j) τ₀,
      mixedSerreExponential_coefficient H G hcompat B hB (k + j - 1) (m - j) τ₀⟩
  exact transport (k + m - 1) hpq

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM
open NativeRawHostPolarization

/-- The complete native mixed exponential uses both actual elliptic
orientations on the same half-different. Its kernel is the existing
prescribed period lattice for all original signatures, its coefficient
action is the existing signed type, and both full block ranks are retained. -/
theorem nativeDyadicHost_exists_mixedSerrePeriods
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ (k m j : ℕ), m + 3 ≤ k → j ≤ m → ∀ τ₀ : cmTypeFinset H.toHostRaw,
        Module.finrank (OK G) (twistedLattice H.toHostRaw B (k + j - 1)) =
          (2 * 2 ^ e) * (k + j - 1) ∧
        Module.finrank (OK G) (twistedLattice H.toHostRaw B (m - j)) =
          (2 * 2 ^ e) * (m - j) ∧
        ∃ ex : (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1)) → ℂ) →+
            mixedSerrePoints H.toHostRaw G B (k + j - 1) (m - j) τ₀,
          Function.Surjective ex ∧
          (∀ v, ex v = 0 ↔ v ∈ (prescribedPeriodMap H.toHostRaw B hB k m j).range) ∧
          ∀ (a : 𝓞 H.E) v,
            ex (fun s => prescribedPeriodType H.toHostRaw k m j s (a : H.E) * v s) =
              a • ex v := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro k m j hk hj τ₀
  let _ : Algebra (OK G) ℂ := (embed G (τ₀ : H.E →+* ℂ)).toAlgebra
  have hcompat : ∀ τ : cmTypeFinset H.toHostRaw,
      embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ := by
    intro τ
    exact nativeDyadic_quadraticEmbeddings_eq e q d he hH τ τ₀
  have hrank (N : ℕ) : Module.finrank (OK G) (twistedLattice H.toHostRaw B N) =
      (2 * 2 ^ e) * N := by
    have hr := ((OK_isDedekindDomain_and_projective H.E G).2.2.2.2.2
      (twistedLattice H.toHostRaw B N) (twistedLattice_finite H.toHostRaw B N)
      (twistedLattice_projective H.toHostRaw B N)).2.2
    rw [hr, twistedLattice_rank H.toHostRaw B hB N]
    have hdeg : Module.finrank ℚ H.E / 2 = 2 * 2 ^ e := by
      change Module.finrank ℚ (nativeDyadicHostRaw e q d he hH).E / 2 = 2 * 2 ^ e
      rw [nativeDyadicHostRaw_finrank_E, nativeDyadicFrame_ord]
      omega
    rw [hdeg]
  exact ⟨hrank _, hrank _, exists_prescribedMixedSerreExponential H.toHostRaw G hcompat
    B hB k m j hk hj τ₀⟩

end RHLean.Analysis.AlpogeThin

end
