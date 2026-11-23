import RHLean.Geometry.NativeThetaCuspNativeFlagPeriods

/-!
# Holomorphic variation of the actual native flag periods

The period map is defined by the explicit source formula on the full
frame space. On the actual open signed flag domain it gives the same
complete IsPeriod constructed previously and varies holomorphically for
every element of the original projective lattice. Cramer's rule supplies
the inverse-frame coordinates; no holomorphic-family premise is assumed.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean
(`differentiable_det`, `inv_mulVec_apply`, the holomorphic clause of `per_move`),
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFramePeriods.lean
(the explicit additive family), and
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientDomain.lean
(`cont_gram`, `isOpen_dom`). The source mirror states no license;
attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open NumberField Matrix
open scoped Classical Pointwise ComplexConjugate

namespace RHLean.Geometry.NativeTheta.Cusp.FlagHolomorphic

open NativeGeometricPeriods

lemma differentiable_det {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}
    (M : X → Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ a b, Differentiable ℂ fun x => M x a b) :
    Differentiable ℂ fun x => (M x).det := by
  simp only [Matrix.det_apply]
  fun_prop

lemma inv_mulVec_apply {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ)
    (w : Fin r → ℂ) (a : Fin r) :
    (A⁻¹ *ᵥ w) a = (A.det)⁻¹ * (A.updateCol a w).det := by
  rw [Matrix.inv_def, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    Ring.inverse_eq_inv', ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]

section Frame

variable {E : Type} [Field E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}

lemma differentiable_hermC_col_mat (G : Matrix (Fin r) (Fin r) E)
    (σ : Ψ) (a : Fin r) (w : Fin r → ℂ) :
    Differentiable ℂ fun x : FlagDomain.Frame Ψ r =>
      FlagDomain.hermC σ.1 G (FlagDomain.col (FlagDomain.mat x σ) a) w := by
  unfold FlagDomain.hermC FlagDomain.col FlagDomain.mat
  simp only [Matrix.of_apply]
  fun_prop

lemma differentiableOn_mat_inv_mulVec_apply (s : Set (FlagDomain.Frame Ψ r))
    (hs : ∀ x ∈ s, ∀ σ, (FlagDomain.mat x σ).det ≠ 0)
    (σ : Ψ) (a : Fin r) (w : Fin r → ℂ) :
    DifferentiableOn ℂ
      (fun x : FlagDomain.Frame Ψ r => ((FlagDomain.mat x σ)⁻¹ *ᵥ w) a) s := by
  simp only [inv_mulVec_apply]
  refine DifferentiableOn.mul ?_ ?_
  · refine DifferentiableOn.inv ?_ fun x hx => hs x hx σ
    refine (differentiable_det _ fun i j => ?_).differentiableOn
    unfold FlagDomain.mat
    simp only [Matrix.of_apply]
    fun_prop
  · refine (differentiable_det _ fun i j => ?_).differentiableOn
    unfold FlagDomain.mat
    simp only [Matrix.updateCol_apply, Matrix.of_apply]
    split_ifs <;> fun_prop

lemma continuous_gram (G : Matrix (Fin r) (Fin r) E) (τ : Ψ) :
    Continuous fun x : FlagDomain.Frame Ψ r => FlagDomain.gram τ.1 G (FlagDomain.mat x τ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [FlagDomain.gram, FlagDomain.hermC, FlagDomain.col, FlagDomain.mat, Matrix.of_apply]
  fun_prop

/-- The source signed domain is open in the actual finite complex frame space. -/
theorem isOpen_domain (G : Matrix (Fin r) (Fin r) E) (q : ℕ) :
    IsOpen (FlagDomain.GG Ψ G q) := by
  have h : FlagDomain.GG Ψ G q = ⋂ τ : Ψ,
      ({x : FlagDomain.Frame Ψ r | (FlagDomain.mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < FlagDomain.psgn q i * (FlagDomain.dmin G x τ i).re}) := by
    ext x
    simp [FlagDomain.GG]
  rw [h]
  refine isOpen_iInter_of_finite fun τ =>
    IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun
      (show Continuous fun x : FlagDomain.Frame Ψ r => FlagDomain.mat x τ from
        continuous_apply τ).matrix_det continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp
      ((continuous_gram G τ).matrix_submatrix _ _).matrix_det))

end Frame

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization

variable {φ : Frame} (H : HostRaw φ)

/-- The explicit additive period family, defined before restricting to
invertible signed frames. It retains the literal inverse-ideal lattice. -/
def periodMap (B : Ideal (𝓞 H.E)) (N q : ℕ)
    (x : FlagDomain.Frame (cmTypeFinset H) N) :
    twistedLattice H B N →+ (Fin ((cmTypeFinset H).card * N) → ℂ) :=
  (FlagFramePeriod.allPer (NativeFlag.matrix H N q) q x
    (NativeFlagPeriods.index H N)).toAddMonoidHom.comp
      { toFun := fun v (τ : cmTypeFinset H) a => τ.1 (v.1 a)
        map_zero' := by
          funext τ a
          exact map_zero τ.1
        map_add' := fun v w => by
          funext τ a
          exact map_add τ.1 (v.1 a) (w.1 a) }

theorem periodMap_apply (B : Ideal (𝓞 H.E)) (N q : ℕ)
    (x : FlagDomain.Frame (cmTypeFinset H) N) (v : twistedLattice H B N)
    (i : Fin ((cmTypeFinset H).card * N)) :
    periodMap H B N q x v i =
      if ((NativeFlagPeriods.index H N i).2 : ℕ) < q then
        FlagDomain.hermC (NativeFlagPeriods.index H N i).1.1 (NativeFlag.matrix H N q)
          (FlagDomain.col (FlagDomain.mat x (NativeFlagPeriods.index H N i).1)
            (NativeFlagPeriods.index H N i).2)
          (FlagDomain.Data.emb (NativeFlagPeriods.index H N i).1.1 v.1)
      else ((FlagDomain.mat x (NativeFlagPeriods.index H N i).1)⁻¹ *ᵥ
        FlagDomain.Data.emb (NativeFlagPeriods.index H N i).1.1 v.1)
          (NativeFlagPeriods.index H N i).2 := rfl

/-- Every literal lattice period varies holomorphically over the signed domain. -/
theorem periodMap_holomorphic (B : Ideal (𝓞 H.E)) (N q : ℕ)
    (v : twistedLattice H B N) :
    DifferentiableOn ℂ (fun x => periodMap H B N q x v)
      (FlagDomain.GG (cmTypeFinset H) (NativeFlag.matrix H N q) q) := by
  rw [differentiableOn_pi]
  intro i
  simp only [periodMap_apply]
  split_ifs
  · exact (differentiable_hermC_col_mat (NativeFlag.matrix H N q) _ _ _).differentiableOn
  · exact differentiableOn_mat_inv_mulVec_apply _ (fun x hx τ => (hx τ).1) _ _ _

/-- The canonical native family has the complete period and holomorphy
properties on an actual nonempty open signed domain. Algebraic moduli
realization is not part of this assertion. -/
theorem native_holomorphic_period_family
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostRaw e q d he hH
    let _ : IsCMField H.E := nativeDyadicHostRaw_cm e q d he hH
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    let U := FlagDomain.GG (cmTypeFinset H)
      (NativeFlag.matrix H (k + m - 1) (m - j)) (m - j)
    IsOpen U ∧ U.Nonempty ∧
      IsTypeFn G (k + j - 1) (m - j)
        (NativeFlagPeriods.periodType H (k + m - 1) (m - j)) ∧
      (∀ x ∈ U, IsPeriod D
        (NativeFlagPeriods.periodType H (k + m - 1) (m - j))
        (periodMap H B (k + m - 1) (m - j) x)) ∧
      ∀ v : prescribedLattice H B k m,
        DifferentiableOn ℂ (fun x => periodMap H B (k + m - 1) (m - j) x v) U := by
  let H := nativeDyadicHostRaw e q d he hH
  let _ : IsCMField H.E := nativeDyadicHostRaw_cm e q d he hH
  obtain ⟨ht, hp⟩ := NativeFlagPeriods.native_frame_periods e q d he hH B hB k m j hk hj
  refine ⟨isOpen_domain _ _, NativeFlagPeriods.domain_nonempty H _ _ (by omega),
    ht, ?_, fun v => periodMap_holomorphic H B _ _ v⟩
  intro x hx
  obtain ⟨P, hP, hper⟩ := hp x hx
  have hEq : P = periodMap H B (k + m - 1) (m - j) x := by
    ext v i
    exact hP v i
  rwa [hEq] at hper

end RHLean.Geometry.NativeTheta.Cusp.FlagHolomorphic
