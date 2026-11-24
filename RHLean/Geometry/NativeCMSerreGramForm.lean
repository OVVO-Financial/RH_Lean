import RHLean.Geometry.NativeCMSerrePolarization

/-!
# The exact Gram expansion on the original projective trace module

The finite Hermitian dual frame reconstructs the original pairing. The
quadratic expression used by the explicit tensor line bundle polarizes to
that Gram pairing because the actual quadratic-order generator satisfies
w + conjugate(w) = 1. No free basis or prescribed metric replaces the
original module.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsTensorBundle.lean`, the algebraic Gram-form declarations. The final
specialization is native glue to the actual trace form and dual frame.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical BigOperators

namespace RHLean.Geometry.NativeCM.SerreGram

variable {O V W U I : Type} [CommRing O] [AddCommGroup V] [Module O V]
    [AddCommGroup W] [Module O W] [AddCommGroup U] [Fintype I]

def gramForm (β : V →+ V →+ U) (p : I → W →ₗ[O] V)
    (g : I → I → O) (x y : W) : U :=
  ∑ k : I × I, β (g k.1 k.2 • p k.1 x) (p k.2 y)

variable {β : V →+ V →+ U} {p : I → W →ₗ[O] V}
    {g : I → I → O} {br : O ≃+* O}

theorem gramForm_add_left (x y z : W) :
    gramForm β p g (x + y) z = gramForm β p g x z + gramForm β p g y z := by
  simp only [gramForm, map_add, smul_add, AddMonoidHom.add_apply, Finset.sum_add_distrib]

theorem gramForm_add_right (x y z : W) :
    gramForm β p g x (y + z) = gramForm β p g x y + gramForm β p g x z := by
  simp only [gramForm, map_add, Finset.sum_add_distrib]

theorem gramForm_zero (y : W) : gramForm β p g 0 y = 0 := by
  simp [gramForm]

theorem gramForm_adj (ha : ∀ c x y, β (c • x) y = β x (br c • y)) (c : O) (x y : W) :
    gramForm β p g (c • x) y = gramForm β p g x (br c • y) := by
  simp only [gramForm, map_smul]
  exact Finset.sum_congr rfl fun _ _ => by rw [smul_comm, ha]

theorem gramForm_comm (hs : ∀ x y, β x y = β y x)
    (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hg : ∀ i j, g j i = br (g i j)) (x y : W) :
    gramForm β p g x y = gramForm β p g y x :=
  Fintype.sum_equiv (Equiv.prodComm I I) _ _ fun _ => by
    rw [ha, hs, ← hg]
    rfl

/-- The half-root identity supplies the exact factor one in polarization. -/
theorem gramForm_polar (hs : ∀ x y, β x y = β y x)
    (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hg : ∀ i j, g j i = br (g i j)) {w : O} (hw : w + br w = 1) (x y : W) :
    gramForm β p g (x + y) (w • (x + y)) - gramForm β p g x (w • x) -
        gramForm β p g y (w • y) + gramForm β p g 0 (w • 0) = gramForm β p g x y := by
  have e : gramForm β p g x y =
      gramForm β p g x (w • y) + gramForm β p g y (w • x) := by
    rw [gramForm_comm hs ha hg y, gramForm_adj ha, ← gramForm_add_right,
      ← add_smul, hw, one_smul]
  rw [e, gramForm_zero, smul_add, gramForm_add_left, gramForm_add_right, gramForm_add_right]
  abel

theorem gramForm_pure (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hb : ∀ c, br (br c) = c) {x y : W} {u v : V} {s s' : I → O}
    (hx : ∀ i, p i x = s i • u) (hy : ∀ i, p i y = s' i • v) :
    gramForm β p g x y =
      β ((∑ k : I × I, br (s' k.2) * (g k.1 k.2 * s k.1)) • u) v := by
  rw [Finset.sum_smul, map_sum, AddMonoidHom.finsetSum_apply]
  exact Finset.sum_congr rfl fun _ _ => by
    rw [hx, hy, mul_smul (br _), ha (br _), hb, mul_smul]

theorem hermitian_expand {M : Type} [AddCommGroup M] [Module O M]
    (h : M →ₗ[O] M →+ O) (hh : ∀ x y, h y x = br (h x y))
    (e : I → M) (s s' : I → O) :
    ∑ k : I × I, br (s' k.2) * (h (e k.1) (e k.2) * s k.1) =
      h (∑ i, s i • e i) (∑ i, s' i • e i) := by
  have sm : ∀ c x y, h x (c • y) = br c * h x y := fun c x y => by
    rw [hh (c • y) x, map_smul, AddMonoidHom.smul_apply, smul_eq_mul, map_mul, ← hh]
  rw [map_sum h, AddMonoidHom.finsetSum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sm, map_smul, AddMonoidHom.smul_apply, smul_eq_mul, mul_comm (s i)]

end RHLean.Geometry.NativeCM.SerreGram

namespace RHLean.Geometry.NativeCM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ)

theorem kLin_barOK (x y : D.La) : kLin D ε y x = barOK H (kLin D ε x y) := by
  obtain ⟨h, hK, -, hc, -⟩ := exists_kForm E H D ε
  have heq : h = kLin D ε := by
    apply LinearMap.ext
    intro a
    apply AddMonoidHom.ext
    intro b
    exact Subtype.ext ((hK a b).trans (kFun_coe D ε a b).symm)
  subst h
  exact Subtype.ext (hc x y)

theorem wK_add_barOK : wK H + barOK H (wK H) = 1 := by
  apply Subtype.ext
  change H.w0 + H.bar H.w0 = 1
  rw [bar_w0]
  ring

theorem barOK_apply_apply (c : OK H) : barOK H (barOK H c) = c :=
  Subtype.ext (bar_bar H c)

namespace TraceFrame

variable {D ε} (F : TraceFrame D ε)

/-- The original Hermitian form, reconstructed by its own integral dual frame. -/
theorem gram_eq_kLin (m m' : D.La) :
    (∑ k : Fin F.n × Fin F.n,
      barOK H (F.incl m' k.2) * (kLin D ε (F.x k.1) (F.x k.2) * F.incl m k.1)) =
        kLin D ε m m' := by
  rw [SerreGram.hermitian_expand (kLin D ε) (kLin_barOK D ε) F.x]
  rw [show (∑ i, F.incl m i • F.x i) = m from (F.resolve m).symm,
    show (∑ i, F.incl m' i • F.x i) = m' from (F.resolve m').symm]

/-- The pure-tensor value retains exactly the original integral trace form. -/
theorem gram_pure {V U W : Type} [AddCommGroup V] [Module (OK H) V]
    [AddCommGroup U] [AddCommGroup W] [Module (OK H) W]
    (β : V →+ V →+ U)
    (hβ : ∀ c x y, β (c • x) y = β x (barOK H c • y))
    (p : Fin F.n → W →ₗ[OK H] V) {x y : W} {u v : V} (m m' : D.La)
    (hx : ∀ i, p i x = F.incl m i • u)
    (hy : ∀ i, p i y = F.incl m' i • v) :
    SerreGram.gramForm β p (fun i j => kLin D ε (F.x i) (F.x j)) x y =
      β (kLin D ε m m' • u) v := by
  rw [SerreGram.gramForm_pure hβ (barOK_apply_apply (H := H)) hx hy, F.gram_eq_kLin]

end TraceFrame

end RHLean.Geometry.NativeCM

end
