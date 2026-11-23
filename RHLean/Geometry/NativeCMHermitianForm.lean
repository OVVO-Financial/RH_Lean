import RHLean.Geometry.NativeCMQuadraticOrder
import RHLean.Geometry.NativePolarizationCoefficientLattice

/-!
# The unique perfect CM Hermitian form on the original trace lattice

The formula is constructed from the actual alternating integer `EF` and
native half-root. Its quadratic-order linearity, conjugate adjointness,
perfection and finite dual frame are proved. The form need not be positive
for a mixed signature: positivity is a separate pure-block statement needed
by the polarized Serre scheme construction. No CM-degree estimate follows
from this algebraic form alone.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsUniqueCmHermitianLatticeForm.lean`. The complete proofs are rebuilt
against the native host and datum; no source compiled object is imported.
The source mirror states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open NumberField

namespace RHLean.Geometry.NativeCM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- The algebraic part of a polarized lattice needed by the Serre tensor
construction. No complex domain or positivity is claimed by this record. -/
structure TraceLattice (H : NativeGeometricHost E) where
  La : Type
  [acg : AddCommGroup La]
  [mod : Module (𝓞 E) La]
  fin : Module.Finite (𝓞 E) La
  proj : Module.Projective (𝓞 E) La
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  unimod : Function.Bijective EF
  adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)

attribute [instance] TraceLattice.acg TraceLattice.mod

/-- Restriction retains the actual module and exact trace form. -/
def traceLatticeOfDatum {H : NativeGeometricHost E} (D : NativeGeometricDatum H) :
    TraceLattice H where
  La := D.La
  fin := D.fin
  proj := D.proj
  EF := D.EF
  alt := D.alt
  unimod := D.unimod
  adj := D.adj

/-- The precise defining equation consumed by the source tensor bundle. -/
def IsKForm {H : NativeGeometricHost E} (D : TraceLattice H)
    (ε : ℤˣ) (h : D.La → D.La → OK H) : Prop :=
  ∀ x y, ((h x y : OK H) : 𝓞 E) =
    (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : 𝓞 E) +
      (((ε : ℤ) * D.EF x y : ℤ) : 𝓞 E) * H.w0

def kFun {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) (x y : D.La) : OK H :=
  (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H

theorem kFun_coe {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) (x y : D.La) : ((kFun D ε x y : OK H) : 𝓞 E) =
    (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : 𝓞 E) + (((ε : ℤ) * D.EF x y : ℤ) : 𝓞 E) * H.w0 := by
  simp only [kFun, wK, Subalgebra.coe_add, Subalgebra.coe_mul, SubringClass.coe_intCast]

theorem kform_w0_sq (H : NativeGeometricHost E) : H.w0 * H.w0 = H.w0 - (((1 + H.d) / 4 : ℕ) : 𝓞 E) := by
  have h := congrArg (fun a : OK H => (a : 𝓞 E)) (OK_isDedekindDomain_and_projective E H).2.2.2.1
  simp only [wK, Subalgebra.coe_add, SubmonoidClass.coe_pow, SubringClass.coe_natCast] at h
  linear_combination h


theorem kform_skew {H : NativeGeometricHost E} (D : TraceLattice H) (x y : D.La) : D.EF y x = - D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt] at h
  linarith

theorem kFun_add_left {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) (x x' y : D.La) :
    kFun D ε (x + x') y = kFun D ε x y + kFun D ε x' y := by
  simp only [kFun, smul_add, map_add, LinearMap.add_apply]
  push_cast; ring

theorem kFun_add_right {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) (x y y' : D.La) :
    kFun D ε x (y + y') = kFun D ε x y + kFun D ε x y' := by
  simp only [kFun, map_add]
  push_cast; ring

theorem kFun_zsmul {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) (m : ℤ) (x y : D.La) :
    kFun D ε (m • x) y = (m : OK H) * kFun D ε x y := by
  simp only [kFun, smul_comm H.w0 m x, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  push_cast; ring

theorem kFun_w0 {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) (x y : D.La) :
    kFun D ε (H.w0 • x) y = wK H * kFun D ε x y := by
  apply Subtype.ext
  have hw : H.w0 • H.w0 • x = H.w0 • x - (((1 + H.d) / 4 : ℕ) : ℤ) • x := by
    rw [smul_smul, kform_w0_sq, sub_smul, Nat.cast_smul_eq_nsmul, natCast_zsmul]
  have h2 := kform_w0_sq H
  rw [Subalgebra.coe_mul, kFun_coe, kFun_coe, hw]
  simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, wK]
  generalize ((1 + H.d) / 4 : ℕ) = N at *
  push_cast
  linear_combination (-((ε : ℤ) : 𝓞 E) * (D.EF x y : 𝓞 E)) * h2

theorem kFun_smul {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) (a : OK H) (x y : D.La) :
    kFun D ε (a • x) y = a * kFun D ε x y := by
  obtain ⟨⟨m, n⟩, rfl, -⟩ := (OK_isDedekindDomain_and_projective E H).2.1 a
  have : ((m : OK H) + (n : OK H) * wK H) • x = m • x + n • H.w0 • x := by
    rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; rfl
  simp only
  rw [this, kFun_add_left, kFun_zsmul, kFun_zsmul, kFun_w0]; ring

def kLin {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) : D.La →ₗ[OK H] D.La →+ OK H where
  toFun x := AddMonoidHom.mk' (kFun D ε x) (kFun_add_right D ε x)
  map_add' x x' := by ext1 y; exact kFun_add_left D ε x x' y
  map_smul' a x := by ext1 y; exact kFun_smul D ε a x y

theorem kLin_apply {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) (x y : D.La) : kLin D ε x y = kFun D ε x y := rfl

theorem kform_coeff_unique (H : NativeGeometricHost E) {a b c d : ℤ}
    (h : (a : OK H) + (b : OK H) * wK H = (c : OK H) + (d : OK H) * wK H) : a = c ∧ b = d := by
  have := ((OK_isDedekindDomain_and_projective E H).2.1 ((a : OK H) + (b : OK H) * wK H)).unique (y₁ := (a, b)) (y₂ := (c, d)) rfl h
  exact Prod.mk.inj this

theorem kLin_perfect {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) (f : D.La →ₗ[OK H] OK H) :
    ∃! y, ∀ x, f x = kLin D ε x y := by
  have hε : (ε : ℤ) * ε = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  choose c hc using fun a => ((OK_isDedekindDomain_and_projective E H).2.1 a).exists
  let b : D.La →+ ℤ := AddMonoidHom.mk' (fun x => -(ε : ℤ) * (c (f x)).2) (by
    intro x x'
    have : (((c (f (x + x'))).1 : ℤ) : OK H) + ((c (f (x + x'))).2 : OK H) * wK H =
        (((c (f x)).1 + (c (f x')).1 : ℤ) : OK H) + (((c (f x)).2 + (c (f x')).2 : ℤ) : OK H) * wK H := by
      rw [← hc, map_add]
      have h1 := hc (f x)
      have h2 := hc (f x')
      push_cast
      linear_combination h1 + h2
    rw [(kform_coeff_unique H this).2]; ring)
  obtain ⟨y, hy⟩ := D.unimod.2 b.toIntLinearMap
  have hb : ∀ x, (ε : ℤ) * D.EF x y = (c (f x)).2 := by
    intro x
    rw [kform_skew, hy]
    change (ε : ℤ) * -(-(ε : ℤ) * (c (f x)).2) = _
    linear_combination (c (f x)).2 * hε
  have hint : ∀ x, ∃ m : ℤ, f x - kFun D ε x y = m := by
    intro x
    refine ⟨(c (f x)).1 - (ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y), ?_⟩
    have h1 := hc (f x)
    rw [kFun, hb]
    push_cast
    linear_combination h1
  refine ⟨y, fun x => ?_, fun y' hy' => ?_⟩
  · obtain ⟨m, hm⟩ := hint x
    obtain ⟨m', hm'⟩ := hint (wK H • x)
    rw [map_smul, kFun_smul, smul_eq_mul, ← mul_sub, hm] at hm'
    have : ((0 : ℤ) : OK H) + (m : OK H) * wK H = (m' : OK H) + ((0 : ℤ) : OK H) * wK H := by
      push_cast; linear_combination hm'
    rw [(kform_coeff_unique H this).2] at hm
    rw [kLin_apply, ← sub_eq_zero, hm, Int.cast_zero]
  · apply D.unimod.1
    ext x
    have h1 := (hc (f x)).symm.trans (hy' x)
    have h2 := (kform_coeff_unique H h1).2
    rw [kform_skew D x y', kform_skew D x y]
    have h3 := hb x
    linear_combination (ε : ℤ) * (h2 + h3) + (D.EF x y' - D.EF x y) * hε

theorem exists_kForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : NativeGeometricHost E) (D : TraceLattice H) (ε : ℤˣ), ∃ h : D.La →ₗ[OK H] D.La →+ OK H, IsKForm D ε (fun x y => h x y) ∧ (∀ h' : D.La → D.La → OK H, IsKForm D ε h' → h' = fun x y => h x y) ∧ (∀ x y, ((h y x : OK H) : 𝓞 E) = H.bar (h x y : OK H)) ∧ (∀ (s : 𝓞 E) x y, h (s • x) y = h x (H.bar s • y)) ∧ (∀ x, ((h x x : OK H) : 𝓞 E) = (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E)) ∧ (∀ f : D.La →ₗ[OK H] OK H, ∃! y, ∀ x, f x = h x y) ∧ ∃ (n : ℕ) (x y : Fin n → D.La), ∀ a, a = ∑ i, h a (y i) • x i := by
  intro E _ _ _ H D ε
  refine ⟨kLin D ε, kFun_coe D ε, fun h' hh => ?_, fun x y => ?_, fun s x y => ?_, fun x => ?_,
    kLin_perfect D ε, ?_⟩
  · funext x y
    exact Subtype.ext ((hh x y).trans (kFun_coe D ε x y).symm)
  · have h1 : D.EF (H.w0 • y) x = D.EF (H.w0 • x) y - D.EF x y := by
      rw [D.adj, bar_w0, sub_smul, one_smul, map_sub, kform_skew D x y, kform_skew D (H.w0 • x) y]
      ring
    rw [kLin_apply, kLin_apply, kFun_coe, kFun_coe, h1, kform_skew D x y, map_add, map_mul, map_intCast,
      map_intCast, bar_w0]
    push_cast; ring
  · rw [kLin_apply, kLin_apply, kFun, kFun, smul_comm H.w0 s x, D.adj, D.adj s]
  · rw [kLin_apply, kFun_coe, D.alt]
    push_cast; ring
  · obtain ⟨h1, h2, -⟩ := (OK_isDedekindDomain_and_projective E H).2.2.2.2.2 D.La D.fin D.proj
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (OK H) D.La
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    choose y hy using fun i : Fin n => (kLin_perfect D ε ((LinearMap.proj i).comp s)).exists
    refine ⟨n, fun i => π (Pi.single i 1), y, fun a => ?_⟩
    have ha : π (s a) = a := LinearMap.congr_fun hs a
    conv_lhs => rw [← ha, ← Finset.univ_sum_single (s a), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hy, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rfl

/-- The unique form is the explicit `kLin`, so its finite dual frame is
constructed on the original module without choosing a free coefficient basis. -/
theorem kLin_dual_frame {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ) :
    ∃ (n : ℕ) (x y : Fin n → D.La),
      ∀ a, a = ∑ i, kLin D ε a (y i) • x i := by
  obtain ⟨h, hK, -, -, -, -, -, hf⟩ := exists_kForm E H D ε
  have heq : h = kLin D ε := by
    ext x y
    exact Subtype.ext ((hK x y).trans (kFun_coe D ε x y).symm)
  subst h
  exact hf

/-- The diagonal coefficient is exactly the original trace-polarization
value. In particular a mixed signature is not silently declared positive. -/
theorem kLin_diagonal {H : NativeGeometricHost E} (D : TraceLattice H)
    (ε : ℤˣ) (x : D.La) :
    ((kLin D ε x x : OK H) : 𝓞 E) =
      (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E) := by
  rw [kLin_apply, kFun_coe, D.alt]
  push_cast
  ring


end RHLean.Geometry.NativeCM
end

noncomputable section

open NumberField
open scoped Pointwise nonZeroDivisors

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]

/-- The actual inverse half-different with its already proved integral trace
polarization. Every field is supplied; neither a Hermitian form nor a
projective presentation is an input. -/
def coefficientTraceLattice (G : NativeGeometricHost H.E)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    TraceLattice G where
  La := coefficientIdeal H B
  fin := coefficientIdeal_finite_over_integers H B
  proj := coefficientIdeal_projective H B
  EF := integralTraceForm H B hB
  alt := integralTraceForm_alternating H B hB
  unimod := integralTraceForm_bijective H B hB
  adj := by
    intro a x y
    rw [hbar]
    exact integralTraceForm_adjoint H B hB a x y

/-- The new quadratic-order form still has the SAME literal arithmetic
trace on its imaginary coefficient. -/
theorem coefficient_kFun_formula (G : NativeGeometricHost H.E)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (ε : ℤˣ) (x y : coefficientIdeal H B) :
    ((kLin (coefficientTraceLattice H G hbar B hB) ε x y : OK G) : 𝓞 H.E) =
      (((ε : ℤ) * (integralTraceForm H B hB (G.w0 • x) y -
        integralTraceForm H B hB x y) : ℤ) : 𝓞 H.E) +
      (((ε : ℤ) * integralTraceForm H B hB x y : ℤ) : 𝓞 H.E) * G.w0 :=
  kFun_coe (coefficientTraceLattice H G hbar B hB) ε x y

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization
end
