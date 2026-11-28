import «research.NativeWheelFitProjector»
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.GroupTheory.Index

/-! Exact arithmetic of the native coefficient pairing. The finite pole
module retains each individual denominator exponent. The orthogonality
bound below applies to arbitrary subgroup images, not just diagonal
choices of coordinate basis. No lift norm is assigned from a test ratio. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open RHLean.Analysis.AlpogeThin.WheelFit

namespace RHLean.Analysis.AlpogeThin.PairedIndex

/-- Perfect finite character pairing: a subgroup orthogonal to W injects
into the dual of the actual quotient by W. -/
theorem orthogonal_card_mul_le {G : Type*} [AddCommGroup G] [Finite G]
    (W V : AddSubgroup G) (pair : G → AddChar G ℂ)
    (hinj : Function.Injective pair)
    (horth : ∀ x : V, ∀ y : W, pair x.1 y.1 = 1) :
    Nat.card W * Nat.card V ≤ Nat.card G := by
  classical
  let f (x : V) : AddChar (G ⧸ W) ℂ :=
    AddChar.toAddMonoidHomEquiv.symm
      (QuotientAddGroup.lift W (pair x.1).toAddMonoidHom (by
        intro y hy
        change pair x.1 y = 1
        exact horth x ⟨y, hy⟩))
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply hinj
    ext z
    have e := congrArg (fun χ : AddChar (G ⧸ W) ℂ => χ (z : G ⧸ W)) h
    simpa [f] using e
  letI : Fintype (G ⧸ W) := Fintype.ofFinite _
  have hc : Nat.card (AddChar (G ⧸ W) ℂ) = Nat.card (G ⧸ W) := by
    simp only [Nat.card_eq_fintype_card, AddChar.card_eq]
  have h := (Nat.card_le_card_of_injective f hf).trans_eq hc
  calc
    _ ≤ Nat.card W * Nat.card (G ⧸ W) := Nat.mul_le_mul_left _ h
    _ = Nat.card G := by simpa only [AddSubgroup.index_eq_card] using W.card_mul_index

/-- Nonuniform pole module: coordinate i has its own cyclic modulus,
and its actual unit numerator is retained. -/
def poleChar {ι : Type*} [Fintype ι] (n : ι → ℕ) [∀ i, NeZero (n i)]
    (u : ∀ i, (ZMod (n i))ˣ) (a : ∀ i, ZMod (n i)) :
    AddChar (∀ i, ZMod (n i)) ℂ where
  toFun b := ∏ i, ZMod.stdAddChar ((u i : ZMod (n i)) * a i * b i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' b c := by
    simp only [Pi.add_apply, mul_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

theorem poleChar_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (u : ∀ i, (ZMod (n i))ˣ)
    (a : ∀ i, ZMod (n i)) (i : ι) :
    poleChar n u a (Pi.single i (1 : ZMod (n i))) =
      ZMod.stdAddChar ((u i : ZMod (n i)) * a i) := by
  classical
  change (∏ j, ZMod.stdAddChar ((u j : ZMod (n j)) * a j *
    (Pi.single i (1 : ZMod (n i))) j)) = _
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- The pairing is perfect even when different rows have different pole
orders and unit parts. No rank quota is a premise. -/
theorem poleChar_injective {ι : Type*} [Fintype ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (u : ∀ i, (ZMod (n i))ˣ) :
    Function.Injective (poleChar n u) := by
  classical
  intro a b h
  funext i
  have e := congrArg (fun χ : AddChar (∀ j, ZMod (n j)) ℂ =>
    χ (Pi.single i (1 : ZMod (n i)))) h
  rw [poleChar_single, poleChar_single] at e
  have e' := ZMod.injective_stdAddChar e
  calc
    a i = (↑((u i)⁻¹) : ZMod (n i)) * ((u i : ZMod (n i)) * a i) := by
      simp [← mul_assoc]
    _ = (↑((u i)⁻¹) : ZMod (n i)) * ((u i : ZMod (n i)) * b i) := by rw [e']
    _ = b i := by simp [← mul_assoc]

theorem pole_card_bound {ι : Type*} [Fintype ι] (n : ι → ℕ)
    [∀ i, NeZero (n i)] (u : ∀ i, (ZMod (n i))ˣ)
    (W V : AddSubgroup (∀ i, ZMod (n i)))
    (horth : ∀ x : V, ∀ y : W, poleChar n u x.1 y.1 = 1) :
    Nat.card W * Nat.card V ≤ ∏ i, n i := by
  classical
  have h := orthogonal_card_mul_le W V (poleChar n u) (poleChar_injective n u) horth
  simpa only [Nat.card_pi, Nat.card_zmod] using h

/-- An inclusion of actual subgroup images, with its exact relative
index. This is a finite equality, not an assumed rank estimate. -/
theorem relative_card {G : Type*} [AddCommGroup G] [Finite G]
    (W W₀ : AddSubgroup G) (hW : W ≤ W₀) :
    Nat.card W * W.relIndex W₀ = Nat.card W₀ := by
  let e : W ≃ W.subgroupOf W₀ :=
    { toFun := fun x => ⟨⟨x.1, hW x.2⟩, x.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, AddSubgroup.relIndex]
  exact (W.subgroupOf W₀).card_mul_index

/-- Retained finite images with actual saturated image inclusions.
The rank/complement estimates may be supplied by a basis of the
saturated integral lattice. The result charges both relative indices. -/
theorem paired_saturated_images {G : Type*} [AddCommGroup G] [Finite G]
    (W V W₀ V₀ : AddSubgroup G) (hW : W ≤ W₀) (hV : V ≤ V₀)
    (pair : G → AddChar G ℂ) (hinj : Function.Injective pair)
    (horth : ∀ x : V, ∀ y : W, pair x.1 y.1 = 1) :
    Nat.card W₀ * Nat.card V₀ ≤ Nat.card G * (W.relIndex W₀ * V.relIndex V₀) := by
  calc
    _ = (Nat.card W * Nat.card V) * (W.relIndex W₀ * V.relIndex V₀) := by
      rw [← relative_card W W₀ hW, ← relative_card V V₀ hV]
      ring
    _ ≤ _ := Nat.mul_le_mul_right _ (orthogonal_card_mul_le W V pair hinj horth)

/-- From the genuine finite image sizes and their saturation losses to
the nonuniform logarithmic index inequality. Here a and b are the
logarithmic lower sizes of the saturated images. -/
theorem paired_exponent_bound {p T a b dL dR : ℕ} (hp : 1 < p)
    {G : Type*} [AddCommGroup G] [Finite G]
    (W V : AddSubgroup G) (pair : G → AddChar G ℂ)
    (hinj : Function.Injective pair) (horth : ∀ x : V, ∀ y : W, pair x.1 y.1 = 1)
    (hG : Nat.card G = p^T) (hW : p^a ≤ Nat.card W * p^dL)
    (hV : p^b ≤ Nat.card V * p^dR) :
    a+b ≤ T+dL+dR := by
  apply (Nat.pow_le_pow_iff_right hp).mp
  calc
    p^(a+b) = p^a * p^b := pow_add _ _ _
    _ ≤ (Nat.card W * p^dL) * (Nat.card V * p^dR) := Nat.mul_le_mul hW hV
    _ = (Nat.card W * Nat.card V) * (p^dL * p^dR) := by ring
    _ ≤ p^T * (p^dL * p^dR) := by
      rw [← hG]
      exact Nat.mul_le_mul_right _ (orthogonal_card_mul_le W V pair hinj horth)
    _ = p^(T+dL+dR) := by rw [pow_add, pow_add]; ring

/-- If the full pole length is T and the saturated quotients have the
two stated length ceilings, the loss is the positive part of their
subtraction from T. This is the arithmetic form of the index bound. -/
theorem nonuniform_index_arithmetic {T SL SR dL dR : ℕ}
    (h : (T-SL)+(T-SR) ≤ T+dL+dR) :
    T-SL-SR ≤ dL+dR := by omega

/-- Uniform pole length t, dimensions D,r,s. Missing ranks are charged
on both sides, rather than assigning the same loss twice. -/
theorem uniform_index_arithmetic {D r s t dL dR : ℕ}
    (h : t*r+t*s ≤ t*D+dL+dR) :
    t*(r+s-D) ≤ dL+dR := by
  by_cases hle : r+s ≤ D
  · simp [Nat.sub_eq_zero_of_le hle]
  · have he : t*(r+s-D)+t*D = t*r+t*s := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_of_not_ge hle)), Nat.mul_add]
    omega

/-- Cardinal bound for a saturated finite image using its actual
complement coordinates: a surjection from the complement is sufficient,
and the relative index is measured on the same image. -/
theorem uniform_image_size (p t D r dL : ℕ) [NeZero (p^t)]
    (W W₀ : AddSubgroup (Fin D → ZMod (p^t))) (hW : W ≤ W₀)
    (f : (Fin (D-r) → ZMod (p^t)) → ((Fin D → ZMod (p^t)) ⧸ W₀))
    (hf : Function.Surjective f) (hidx : W.relIndex W₀ ≤ p^dL) :
    p^(t*D) ≤ Nat.card W * p^(dL+t*(D-r)) := by
  have hG : Nat.card (Fin D → ZMod (p^t)) = p^(t*D) := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod, pow_mul]
  have hq : W₀.index ≤ p^(t*(D-r)) := by
    rw [AddSubgroup.index_eq_card]
    refine (Nat.card_le_card_of_surjective f hf).trans_eq ?_
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod, pow_mul]
  calc
    _ = Nat.card W₀ * W₀.index := hG.symm.trans W₀.card_mul_index.symm
    _ = Nat.card W * W.relIndex W₀ * W₀.index := by rw [relative_card W W₀ hW]
    _ ≤ Nat.card W * p^dL * p^(t*(D-r)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hidx) hq
    _ = _ := by rw [pow_add]; ring

/-- The uniform two-lattice index obstruction using the actual finite
pole pairing and explicit surjective complement coordinate maps. -/
theorem uniform_paired_index (p t D r s dL dR : ℕ) [NeZero (p^t)]
    (hp : 1 < p) (hr : r ≤ D) (hs : s ≤ D)
    (u : Fin D → (ZMod (p^t))ˣ)
    (W V W₀ V₀ : AddSubgroup (Fin D → ZMod (p^t)))
    (hW : W ≤ W₀) (hV : V ≤ V₀)
    (f : (Fin (D-r) → ZMod (p^t)) → ((Fin D → ZMod (p^t)) ⧸ W₀))
    (g : (Fin (D-s) → ZMod (p^t)) → ((Fin D → ZMod (p^t)) ⧸ V₀))
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hiL : W.relIndex W₀ ≤ p^dL) (hiR : V.relIndex V₀ ≤ p^dR)
    (horth : ∀ x : V, ∀ y : W, poleChar (fun _ : Fin D => p^t) u x.1 y.1 = 1) :
    t*(r+s-D) ≤ dL+dR := by
  have hG : Nat.card (Fin D → ZMod (p^t)) = p^(t*D) := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod, pow_mul]
  have h := paired_exponent_bound hp W V
    (poleChar (fun _ : Fin D => p^t) u)
    (poleChar_injective (fun _ : Fin D => p^t) u) horth hG
    (uniform_image_size p t D r dL W W₀ hW f hf hiL)
    (uniform_image_size p t D s dR V V₀ hV g hg hiR)
  have er : t*(D-r)+t*r = t*D := by rw [← Nat.mul_add, Nat.sub_add_cancel hr]
  have es : t*(D-s)+t*s = t*D := by rw [← Nat.mul_add, Nat.sub_add_cancel hs]
  apply uniform_index_arithmetic
  omega

/-- On a common retained image, both tests charge the same actual
relative index. No primitive near-full-rank image can ignore a pole. -/
theorem uniform_common_index (p t D r d : ℕ) [NeZero (p^t)]
    (hp : 1 < p) (hr : r ≤ D) (u : Fin D → (ZMod (p^t))ˣ)
    (W W₀ : AddSubgroup (Fin D → ZMod (p^t))) (hW : W ≤ W₀)
    (f : (Fin (D-r) → ZMod (p^t)) → ((Fin D → ZMod (p^t)) ⧸ W₀))
    (hf : Function.Surjective f) (hi : W.relIndex W₀ ≤ p^d)
    (horth : ∀ x : W, ∀ y : W, poleChar (fun _ : Fin D => p^t) u x.1 y.1 = 1) :
    t*(r+r-D) ≤ d+d :=
  uniform_paired_index p t D r r d d hp hr hr u W W W₀ W₀ hW hW f f hf hf hi hi horth

/-- An actual coordinate clearing, applied to the right coefficients
only on the overlapping left directions. -/
def rightClearing {ι : Type*} [DecidableEq ι] (W : Finset ι) (p t : ℕ)
    (i : ι) : ℤ := if i ∈ W then (p:ℤ)^t else 1

theorem paired_coordinate_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Finset ι) (p t : ℕ) (u x y : ι → ℤ)
    (hx : ∀ i, i ∉ W → x i = 0) :
    (p:ℤ)^t ∣ ∑ i, u i * x i * (rightClearing W p t i * y i) := by
  apply Finset.dvd_sum
  intro i _
  by_cases hi : i ∈ W
  · refine ⟨u i * x i * y i, ?_⟩
    simp only [rightClearing, if_pos hi]
    ring
  · simp [hx i hi]

theorem paired_coordinate_price {ι : Type*} [DecidableEq ι]
    (W V : Finset ι) (t : ℕ) :
    (∑ i ∈ V, if i ∈ W then t else 0) = t * (W ∩ V).card := by
  classical
  rw [← Finset.sum_filter]
  have he : V.filter (fun i => i ∈ W) = W ∩ V := by
    ext i
    simp [and_comm]
  rw [he, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem first_last_overlap (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D) :
    ((Finset.range r) ∩ Finset.Ico (D-s) D).card = r+s-D := by
  have he : Finset.range r ∩ Finset.Ico (D-s) D = Finset.Ico (D-s) r := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he, Nat.card_Ico]
  omega

/-- Ratios of two actual nonzero tested entries have the norm of the
ratio of the corresponding rational prices. -/
theorem ratio_place_norm (p : ℕ) [Fact p.Prime] (ι : ℂ →+* PadicAlgCl p)
    (z z' : ℂ) (Q Q' : ℚ)
    (h : ‖ι z‖ = (padicNorm p Q:ℝ)) (h' : ‖ι z'‖ = (padicNorm p Q':ℝ)) :
    ‖ι (z/z')‖ = (padicNorm p (Q/Q'):ℝ) := by
  calc
    _ = ‖ι z‖ / ‖ι z'‖ := by rw [map_div₀, norm_div]
    _ = ‖ι (Q:ℂ)‖ / ‖ι (Q':ℂ)‖ := by rw [h, h', place_rat, place_rat]
    _ = ‖ι ((Q/Q':ℚ):ℂ)‖ := by rw [Rat.cast_div, map_div₀, norm_div]
    _ = _ := place_rat p ι _

/-- Direct specialization to two native measured wheel rows, keeping both
character channels, both class factors, and their distinct nominal orders. -/
theorem native_test_ratio (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ)
    (w w' : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    {S : Type*} (α α' : S →₀ ℕ) (r r' : ℚ) (hr : 0 < r) (hr' : 0 < r')
    (h h' : ℕ) (χ ψ χ' ψ' : AddChar ((alpogeNativeHostData e q d).inertia p) ℂ)
    (hn : tested α r h (readAt e q d N P w p χ) (readAt e q d N P w p ψ) ≠ 0)
    (hn' : tested α' r' h' (readAt e q d N P w' p χ') (readAt e q d N P w' p ψ') ≠ 0) :
    ‖ι (tested α r h (readAt e q d N P w p χ) (readAt e q d N P w p ψ) /
      tested α' r' h' (readAt e q d N P w' p χ') (readAt e q d N P w' p ψ'))‖ =
      (padicNorm p (payment α r h (wheel e q d N P w) /
        payment α' r' h' (wheel e q d N P w')):ℝ) := by
  exact ratio_place_norm p ι _ _ _ _
    (nonzero_projector_price e q d N p hH ι P w α r hr h χ ψ hn)
    (nonzero_projector_price e q d N p hH ι P w' α' r' hr' h' χ' ψ' hn')

/-- Recenter any auxiliary height witness, not just rational ones.
The equality of all local bounds is literal and leaves the same finite
allowances for the constant family. -/
theorem recenter_finite (p : ℕ) [Fact p.Prime] (ι : ℂ →+* PadicAlgCl p)
    (H z : ℂ) (R : ℚ) (h : ‖ι z‖ = (padicNorm p R:ℝ)) :
    ‖ι (H*z)‖ = ‖ι (H*(R:ℂ))‖ := by
  rw [map_mul, map_mul, norm_mul, norm_mul, h, place_rat]

theorem recenter_arch (σ : ℂ ≃+* ℂ) (H : ℂ) (R : ℚ) :
    ‖σ (H*(R:ℂ))‖ = ‖σ H‖ * |(R:ℝ)| := by
  rw [map_mul, map_ratCast, norm_mul, ← Complex.ofReal_ratCast, Complex.norm_real]

/-- The explicit reciprocal rational witness kills the finite factor
at every place, independently of the character or auxiliary embedding. -/
theorem reciprocal_witness (p : ℕ) [Fact p.Prime] (ι : ℂ →+* PadicAlgCl p)
    (z : ℂ) (R : ℚ) (hR : R ≠ 0) (h : ‖ι z‖ = (padicNorm p R:ℝ)) :
    ‖ι (((R⁻¹:ℚ):ℂ)*z)‖ = 1 := by
  rw [recenter_finite p ι _ _ R h]
  have hRc : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  rw [Rat.cast_inv, inv_mul_cancel₀ hRc, map_one, norm_one]

end RHLean.Analysis.AlpogeThin.PairedIndex
