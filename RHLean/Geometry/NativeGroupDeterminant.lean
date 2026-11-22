import RHLean.Geometry.NativeRegularSectionSelection

/-!
# A regular group determinant from independent orbit evaluations

The finite regular-seed constructor from
`GlobalTheory.GenericGroupDet.exists_vec_det_ne_zero` is reproduced here with
only native/Mathlib imports. Independent component evaluations first construct
an identity delta function over the complex scalar extension. The product of
the resulting nonzero determinant polynomials then has a point over the
original characteristic-zero field. No regular-seed hypothesis is assumed.

Upstream source:
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsVectorGroupDeterminantsNeZero.lean`,
commit `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The geometric orbit-separation theorem is the supplier of the explicit finite
linear-independence data; the present theorem proves their finite consequence.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators

namespace RHLean.Geometry.NativeGroupDeterminant

theorem det_delta_ne_zero (S : Type) [Group S] [Fintype S] [DecidableEq S] (f : S → ℂ)
    (hf : ∀ h, f h = if h = 1 then 1 else 0) :
    (Matrix.of fun h g : S => f (h * g)).det ≠ 0 := by
  have : (Matrix.of fun h g : S => f (h * g)) = (Equiv.inv S).permMatrix ℂ := by
    ext h g
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hf, mul_eq_one_iff_inv_eq]
  rw [this, Matrix.det_permutation]
  simp

theorem exists_combination_delta (F V S J : Type) [Field F] [Algebra F ℂ] [AddCommGroup V] [Module F V]
    [Group S] [Fintype S] [DecidableEq S] [Fintype J]
    (ev : V →ₗ[F] (S → ℂ)) (r : J → S) (W : Submodule F V) (h1 : ∃ j, r j = 1)
    (h2 : ∀ v ∈ W, ∀ h, h ∉ Set.range r → ev v h = 0)
    (h3 : ∀ a : J → ℂ, (∀ v ∈ W, ∑ j, a j * ev v (r j) = 0) → a = 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → V), (∀ k, w k ∈ W) ∧
      ∀ h, ∑ k, c k * ev (w k) h = if h = 1 then 1 else 0 := by
  classical
  set s : Set (J → ℂ) := (fun v => fun j => ev v (r j)) '' (W : Set V) with hs
  have htop : Submodule.span ℂ s = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφ : ∀ x : J → ℂ, φ x = ∑ j, x j * φ (fun j' => if j = j' then 1 else 0) := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp [smul_eq_mul]
    have ha := h3 (fun j => φ (fun j' => if j = j' then 1 else 0)) fun v hv => by
      have := hle (Submodule.subset_span ⟨v, hv, rfl⟩)
      rw [LinearMap.mem_ker, hφ] at this
      simpa [mul_comm] using this
    apply hφ0
    refine LinearMap.ext fun x => ?_
    rw [hφ x, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [congrFun ha j]; simp
  let b : J → ℂ := fun j => if r j = 1 then 1 else 0
  have hb : b ∈ Submodule.span ℂ s := htop ▸ Submodule.mem_top
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hb
  choose w hw hwg using fun k => (g k).2
  refine ⟨n, c, w, hw, fun h => ?_⟩
  by_cases hr : h ∈ Set.range r
  · obtain ⟨j, rfl⟩ := hr
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hwg k]
  · have h1' : h ≠ 1 := by
      rintro rfl
      obtain ⟨j, hj⟩ := h1
      exact hr ⟨j, hj⟩
    rw [if_neg h1']
    exact Finset.sum_eq_zero fun k _ => by rw [h2 _ (hw k) h hr, mul_zero]

theorem exists_vec_det_ne_zero (F : Type) [Field F] [CharZero F] [Algebra F ℂ] (V : Type) [AddCommGroup V] [Module F V]
    (S : Type) [Group S] [Fintype S] [DecidableEq S] (ι : Type) [Finite ι] (ev : ι → V →ₗ[F] (S → ℂ))
    (J : ι → Type) [∀ i, Fintype (J i)] (r : ∀ i, J i → S) (W : ι → Submodule F V)
    (h1 : ∀ i, ∃ j, r i j = 1) (h2 : ∀ i, ∀ v ∈ W i, ∀ h, h ∉ Set.range (r i) → ev i v h = 0)
    (h3 : ∀ i (a : J i → ℂ), (∀ v ∈ W i, ∑ j, a j * ev i v (r i j) = 0) → a = 0) :
    ∃ v : V, ∀ i, (Matrix.of fun h g : S => ev i v (h * g)).det ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  choose n c w hw hcw using fun i => exists_combination_delta F V S (J i) (ev i) (r i) (W i) (h1 i) (h2 i) (h3 i)
  let vec : (Σ i, Fin (n i)) → V := fun p => w p.1 p.2
  let P : ι → MvPolynomial (Σ i, Fin (n i)) ℂ := fun i =>
    Matrix.det (Matrix.of fun h g : S => ∑ p, MvPolynomial.X p * MvPolynomial.C (ev i (vec p) (h * g)))
  have hP : ∀ i (x : (Σ i, Fin (n i)) → ℂ), MvPolynomial.eval x (P i) =
      (Matrix.of fun h g : S => ∑ p, x p * ev i (vec p) (h * g)).det := by
    intro i x
    rw [RingHom.map_det]
    congr 1
    ext h g
    simp [RingHom.mapMatrix_apply]
  have hPi : ∀ i, P i ≠ 0 := by
    intro i hz
    let x : (Σ i, Fin (n i)) → ℂ := fun p => if p.1 = i then c p.1 p.2 else 0
    have hx : ∀ h, ∑ p, x p * ev i (vec p) h = if h = 1 then 1 else 0 := by
      intro h
      rw [← hcw i h, Fintype.sum_sigma, Finset.sum_eq_single i]
      · simp [x, vec]
      · intro b _ hb
        exact Finset.sum_eq_zero fun k _ => by simp [x, hb]
      · simp
    have := det_delta_ne_zero S _ hx
    rw [← hP, hz, map_zero] at this
    exact this rfl
  have hQ : (∏ i, P i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hPi i
  obtain ⟨x, hx, hQx⟩ : ∃ x ∈ Set.pi Set.univ (fun _ : (Σ i, Fin (n i)) => Set.range (algebraMap F ℂ)),
      MvPolynomial.eval x (∏ i, P i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ (MvPolynomial.funext_set (fun _ => Set.range (algebraMap F ℂ))
      (fun _ => Set.infinite_range_of_injective (algebraMap F ℂ).injective)
      fun x hx => by rw [hcon x hx, map_zero])
  choose t ht using fun p => hx p (Set.mem_univ p)
  refine ⟨∑ p, t p • vec p, fun i => ?_⟩
  have hne : MvPolynomial.eval x (P i) ≠ 0 := by
    rw [map_prod] at hQx
    exact Finset.prod_ne_zero_iff.1 hQx i (Finset.mem_univ _)
  rw [hP] at hne
  convert hne using 2
  ext h g
  simp [map_sum, Finset.sum_apply, Algebra.smul_def, ht]

end RHLean.Geometry.NativeGroupDeterminant

namespace RHLean.Geometry

/-- Construct a short integral regular group section directly from independent
orbit evaluations. This combines the regular-seed construction and bounded
integer determinant avoidance, so the regular seed is no longer a hypothesis.
All-place norms and the original integral scalar ring are retained. -/
theorem nativeExists_short_integral_group_section
    {F R V I Z S P : Type} [Field F] [CharZero F] [Algebra F ℂ]
    [Ring R] [AddCommGroup V] [Module F V] [Module R V]
    [Fintype I] [Finite Z] [Group S] [Fintype S] [DecidableEq S]
    (ev : Z → V →ₗ[F] (S → ℂ)) (J : Z → Type) [∀ z, Fintype (J z)]
    (r : ∀ z, J z → S) (W : Z → Submodule F V)
    (h1 : ∀ z, ∃ j, r z j = 1)
    (h2 : ∀ z, ∀ v ∈ W z, ∀ h, h ∉ Set.range (r z) → ev z v h = 0)
    (h3 : ∀ z (a : J z → ℂ),
      (∀ v ∈ W z, ∑ j, a j * ev z v (r z j) = 0) → a = 0)
    (L : Submodule R V) (w : I → V) (hw : ∀ i, w i ∈ L)
    (hwspan : Submodule.span F (Set.range w) = ⊤)
    (support : I → Finset Z)
    (hsupport : ∀ i, (support i).card ≤ Fintype.card S)
    (hdetOff : ∀ i z, z ∉ support i → ∀ h, ev z (w i) h = 0)
    (E : P → Type) [∀ p, SeminormedAddCommGroup (E p)]
    (realize : ∀ p, V →+ E p) (active : P → Finset I)
    {B N : ℝ} (hB : 0 ≤ B)
    (hactive : ∀ p, ((active p).card : ℝ) ≤ N)
    (hevOff : ∀ p i, i ∉ active p → realize p (w i) = 0)
    (hshort : ∀ p i, ‖realize p (w i)‖ ≤ B) :
    ∃ n : I → ℕ,
      (∀ i, n i ≤ Fintype.card S ^ 2) ∧
      (∑ i, n i • w i) ∈ L ∧
      (∀ z, (Matrix.of fun h g : S => ev z (∑ i, n i • w i) (h * g)).det ≠ 0) ∧
      ∀ p, ‖realize p (∑ i, n i • w i)‖ ≤
        N * ((Fintype.card S : ℝ) ^ 2 * B) := by
  classical
  obtain ⟨u, hu⟩ := NativeGroupDeterminant.exists_vec_det_ne_zero F V S Z ev J r W h1 h2 h3
  let D : ∀ z : Z, V →ₗ[F] Matrix S S ℂ := fun z =>
    { toFun := fun v => Matrix.of fun h g => ev z v (h * g)
      map_add' := fun v v' => by ext h g; simp
      map_smul' := fun a v => by ext h g; simp }
  have hOff : ∀ i z, z ∉ support i → D z (w i) = 0 := by
    intro i z hz
    ext h g
    exact hdetOff i z hz (h * g)
  have hspan : u ∈ Submodule.span F (Set.range w) := by
    rw [hwspan]
    exact Submodule.mem_top
  exact nativeExists_short_integral_regular_section (fun _ : Z => ℂ) D L w hw
    support hsupport hOff u hspan hu E realize active hB hactive hevOff hshort

end RHLean.Geometry

