import RHLean.Geometry.NativeServedPrimeLength

/-!
# Apply the existing served-prime length theorem to the original lattice sandwich

This is the lattice compatibility part of the existing recovery argument,
not a new signed-gain mechanism. The source is Levent Alpoge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4:

* Formalism.InvariantFactorPaths.G0.invariant_factors_submodule and inverse_shift,
  src/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ProductIdealProofs/
  ElementarySymmetricExpBound.lean;
* saturated_ramified_lattice in
  src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean;
* FormalGroupSystem.Pf.core and stmt6G in
  src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/StabilizerCount.lean.

The existing native AllButLE and lengthFromAllBut_saturated are the only
length mechanism used here. The actual smaller lattice, restriction
submodule, exceptional generators and stopping inclusion retain their
original meanings. The exceptional sets are transferred from the larger
lattice using a quotient and a PID basis, rather than assumed a second
time. Saturation is automatic for the intersection with the original
fraction-field subspace. The existing length bound then applies directly.

The physical theta-kernel expansion must still furnish the exceptional
sets and actual operator compatibility. This file does not construct the
full family or bound its arithmetic top excess. In particular there is no
zero-chain substitution for a physical gain or valuation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise

namespace RHLean.Geometry.NativeServedPrimeLength

/-- Restriction of an exceptional-generator bound to an intermediate
lattice containing the paid submodule. The auxiliary generators are
obtained from a basis of the actual quotient preimage. -/
theorem allButLE_restrict
    {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X]
    (a : R) (A B N : Submodule R X) (g E : ℕ)
    (hNB : N ≤ B) (hBA : B ≤ A) (h : AllButLE a A N g E) :
    AllButLE a B N g E := by
  classical
  have _hNA : N ≤ A := hNB.trans hBA
  obtain ⟨C, _, hCg, hC⟩ := h
  let f : (C → R) →ₗ[R] X ⧸ N :=
    { toFun := fun u => ∑ c : C, u c • N.mkQ (c : X)
      map_add' := by
        intro u v
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r u
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  let W : Submodule R (X ⧸ N) := B.map (N.mkQ ∘ₗ ((a ^ E) • LinearMap.id))
  let U : Submodule R (C → R) := W.comap f
  obtain ⟨n, basis⟩ := Submodule.basisOfPid (Pi.basisFun R C) U
  have hn : n ≤ C.card := by
    have hi := basis.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
      hi.fintype_card_le_finrank
  have hb : ∀ i, ∃ x ∈ B, N.mkQ (a ^ E • x) = f (basis i) := by
    intro i
    have hi : f (basis i) ∈ W := (basis i).2
    obtain ⟨x, hx, hq⟩ := Submodule.mem_map.mp hi
    exact ⟨x, hx, hq⟩
  choose v hv hq using hb
  refine ⟨Finset.univ.image v, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
    exact hv i
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    exact hn.trans hCg
  · intro x hx
    obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp (hC x (hBA hx))
    obtain ⟨c, _, hc⟩ := Submodule.mem_span_finset.mp hz
    have hf : f (fun i => c i) = N.mkQ (a ^ E • x) := by
      show ∑ i : C, c i • N.mkQ (i : X) = _
      rw [← he, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hy,
        zero_add, ← hc, map_sum, ← Finset.sum_coe_sort C]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
    have hu : (fun i : C => c (i : X)) ∈ U := by
      show f _ ∈ W
      rw [hf]
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    have hs := congrArg Subtype.val (basis.sum_repr ⟨_, hu⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hs
    set r := basis.repr ⟨_, hu⟩ with hr
    have hsum : N.mkQ (a ^ E • x) = N.mkQ (∑ i, r i • a ^ E • v i) := by
      rw [← hf, ← hs, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, hq i]
    have hnmem : a ^ E • x - ∑ i, r i • a ^ E • v i ∈ N := by
      rw [← Submodule.ker_mkQ N, LinearMap.mem_ker, map_sub, hsum, sub_self]
    have hspan : ∑ i, r i • a ^ E • v i ∈
        Submodule.span R (↑(Finset.univ.image v) : Set X) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem v (Finset.mem_univ i)))))
    exact Submodule.mem_sup.mpr ⟨_, hnmem, _, hspan, sub_add_cancel _ _⟩

/-- Original inverse shift: transfer the same exceptional-count allowance
from the larger lattice to the sandwiched lattice and charge the actual
shift exponent once. -/
theorem allButLE_inverse_shift
    {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X]
    (a : R) (A B NA NB : Submodule R X) (g E e : ℕ)
    (hBA : B ≤ A) (hNA : NA ≤ A)
    (hshift : ∀ x ∈ NA, a ^ e • x ∈ NB) (hNB : NB ≤ B)
    (h : AllButLE a A NA g E) :
    AllButLE a B NB g (E + e) := by
  classical
  obtain ⟨C, hC, hcard, hmem⟩ :=
    allButLE_restrict a A (B ⊔ NA) NA g E le_sup_right (sup_le hBA hNA) h
  let D := C.image (fun c => a ^ e • c)
  refine ⟨D, ?_, Finset.card_image_le.trans hcard, ?_⟩
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
    obtain ⟨b, hb, u, hu, he⟩ := Submodule.mem_sup.mp (hC hc)
    rw [← he, smul_add]
    exact B.add_mem (B.smul_mem _ hb) (hNB (hshift u hu))
  · intro x hx
    obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp
      (hmem x (le_sup_left (a := B) hx))
    have hz' : a ^ e • z ∈ Submodule.span R (↑D : Set X) := by
      refine Submodule.span_induction
        (p := fun z _ => a ^ e • z ∈ Submodule.span R (↑D : Set X))
        ?_ ?_ ?_ ?_ hz
      · intro c hc
        exact Submodule.subset_span
          (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hc))
      · simp
      · intro u v _ _ hu hv
        rw [smul_add]
        exact add_mem hu hv
      · intro r u _ hu
        rw [smul_comm]
        exact Submodule.smul_mem _ _ hu
    rw [pow_add, mul_comm, mul_smul, ← he, smul_add]
    exact Submodule.mem_sup.mpr ⟨_, hshift y hy, _, hz', rfl⟩

/-- The actual ramified part is a fraction-field subspace intersected
with the integral lattice. Nonzero scalar cancellation supplies its
saturation; there is no independent saturation premise. -/
theorem fractionIntersection_saturated
    {R K X : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup X] [Module R X] [Module K X]
    [IsScalarTower R K X]
    (M : Submodule R X) (V : Submodule K X)
    (r : R) (x : X) (hx : x ∈ M) (hr : r ≠ 0)
    (h : r • x ∈ M ⊓ V.restrictScalars R) :
    x ∈ M ⊓ V.restrictScalars R := by
  have hrK : algebraMap R K r ≠ 0 := by
    intro hzero
    exact hr ((IsFractionRing.injective R K) (by rw [hzero, map_zero]))
  have hV : (algebraMap R K r) • x ∈ V := by
    rw [← algebraMap_smul K r x]
    exact h.2
  have hinv := V.smul_mem (algebraMap R K r)⁻¹ hV
  rw [inv_smul_smul₀ hrK] at hinv
  exact ⟨hx, hinv⟩

/-- Apply the existing served-prime theorem after the original lattice
transfer and fraction-space intersection. Exceptional generators need
only be supplied on the larger lattice A. The target submodule NB is
unchanged, and its actual stopping exponent is still required. -/
theorem lengthFromAllBut_of_sandwich
    {R K X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup X]
    [Module R X] [Module K X] [IsScalarTower R K X]
    (a : R) (ha : a ≠ 0) (A B NA NB : Submodule R X) (Vram : Submodule K X)
    [Module.Free R B] [Module.Finite R B]
    (e : ℕ) (hBA : B ≤ A) (hNA : NA ≤ A)
    (hshift : ∀ x ∈ NA, a ^ e • x ∈ NB) (hNB : NB ≤ B)
    (d : ℕ) (hd : Module.finrank R B = d) (τ S V : ℕ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (hExc : ∀ β < V, ∃ g : ℕ, (g : ℝ) ≤ d * s ^ (β + 1) ∧
      AllButLE a A NA g (τ + β * S))
    (hstop : ∀ x ∈ B, a ^ (V * S) • x ∈ NB) :
    let W := B ⊓ Vram.restrictScalars R
    (NB ⊓ (Ideal.span {a ^ (e + τ)}) • B) ⊓ W ≤
      (Ideal.span {a ^ (e + τ)}) • W ∧
    ∃ ℓ : ℕ, Module.length R (↥W ⧸
      ((NB ⊓ (Ideal.span {a ^ (e + τ)}) • B) ⊓ W).comap W.subtype) = ℓ ∧
      (ℓ : ℝ) ≤ ((IsDiscreteValuationRing.addVal R a).toNat : ℝ) *
        ((d : ℝ) * (e + τ) + 2 * S * s * d) := by
  let W := B ⊓ Vram.restrictScalars R
  have hLayers : ∀ β < V, ∃ C : Finset X, (↑C : Set X) ⊆ B ∧
      (C.card : ℝ) ≤ d * s ^ (β + 1) ∧
      ∀ x ∈ B, a ^ (e + τ + β * S) • x ∈ NB ⊔ Submodule.span R (↑C : Set X) := by
    intro β hβ
    obtain ⟨g, hg, h⟩ := hExc β hβ
    obtain ⟨C, hC, hc, hpow⟩ :=
      allButLE_inverse_shift a A B NA NB g (τ + β * S) e hBA hNA hshift hNB h
    refine ⟨C, hC, (by exact_mod_cast hc : (C.card : ℝ) ≤ g).trans hg, ?_⟩
    intro x hx
    have heq : e + τ + β * S = (τ + β * S) + e := by ring
    rw [heq]
    exact hpow x hx
  exact lengthFromAllBut_saturated a ha B NB W (inf_le_left)
    (fractionIntersection_saturated B Vram) d hd (e + τ) S V s hs0 hs hLayers hstop

end RHLean.Geometry.NativeServedPrimeLength

end
