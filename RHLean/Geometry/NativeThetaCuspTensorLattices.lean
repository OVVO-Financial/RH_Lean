import RHLean.Geometry.NativeThetaCuspPseudoBasis
import RHLean.Geometry.NativeThetaCuspAuxiliaryLattices

/-!
# Full auxiliary tensor lattices over the actual native field

The tensor lattice is the literal additive span of pure products of two
projective integral lattices. Its finite generation, integral trace
self-duality, common half-root phase and exact relative-index powers are
proved for every auxiliary lattice in the original family. No free-module
replacement or chosen numerical index is used.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/
TensorLatticeSelfDualSemicharacterIndex.lean. The symplectic sign is adapted
to the previously proved native convention Omega = +EF. The source mirror
states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module Matrix
open scoped nonZeroDivisors BigOperators Pointwise Classical

namespace RHLean.Geometry.NativeTheta.Cusp.TensorLattices

section Algebra

variable {E : Type} [Field E] [NumberField E] {n r : ℕ}

abbrev Lt (E : Type) [Field E] [NumberField E] (r : ℕ) :=
  Submodule (𝓞 E) (Fin r → E)

/-- The literal integral additive span of pure tensor vectors. -/
def tens (A : Lt E n) (B : Lt E r) : AddSubgroup (Matrix (Fin n) (Fin r) E) :=
  AddSubgroup.closure {y | ∃ v ∈ A, ∃ u ∈ B, y = vecMulVec v u}

theorem int_smul_mem {L : Lt E r} {a : E} (ha : IsIntegral ℤ a) {u : Fin r → E} (hu : u ∈ L) :
    a • u ∈ L := L.smul_mem (⟨a, ha⟩ : 𝓞 E) hu

theorem pure_mem {A : Lt E n} {B : Lt E r} {v : Fin n → E} {u : Fin r → E} (hv : v ∈ A)
    (hu : u ∈ B) : vecMulVec v u ∈ tens A B := AddSubgroup.subset_closure ⟨v, hv, u, hu, rfl⟩

theorem tens_le {A : Lt E n} {B : Lt E r} {H : AddSubgroup (Matrix (Fin n) (Fin r) E)}
    (h : ∀ v ∈ A, ∀ u ∈ B, vecMulVec v u ∈ H) : tens A B ≤ H := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨v, hv, u, hu, rfl⟩
  exact h v hv u hu

theorem tens_eq_comap (A : Lt E n) (B : Lt E r) :
    tens A B = (tens B A).comap (Matrix.transposeAddEquiv (Fin n) (Fin r) E).toAddMonoidHom := by
  have key : ∀ {n r : ℕ} (A : Lt E n) (B : Lt E r), tens A B ≤
      (tens B A).comap (Matrix.transposeAddEquiv (Fin n) (Fin r) E).toAddMonoidHom :=
    fun A B => tens_le fun v hv u hu => by
      change (vecMulVec v u)ᵀ ∈ tens B A
      rw [Matrix.transpose_vecMulVec]
      exact pure_mem hu hv
  exact le_antisymm (key A B) fun y hy => key B A hy

theorem isIntegral_mul_inv {c : FractionalIdeal (𝓞 E)⁰ E} (hc : c ≠ 0) {x b : E} (hx : x ∈ c)
    (hb : b ∈ c⁻¹) : IsIntegral ℤ (b * x) := by
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hc).1 hb x hx)
  exact ha ▸ a.isIntegral_coe

def fracMul (c : FractionalIdeal (𝓞 E)⁰ E) (B : Lt E r) : AddSubgroup (Fin r → E) where
  carrier := {u | ∀ b ∈ c⁻¹, b • u ∈ B}
  add_mem' := fun hu hv b hb => by rw [smul_add]; exact B.add_mem (hu b hb) (hv b hb)
  zero_mem' := fun b _ => by rw [smul_zero]; exact B.zero_mem
  neg_mem' := fun hu b hb => by rw [smul_neg]; exact B.neg_mem (hu b hb)

theorem relIndex_fracMul {c : FractionalIdeal (𝓞 E)⁰ E} (hc : c ≠ 0) {B B' : Lt E r} {N : 𝓞 E}
    (hN : N ≠ 0) (hB : ∀ u ∈ B, (N : E) • u ∈ B') :
    B'.toAddSubgroup.relIndex B.toAddSubgroup = (fracMul c B').relIndex (fracMul c B) := by
  have hNE : (N : E) ≠ 0 := by simpa using hN
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq
    (a := FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (b := c⁻¹) (c := 1)
    (FractionalIdeal.spanSingleton_le_iff_mem.2 ((FractionalIdeal.mem_one_iff _).2 ⟨N, rfl⟩))
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 hNE) (inv_ne_zero hc)
  have hxc : x ∈ c := by
    have h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x * c⁻¹ ≤ 1 := hx ▸ le_sup_right
    have h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x * c⁻¹ * c ≤ 1 * c := by gcongr
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one, one_mul] at h2
    exact FractionalIdeal.spanSingleton_le_iff_mem.1 h2
  obtain ⟨t, b, ht, hb, htb⟩ : ∃ t b : E, IsIntegral ℤ t ∧ b ∈ c⁻¹ ∧ t * N + x * b = 1 := by
    have h1 : (1 : E) ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) +
        FractionalIdeal.spanSingleton (𝓞 E)⁰ x * c⁻¹ := hx ▸ FractionalIdeal.one_mem_one _
    obtain ⟨y, hy, z, hz, hyz⟩ := (FractionalIdeal.mem_add _ _ _).1 h1
    obtain ⟨t, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hy
    obtain ⟨b, hb, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hz
    exact ⟨t, b, t.isIntegral_coe, hb, hyz⟩
  refine PseudoBasis.relIndex_eq_of_hom (DistribSMul.toAddMonoidHom (Fin r → E) x) (fun v hv => ?_)
    (fun v hv => ?_) (fun u hu => ?_)
  · intro b' hb'
    rw [DistribSMul.toAddMonoidHom_apply, smul_smul]
    exact int_smul_mem (isIntegral_mul_inv hc hxc hb') hv
  · rw [DistribSMul.toAddMonoidHom_apply]
    refine ⟨fun h => ?_, fun h b' hb' => ?_⟩
    · have : v = t • (N : E) • v + b • x • v := by
        rw [smul_smul, smul_smul, ← add_smul, mul_comm b, htb, one_smul]
      rw [this]
      exact B'.add_mem (int_smul_mem ht (hB v hv)) (h b hb)
    · rw [smul_smul]
      exact int_smul_mem (isIntegral_mul_inv hc hxc hb') h
  · refine ⟨b • u, hu b hb, fun b' hb' => ?_⟩
    have h1 : u - DistribSMul.toAddMonoidHom (Fin r → E) x (b • u) = t • (N : E) • u := by
      rw [DistribSMul.toAddMonoidHom_apply, smul_smul, smul_smul, eq_sub_of_add_eq htb, sub_smul,
        one_smul]
    rw [h1, smul_comm b', smul_comm b']
    exact int_smul_mem ht (hB _ (hu b' hb'))

theorem exists_mul_le {B B' : Lt E r} (hfg : B.FG)
    (hsp : Submodule.span E (B' : Set (Fin r → E)) = ⊤) :
    ∃ N : 𝓞 E, N ≠ 0 ∧ ∀ u ∈ B, (N : E) • u ∈ B' := by
  obtain ⟨s, rfl⟩ := hfg
  choose d hd0 hd using fun v : Fin r → E =>
    PseudoBasis.exists_smul_mem_of_mem_span_fraction (K := E) B' v (hsp ▸ Submodule.mem_top)
  refine ⟨∏ v ∈ s, d v, Finset.prod_ne_zero_iff.2 fun v _ => hd0 v, fun u hu => ?_⟩
  change (∏ v ∈ s, d v) • u ∈ B'
  induction hu using Submodule.span_induction with
  | mem v hv =>
    rw [← Finset.prod_erase_mul _ _ hv, mul_smul]
    exact B'.smul_mem _ (hd v)
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact B'.add_mem ha hb
  | smul α a _ ha => rw [smul_comm]; exact B'.smul_mem α ha

def colCoord (e : Module.Basis (Fin n) E (Fin n → E)) :
    Matrix (Fin n) (Fin r) E →+ (Fin n → Fin r → E) :=
  AddMonoidHom.mk' (fun y a j => e.repr (yᵀ j) a) fun y y' => by
    funext a j
    change e.repr (yᵀ j + y'ᵀ j) a = _
    simp

theorem tens_eq_of_pseudoBasis {A : Lt E n} (e : Module.Basis (Fin n) E (Fin n → E))
    (c : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, c a ≠ 0)
    (hA : ∀ v, v ∈ A ↔ ∀ a, e.repr v a ∈ c a) (B : Lt E r) :
    tens A B = (AddSubgroup.pi Set.univ fun a => fracMul (c a) B).comap (colCoord e) := by
  refine le_antisymm (tens_le fun v hv u hu a _ b hb => ?_) fun y hy => ?_
  · have : colCoord e (vecMulVec v u) a = e.repr v a • u := by
      funext j
      have : (vecMulVec v u)ᵀ j = u j • v := by
        funext k; simp [vecMulVec_apply, mul_comm]
      change e.repr ((vecMulVec v u)ᵀ j) a = _
      rw [this]; simp [mul_comm]
    rw [this, smul_smul]
    exact int_smul_mem (isIntegral_mul_inv (hc a) ((hA v).1 hv a) hb) hu
  · have h1 : y = ∑ a, vecMulVec (e a) (colCoord e y a) := by
      ext k j
      have := congrFun (e.sum_repr (yᵀ j)) k
      rw [Matrix.transpose_apply] at this
      rw [← this, Matrix.sum_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [h1]
    refine AddSubgroup.sum_mem _ fun a _ => ?_
    have h2 : ∀ z ∈ c a * (c a)⁻¹, vecMulVec (e a) (z • colCoord e y a) ∈ tens A B := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun t ht b hb => ?_) fun s t hs ht => ?_
      · rw [mul_smul, vecMulVec_smul, ← smul_vecMulVec]
        refine pure_mem ((hA _).2 fun a' => ?_) (hy a (Set.mem_univ _) b hb)
        by_cases h : a = a'
        · subst h; simpa using ht
        · simpa [h] using (c a').zero_mem
      · rw [add_smul, vecMulVec_add]
        exact add_mem hs ht
    simpa using h2 1 (by rw [mul_inv_cancel₀ (hc a)]; exact FractionalIdeal.one_mem_one _)

theorem relIndex_tens_right {A : Lt E n} (hA : A.FG)
    (hAs : Submodule.span E (A : Set (Fin n → E)) = ⊤) {B B' : Lt E r} (hfg : B.FG)
    (hsp : Submodule.span E (B' : Set (Fin r → E)) = ⊤) :
    (tens A B').relIndex (tens A B) = B'.toAddSubgroup.relIndex B.toAddSubgroup ^ n := by
  obtain ⟨-, e, c, hc, he, -⟩ := PseudoBasis.exists_pseudoBasis_adapted E n A ⊤ hA hAs
  obtain ⟨N, hN, hB⟩ := exists_mul_le hfg hsp
  have hs : Function.Surjective (colCoord (r := r) e) := fun z =>
    ⟨(Matrix.of fun j => e.equivFun.symm fun a => z a j)ᵀ, by
      funext a j
      exact congrFun (e.equivFun.apply_symm_apply fun a => z a j) a⟩
  rw [tens_eq_of_pseudoBasis e c hc he, tens_eq_of_pseudoBasis e c hc he,
    AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hs,
    PseudoBasis.relIndex_pi_univ,
    Finset.prod_congr rfl fun a _ => (relIndex_fracMul (hc a) hN hB).symm]
  simp

theorem relIndex_tens_left {B : Lt E r} (hB : B.FG)
    (hBs : Submodule.span E (B : Set (Fin r → E)) = ⊤) {A A' : Lt E n} (hfg : A.FG)
    (hsp : Submodule.span E (A' : Set (Fin n → E)) = ⊤) :
    (tens A' B).relIndex (tens A B) = A'.toAddSubgroup.relIndex A.toAddSubgroup ^ r := by
  rw [tens_eq_comap A, tens_eq_comap A', AddSubgroup.relIndex_comap,
    AddSubgroup.map_comap_eq_self_of_surjective (AddEquiv.surjective _),
    relIndex_tens_right hB hBs hfg hsp]


end Algebra

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open NativePrescribedHermitian AuxiliaryLattices ShiftedLattice

variable {φ : Frame} (H : HostRaw φ) {n r : ℕ}

def ctr (y : Matrix (Fin n) (Fin r) H.E) (w : Fin n → H.E) : Fin r → H.E := ∑ k, H.conj (w k) • y k

theorem ctr_apply (y : Matrix (Fin n) (Fin r) H.E) (w : Fin n → H.E) (j : Fin r) :
    ctr H y w j = herm H (yᵀ j) w := by
  simp [ctr, herm, Finset.sum_apply, mul_comm]

theorem ctr_pure (v w : Fin n → H.E) (u : Fin r → H.E) : ctr H (vecMulVec v u) w = herm H v w • u := by
  funext j
  simp only [ctr_apply, herm, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Matrix.transpose_apply, vecMulVec_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem eq_sum_ctr {m : ℕ} {v w : Fin m → Fin n → H.E}
    (h : ∀ u : Fin n → H.E, u = ∑ i, herm H u (w i) • v i) (y : Matrix (Fin n) (Fin r) H.E) :
    y = ∑ i, vecMulVec (v i) (ctr H y (w i)) := by
  ext k j
  have := congrFun (h (yᵀ j)) k
  rw [Matrix.transpose_apply] at this
  rw [this, Matrix.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => by simp [vecMulVec_apply, ctr_apply, mul_comm]

theorem mem_tens_iff {M : ℕ} {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n M) (L : Lt H.E r)
    (y : Matrix (Fin n) (Fin r) H.E) : y ∈ tens Λ L ↔ ∀ w ∈ Λ, ctr H y w ∈ L := by
  obtain ⟨-, m, v, w, hv, hw, h⟩ := exists_dual_family H Λ hΛ.1 (fun x => (hΛ.2.1 x).1)
    fun x => (hΛ.2.1 x).2
  constructor
  · intro hy u hu
    let f : Matrix (Fin n) (Fin r) H.E →+ (Fin r → H.E) := AddMonoidHom.mk' (fun y => ctr H y u)
      fun y y' => by
        have : ∀ i, (y + y') i = y i + y' i := fun _ => rfl
        simp only [ctr, this, smul_add, Finset.sum_add_distrib]
    refine tens_le (H := L.toAddSubgroup.comap f) (fun a ha b hb => ?_) hy
    change ctr H _ u ∈ L
    rw [ctr_pure]
    exact int_smul_mem ((hΛ.2.1 a).1 ha u hu) hb
  · intro hy
    rw [eq_sum_ctr H h y]
    exact AddSubgroup.sum_mem _ fun i _ => pure_mem (hv i) (hy _ (hw i))

theorem tens_fg {M : ℕ} {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n M) {L : Lt H.E r} (hL : L.FG) :
    (tens Λ L).FG := by
  obtain ⟨-, m, v, w, hv, hw, h⟩ := exists_dual_family H Λ hΛ.1 (fun x => (hΛ.2.1 x).1)
    fun x => (hΛ.2.1 x).2
  let f : (Fin m → Fin r → H.E) →+ Matrix (Fin n) (Fin r) H.E :=
    AddMonoidHom.mk' (fun u => ∑ i, vecMulVec (v i) (u i))
      fun y y' => by simp [vecMulVec_add, Finset.sum_add_distrib]
  have h1 : (Submodule.pi Set.univ fun _ : Fin m => L.restrictScalars ℤ).FG :=
    Submodule.fg_pi fun _ => hL.restrictScalars
  have h2 : tens Λ L = ((Submodule.pi Set.univ fun _ : Fin m => L.restrictScalars ℤ).map
      f.toIntLinearMap).toAddSubgroup := by
    ext y
    constructor
    · intro hy
      exact ⟨fun i => ctr H y (w i), fun i _ => (mem_tens_iff H hΛ L y).1 hy _ (hw i),
        (eq_sum_ctr H h y).symm⟩
    · rintro ⟨u, hu, rfl⟩
      change ∑ i, vecMulVec (v i) (u i) ∈ tens Λ L
      exact AddSubgroup.sum_mem _ fun i _ => pure_mem (hv i) (hu i (Set.mem_univ _))
  rw [h2]
  exact (Submodule.fg_iff_addSubgroup_fg _).1 (h1.map _)

/-- The native trace pairing, bundled without changing its normalization. -/
def pairBilin (neg : Fin r → Bool) :
    (Fin r → H.E) →ₗ[ℚ] (Fin r → H.E) →ₗ[ℚ] ℚ where
  toFun x :=
    { toFun := Ambient.pair H neg x
      map_add' := Ambient.pair_add_right H neg x
      map_smul' := fun q y => Ambient.pair_smul_right H neg q x y }
  map_add' x y := LinearMap.ext fun z => Ambient.pair_add_left H neg x y z
  map_smul' q x := LinearMap.ext fun y => Ambient.pair_smul_left H neg q x y

theorem pair_eq_bilin (neg : Fin r → Bool) (x y : Fin r → H.E) :
    Ambient.pair H neg x y = pairBilin H neg x y := rfl

theorem sum_pair_pure (neg : Fin r → Bool) (y : Matrix (Fin n) (Fin r) H.E)
    (v : Fin n → H.E) (u : Fin r → H.E) :
    ∑ k, Ambient.pair H neg (y k) (vecMulVec v u k) =
      Ambient.pair H neg (ctr H y v) u := by
  change (∑ k, pairBilin H neg (y k) (vecMulVec v u k)) =
    pairBilin H neg (∑ k, H.conj (v k) • y k) u
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  change Ambient.pair H neg (y k) (vecMulVec v u k) =
    Ambient.pair H neg (H.conj (v k) • y k) u
  simp only [Ambient.pair_adjoint_field, conj_conj]

attribute [local instance] NativeRawHostPolarization.conjugationStar

/-- Trace self-duality forces full span in the unchanged field space. -/
theorem span_of_selfDual {neg : Fin r → Bool} {L : Lt H.E r}
    (hL : SelfDual H neg L) : Submodule.span H.E (L : Set (Fin r → H.E)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨z, hz⟩ := AuxiliaryLattices.exists_herm_eq H f
  let z' : Fin r → H.E := fun i => (sgn (neg i) : H.E) * z i
  have hp (c : H.E) (y : Fin r → H.E) : Ambient.pair H neg (c • z') y =
      Algebra.trace ℚ H.E (xi H * H.conj c * herm H y z) := by
    have hs : (∑ i, H.conj (c * ((sgn (neg i) : H.E) * z i)) *
        sgn (neg i) * y i) = H.conj c * herm H y z := by
      rw [herm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, map_sgn H.conj.toRingHom]
      calc
        _ = H.conj c * ((sgn (neg i) : H.E) * sgn (neg i)) * (y i * H.conj (z i)) := by ring
        _ = _ := by rw [sgn_mul_self, mul_one]
    change Algebra.trace ℚ H.E
      (xi H * ∑ i, H.conj (c * ((sgn (neg i) : H.E) * z i)) *
        sgn (neg i) * y i) = _
    rw [hs, mul_assoc]
  have hz' : z' = 0 := AuxiliaryLattices.eq_zero_of_line H L hL.1 z' fun c =>
    (hL.2 _).2 fun y hy => ⟨0, by
      rw [hp, ← hz, show f y = 0 from hf (Submodule.subset_span hy)]
      simp⟩
  have hz0 : z = 0 := by
    funext i
    have hi := congrFun hz' i
    change (sgn (neg i) : H.E) * z i = 0 at hi
    have he := congrArg (fun t => (sgn (neg i) : H.E) * t) hi
    simpa only [← mul_assoc, sgn_mul_self, one_mul, mul_zero] using he
  exact hf0 (LinearMap.ext fun u => by simp [hz u, hz0, herm])

/-- The tensor product of the auxiliary integral Hermitian lattice and
the actual trace lattice is self-dual for the original summed trace. -/
theorem tens_selfDual {M : ℕ} {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n M)
    {neg : Fin r → Bool} {L : Lt H.E r} (hL : SelfDual H neg L)
    (y : Matrix (Fin n) (Fin r) H.E) :
    y ∈ tens Λ L ↔ ∀ y' ∈ tens Λ L,
      ∃ k : ℤ, ∑ i, Ambient.pair H neg (y i) (y' i) = k := by
  constructor
  · intro hy y' hy'
    let f : Matrix (Fin n) (Fin r) H.E →+ ℚ :=
      AddMonoidHom.mk' (fun y' => ∑ i, Ambient.pair H neg (y i) (y' i))
        fun a b => by
          simp only [Pi.add_apply, Ambient.pair_add_right, Finset.sum_add_distrib]
    obtain ⟨k, hk⟩ := tens_le (H := (Int.castAddHom ℚ).range.comap f)
      (fun a ha b hb => by
        obtain ⟨k, hk⟩ := (hL.2 _).1 ((mem_tens_iff H hΛ L y).1 hy a ha) b hb
        exact ⟨k, (hk.symm.trans (sum_pair_pure H neg y a b).symm :)⟩) hy'
    exact ⟨k, hk.symm⟩
  · intro h
    refine (mem_tens_iff H hΛ L y).2 fun w hw => (hL.2 _).2 fun u hu => ?_
    rw [← sum_pair_pure]
    exact h _ (pure_mem hw hu)

theorem smul_mem_tens {M : ℕ} {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n M)
    {L : Lt H.E r} {w : H.E} (hw : IsIntegral ℤ w)
    {y : Matrix (Fin n) (Fin r) H.E} (hy : y ∈ tens Λ L) : w • y ∈ tens Λ L := by
  rw [mem_tens_iff H hΛ] at hy ⊢
  intro v hv
  have he : ctr H (w • y) v = w • ctr H y v := by
    funext j
    simp [ctr, Finset.sum_apply, Finset.mul_sum, mul_left_comm]
  rw [he]
  exact int_smul_mem hw (hy v hv)

/-- The common physical half-root phase on every actual auxiliary tensor
lattice, with the same positive symplectic convention as the native vacuum. -/
theorem phase_semichar {M : ℕ} {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n M)
    {neg : Fin r → Bool} {L : Lt H.E r} (hL : SelfDual H neg L)
    (w : 𝓞 H.E) (hw : w + bar H w = 1) {y : Matrix (Fin n) (Fin r) H.E}
    (hy : y ∈ tens Λ L) :
    ShiftedPhase.phase H neg w y ^ 2 = 1 ∧
      ∀ y' ∈ tens Λ L, ShiftedPhase.phase H neg w (y + y') =
        ShiftedPhase.phase H neg w y * ShiftedPhase.phase H neg w y' *
          Complex.exp (Real.pi * Complex.I *
            ((∑ k, Ambient.pair H neg (y k) (y' k) : ℚ) : ℂ)) := by
  have hint (a : 𝓞 H.E) (y' : Matrix (Fin n) (Fin r) H.E) (hy' : y' ∈ tens Λ L) :
      ∃ z : ℤ, ∑ k, Ambient.pair H neg (y k) (a • y' k) = z :=
    (tens_selfDual H hΛ hL y).1 hy _ (smul_mem_tens H hΛ a.isIntegral_coe hy')
  constructor
  · obtain ⟨z, hz⟩ := hint w y hy
    rw [ShiftedPhase.phase, pow_two, ← Complex.exp_add]
    simp only [ShiftedPhase.quadratic, hz]
    have he : Real.pi * Complex.I * ((z : ℚ) : ℂ) +
        Real.pi * Complex.I * ((z : ℚ) : ℂ) = (z : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [he]
    exact Complex.exp_int_mul_two_pi_mul_I z
  · intro y' hy'
    obtain ⟨z, hz⟩ := hint (bar H w) y' hy'
    have hq : (∑ k, ShiftedPhase.quadratic H neg w ((y + y') k)) =
        (∑ k, ShiftedPhase.quadratic H neg w (y k)) +
        (∑ k, ShiftedPhase.quadratic H neg w (y' k)) +
        (∑ k, Ambient.pair H neg (y k) (y' k)) - 2 * (z : ℚ) := by
      simp only [Pi.add_apply, ShiftedPhase.quadratic_add H neg w hw,
        Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hz]
    simp only [ShiftedPhase.phase]
    rw [hq]
    have he : Real.pi * Complex.I *
        (((∑ k, ShiftedPhase.quadratic H neg w (y k)) +
          (∑ k, ShiftedPhase.quadratic H neg w (y' k)) +
          (∑ k, Ambient.pair H neg (y k) (y' k)) - 2 * (z : ℚ) : ℚ) : ℂ) =
        Real.pi * Complex.I * ((∑ k, ShiftedPhase.quadratic H neg w (y k) : ℚ) : ℂ) +
        Real.pi * Complex.I * ((∑ k, ShiftedPhase.quadratic H neg w (y' k) : ℚ) : ℂ) +
        Real.pi * Complex.I * ((∑ k, Ambient.pair H neg (y k) (y' k) : ℚ) : ℂ) +
        ((-z : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
      Complex.exp_add, Complex.exp_add]

theorem mem_tens_stdL (L : Lt H.E r) (y : Matrix (Fin n) (Fin r) H.E) :
    y ∈ tens (stdL H n) L ↔ ∀ k, y k ∈ L := by
  rw [mem_tens_iff H (stdL_mem_Vset H n 1)]
  constructor
  · intro h k
    have he := h (Pi.single k 1) (Submodule.subset_span ⟨k, rfl⟩)
    rw [ctr, Finset.sum_eq_single k] at he
    · simpa using he
    · intro j _ hj
      simp [hj]
    · simp
  · intro h w hw
    exact L.sum_mem fun k _ => int_smul_mem (isIntegral_conj H ((mem_stdL H).1 hw k)) (h k)

theorem tens_inf {M : ℕ} {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n M) (L L' : Lt H.E r) :
    tens Λ L ⊓ tens Λ L' = tens Λ (L ⊓ L') := by
  ext y
  simp only [AddSubgroup.mem_inf, mem_tens_iff H hΛ, Submodule.mem_inf]
  exact ⟨fun h v hv => ⟨h.1 v hv, h.2 v hv⟩,
    fun h => ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩⟩

/-- Exact powers of the original relative index, retaining its direction
`L'.relIndex L = [L : L ∩ L']`. -/
theorem tens_relative_indices {M : ℕ} {Λ : Lt H.E n} (hΛ : Λ ∈ Vset H n M)
    {neg : Fin r → Bool} {L : Lt H.E r} (hL : SelfDual H neg L) :
    (∀ L', SelfDual H neg L' →
      (tens Λ L').relIndex (tens Λ L) = L'.toAddSubgroup.relIndex L.toAddSubgroup ^ n) ∧
      ∀ Λ' ∈ Vset H n M,
        (tens Λ' L).relIndex (tens Λ L) =
          Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup ^ r := by
  have hspan : ∀ A ∈ Vset H n M, Submodule.span H.E (A : Set (Fin n → H.E)) = ⊤ :=
    fun A hA => AuxiliaryLattices.span_eq_top H A hA.1 fun x => (hA.2.1 x).2
  exact ⟨fun L' hL' => relIndex_tens_right hΛ.1 (hspan Λ hΛ) hL.1 (span_of_selfDual H hL'),
    fun Λ' hΛ' => relIndex_tens_left hL.1 (span_of_selfDual H hL) hΛ.1 (hspan Λ' hΛ')⟩

end RHLean.Geometry.NativeTheta.Cusp.TensorLattices
