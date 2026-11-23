import Mathlib

/-!
# Local flatness from actual residue and cotangent relations

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.
src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean
src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsMemPowSubMemPowSucc.lean

These native declaration cuts prove the local algebra and actual scheme
flatness needed by the generic graph's torsion argument. They introduce
no homomorphism-extension or polarized-variety premise. Completion and
redundant statement wrappers outside this dependency cut are omitted.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open TensorProduct LinearMap

universe u v w

namespace RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

namespace LocalFlat

variable {A : Type u} [CommRing A]

def RelationsLift (I : Ideal A) (M : Type w) [AddCommGroup M] [Module A M] : Prop :=
  ∀ (F : Type u) [AddCommGroup F] [Module A F] (f : F →ₗ[A] A) (x : M ⊗[A] F),
    TensorProduct.rid A M (f.lTensor M x) ∈ I • (⊤ : Submodule A M) →
      x ∈ range ((Submodule.comap f I).subtype.lTensor M)

variable {M : Type w} [AddCommGroup M] [Module A M]

theorem range_lTensor_le {F G : Type*} [AddCommGroup F] [Module A F] [AddCommGroup G] [Module A G]
    (h : G →ₗ[A] F) (N : Submodule A F) (hN : ∀ g, h g ∈ N) :
    range (h.lTensor M) ≤ range (N.subtype.lTensor M) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨(h.codRestrict N hN).lTensor M y, ?_⟩
  rw [← lTensor_comp_apply]
  rfl

theorem relationsLift_of_flat {I : Ideal A} {C : Type*} [CommRing C] [Algebra A C]
    (hC : Function.Surjective (algebraMap A C)) (hI : RingHom.ker (algebraMap A C) = I)
    {M' : Type*} [AddCommGroup M'] [Module A M'] [Module C M'] [IsScalarTower A C M']
    [Module.Flat C M'] (q : M →ₗ[A] M') (hq : Function.Surjective q)
    (hker : ker q = I • (⊤ : Submodule A M)) : RelationsLift I M := by
  intro F _ _ f x hx
  obtain ⟨k, m, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  rw [← hker, mem_ker] at hx
  have h0 : ∑ i, algebraMap A C (f (v i)) • q (m i) = 0 := by
    simpa [map_sum] using hx
  obtain ⟨l, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h0
  choose a ha using fun i j => hC (c i j)
  choose z hz using fun j => hq (y j)
  have hd : ∀ i, m i - ∑ j, a i j • z j ∈ I • (⊤ : Submodule A M) := by
    intro i
    rw [← hker, mem_ker, map_sub, show q (m i) = _ from hy i, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hz, ← ha, algebraMap_smul]
  have hsum : ∑ i, m i ⊗ₜ[A] v i = ∑ i, (m i - ∑ j, a i j • z j) ⊗ₜ[A] v i +
      ∑ j, z j ⊗ₜ[A] (∑ i, a i j • v i) := by
    simp only [sub_tmul, sum_tmul, tmul_sum, smul_tmul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun j i => z j ⊗ₜ[A] (a i j • v i))]
    abel
  rw [hsum]
  refine add_mem (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun j _ => ?_)
  · refine Submodule.smul_induction_on (p := fun d => d ⊗ₜ[A] v i ∈
      range ((Submodule.comap f I).subtype.lTensor M)) (hd i) ?_ ?_
    · intro r hr n _
      refine ⟨n ⊗ₜ ⟨r • v i, ?_⟩, ?_⟩
      · simpa using I.mul_mem_right _ hr
      · simp [smul_tmul]
    · intro d e hd he
      rw [add_tmul]
      exact add_mem hd he
  · refine ⟨z j ⊗ₜ ⟨∑ i, a i j • v i, ?_⟩, by simp⟩
    rw [Submodule.mem_comap, ← hI]
    change algebraMap A C _ = 0
    rw [← hc j]
    simp [map_sum, ha, mul_comm]

theorem relationsLift_pow {π : A} (h : RelationsLift (Ideal.span {π}) M)
    (hreg : IsSMulRegular M π) (k : ℕ) : RelationsLift (Ideal.span {π} ^ k) M := by
  induction k with
  | zero =>
    intro F _ _ f x _
    refine range_lTensor_le LinearMap.id _ (by simp) ⟨x, by simp⟩
  | succ k ih =>
    intro F _ _ f x hx
    obtain ⟨x₁, hx₁⟩ := h F f x
      (Submodule.smul_mono_left (Ideal.pow_le_self k.succ_ne_zero) hx)
    let G : Submodule A (F × A) := ker (f ∘ₗ fst A F A - π • snd A F A)
    have hG : ∀ g : G, f g.1.1 = π * g.1.2 := fun g => by
      have : f g.1.1 - π * g.1.2 = 0 := g.2
      exact sub_eq_zero.mp this
    let s : G →ₗ[A] F := fst A F A ∘ₗ G.subtype
    let g : G →ₗ[A] A := snd A F A ∘ₗ G.subtype
    have hs : range s = Submodule.comap f (Ideal.span {π}) := by
      ext v
      simp only [mem_range, Submodule.mem_comap, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨_, hG y⟩
      · rintro ⟨c, hc⟩
        exact ⟨⟨(v, c), by simp [G, hc]⟩, rfl⟩
    have hx₂ : x ∈ range (s.lTensor M) := by
      rw [lTensor_range, hs]
      exact ⟨x₁, hx₁⟩
    obtain ⟨x₂, rfl⟩ := hx₂
    have hfs : f ∘ₗ s = π • g := by
      ext y
      exact hG y
    rw [← lTensor_comp_apply, hfs, lTensor_smul, LinearMap.smul_apply, map_smul, Ideal.span_singleton_pow,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨m, -, hm⟩ := hx
    rw [pow_succ', mul_smul] at hm
    obtain ⟨x₃, rfl⟩ := ih G g x₂ (by
      rw [← hreg hm]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) k)
        Submodule.mem_top)
    rw [← lTensor_comp_apply]
    refine range_lTensor_le _ _ (fun y => ?_) ⟨x₃, rfl⟩
    have := y.2
    change f (s y) ∈ Ideal.span {π} ^ (k + 1)
    rw [← comp_apply, hfs, pow_succ']
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self π) this

theorem flat_of_relationsLift [IsNoetherianRing A] (B : Type v) [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] {I : Ideal A}
    (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) (h : ∀ n, RelationsLift (I ^ n) M) :
    Module.Flat A M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  rw [← ker_eq_bot, eq_bot_iff]
  intro x hx
  have : Module.Finite B (M ⊗[A] J) :=
    Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange A B B M J)
  have key := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⊗[A] J) _ hI
  have hx' : x ∈ (⊥ : Submodule B (M ⊗[A] J)) := by
    rw [← key, Submodule.mem_iInf]
    intro n
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (M := A) I J
    obtain ⟨y, rfl⟩ := h (n + k) J J.subtype x (by rw [mem_ker.mp hx]; simp)
    clear hx
    induction y with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul m j =>
      obtain ⟨⟨j, hj⟩, hj'⟩ := j
      have h1 : j ∈ I ^ n • (J : Submodule A A) := by
        have := hk (n + k) (by omega)
        rw [Nat.add_sub_cancel] at this
        refine Submodule.smul_mono le_rfl inf_le_right (this.le ⟨?_, hj⟩)
        simpa using hj'
      have h2 : (⟨j, hj⟩ : J) ∈ I ^ n • (⊤ : Submodule A J) := by
        rwa [Submodule.mem_smul_top_iff]
      simp only [lTensor_tmul, Submodule.subtype_apply]
      refine Submodule.smul_induction_on (p := fun d : J => m ⊗ₜ[A] d ∈
        (I.map (algebraMap A B)) ^ n • (⊤ : Submodule B (M ⊗[A] J))) h2 ?_ ?_
      · intro r hr d _
        rw [tmul_smul, ← algebraMap_smul B r]
        refine Submodule.smul_mem_smul ?_ Submodule.mem_top
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hr
      · intro d e hd he
        rw [tmul_add]
        exact add_mem hd he
  simpa using hx'

theorem relationsLift_of_square {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] {I : Ideal A} (p : A →+* C) (q : B →+* D) (ψ : C →+* D)
    (hp : Function.Surjective p) (hq : Function.Surjective q) (hpI : RingHom.ker p = I)
    (hqI : RingHom.ker q = I.map (algebraMap A B)) (hsq : ψ.comp p = q.comp (algebraMap A B))
    (hψ : ψ.Flat) : RelationsLift I B := by
  letI := p.toAlgebra
  letI := ψ.toAlgebra
  letI := (q.comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' hsq.symm
  have : Module.Flat C D := hψ
  let q' : B →ₐ[A] D := { q with commutes' := fun _ => rfl }
  refine relationsLift_of_flat (C := C) hp hpI q'.toLinearMap hq ?_
  rw [Ideal.smul_top_eq_map, ← hqI]
  rfl

end LocalFlat

open IsLocalRing

section LocalCriterion

theorem flat_of_flat_quotient_pow {A : Type u} (B : Type v) {M : Type w} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B] [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] [Module.Finite B M] {I : Ideal A}
    (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : ∀ n : ℕ, Module.Flat (A ⧸ I ^ n) (M ⧸ (I ^ n • ⊤ : Submodule A M))) :
    Module.Flat A M :=
  LocalFlat.flat_of_relationsLift B hI fun n =>
    have := h n
    LocalFlat.relationsLift_of_flat (C := A ⧸ I ^ n) Ideal.Quotient.mk_surjective
      Ideal.mk_ker (Submodule.mkQ _) (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _)

theorem flat_of_isSMulRegular_of_flat_quotient {A : Type u} (B : Type v) {M : Type w} [CommRing A]
    [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B] [AddCommGroup M]
    [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M] {π : A}
    (hπ : algebraMap A B π ∈ Ideal.jacobson (⊥ : Ideal B)) (hreg : IsSMulRegular M π)
    [Module.Flat (A ⧸ Ideal.span {π}) (M ⧸ (Ideal.span {π} • ⊤ : Submodule A M))] :
    Module.Flat A M :=
  LocalFlat.flat_of_relationsLift B (I := Ideal.span {π})
    (by rwa [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem])
    (LocalFlat.relationsLift_pow
      (LocalFlat.relationsLift_of_flat (C := A ⧸ Ideal.span {π}) Ideal.Quotient.mk_surjective
        Ideal.mk_ker (Submodule.mkQ _) (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _)) hreg)

variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]

theorem ringHom_flat_of_flat_quotientMap_pow (φ : A →+* B) {I : Ideal A} {J : Ideal B}
    (hIJ : I.map φ = J) (hJ : J ≤ Ideal.jacobson ⊥) (hle : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap φ)
    (h : ∀ n : ℕ, (Ideal.quotientMap (J ^ n) φ (hle n)).Flat) : φ.Flat := by
  letI := φ.toAlgebra
  refine LocalFlat.flat_of_relationsLift B (I := I) (hIJ.le.trans hJ) fun n => ?_
  refine LocalFlat.relationsLift_of_square (Ideal.Quotient.mk (I ^ n)) (Ideal.Quotient.mk (J ^ n))
    _ Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective Ideal.mk_ker ?_ ?_ (h n)
  · rw [Ideal.mk_ker, Ideal.map_pow, ← hIJ]
    rfl
  · exact Ideal.quotientMap_comp_mk (hle n)

theorem ringHom_flat_of_flat_reduction {C D : Type*} [CommRing C] [CommRing D] (φ : A →+* B)
    {π : A} (hπ : φ π ∈ Ideal.jacobson (⊥ : Ideal B)) (hreg : IsSMulRegular B (φ π))
    (p : A →+* C) (q : B →+* D) (ψ : C →+* D)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hpπ : RingHom.ker p = Ideal.span {π}) (hqπ : RingHom.ker q = Ideal.span {φ π})
    (hsq : ψ.comp p = q.comp φ) (hψ : ψ.Flat) : φ.Flat := by
  letI := φ.toAlgebra
  have hmap : (Ideal.span {π}).map (algebraMap A B) = Ideal.span {φ π} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  refine LocalFlat.flat_of_relationsLift B (I := Ideal.span {π})
    (by rwa [hmap, Ideal.span_singleton_le_iff_mem]) (LocalFlat.relationsLift_pow ?_ hreg)
  exact LocalFlat.relationsLift_of_square p q ψ hp hq hpπ (hqπ.trans hmap.symm) hsq hψ

variable {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra T A] [Algebra T B] [IsLocalRing B] [IsLocalHom (algebraMap T B)] [Module.Flat T B]

theorem flat_of_flat_reduction_dvr {C D : Type*} [CommRing C] [CommRing D] (φ : A →ₐ[T] B)
    (p : A →+* C) (q : B →+* D) (ψ : C →+* D)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hp𝔪 : RingHom.ker p = (maximalIdeal T).map (algebraMap T A))
    (hq𝔪 : RingHom.ker q = (maximalIdeal T).map (algebraMap T B))
    (hsq : ψ.comp p = q.comp φ) (hψ : ψ.Flat) : (φ : A →+* B).Flat := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have h𝔪 := hπ.maximalIdeal_eq
  have hφ : (φ : A →+* B) (algebraMap T A π) = algebraMap T B π := φ.commutes π
  refine ringHom_flat_of_flat_reduction (φ : A →+* B) (π := algebraMap T A π) ?_ ?_ p q ψ hp hq
    ?_ ?_ hsq hψ
  · rw [hφ]
    exact maximalIdeal_le_jacobson _ (map_nonunit _ _ hπ.not_isUnit)
  · rw [hφ]
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
      (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
    intro x y hxy
    apply this
    simpa [Algebra.smul_def] using hxy
  · rw [hp𝔪, h𝔪, Ideal.map_span, Set.image_singleton]
  · rw [hq𝔪, h𝔪, Ideal.map_span, Set.image_singleton, hφ]

theorem flat_of_flat_quotientMap_dvr (φ : A →ₐ[T] B)
    (hle : (maximalIdeal T).map (algebraMap T A) ≤
      ((maximalIdeal T).map (algebraMap T B)).comap (φ : A →+* B))
    (h : (Ideal.quotientMap _ (φ : A →+* B) hle).Flat) : (φ : A →+* B).Flat :=
  flat_of_flat_reduction_dvr φ (Ideal.Quotient.mk _) (Ideal.Quotient.mk _) _
    Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective Ideal.mk_ker Ideal.mk_ker
    (Ideal.quotientMap_comp_mk hle) h

theorem ker_includeRight_quotient {T : Type*} (A : Type*) [CommRing T] [CommRing A] [Algebra T A]
    (I : Ideal T) :
    RingHom.ker ((Algebra.TensorProduct.includeRight : A →ₐ[T] (T ⧸ I) ⊗[T] A) :
      A →+* (T ⧸ I) ⊗[T] A) = I.map (algebraMap T A) := by
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem,
    ← map_eq_zero_iff _ (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).injective,
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  rfl

theorem flat_of_flat_residueField_baseChange_dvr (φ : A →ₐ[T] B)
    (h : (Algebra.TensorProduct.map (AlgHom.id T (ResidueField T)) φ :
      ResidueField T ⊗[T] A →+* ResidueField T ⊗[T] B).Flat) : (φ : A →+* B).Flat :=
  flat_of_flat_reduction_dvr φ
    (Algebra.TensorProduct.includeRight : A →ₐ[T] ResidueField T ⊗[T] A)
    (Algebra.TensorProduct.includeRight : B →ₐ[T] ResidueField T ⊗[T] B) _
    (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
    (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
    (ker_includeRight_quotient A (maximalIdeal T)) (ker_includeRight_quotient B (maximalIdeal T))
    (by ext a; simp) h

end LocalCriterion

section Endomorphism

variable {A : Type*} [CommRing A]

theorem ringHom_injective_of_surjective [IsNoetherianRing A] (φ : A →+* A)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  let c : ℕ →o Ideal A := ⟨fun n => RingHom.ker (φ ^ n), monotone_nat_of_le_succ fun n x hx => by
    rw [RingHom.mem_ker] at hx ⊢
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, hx, map_zero]⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherianRing A› c
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, (φ ^ n) y = x := by
    rw [RingHom.coe_pow]
    exact hφ.iterate n x
  have : y ∈ c (n + 1) := by
    change (φ ^ (n + 1)) y = 0
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, hx]
  rw [← hn (n + 1) n.le_succ] at this
  exact this

variable {B : Type*} [CommRing B] {φ : A →+* B} {I : Ideal A} {J : Ideal B}

theorem pow_le_comap_pow_of_le (hle : I ≤ J.comap φ) (n : ℕ) : I ^ n ≤ (J ^ n).comap φ :=
  (Ideal.pow_right_mono hle n).trans (Ideal.le_comap_pow φ n)

theorem exists_sub_mem_pow_succ (hle : I ≤ J.comap φ) (h₀ : ∀ b, ∃ a, φ a - b ∈ J)
    (h₁ : ∀ y ∈ J, ∃ x ∈ I, φ x - y ∈ J ^ 2) (n : ℕ) :
    ∀ y ∈ J ^ n, ∃ x ∈ I ^ n, φ x - y ∈ J ^ (n + 1) := by
  induction n with
  | zero =>
    intro y _
    obtain ⟨a, ha⟩ := h₀ y
    exact ⟨a, by simp, by simpa using ha⟩
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun p hp q hq => ?_) (fun y1 y2 h₁' h2' => ?_)
    · obtain ⟨xp, hxp, hp'⟩ := ih p hp
      obtain ⟨xq, hxq, hq'⟩ := h₁ q hq
      refine ⟨xp * xq, by rw [pow_succ]; exact Ideal.mul_mem_mul hxp hxq, ?_⟩
      have e : φ (xp * xq) - p * q = (φ xp - p) * φ xq + p * (φ xq - q) := by
        rw [map_mul]
        ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hp' (Ideal.mem_comap.1 (hle hxq))
      · rw [show n + 1 + 1 = n + 2 from rfl, pow_add]
        exact Ideal.mul_mem_mul hp hq'
    · obtain ⟨x1, hx1, e1⟩ := h₁'
      obtain ⟨x2, hx2, e2⟩ := h2'
      refine ⟨x1 + x2, Ideal.add_mem _ hx1 hx2, ?_⟩
      have e : φ (x1 + x2) - (y1 + y2) = (φ x1 - y1) + (φ x2 - y2) := by
        rw [map_add]
        ring
      rw [e]
      exact Ideal.add_mem _ e1 e2

theorem quotientMap_pow_surjective (hle : I ≤ J.comap φ) (h₀ : ∀ b, ∃ a, φ a - b ∈ J)
    (h₁ : ∀ y ∈ J, ∃ x ∈ I, φ x - y ∈ J ^ 2) (n : ℕ) :
    Function.Surjective (Ideal.quotientMap (J ^ n) φ (pow_le_comap_pow_of_le hle n)) := by
  have key : ∀ b, ∃ a, φ a - b ∈ J ^ n := by
    induction n with
    | zero => intro b; exact ⟨0, by simp⟩
    | succ n ih =>
      intro b
      obtain ⟨a, ha⟩ := ih b
      obtain ⟨x, -, hx⟩ := exists_sub_mem_pow_succ hle h₀ h₁ n _ ha
      refine ⟨a - x, ?_⟩
      have : φ (a - x) - b = -(φ x - (φ a - b)) := by
        rw [map_sub]; ring
      rw [this]
      exact neg_mem hx
  intro b
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨a, ha⟩ := key b
  exact ⟨Ideal.Quotient.mk _ a, by rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]; exact ha⟩

variable [IsNoetherianRing A] {φ : A →+* A}

theorem quotientMap_pow_bijective (hle : I ≤ I.comap φ) (h₀ : ∀ b, ∃ a, φ a - b ∈ I)
    (h₁ : ∀ y ∈ I, ∃ x ∈ I, φ x - y ∈ I ^ 2) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (I ^ n) φ (pow_le_comap_pow_of_le hle n)) :=
  ⟨ringHom_injective_of_surjective _ (quotientMap_pow_surjective hle h₀ h₁ n),
    quotientMap_pow_surjective hle h₀ h₁ n⟩

theorem flat_of_surjective_quotient_sq (hI : I ≤ Ideal.jacobson ⊥) (hle : I ≤ I.comap φ)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ I) (h₁ : ∀ y ∈ I, ∃ x ∈ I, φ x - y ∈ I ^ 2) : φ.Flat := by
  refine ringHom_flat_of_flat_quotientMap_pow φ ?_ hI (pow_le_comap_pow_of_le hle) fun n =>
    RingHom.Flat.of_bijective (quotientMap_pow_bijective hle h₀ h₁ n)
  refine le_antisymm (Ideal.map_le_of_le_comap hle)
    (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) hI fun y hy => ?_)
  obtain ⟨x, hx, hxy⟩ := h₁ y hy
  rw [show y = φ x - (φ x - y) by ring]
  refine sub_mem (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hx)) (Submodule.mem_sup_right ?_)
  rwa [smul_eq_mul, ← pow_two]


end Endomorphism

section Descent

variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

theorem ringHom_flat_of_comp_faithfullyFlat {φ : A →+* B} {β : B →+* B'}
    (hβ : β.FaithfullyFlat) (h : (β.comp φ).Flat) : φ.Flat := by
  algebraize [φ, β, β.comp φ]
  rw [RingHom.Flat, Module.Flat.iff_lTensor_injective']
  intro J
  change Function.Injective (AlgebraTensorModule.lTensor B B J.subtype)
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective B B']
  have : (LinearMap.lTensor B' (AlgebraTensorModule.lTensor B B J.subtype)) =
      (AlgebraTensorModule.cancelBaseChange A B B B' A).symm.toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor B B' J.subtype ∘ₗ
          (AlgebraTensorModule.cancelBaseChange A B B B' J).toLinearMap := by
    ext
    simp
  rw [this]
  simpa using Module.Flat.lTensor_preserves_injective_linearMap (M := B') J.subtype
    J.injective_subtype

theorem ringHom_flat_of_square {φ : A →+* B} {φ' : A' →+* B'} {α : A →+* A'} {β : B →+* B'}
    (hsq : φ'.comp α = β.comp φ) (hα : α.Flat) (hβ : β.FaithfullyFlat) (hφ' : φ'.Flat) :
    φ.Flat :=
  ringHom_flat_of_comp_faithfullyFlat hβ (hsq ▸ hα.comp hφ')

theorem ringHom_flat_of_square_of_isLocalHom [IsLocalRing B] [IsLocalRing B'] {φ : A →+* B}
    {φ' : A' →+* B'} {α : A →+* A'} {β : B →+* B'} [IsLocalHom β]
    (hsq : φ'.comp α = β.comp φ) (hα : α.Flat) (hβ : β.Flat) (hφ' : φ'.Flat) : φ.Flat := by
  refine ringHom_flat_of_square hsq hα ?_ hφ'
  algebraize [β]
  have : IsLocalHom (algebraMap B B') := ‹IsLocalHom β›
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem ringHom_faithfullyFlat_comp {f : A →+* B} {g : B →+* B'} (hf : f.FaithfullyFlat)
    (hg : g.FaithfullyFlat) : (g.comp f).FaithfullyFlat := by
  algebraize [f, g, g.comp f]
  exact Module.FaithfullyFlat.trans A B B'

theorem includeRight_faithfullyFlat (k K B : Type*) [CommRing k] [CommRing K] [CommRing B]
    [Algebra k K] [Algebra k B] [Module.FaithfullyFlat k K] :
    ((Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) : B →+* K ⊗[k] B).FaithfullyFlat := by
  have h := ringHom_faithfullyFlat_comp (f := algebraMap B (B ⊗[k] K))
    (g := (Algebra.TensorProduct.comm k B K : B ⊗[k] K →+* K ⊗[k] B))
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    (.of_bijective (Algebra.TensorProduct.comm k B K).bijective)
  exact h

theorem flat_of_flat_baseChange {k : Type*} (K : Type*) [CommRing k] [CommRing K] [Algebra k K]
    [Module.FaithfullyFlat k K] [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B)
    (h : (Algebra.TensorProduct.map (AlgHom.id k K) φ : K ⊗[k] A →+* K ⊗[k] B).Flat) :
    (φ : A →+* B).Flat :=
  ringHom_flat_of_square (by ext a; simp) (includeRight_faithfullyFlat k K A).flat
    (includeRight_faithfullyFlat k K B) h

end Descent


end RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

end
