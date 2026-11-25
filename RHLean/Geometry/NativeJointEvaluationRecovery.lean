import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Simultaneous integral recovery on a chosen frame

For a lattice `L`, the decoded map `E` and every competing coordinate `C`
are evaluated on the same element of `L`. On a nonsingular square frame,
entrywise tests on the two adjugate products characterize the existence of
an integral decoder on that frame. They retain common factors in the minors.

In the community `SrcTests` (revision `251c7b0`, `ScaleEdges/ManyEdges.lean`),
source sections have divisibility on competing outgoing edges. A dual test
belongs to the local lattices of the competing incoming edges. Applying the
criterion on either side requires integral coordinates for that side's
actual lattice and incidence.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace RHLean.Geometry.NativeJointEvaluationRecovery

section BlockImage

variable {O L U V : Type*} [CommRing O] [AddCommGroup L] [Module O L]
  [AddCommGroup U] [Module O U] [AddCommGroup V] [Module O V]

private theorem mem_blockImage_iff (E : L →ₗ[O] U) (C : L →ₗ[O] V)
    (K : Submodule O V) (y : U) :
    (y, (0 : V)) ∈ LinearMap.range (E.prod C) ⊔ (⊥ : Submodule O U).prod K ↔
      y ∈ (K.comap C).map E := by
  constructor
  · intro h
    obtain ⟨v, hv, ⟨z, w⟩, hw, hsum⟩ := Submodule.mem_sup.mp h
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hv
    change z ∈ (⊥ : Submodule O U) ∧ w ∈ K at hw
    have hz : z = 0 := (Submodule.mem_bot O).mp hw.1
    subst z
    have hy : E x + 0 = y := congrArg Prod.fst hsum
    have hc : C x + w = 0 := congrArg Prod.snd hsum
    refine Submodule.mem_map.mpr ⟨x, ?_, by simpa only [add_zero] using hy⟩
    change C x ∈ K
    rw [eq_neg_of_add_eq_zero_left hc]
    exact K.neg_mem hw.2
  · intro h
    obtain ⟨x, hx, hy⟩ := Submodule.mem_map.mp h
    refine Submodule.mem_sup.mpr ⟨(E x, C x), ⟨x, rfl⟩, ((0 : U), -C x),
      ⟨Submodule.zero_mem _, K.neg_mem hx⟩, ?_⟩
    change (E x + 0, C x + -C x) = (y, 0)
    rw [add_zero, add_neg_cancel, hy]

/-- Take `P = p^D O^r` and `K = ϖ^c O^s` for the selected and competing
coordinates. The domain `L` can itself be an integral submodule. -/
theorem recovery_iff_blockImage (E : L →ₗ[O] U) (C : L →ₗ[O] V)
    (P : Submodule O U) (K : Submodule O V) :
    P ≤ (K.comap C).map E ↔
      P.prod (⊥ : Submodule O V) ≤ LinearMap.range (E.prod C) ⊔ (⊥ : Submodule O U).prod K := by
  constructor
  · rintro h ⟨y, z⟩ hz
    change y ∈ P ∧ z ∈ (⊥ : Submodule O V) at hz
    have hzero : z = 0 := (Submodule.mem_bot O).mp hz.2
    subst z
    exact (mem_blockImage_iff E C K y).mpr (h hz.1)
  · intro h y hy
    apply (mem_blockImage_iff E C K y).mp
    exact h (show (y, (0 : V)) ∈ P.prod (⊥ : Submodule O V) from ⟨hy, Submodule.zero_mem _⟩)

end BlockImage

section PrimitiveTests

open Module

/-- Smith step of Alpöge's actual primitive-test recovery, specialized to an
integral evaluation image. Adapted from
leanprover-community/riemann-hypothesis@8e5cefee,
Formalism/SharpRestriction/GrowthBounds/ScaleEdges/DvdOfAdd.lean (smith_mem).
The submodule S is the actual image, not an assumed full coordinate lattice. -/
theorem smith_mem_of_primitive_tests
    {O I : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [IsLocalRing O] [Fintype I] (S : Submodule O (I → O)) (a : O)
    (h : ∀ c : I → O, (∃ i, IsUnit (c i)) →
      ∃ s ∈ S, (∑ i, c i * s i) ∣ a) (x : I → O) : a • x ∈ S := by
  classical
  obtain ⟨n, snf⟩ := S.smithNormalForm (Pi.basisFun O I)
  have key : ∀ j, a • snf.bM j ∈ S := by
    intro j
    set φ : I → O := fun i => snf.bM.coord j (Pi.single i 1) with hφdef
    have hφ : ∀ y : I → O, ∑ i, φ i * y i = snf.bM.coord j y := by
      intro y
      conv_rhs => rw [show y = ∑ i, y i • Pi.single i (1 : O) by
        ext k; simp [Finset.sum_apply, Pi.single_apply]]
      simp only [map_sum, map_smul, smul_eq_mul, hφdef, mul_comm]
    have hprim : ∃ i, IsUnit (φ i) := by
      by_contra! hne
      have h1 : snf.bM.coord j (snf.bM j) = 1 := by simp
      rw [← hφ] at h1
      have hmem : ∑ i, φ i * snf.bM j i ∈ IsLocalRing.maximalIdeal O :=
        Ideal.sum_mem _ fun i _ =>
          Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i))
      rw [h1] at hmem
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hmem)
    obtain ⟨s, hs, hsd⟩ := h φ hprim
    rw [hφ] at hsd
    have hs' : s = ∑ k, snf.bN.repr ⟨s, hs⟩ k • snf.a k • snf.bM (snf.f k) := by
      have hrepr := congrArg Subtype.val (snf.bN.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, snf.snf] at hrepr
      exact hrepr.symm
    have hc : snf.bM.coord j s =
        ∑ k, snf.bN.repr ⟨s, hs⟩ k * snf.a k * (if snf.f k = j then 1 else 0) := by
      conv_lhs => rw [hs']
      simp [map_sum, map_smul, Finsupp.single_apply]
    by_cases hj : ∃ k, snf.f k = j
    · obtain ⟨k0, rfl⟩ := hj
      have hc0 : snf.bM.coord (snf.f k0) s = snf.bN.repr ⟨s, hs⟩ k0 * snf.a k0 := by
        rw [hc, Finset.sum_eq_single k0]
        · simp
        · intro k _ hk
          simp [snf.f.injective.ne hk]
        · simp
      rw [hc0] at hsd
      obtain ⟨t, ht⟩ := (Dvd.intro_left _ rfl :
        snf.a k0 ∣ snf.bN.repr ⟨s, hs⟩ k0 * snf.a k0).trans hsd
      rw [ht, mul_comm, mul_smul, ← snf.snf k0]
      exact S.smul_mem t (snf.bN k0).2
    · have hj' : ∀ k, snf.f k ≠ j := fun k hk => hj ⟨k, hk⟩
      have hc0 : snf.bM.coord j s = 0 := by
        rw [hc]
        exact Finset.sum_eq_zero fun k _ => by simp [hj' k]
      rw [hc0, zero_dvd_iff] at hsd
      simp [hsd]
  rw [← snf.bM.sum_repr x, Finset.smul_sum]
  refine S.sum_mem fun j _ => ?_
  rw [smul_comm]
  exact S.smul_mem _ (key j)

/-- The original goodRank primitive-test mechanism on the constrained native
lattice. The chosen test may depend on the primitive coefficients, as in
SrcTests. The competing constraints are imposed before taking the image.
No separately constructed square frame or invertible minor is required. -/
theorem recovery_of_primitive_tests
    {O L I V : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [IsLocalRing O] [Fintype I] [AddCommGroup L] [Module O L]
    [AddCommGroup V] [Module O V]
    (E : L →ₗ[O] (I → O)) (C : L →ₗ[O] V) (K : Submodule O V) (a : O)
    (h : ∀ c : I → O, (∃ i, IsUnit (c i)) →
      ∃ v : L, C v ∈ K ∧ (∑ i, c i * E v i) ∣ a) :
    ∀ y : I → O, ∃ v : L, C v ∈ K ∧ E v = a • y := by
  let S := (K.comap C).map E
  have hS : ∀ c : I → O, (∃ i, IsUnit (c i)) →
      ∃ s ∈ S, (∑ i, c i * s i) ∣ a := by
    intro c hc
    obtain ⟨v, hv, hdiv⟩ := h c hc
    exact ⟨E v, Submodule.mem_map.mpr ⟨v, hv, rfl⟩, hdiv⟩
  intro y
  obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp
    (show a • y ∈ (K.comap C).map E from smith_mem_of_primitive_tests S a hS y)
  exact ⟨v, hv, he⟩

/-- An integral comparison on each primitive test suffices. The comparison maps
live on the same lattice. Their competing read may differ inside K, and their
selected pairing may differ by a multiple of a * π. For a = p^D in a DVR,
one uniformizer digit beyond the valuation of p^D preserves the depth D. -/
theorem recovery_of_congruent_primitive_tests
    {O L I V : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [IsLocalRing O] [Fintype I] [AddCommGroup L] [Module O L]
    [AddCommGroup V] [Module O V]
    (E E₀ : L →ₗ[O] (I → O)) (C C₀ : L →ₗ[O] V)
    (K : Submodule O V) (a π : O) (hπ : π ∈ IsLocalRing.maximalIdeal O)
    (htest : ∀ c : I → O, (∃ i, IsUnit (c i)) → ∃ v : L,
      C₀ v ∈ K ∧ C v - C₀ v ∈ K ∧ (∑ i, c i * E₀ v i) ∣ a ∧
      a * π ∣ (∑ i, c i * E v i) - (∑ i, c i * E₀ v i)) :
    ∀ y : I → O, ∃ v : L, C v ∈ K ∧ E v = a • y := by
  apply recovery_of_primitive_tests E C K a
  intro c hc
  obtain ⟨v, hv, hdiff, hdiv, hcong⟩ := htest c hc
  obtain ⟨b, hb⟩ := hdiv
  obtain ⟨z, hz⟩ := hcong
  let s := ∑ i, c i * E₀ v i
  have hab : a = s * b := hb
  have hunit : IsUnit (1 + π * (b * z)) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_add, map_one, map_mul, (IsLocalRing.residue_eq_zero_iff π).mpr hπ,
      zero_mul, add_zero]
    exact one_ne_zero
  have he : (∑ i, c i * E v i) = s * (1 + π * (b * z)) := by
    calc
      _ = s + (a * π) * z := by
        have h : (∑ i, c i * E v i) - s = (a * π) * z := hz
        exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
      _ = _ := by rw [hab]; ring
  refine ⟨v, ?_, ?_⟩
  · simpa only [sub_add_cancel] using K.add_mem hdiff hv
  · rw [he, hunit.mul_right_dvd]
    exact ⟨b, hab⟩

end PrimitiveTests

section Minors

variable {O I J : Type*} [CommRing O] [IsDomain O] [Fintype I] [DecidableEq I]

/-- On this square frame, set `a = p^D`, `b = ϖ^c`. The first test makes
`a A⁻¹` integral; the second makes every entry of its image under `B`
divisible by `b`. The proof takes place entirely in the integral domain. -/
theorem decoderMatrix_iff_minors (A : Matrix I I O) (B : Matrix J I O)
    (a b : O) (hdet : A.det ≠ 0) :
    (∃ T : Matrix I I O, A * T = a • (1 : Matrix I I O) ∧ ∀ j i, b ∣ (B * T) j i) ↔
      (∀ i k, A.det ∣ a * A.adjugate i k) ∧
      (∀ j k, A.det * b ∣ a * (B * A.adjugate) j k) := by
  have transport (T : Matrix I I O) (hs : A.det • T = a • A.adjugate) :
      A.det • (B * T) = a • (B * A.adjugate) := by
    calc A.det • (B * T) = B * (A.det • T) := (Matrix.mul_smul B A.det T).symm
         _ = a • (B * A.adjugate) := by rw [hs, Matrix.mul_smul]
  constructor
  · rintro ⟨T, hT, hB⟩
    have hs : A.det • T = a • A.adjugate := by
      calc A.det • T = (A.adjugate * A) * T := by
             rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
           _ = A.adjugate * (A * T) := Matrix.mul_assoc _ _ _
           _ = a • A.adjugate := by rw [hT, Matrix.mul_smul, Matrix.mul_one]
    constructor
    · intro i k
      exact ⟨T i k, (congrFun (congrFun hs i) k).symm⟩
    · intro j k
      obtain ⟨z, hz⟩ := hB j k
      refine ⟨z, ?_⟩
      calc a * (B * A.adjugate) j k = A.det * (B * T) j k :=
             (congrFun (congrFun (transport T hs) j) k).symm
           _ = (A.det * b) * z := by rw [hz, mul_assoc]
  · rintro ⟨hA, hB⟩
    choose t ht using hA
    let T : Matrix I I O := Matrix.of t
    have hs : A.det • T = a • A.adjugate := by
      ext i k
      exact (ht i k).symm
    have hc : A.det • (A * T) = A.det • (a • (1 : Matrix I I O)) := by
      calc A.det • (A * T) = A * (A.det • T) := (Matrix.mul_smul A A.det T).symm
           _ = a • (A.det • (1 : Matrix I I O)) := by
             rw [hs, Matrix.mul_smul, Matrix.mul_adjugate]
           _ = A.det • (a • (1 : Matrix I I O)) := smul_comm _ _ _
    refine ⟨T, ?_, ?_⟩
    · ext i k
      exact mul_left_cancel₀ hdet (congrFun (congrFun hc i) k)
    · intro j k
      obtain ⟨z, hz⟩ := hB j k
      refine ⟨z, mul_left_cancel₀ hdet ?_⟩
      calc A.det * (B * T) j k = a * (B * A.adjugate) j k :=
             congrFun (congrFun (transport T hs) j) k
           _ = A.det * (b * z) := hz.trans (mul_assoc _ _ _)

end Minors

section Frame

variable {O L I J : Type*} [CommRing O] [AddCommGroup L] [Module O L]

/-- Columns are evaluations of a single integral family. -/
def evaluationMatrix (F : L →ₗ[O] (J → O)) (v : I → L) : Matrix J I O :=
  Matrix.of fun j i => F (v i) j

variable [Fintype I]

private theorem eval_linearCombination (F : L →ₗ[O] (J → O)) (v : I → L) (z : I → O) :
    F (Fintype.linearCombination O v z) = (evaluationMatrix F v).mulVec z := by
  rw [Fintype.linearCombination_apply, map_sum]
  funext j
  rw [Finset.sum_apply]
  change (∑ i, F (z i • v i) j) = ∑ i, F (v i) j * z i
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  exact mul_comm _ _

variable [IsDomain O] [DecidableEq I]

/-- One linear lift decodes every vector with all competing coordinates
simultaneously divisible. Both minor tests are computed on the given
integral vectors `v` and the two specified evaluation maps. -/
theorem exists_decoder_of_frame_minors (E : L →ₗ[O] (I → O)) (C : L →ₗ[O] (J → O))
    (v : I → L) (a b : O) (hdet : (evaluationMatrix E v).det ≠ 0)
    (hselected : ∀ i k, (evaluationMatrix E v).det ∣ a * (evaluationMatrix E v).adjugate i k)
    (hcompeting : ∀ j k, (evaluationMatrix E v).det * b ∣
      a * (evaluationMatrix C v * (evaluationMatrix E v).adjugate) j k) :
    ∃ u : (I → O) →ₗ[O] L, ∀ y, E (u y) = a • y ∧ ∀ j, b ∣ C (u y) j := by
  obtain ⟨T, hT, hB⟩ := (decoderMatrix_iff_minors (evaluationMatrix E v)
    (evaluationMatrix C v) a b hdet).mpr ⟨hselected, hcompeting⟩
  refine ⟨(Fintype.linearCombination O v).comp T.mulVecLin, fun y => ⟨?_, ?_⟩⟩
  · change E (Fintype.linearCombination O v (T.mulVec y)) = a • y
    rw [eval_linearCombination, Matrix.mulVec_mulVec, hT, Matrix.smul_mulVec, Matrix.one_mulVec]
  · intro j
    change b ∣ C (Fintype.linearCombination O v (T.mulVec y)) j
    rw [eval_linearCombination, Matrix.mulVec_mulVec]
    change b ∣ ∑ i, (evaluationMatrix C v * T) j i * y i
    exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (hB j i) (y i)

end Frame

section LocalFrame

variable {O L I J : Type*} [CommRing O] [IsLocalRing O] [AddCommGroup L] [Module O L]
  [Fintype I] [DecidableEq I]

/-- Integral lifts whose selected matrix agrees with `a • 1` modulo `a * π`
give an exact decoder. Every competing coordinate stays divisible by `b`.
For `a = p^D` in a DVR with `vπ(p) = e`, the selected error ideal has
uniformizer exponent `e * D + 1`. -/
theorem exists_decoder_of_frame_congruence
    (E : L →ₗ[O] (I → O)) (C : L →ₗ[O] (J → O)) (v : I → L)
    (a b π : O) (hπ : π ∈ IsLocalRing.maximalIdeal O)
    (hselected : ∀ i k, a * π ∣ E (v k) i - a * (1 : Matrix I I O) i k)
    (hcompeting : ∀ j k, b ∣ C (v k) j) :
    ∃ u : (I → O) →ₗ[O] L, ∀ y, E (u y) = a • y ∧ ∀ j, b ∣ C (u y) j := by
  choose z hz using hselected
  let N : Matrix I I O := Matrix.of z
  let U : Matrix I I O := 1 + π • N
  have hEU : evaluationMatrix E v = a • U := by
    ext i k
    change E (v k) i = a * ((1 : Matrix I I O) i k + π * z i k)
    calc
      _ = (a * π) * z i k + a * (1 : Matrix I I O) i k :=
        sub_eq_iff_eq_add.mp (hz i k)
      _ = _ := (add_comm _ _).trans (by rw [mul_add, mul_assoc])
  have hπzero : IsLocalRing.residue O π = 0 := (IsLocalRing.residue_eq_zero_iff π).mpr hπ
  have hNzero : (IsLocalRing.residue O).mapMatrix (π • N) = 0 := by
    ext i k
    change IsLocalRing.residue O (π * N i k) = 0
    rw [map_mul, hπzero, zero_mul]
  have hUres : (IsLocalRing.residue O).mapMatrix U = 1 := by
    change (IsLocalRing.residue O).mapMatrix (1 + π • N) = 1
    rw [map_add, map_one, hNzero, add_zero]
  have hdet : IsUnit U.det := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit U.det).mp
    rw [RingHom.map_det, hUres, Matrix.det_one]
    exact one_ne_zero
  refine ⟨(Fintype.linearCombination O v).comp (U⁻¹).mulVecLin, fun y => ⟨?_, ?_⟩⟩
  · change E (Fintype.linearCombination O v ((U⁻¹).mulVec y)) = a • y
    rw [eval_linearCombination, Matrix.mulVec_mulVec, hEU, Matrix.smul_mul,
      Matrix.mul_nonsing_inv _ hdet, Matrix.smul_mulVec, Matrix.one_mulVec]
  · intro j
    change b ∣ C (Fintype.linearCombination O v ((U⁻¹).mulVec y)) j
    rw [eval_linearCombination]
    change b ∣ ∑ k, C (v k) j * ((U⁻¹).mulVec y) k
    exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (hcompeting j k) _

end LocalFrame

end RHLean.Geometry.NativeJointEvaluationRecovery

end
