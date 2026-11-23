import Mathlib

/-!
# Highest vectors and their dominant integral weights

Finite-dimensional invariant spaces admit actual joint highest vectors.
The sl2 calculation proves dominance from the displayed operator identities
and does not assume a target polynomial spanning theorem.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/`,
`Proofs/CuspFormEvaluations/Sl2NonnegWeightOfHighestWeightVector.lean`;
`Proofs/CuspFormEvaluations/ExistsJointIntEigenvectorOfStable.lean`;
only the declarations used by the native highest-weight construction.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Geometry.NativeTheta

theorem casimir_on_highest {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {m : ℕ} (e : Fin m → Fin m → Module.End K V)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0))
    (v : V) (κ : Fin m → ℤ) (hv : ∀ i j, i < j → e i j v = 0) (hκ : ∀ i, e i i v = (κ i : K) • v) :
    ∑ i, ∑ j, e i j (e j i v) = ((∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ)) : ℤ) : K) • v := by
  have key : ∀ i j, e i j (e j i v) =
      ((if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ) : K) • v := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have h1 := congrArg (fun f : Module.End K V => f v) (he i j j i)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, ↓reduceIte] at h1
      rw [hv i j h, map_zero, sub_zero, hκ, hκ] at h1
      rw [h1, ite_eq_left h]
      push_cast
      rw [sub_smul]
    · subst h
      rw [ite_eq_right (lt_irrefl i), ite_eq_left rfl, hκ, map_smul, hκ, smul_smul]
      push_cast
      rfl
    · rw [hv j i h, map_zero, ite_eq_right (lt_asymm h), ite_eq_right h.ne']
      simp
  have hsum : (∑ i : Fin m, ∑ j : Fin m,
      (if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ)) =
      ∑ i : Fin m, κ i * (κ i + m - 1 - 2 * (i : ℕ)) := by
    have h2 : ∀ i j : Fin m, (if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ) =
        ((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0)) -
          (if i < j then κ j else 0) := by
      intro i j
      by_cases h : i < j
      · simp [h, h.ne]
      · simp [h]
    simp_rw [h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if i < j then κ j else 0)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio,
      nsmul_eq_mul, nsmul_eq_mul]
    have hi := i.isLt
    have hc : ((m - 1 - (i : ℕ) : ℕ) : ℤ) = m - 1 - (i : ℕ) := by omega
    rw [hc]
    ring
  simp_rw [key]
  rw [← hsum, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_sum, Finset.sum_smul]

theorem sl2_nonneg_weight_of_highest_weight_vector {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (E F H : Module.End K V) (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F))
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ w ∈ W, F w ∈ W)
    (v : V) (hvW : v ∈ W) (hv0 : v ≠ 0) (l : ℤ) (hE : E v = 0) (hH : H v = (l : K) • v) : 0 ≤ l := by
  have hHFk : ∀ k : ℕ, H ((F ^ k) v) = ((l : K) - 2 * k) • (F ^ k) v := by
    intro k
    induction k with
    | zero => simp [hH]
    | succ k ih =>
      have h1 := congrArg (fun f : Module.End K V => f ((F ^ k) v)) hHF
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
        LinearMap.add_apply] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [pow_succ', Module.End.mul_apply, h1, ih, map_smul]
      push_cast
      module
  have hEFk : ∀ k : ℕ, E ((F ^ (k + 1)) v) = (((k : K) + 1) * ((l : K) - k)) • (F ^ k) v := by
    intro k
    induction k with
    | zero =>
      have h1 := congrArg (fun f : Module.End K V => f v) hEF
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hE, map_zero, sub_zero] at h1
      simp [h1, hH]
    | succ k ih =>
      have h1 := congrArg (fun f : Module.End K V => f ((F ^ (k + 1)) v)) hEF
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      rw [sub_eq_iff_eq_add] at h1
      have hp : (F ^ (k + 1 + 1)) v = F ((F ^ (k + 1)) v) := by
        rw [pow_succ' F (k + 1), Module.End.mul_apply]
      have hq : F ((F ^ k) v) = (F ^ (k + 1)) v := by
        rw [pow_succ' F k, Module.End.mul_apply]
      rw [hp, h1, ih, map_smul, hq, hHFk, ← add_smul]
      congr 1
      push_cast
      ring
  by_contra hl0
  have hl : l < 0 := not_le.mp hl0
  have hne : ∀ k : ℕ, (F ^ k) v ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using hv0
    | succ k ih =>
      intro h0
      have h1 := hEFk k
      rw [h0, map_zero] at h1
      have hc : ((k : K) + 1) * ((l : K) - k) ≠ 0 := by
        refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
        intro h
        have h3 : ((l : ℤ) : K) = ((k : ℤ) : K) := by
          rw [sub_eq_zero] at h
          rw [h]
          push_cast
          rfl
        have h4 : l = (k : ℤ) := Int.cast_injective h3
        omega
      exact ih ((smul_eq_zero.mp h1.symm).resolve_left hc)
  have hmem : ∀ k : ℕ, (F ^ k) v ∈ W := by
    intro k
    induction k with
    | zero => simpa using hvW
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hW _ ih
  have hli : LinearIndependent K (fun k : Fin (Module.finrank K W + 1) => (F ^ (k : ℕ)) v) := by
    refine Module.End.eigenvectors_linearIndependent' H
      (fun k : Fin (Module.finrank K W + 1) => (l : K) - 2 * ((k : ℕ) : K)) ?_ _
      (fun k => ⟨Module.End.mem_eigenspace_iff.2 (hHFk k), hne k⟩)
    intro a b hab
    have h1 : (2 : K) * ((a : ℕ) : K) = 2 * ((b : ℕ) : K) := sub_right_injective hab
    have h2 : ((a : ℕ) : K) = ((b : ℕ) : K) := mul_left_cancel₀ two_ne_zero h1
    exact Fin.ext (Nat.cast_injective h2)
  have hw : LinearIndependent K
      (fun k : Fin (Module.finrank K W + 1) => (⟨(F ^ (k : ℕ)) v, hmem k⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hli
  have h5 := hw.fintype_card_le_finrank
  simp at h5

theorem highest_weight_antitone {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {m : ℕ} (e : Fin m → Fin m → Module.End K V)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0))
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ i j, ∀ w ∈ W, e i j w ∈ W)
    (v : V) (hvW : v ∈ W) (hv0 : v ≠ 0) (κ : Fin m → ℤ) (hv : ∀ i j, i < j → e i j v = 0) (hκ : ∀ i, e i i v = (κ i : K) • v) : Antitone κ := by
  intro a b hab
  rcases hab.lt_or_eq with h | h
  · have hne : a ≠ b := h.ne
    have hEF : e a b * e b a - e b a * e a b = e a a - e b b := by
      simpa only [↓reduceIte] using he a b b a
    have hHF : (e a a - e b b) * e b a - e b a * (e a a - e b b) = -(e b a + e b a) := by
      have h1 := he a a b a
      have h2 := he b b b a
      simp only [ite_eq_right hne, ↓reduceIte, zero_sub, sub_zero] at h1 h2
      calc (e a a - e b b) * e b a - e b a * (e a a - e b b)
          = (e a a * e b a - e b a * e a a) - (e b b * e b a - e b a * e b b) := by
            rw [sub_mul, mul_sub]
            abel
        _ = -(e b a + e b a) := by
            rw [h1, h2]
            abel
    have hHv : (e a a - e b b) v = (((κ a - κ b : ℤ)) : K) • v := by
      rw [LinearMap.sub_apply, hκ, hκ]
      push_cast
      rw [sub_smul]
    have h0 := sl2_nonneg_weight_of_highest_weight_vector (e a b) (e b a) (e a a - e b b) hEF hHF W
      (hW b a) v hvW hv0 (κ a - κ b) (hv a b h) hHv
    linarith
  · subst h
    exact le_rfl

end RHLean.Geometry.NativeTheta

namespace RHLean.Geometry.NativeTheta

theorem exists_int_eigenvector_of_stable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hf : ⨆ n : ℤ, f.eigenspace (n : K) = ⊤)
    (U : Submodule K V) (hU : ∀ x ∈ U, f x ∈ U) (hU0 : U ≠ ⊥) :
    ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u := by
  classical
  have key : ∀ s : Finset ℤ, ∀ x ∈ U, x ≠ 0 → x ∈ (⨆ n ∈ s, f.eigenspace (n : K)) →
      ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ hx0 hx; simp at hx; exact absurd hx hx0
    | insert a s _ ih =>
      intro x hxU hx0 hx
      by_cases hw : f x - (a : K) • x = 0
      · exact ⟨a, x, hxU, hx0, sub_eq_zero.mp hw⟩
      · refine ih _ (U.sub_mem (hU x hxU) (U.smul_mem _ hxU)) hw ?_
        rw [Finset.iSup_insert, Submodule.mem_sup] at hx
        obtain ⟨y, hy, z, hz, rfl⟩ := hx
        rw [Module.End.mem_eigenspace_iff] at hy
        have h1 : f (y + z) - (a : K) • (y + z) = f z - (a : K) • z := by
          rw [map_add, hy, smul_add]; abel
        rw [h1]
        refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ hz)
        have : (⨆ n ∈ s, f.eigenspace (n : K)) ≤ (⨆ n ∈ s, f.eigenspace (n : K)).comap f := by
          refine iSup₂_le fun n hn => ?_
          intro w hw
          rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.mp hw]
          exact Submodule.smul_mem _ _
            (le_iSup₂ (f := fun n (_ : n ∈ s) => f.eigenspace (n : K)) n hn hw)
        exact this hz
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hx : x ∈ ⨆ n : ℤ, f.eigenspace (n : K) := by rw [hf]; trivial
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
  exact key s x hxU hx0 hs

theorem exists_joint_int_eigenvector_of_stable {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (f : ι → Module.End K V) (hc : ∀ a b, f a * f b = f b * f a)
    (hf : ∀ a, ⨆ n : ℤ, (f a).eigenspace (n : K) = ⊤)
    (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, f a x ∈ W) (hW0 : W ≠ ⊥) :
    ∃ κ : ι → ℤ, ∃ u ∈ W, u ≠ 0 ∧ ∀ a, f a u = (κ a : K) • u := by
  classical
  have key : ∀ s : Finset ι, ∃ U : Submodule K V, U ≤ W ∧ U ≠ ⊥ ∧ (∀ a, ∀ x ∈ U, f a x ∈ U) ∧
      ∃ κ : ι → ℤ, ∀ a ∈ s, ∀ x ∈ U, f a x = (κ a : K) • x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨W, le_rfl, hW0, hW, 0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨U, hUW, hU0, hU, κ, hκ⟩ := ih
      obtain ⟨n, u, huU, hu0, hu⟩ := exists_int_eigenvector_of_stable (f a) (hf a) U (hU a) hU0
      refine ⟨U ⊓ (f a).eigenspace (n : K), inf_le_left.trans hUW, ?_, ?_,
        Function.update κ a n, ?_⟩
      · rw [Submodule.ne_bot_iff]
        exact ⟨u, ⟨huU, Module.End.mem_eigenspace_iff.mpr hu⟩, hu0⟩
      · intro b x hx
        refine ⟨hU b x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h1 := Module.End.mem_eigenspace_iff.mp hx.2
        have h2 := LinearMap.congr_fun (hc a b) x
        simp only [Module.End.mul_apply] at h2
        rw [h2, h1, map_smul]
      · intro b hb x hx
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [Function.update_self]; exact Module.End.mem_eigenspace_iff.mp hx.2
        · have : b ≠ a := fun h => ha (h ▸ hb)
          rw [Function.update_of_ne this]; exact hκ b hb x hx.1
  obtain ⟨U, hUW, hU0, -, κ, hκ⟩ := key Finset.univ
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  exact ⟨κ, x, hUW hxU, hx0, fun a => hκ a (Finset.mem_univ a) x hxU⟩

theorem exists_highest_vector {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [Fintype T] [DecidableEq T] {m : ℕ}
    (e : T → Fin m → Fin m → Module.End K V)
    (he : ∀ t t' i k l, e t i i * e t' k l - e t' k l * e t i i = (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : K) else 0) • e t' k l)
    (hdiag : ⨆ κ : T → Fin m → ℤ, (⨅ t, ⨅ i, Module.End.eigenspace (e t i i) (κ t i : K)) = ⊤)
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ t i j, ∀ w ∈ W, e t i j w ∈ W) (hW0 : W ≠ ⊥) :
    ∃ v ∈ W, v ≠ 0 ∧ (∀ t i j, i < j → e t i j v = 0) ∧ ∃ κ : T → Fin m → ℤ, ∀ t i, e t i i v = (κ t i : K) • v := by
  classical

  obtain ⟨κ₀, u₀, hu₀W, hu₀, hκ₀⟩ := exists_joint_int_eigenvector_of_stable
    (fun a : T × Fin m => e a.1 a.2 a.2)
    (by
      intro a b
      have := he a.1 b.1 a.2 b.2 b.2
      rw [sub_self, ite_self, zero_smul] at this
      exact sub_eq_zero.mp this)
    (by
      intro a
      rw [eq_top_iff, ← hdiag]
      refine iSup_le fun κ => ?_
      exact le_trans ((iInf_le _ a.1).trans (iInf_le _ a.2))
        (le_iSup (fun n : ℤ => (e a.1 a.2 a.2).eigenspace (n : K)) (κ a.1 a.2)))
    W (fun a => hW a.1 a.2 a.2) hW0

  let ht : (T → Fin m → ℤ) → ℤ := fun κ => ∑ t, ∑ i : Fin m, (i : ℤ) * κ t i
  let h : Module.End K V := ∑ t, ∑ i : Fin m, ((i : ℕ) : K) • e t i i
  have hhW : ∀ w ∈ W, h w ∈ W := by
    intro w hw
    simp only [h, LinearMap.sum_apply, LinearMap.smul_apply]
    exact W.sum_mem fun t _ => W.sum_mem fun i _ => W.smul_mem _ (hW t i i w hw)
  have hh : ∀ (κ : T → Fin m → ℤ) (v : V), (∀ t i, e t i i v = (κ t i : K) • v) →
      h v = (ht κ : K) • v := by
    intro κ v hv
    simp only [h, ht, LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_smul]
    push_cast
    simp only [Finset.sum_smul]
  let S : Set ℤ := {n | ∃ κ : T → Fin m → ℤ, ht κ = n ∧
    ∃ v ∈ W, v ≠ 0 ∧ ∀ t i, e t i i v = (κ t i : K) • v}
  have hS : S.Finite := by
    have hfin := Module.End.finite_hasEigenvalue (h.restrict hhW)
    refine (hfin.preimage (f := fun n : ℤ => (n : K)) Int.cast_injective.injOn).subset ?_
    rintro n ⟨κ, rfl, v, hvW, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvW⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (hh κ v hv)
    · exact fun h0 => hv0 (congrArg Subtype.val h0)
  have hSne : S.Nonempty :=
    ⟨_, fun t i => κ₀ (t, i), rfl, u₀, hu₀W, hu₀, fun t i => hκ₀ (t, i)⟩
  obtain ⟨n, ⟨κ, rfl, v, hvW, hv0, hv⟩, hmin⟩ := Set.exists_min_image S id hS hSne
  refine ⟨v, hvW, hv0, ?_, κ, hv⟩
  intro t' k l hkl
  by_contra hne
  let δ : T → Fin m → ℤ := fun t i =>
    if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0)) else 0
  have hmem : ht (κ + δ) ∈ S := by
    refine ⟨κ + δ, rfl, e t' k l v, hW _ _ _ v hvW, hne, fun t i => ?_⟩
    have h1 := LinearMap.congr_fun (he t t' i k l) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hv,
      map_smul] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, ← add_smul, add_comm]
    congr 1
    simp only [δ, Pi.add_apply]
    push_cast
    rfl
  have hδ : ht δ = (k : ℤ) - (l : ℤ) := by
    simp only [ht, δ]
    rw [Finset.sum_eq_single t']
    · simp [mul_sub, Finset.sum_sub_distrib]
    · intro b _ hb; simp [hb]
    · simp
  have hadd : ht (κ + δ) = ht κ + ht δ := by
    simp only [ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have h2 := hmin _ hmem
  have h3 : (k : ℕ) < l := hkl
  simp only [id] at h2
  omega

end RHLean.Geometry.NativeTheta
