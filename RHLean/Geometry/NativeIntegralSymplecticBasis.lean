import Mathlib

/-!
# Integral symplectic bases for actual perfect alternating forms

Over a principal ideal domain, a finite free module with a perfect
alternating form has a symplectic integral basis. The construction first
chooses a maximal principal pairing ideal, splits off its actual
orthogonal rank-two summand, and inducts on the rank. Perfectness then
makes every elementary pairing a unit, so rescaling only basis vectors
normalizes it to one. The original module and form are never replaced.

The final coordinate equivalence uses the source's exact standard form,
with +1 in the upper-right block and -1 in the lower-left block. No level,
period, scheme, moduli or metric-realization hypothesis is used.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/
DualRestrictSurjectiveOfIsTorsionFreeQuotient.lean, the alternating-PID
basis construction through exists_isSymplecticBasis_of_finrank;
src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/
ExistsEquivStdSymp.lean, exists_equiv_stdSymp; and
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/
BaseOver.lean, Out.stdSymp. Unused matrix, isotropic-quotient and
positive-elementary-divisor branches are omitted.
The source mirror states no license; attribution is preserved without
assigning one. No terminal RH theorem or compiled source artifact is imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Module Function
open scoped BigOperators Classical

namespace RHLean.Geometry.NativeIntegralSymplectic


section Defs

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

structure IsSymplecticFamily (B : LinearMap.BilinForm R M) (e f : ι → M) (d : ι → R) : Prop where
  left_left : ∀ i j, B (e i) (e j) = 0
  right_right : ∀ i j, B (f i) (f j) = 0
  left_right_self : ∀ i, B (e i) (f i) = d i
  left_right_ne : ∀ i j, i ≠ j → B (e i) (f j) = 0

def IsSymplecticBasisOfType (B : LinearMap.BilinForm R M) (b : Basis (ι ⊕ ι) R M) (d : ι → R) :
    Prop :=
  IsSymplecticFamily B (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i)) d

def IsSymplecticBasis (B : LinearMap.BilinForm R M) (b : Basis (ι ⊕ ι) R M) : Prop :=
  IsSymplecticBasisOfType B b fun _ => 1

namespace IsSymplecticFamily

variable {B : LinearMap.BilinForm R M} {e f : ι → M} {d : ι → R}


theorem left_right [DecidableEq ι] (h : IsSymplecticFamily B e f d) (i j : ι) :
    B (e i) (f j) = if i = j then d i else 0 := by
  split_ifs with hij
  · subst hij; exact h.left_right_self i
  · exact h.left_right_ne i j hij

theorem right_left [DecidableEq ι] (h : IsSymplecticFamily B e f d) (hB : B.IsAlt) (i j : ι) :
    B (f i) (e j) = if i = j then -d i else 0 := by
  rw [← hB.neg_eq, h.left_right]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem apply_left_sum [Fintype ι] (h : IsSymplecticFamily B e f d) (c : ι ⊕ ι → R) (k : ι) :
    B (e k) (∑ i, c i • Sum.elim e f i) = c (Sum.inr k) * d k := by
  classical
  simp [Fintype.sum_sum_type, h.left_left, h.left_right]

theorem apply_sum_right [Fintype ι] (h : IsSymplecticFamily B e f d) (c : ι ⊕ ι → R) (k : ι) :
    B (∑ i, c i • Sum.elim e f i) (f k) = c (Sum.inl k) * d k := by
  classical
  simp [Fintype.sum_sum_type, h.right_right, h.left_right]

theorem linearIndependent [Finite ι] [IsDomain R] (h : IsSymplecticFamily B e f d)
    (hd : ∀ i, d i ≠ 0) : LinearIndependent R (Sum.elim e f) := by
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  cases i with
  | inl k =>
    have := h.apply_sum_right c k
    rw [hc] at this
    simpa [hd k] using this.symm
  | inr k =>
    have := h.apply_left_sum c k
    rw [hc] at this
    simpa [hd k] using this.symm

end IsSymplecticFamily

end Defs


section Frobenius

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M]

omit [IsDomain R] in

theorem exists_pair_dvd_of_bilinForm (B : LinearMap.BilinForm R M) (N : Submodule R M) :
    ∃ e ∈ N, ∃ f ∈ N, (∀ y ∈ N, B e f ∣ B e y) ∧ (∀ x ∈ N, B e f ∣ B x f) ∧
      (∀ x ∈ N, ∀ y ∈ N, B e y = 0 → B x f = 0 → B e f ∣ B x y) := by
  let S : Set (Ideal R) := {J | ∃ x ∈ N, ∃ y ∈ N, J = Ideal.span {B x y}}
  obtain ⟨J, ⟨e, he, f, hf, rfl⟩, hmax⟩ :=
    (wellFounded_gt (α := Ideal R)).has_min S ⟨_, 0, N.zero_mem, 0, N.zero_mem, rfl⟩
  have key : ∀ s : R, (∀ u v : R, ∃ x ∈ N, ∃ y ∈ N, B x y = u * B e f + v * s) → B e f ∣ s := by
    intro s hs
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span {B e f, s})).principal
    have hg' : Ideal.span {B e f, s} = Ideal.span {g} := hg
    have : g ∈ Ideal.span {B e f, s} := hg' ▸ Ideal.mem_span_singleton_self g
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 this
    obtain ⟨x, hx, y, hy, hxy⟩ := hs u v
    have h1 : Ideal.span {B e f} ≤ Ideal.span {g} :=
      hg' ▸ Ideal.span_mono (by simp)
    have h2 := hmax (Ideal.span {g}) ⟨x, hx, y, hy, by rw [hxy, huv]⟩
    have h3 : Ideal.span {B e f} = Ideal.span {g} := by
      by_contra hne
      exact h2 (lt_of_le_of_ne h1 hne)
    rw [← Ideal.mem_span_singleton, h3, ← hg']
    exact Ideal.subset_span (by simp)
  refine ⟨e, he, f, hf, fun y hy => key _ fun u v => ?_, fun x hx => key _ fun u v => ?_,
    fun x hx y hy h₁ h₂ => key _ fun u v => ?_⟩
  · exact ⟨e, he, u • f + v • y, N.add_mem (N.smul_mem _ hf) (N.smul_mem _ hy), by simp⟩
  · exact ⟨u • e + v • x, N.add_mem (N.smul_mem _ he) (N.smul_mem _ hx), f, hf, by simp⟩
  · exact ⟨u • e + v • x, N.add_mem (N.smul_mem _ he) (N.smul_mem _ hx), f + y,
      N.add_mem hf hy, by simp [h₁, h₂]⟩

theorem exists_isSymplecticFamily_span_eq [Module.Free R M] [Module.Finite R M]
    {B : LinearMap.BilinForm R M} (hB : B.IsAlt) (N : Submodule R M)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0) :
    ∃ (g : ℕ) (e f : Fin g → M) (d : Fin g → R), IsSymplecticFamily B e f d ∧ (∀ i, d i ≠ 0) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧ Submodule.span R (Set.range (Sum.elim e f)) = N := by
  revert hN
  refine Submodule.inductionOnRank (Module.Free.chooseBasis R M) (fun N => (∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0) →
    ∃ (g : ℕ) (e f : Fin g → M) (d : Fin g → R), IsSymplecticFamily B e f d ∧ (∀ i, d i ≠ 0) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧ Submodule.span R (Set.range (Sum.elim e f)) = N) ?_ N
  intro N ih hN
  by_cases hbot : N = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [hbot, Submodule.span_eq_bot]
    rintro _ ⟨i | i, rfl⟩ <;> exact i.elim0
  obtain ⟨e, he, f, hf, h₁, h₂, h₃⟩ := exists_pair_dvd_of_bilinForm B N
  have hd : B e f ≠ 0 := by
    intro h0
    apply hbot
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine hN x hx fun y hy => ?_
    rw [h0] at h₁ h₂ h₃
    exact zero_dvd_iff.1 (h₃ x hx y hy (zero_dvd_iff.1 (h₁ y hy)) (zero_dvd_iff.1 (h₂ x hx)))
  let N' : Submodule R M := N ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
  have hmem : ∀ y, y ∈ N' ↔ y ∈ N ∧ B e y = 0 ∧ B f y = 0 := fun y => Iff.rfl
  have hdec : ∀ y ∈ N, ∃ a b : R, ∃ y' ∈ N', y = a • e + b • f + y' := by
    intro y hy
    obtain ⟨b, hb⟩ := h₁ y hy
    obtain ⟨a, ha⟩ := h₂ y hy
    refine ⟨a, b, y - a • e - b • f, (hmem _).2 ⟨N.sub_mem (N.sub_mem hy (N.smul_mem _ he))
      (N.smul_mem _ hf), ?_, ?_⟩, by abel⟩
    · simp [hb, hB.self_eq_zero, mul_comm]
    · simp [← hB.neg_eq y f, ← hB.neg_eq e f, ha, hB.self_eq_zero, mul_comm]
  obtain ⟨g, e', f', d', hs, hd', hdvd, hspan⟩ := ih N' inf_le_left f hf (by
    intro c y hy hc
    have := congrArg (B e) hc
    simpa [((hmem y).1 hy).2.1, hd] using this) (by
    intro x hx hx0
    refine hN x hx.1 fun y hy => ?_
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
    simp [hx0 y' hy', hB.eq_iff.1 ((hmem x).1 hx).2.1, hB.eq_iff.1 ((hmem x).1 hx).2.2])
  have he' : ∀ i, e' i ∈ N' := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hf' : ∀ i, f' i ∈ N' := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  refine ⟨g + 1, Fin.cons e e', Fin.cons f f', Fin.cons (B e f) d', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (he' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.1]
    · simp [hs.left_left]
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (hf' _)).2.2]
    · simp [hB.eq_iff.1 ((hmem _).1 (hf' _)).2.2]
    · simp [hs.right_right]
  · intro i
    cases i using Fin.cases
    · simp
    · simp [hs.left_right_self]
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact absurd rfl hij
    · simp [((hmem _).1 (hf' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.2]
    · simpa using hs.left_right_ne _ _ fun a => hij (congrArg _ a)
  · intro i
    cases i using Fin.cases
    · simpa using hd
    · simpa using hd' _
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact dvd_rfl
    · simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hs.left_right_self]
      exact h₃ _ (he' _).1 _ (hf' _).1 ((hmem _).1 (hf' _)).2.1
        (hB.eq_iff.1 ((hmem _).1 (he' _)).2.2)
    · exact absurd hij (by simp)
    · simpa using hdvd _ _ (by simpa using hij)
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i | i, rfl⟩ <;> cases i using Fin.cases
      · exact he
      · exact (he' _).1
      · exact hf
      · exact (hf' _).1
    · intro y hy
      obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_)) ?_
      · exact Submodule.subset_span ⟨Sum.inl 0, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inr 0, rfl⟩
      · rw [← hspan] at hy'
        refine Submodule.span_mono ?_ hy'
        rintro _ ⟨i | i, rfl⟩
        · exact ⟨Sum.inl i.succ, rfl⟩
        · exact ⟨Sum.inr i.succ, rfl⟩

end Frobenius

section BasisLemmas

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : LinearMap.BilinForm R M}

namespace IsSymplecticBasisOfType

variable {b : Basis (ι ⊕ ι) R M} {d : ι → R}


theorem elim_eq (b : Basis (ι ⊕ ι) R M) :
    Sum.elim (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i)) = b := by
  funext i; cases i <;> rfl

theorem apply_left [Finite ι] (h : IsSymplecticBasisOfType B b d) (x : M) (k : ι) :
    B (b (Sum.inl k)) x = b.repr x (Sum.inr k) * d k := by
  have := Fintype.ofFinite ι
  have h' := IsSymplecticFamily.apply_left_sum h (b.repr x) k
  rwa [elim_eq, b.sum_repr] at h'

theorem apply_right [Finite ι] (h : IsSymplecticBasisOfType B b d) (x : M) (k : ι) :
    B x (b (Sum.inr k)) = b.repr x (Sum.inl k) * d k := by
  have := Fintype.ofFinite ι
  have h' := IsSymplecticFamily.apply_sum_right h (b.repr x) k
  rwa [elim_eq, b.sum_repr] at h'

theorem isUnit [Finite ι] (h : IsSymplecticBasisOfType B b d) (hp : Surjective B) (k : ι) :
    IsUnit (d k) := by
  obtain ⟨x, hx⟩ := hp (b.coord (Sum.inr k))
  have := h.apply_right x k
  rw [hx] at this
  simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same] at this
  exact IsUnit.of_mul_eq_one_right _ this.symm

theorem finrank_eq [Fintype ι] [StrongRankCondition R] (b : Basis (ι ⊕ ι) R M) :
    finrank R M = 2 * Fintype.card ι := by
  rw [finrank_eq_card_basis b, Fintype.card_sum, two_mul]

end IsSymplecticBasisOfType

namespace IsSymplecticBasis

variable {b : Basis (ι ⊕ ι) R M}


theorem left_left (h : IsSymplecticBasis B b) (i j : ι) :
    B (b (Sum.inl i)) (b (Sum.inl j)) = 0 := IsSymplecticFamily.left_left h i j

theorem right_right (h : IsSymplecticBasis B b) (i j : ι) :
    B (b (Sum.inr i)) (b (Sum.inr j)) = 0 := IsSymplecticFamily.right_right h i j

theorem left_right [DecidableEq ι] (h : IsSymplecticBasis B b) (i j : ι) :
    B (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0 :=
  IsSymplecticFamily.left_right h i j

theorem right_left [DecidableEq ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) (i j : ι) :
    B (b (Sum.inr i)) (b (Sum.inl j)) = if i = j then -1 else 0 :=
  IsSymplecticFamily.right_left h hB i j

end IsSymplecticBasis


theorem IsSymplecticFamily.exists_isSymplecticBasis [IsDomain R] [Finite ι] {e f : ι → M}
    {d : ι → R} (h : IsSymplecticFamily B e f d) (hd : ∀ i, d i ≠ 0)
    (hspan : Submodule.span R (Set.range (Sum.elim e f)) = ⊤) (hp : Surjective B) :
    ∃ b : Basis (ι ⊕ ι) R M, IsSymplecticBasis B b ∧ ∀ i, b (Sum.inl i) = e i := by
  let b := Basis.mk (h.linearIndependent hd) hspan.ge
  have hb : IsSymplecticBasisOfType B b d := by
    simpa [IsSymplecticBasisOfType, b] using h
  choose u hu using fun k => hb.isUnit hp k
  refine ⟨b.unitsSMul (Sum.elim 1 fun k => (u k)⁻¹), ⟨fun i j => ?_, fun i j => ?_, fun i => ?_,
    fun i j hij => ?_⟩, fun i => ?_⟩
  · simp [Basis.unitsSMul_apply, b, h.left_left]
  · simp [Basis.unitsSMul_apply, b, h.right_right, Units.smul_def]
  · simp [Basis.unitsSMul_apply, b, h.left_right_self, Units.smul_def, ← hu]
  · simp [Basis.unitsSMul_apply, b, h.left_right_ne i j hij, Units.smul_def]
  · simp [Basis.unitsSMul_apply, b]

end BasisLemmas

section Existence

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Free R M] [Module.Finite R M] {B : LinearMap.BilinForm R M}


theorem exists_isSymplecticBasis (hB : B.IsAlt) (hp : Bijective B) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) R M), IsSymplecticBasis B b := by
  obtain ⟨g, e, f, d, h, hd, -, hspan⟩ := exists_isSymplecticFamily_span_eq hB ⊤
    fun x _ hx => (injective_iff_map_eq_zero B).1 hp.1 x (LinearMap.ext fun y => hx y trivial)
  obtain ⟨b, hb, -⟩ := h.exists_isSymplecticBasis hd hspan hp.2
  exact ⟨g, b, hb⟩

theorem exists_isSymplecticBasis_of_finrank (hB : B.IsAlt) (hp : Bijective B) {g : ℕ}
    (hg : finrank R M = 2 * g) : ∃ b : Basis (Fin g ⊕ Fin g) R M, IsSymplecticBasis B b := by
  obtain ⟨g', b, hb⟩ := exists_isSymplecticBasis hB hp
  have := IsSymplecticBasisOfType.finrank_eq b
  obtain rfl : g' = g := by rw [hg, Fintype.card_fin] at this; omega
  exact ⟨b, hb⟩

end Existence

/-- The literal standard integral pairing used by the source's level structure. -/
def stdSymp (g : ℕ) (i j : Fin (2 * g)) : ℤ :=
  if (i : ℕ) < g ∧ (j : ℕ) = (i : ℕ) + g then 1
  else if (j : ℕ) < g ∧ (i : ℕ) = (j : ℕ) + g then -1 else 0

/-- An integral coordinate equivalence for the SAME perfect alternating form. -/

theorem exists_equiv_stdSymp {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    {B : LinearMap.BilinForm ℤ M} (hB : B.IsAlt) (hp : Function.Bijective B) {g : ℕ}
    (hg : Module.finrank ℤ M = 2 * g) :
    ∃ bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] M,
      ∀ i j, B (bas (Pi.single i 1)) (bas (Pi.single j 1)) = stdSymp g i j := by
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hB hp hg
  let e : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)
  have hl : ∀ i, ((e (Sum.inl i) : Fin (2 * g)) : ℕ) = i := fun i => by simp [e]
  have hr : ∀ i, ((e (Sum.inr i) : Fin (2 * g)) : ℕ) = g + i := fun i => by simp [e]; omega
  refine ⟨(b.reindex e).equivFun.symm, fun i j => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  have hs : ∀ k, (b.reindex e).equivFun.symm (Pi.single (e k) 1) = b k := fun k => by
    rw [Module.Basis.equivFun_symm_apply]; simp [Pi.single_apply]
  rw [hs, hs, stdSymp]
  rcases i with i | i <;> rcases j with j | j <;> have := i.2 <;> have := j.2
  · rw [hb.left_left, hl, hl, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [hb.left_right, hl, hr]
    by_cases h : i = j
    · subst h; rw [ite_eq_left rfl, ite_eq_left (by omega)]
    · have : (i : ℕ) ≠ j := fun a => h (Fin.ext a)
      rw [ite_eq_right h, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [hb.right_left hB, hl, hr]
    by_cases h : i = j
    · subst h; rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left (by omega)]
    · have : (i : ℕ) ≠ j := fun a => h (Fin.ext a)
      rw [ite_eq_right h, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [hb.right_right, hr, hr, ite_eq_right (by omega), ite_eq_right (by omega)]


end RHLean.Geometry.NativeIntegralSymplectic

end
