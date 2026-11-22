import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Integral regular sections from bounded determinant avoidance

This is the finite construction used inside Alpoge's short cusp-section
argument, extracted independently of its geometric hypotheses. A determinant
pencil of size `q` has at most `q` bad integer parameters. A generator which
changes at most `q` components therefore admits a replacement coefficient in
`{0, ..., q^2}`. Repeating this for the actual generator family preserves
regularity at every component.

The construction preserves any integral submodule, including an `O_K` lattice.
Its norm estimate is simultaneous over an arbitrary family of additive
realizations. Disjoint component supports enter through the number of active
generators at a point, so the bound has no total-component factor.

Source: `GlobalTheory.ShortDet.card_le_of_det_eq_zero`, `exists_nat_coeff`,
`exists_nat_step`, and `exists_short` in
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardLeOfDetEqZero.lean`,
upstream commit `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The regular seed, short generators, and component-support facts are explicit
mathematical inputs. This file does not assert that the geometric suppliers
have already been constructed in RH_Lean.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Geometry

open Polynomial in
/-- A genuine determinant pencil has at most its matrix size many bad natural
parameters, provided it is regular at one parameter. -/
theorem nativeCard_bad_determinant_le {K S : Type*} [Field K] [CharZero K]
    [Fintype S] [DecidableEq S] (A B : Matrix S S K) {a : K}
    (ha : (A + a • B).det ≠ 0) (T : Finset ℕ)
    (hT : ∀ n ∈ T, (A + (n : K) • B).det = 0) :
    T.card ≤ Fintype.card S := by
  classical
  have hev : ∀ t : K,
      Polynomial.eval t (Matrix.det ((X : Polynomial K) • B.map C + A.map C)) =
        (A + t • B).det := fun t => by
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [add_comm, mul_comm t]
  have h0 : Matrix.det ((X : Polynomial K) • B.map C + A.map C) ≠ 0 :=
    fun h => ha (by rw [← hev, h, eval_zero])
  rw [← Finset.card_image_of_injective T (Nat.cast_injective (R := K))]
  refine (card_le_degree_of_subset_roots fun x hx => ?_).trans
    (natDegree_det_X_add_C_le B A)
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
  exact (mem_roots h0).2 ((hev _).trans (hT n hn))

/-- Replace coefficients one at a time by bounded natural numbers while
preserving a property whose one-coordinate pencils admit such replacements. -/
theorem nativeExists_bounded_nat_coeff {K V I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype I]
    (P : V → Prop) (w : I → V) (N : ℕ)
    (h : ∀ v i (a : K), P (v + a • w i) →
      ∃ n : ℕ, n ≤ N ∧ P (v + (n : K) • w i))
    (a : I → K) (ha : P (∑ i, a i • w i)) :
    ∃ n : I → ℕ, (∀ i, n i ≤ N) ∧ P (∑ i, n i • w i) := by
  classical
  have key : ∀ s : Finset I, ∃ b : I → K,
      (∀ i ∈ s, ∃ n : ℕ, n ≤ N ∧ b i = n) ∧ P (∑ i, b i • w i) := fun s => by
    induction s using Finset.induction_on with
    | empty => exact ⟨a, by simp, ha⟩
    | insert k s hk ih =>
      obtain ⟨b, hb, hP⟩ := ih
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)] at hP
      obtain ⟨n, hn, hP'⟩ := h _ _ _ hP
      refine ⟨Function.update b k n, fun i hi => ?_, ?_⟩
      · by_cases e : i = k
        · exact ⟨n, hn, by rw [e, Function.update_self]⟩
        · rw [Function.update_of_ne e]
          exact hb i ((Finset.mem_insert.1 hi).resolve_left e)
      · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), Function.update_self,
          Finset.sum_congr rfl fun i hi =>
            by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
        exact hP'
  obtain ⟨b, hb, hP⟩ := key Finset.univ
  choose n hn hn' using fun i => hb i (Finset.mem_univ i)
  exact ⟨n, hn, by simpa only [hn', Nat.cast_smul_eq_nsmul] using hP⟩

section Determinants

variable {K V I Z S : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype I] [Fintype S] [DecidableEq S]
  (F : Z → Type*) [∀ z, Field (F z)] [∀ z, CharZero (F z)]
  [∀ z, Algebra K (F z)]

/-- Simultaneous determinant regularity is achieved by actual natural
coefficients bounded by `q^2`. The matrices may live in different component
fields. The support sets contain precisely the components a generator can
change; their size, and the matrix size, both contribute to the coefficient
bound. -/
theorem nativeExists_regular_nat_coeff
    (D : ∀ z, V →ₗ[K] Matrix S S (F z)) (w : I → V)
    (support : I → Finset Z)
    (hcard : ∀ i, (support i).card ≤ Fintype.card S)
    (hoff : ∀ i z, z ∉ support i → D z (w i) = 0)
    (a : I → K) (ha : ∀ z, (D z (∑ i, a i • w i)).det ≠ 0) :
    ∃ n : I → ℕ, (∀ i, n i ≤ Fintype.card S ^ 2) ∧
      ∀ z, (D z (∑ i, n i • w i)).det ≠ 0 := by
  classical
  apply nativeExists_bounded_nat_coeff
    (K := K) (fun v => ∀ z, (D z v).det ≠ 0) w (Fintype.card S ^ 2) ?_ a ha
  intro v i a h
  have hev (z : Z) (t : K) :
      D z (v + t • w i) =
        D z v + (algebraMap K (F z) t) • D z (w i) := by
    rw [map_add, map_smul]
    congr 1
    ext j k
    simp [Algebra.smul_def]
  let T : Z → Finset ℕ := fun z =>
    (Finset.range (Fintype.card S ^ 2 + 1)).filter fun n =>
      (D z (v + (n : K) • w i)).det = 0
  have hT : ∀ z, (T z).card ≤ Fintype.card S := fun z => by
    refine nativeCard_bad_determinant_le (D z v) (D z (w i))
      (a := algebraMap K (F z) a) (hev z a ▸ h z) _ ?_
    intro n hn
    have hn' := (Finset.mem_filter.1 hn).2
    simpa only [hev, map_natCast] using hn'
  have hc : ((support i).biUnion T).card <
      (Finset.range (Fintype.card S ^ 2 + 1)).card := by
    rw [Finset.card_range, Nat.lt_succ_iff, sq]
    exact (Finset.card_biUnion_le_card_mul _ _ _ fun z _ => hT z).trans
      (Nat.mul_le_mul_right _ (hcard i))
  obtain ⟨n, hn, hn'⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨n, Nat.lt_succ_iff.1 (Finset.mem_range.1 hn), fun z h0 => ?_⟩
  by_cases hz : z ∈ support i
  · exact hn' (Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_filter.2 ⟨hn, h0⟩⟩)
  · have hz0 := hoff i z hz
    have hza := h z
    rw [hev, hz0, smul_zero, add_zero] at hza h0
    exact hza h0

end Determinants

/-- A bounded natural combination stays in every integral submodule containing
its generators. No restriction of scalars or free-lattice hypothesis is used. -/
theorem nativeNatCombination_mem {R V I : Type*} [Ring R] [AddCommGroup V]
    [Module R V] [Fintype I] (L : Submodule R V) (w : I → V)
    (hw : ∀ i, w i ∈ L) (n : I → ℕ) :
    (∑ i, n i • w i) ∈ L :=
  Submodule.sum_mem _ fun i _ => nsmul_mem (hw i) _

/-- Pointwise support, rather than the number of all components, pays for the
norm of the constructed section. The family of realizations can index every
archimedean place and every point simultaneously. -/
theorem nativeNatCombination_allPlace_norm_le
    {V I P : Type*} [AddCommGroup V] [Fintype I]
    (E : P → Type*) [∀ p, SeminormedAddCommGroup (E p)]
    (ev : ∀ p, V →+ E p) (w : I → V) (active : P → Finset I)
    {B N : ℝ} (hB : 0 ≤ B)
    (hcard : ∀ p, ((active p).card : ℝ) ≤ N)
    (hoff : ∀ p i, i ∉ active p → ev p (w i) = 0)
    (hshort : ∀ p i, ‖ev p (w i)‖ ≤ B)
    (n : I → ℕ) (M : ℕ) (hn : ∀ i, n i ≤ M) :
    ∀ p, ‖ev p (∑ i, n i • w i)‖ ≤ N * ((M : ℝ) * B) := by
  classical
  intro p
  calc
    ‖ev p (∑ i, n i • w i)‖ ≤ ∑ i, (n i : ℝ) * ‖ev p (w i)‖ := by
      rw [map_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [map_nsmul]
      exact norm_nsmul_le (n := n i) (a := ev p (w i))
    _ = ∑ i ∈ active p, (n i : ℝ) * ‖ev p (w i)‖ := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        rw [hoff p i hi, norm_zero, mul_zero]
    _ ≤ (active p).card • ((M : ℝ) * B) := by
      apply Finset.sum_le_card_nsmul
      intro i _
      exact mul_le_mul (by exact_mod_cast hn i) (hshort p i)
        (norm_nonneg _) (Nat.cast_nonneg _)
    _ = ((active p).card : ℝ) * ((M : ℝ) * B) := by rw [nsmul_eq_mul]
    _ ≤ N * ((M : ℝ) * B) :=
      mul_le_mul_of_nonneg_right (hcard p) (by positivity)

/-- A regular seed in the span of actual short integral component generators
produces an actual integral regular section with a simultaneous all-place norm
bound. Each cost is exposed: matrix size squared, active generator count, and
the generator norm. In the cusp application `B = β * Λ` and `q = |S|`. -/
theorem nativeExists_short_integral_regular_section
    {K R V I Z S P : Type*} [Field K] [Ring R] [AddCommGroup V]
    [Module K V] [Module R V] [Fintype I] [Fintype S] [DecidableEq S]
    (F : Z → Type*) [∀ z, Field (F z)] [∀ z, CharZero (F z)]
    [∀ z, Algebra K (F z)]
    (D : ∀ z, V →ₗ[K] Matrix S S (F z))
    (L : Submodule R V) (w : I → V) (hw : ∀ i, w i ∈ L)
    (support : I → Finset Z)
    (hsupport : ∀ i, (support i).card ≤ Fintype.card S)
    (hdetOff : ∀ i z, z ∉ support i → D z (w i) = 0)
    (u₀ : V) (hspan : u₀ ∈ Submodule.span K (Set.range w))
    (hregular : ∀ z, (D z u₀).det ≠ 0)
    (E : P → Type*) [∀ p, SeminormedAddCommGroup (E p)]
    (ev : ∀ p, V →+ E p) (active : P → Finset I)
    {B N : ℝ} (hB : 0 ≤ B)
    (hactive : ∀ p, ((active p).card : ℝ) ≤ N)
    (hevOff : ∀ p i, i ∉ active p → ev p (w i) = 0)
    (hshort : ∀ p i, ‖ev p (w i)‖ ≤ B) :
    ∃ n : I → ℕ,
      (∀ i, n i ≤ Fintype.card S ^ 2) ∧
      (∑ i, n i • w i) ∈ L ∧
      (∀ z, (D z (∑ i, n i • w i)).det ≠ 0) ∧
      ∀ p, ‖ev p (∑ i, n i • w i)‖ ≤
        N * ((Fintype.card S : ℝ) ^ 2 * B) := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hspan
  obtain ⟨n, hn, hreg⟩ := nativeExists_regular_nat_coeff F D w support
    hsupport hdetOff a (by simpa only [ha] using hregular)
  refine ⟨n, hn, nativeNatCombination_mem L w hw n, hreg, ?_⟩
  simpa only [Nat.cast_pow] using nativeNatCombination_allPlace_norm_le E ev w
    active hB hactive hevOff hshort n (Fintype.card S ^ 2) hn

end RHLean.Geometry
