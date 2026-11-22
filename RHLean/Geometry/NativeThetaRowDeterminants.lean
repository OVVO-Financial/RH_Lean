import Mathlib

/-!
# Row invariance and the leading-minor factorization

These finite algebraic arguments recover exact column support and factor
row-invariant polynomials into leading minors. No analytic theta or cover
interface is imported.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/`,
`Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean`;
`Proofs/CuspFormEvaluations/RowAddGenericRowAddTerm.lean`;
`Proofs/CuspFormEvaluations/ColumnDegreeLe.lean`;
`Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean`;
only the declarations used by the native highest-weight construction.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Geometry.NativeTheta.Paired

open Finset

open Finset in

theorem _root_.RHLean.Geometry.NativeTheta.Paired.sum_filter_lt_eq_sum_range {m : ℕ} (f : Fin m → ℤ) (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), f k =
      ∑ j ∈ range i, if h : j < m then f ⟨j, h⟩ else 0 := by
  rw [Finset.sum_filter]
  have hfin := Fin.sum_univ_eq_sum_range
    (fun j => if j < i then (if h : j < m then f ⟨j, h⟩ else 0) else 0) m
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at hfin
  rw [hfin, ← Finset.sum_filter]
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact hj.2
  · intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hj hj'
    have hjm : ¬ j < m := fun hjm => hj' hjm hj
    simp [hjm]

open Finset in
private theorem sum_range_sub_mul_eq_abel_summation (D e : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ range n, (D (i + 1) - D i) * e i =
      D n * e n + ∑ i ∈ range n, D (i + 1) * (e i - e (i + 1)) - D 0 * e 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ, ih]; ring

open Finset in

theorem _root_.RHLean.Geometry.NativeTheta.Paired.casimir_value_strict {m : ℕ} (κ κ₀ : Fin m → ℤ) (h : Antitone κ)
    (h₀ : Antitone κ₀)
    (hle : ∀ i : ℕ, ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), κ k ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), κ₀ k)
    (hsum : ∑ k, κ k = ∑ k, κ₀ k)
    (hC : ∑ i, κ₀ i * (κ₀ i + m - 1 - 2 * (i : ℕ)) ≤ ∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ))) : κ = κ₀ := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℤ, d = fun j =>
      (if h : j < m then κ₀ ⟨j, h⟩ else 0) - (if h : j < m then κ ⟨j, h⟩ else 0) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℤ, e = fun j =>
      if h : j < m then κ₀ ⟨j, h⟩ + κ ⟨j, h⟩ + (m : ℤ) - 1 - 2 * (j : ℤ) else 0 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℤ, D = fun j => ∑ i ∈ range j, d i := ⟨_, rfl⟩
  have hDj : ∀ j, D j = ∑ k ∈ univ.filter (fun k : Fin m => (k : ℕ) < j), κ₀ k -
      ∑ k ∈ univ.filter (fun k : Fin m => (k : ℕ) < j), κ k := by
    intro j
    simp only [hD, hd, sum_sub_distrib, _root_.RHLean.Geometry.NativeTheta.Paired.sum_filter_lt_eq_sum_range]
  have hD0 : ∀ j, 0 ≤ D j := fun j => by rw [hDj]; linarith [hle j]
  have hDm : D m = 0 := by rw [hDj]; simp [hsum]
  have hDzero : D 0 = 0 := by simp [hD]
  have hdD : ∀ j, d j = D (j + 1) - D j := by intro j; simp [hD, sum_range_succ]
  have hC' : ∑ i ∈ range m, (D (i + 1) - D i) * e i ≤ 0 := by
    have h1 : ∑ i ∈ range m, d i * e i =
        ∑ i : Fin m, (κ₀ i - κ i) * (κ₀ i + κ i + m - 1 - 2 * (i : ℕ)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => d i * e i) m]
      refine sum_congr rfl (fun i _ => ?_)
      simp [hd, he, i.isLt]
    have h2 : ∑ i : Fin m, (κ₀ i - κ i) * (κ₀ i + κ i + m - 1 - 2 * (i : ℕ)) =
        ∑ i, κ₀ i * (κ₀ i + m - 1 - 2 * (i : ℕ)) - ∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ)) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl (fun i _ => ?_)
      ring
    simp_rw [← hdD]
    rw [h1, h2]
    linarith
  have key := sum_range_sub_mul_eq_abel_summation D e m
  rw [hDm, hDzero, zero_mul, zero_mul, zero_add, sub_zero] at key
  have he_gap : ∀ i, i + 1 < m → 2 ≤ e i - e (i + 1) := by
    intro i hi
    have h1 := h₀ (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, by omega⟩ : Fin m) ≤ ⟨i + 1, hi⟩)
    have h2 := h (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, by omega⟩ : Fin m) ≤ ⟨i + 1, hi⟩)
    simp only [he, hi, show i < m by omega, ↓reduceDIte]
    push_cast
    linarith
  have hterm : ∀ i ∈ range m, 0 ≤ D (i + 1) * (e i - e (i + 1)) := by
    intro i hi
    rw [mem_range] at hi
    rcases Nat.lt_or_ge (i + 1) m with h' | h'
    · exact mul_nonneg (hD0 _) (by linarith [he_gap i h'])
    · rw [show i + 1 = m by omega, hDm, zero_mul]
  have hsum0 : ∑ i ∈ range m, D (i + 1) * (e i - e (i + 1)) = 0 :=
    le_antisymm (by linarith) (sum_nonneg hterm)
  have hall := (sum_eq_zero_iff_of_nonneg hterm).mp hsum0
  have hDall : ∀ j, j ≤ m → D j = 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hDzero
    rcases Nat.lt_or_ge j m with hjm | hjm
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rcases mul_eq_zero.mp (hall i (mem_range.mpr (by omega))) with h0 | h0
      · exact h0
      · linarith [he_gap i hjm]
    · rw [show j = m by omega]
      exact hDm
  funext k
  have hk' := k.isLt
  have hk := hdD k
  rw [hDall ((k : ℕ) + 1) (by omega), hDall (k : ℕ) (by omega)] at hk
  simp [hd, k.isLt] at hk
  linarith

def mixedWeight (m : ℕ) {p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ) : Fin m → ℤ := fun k =>
  (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) -
    (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0)

theorem mixedWeight_apply (m : ℕ) {p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ) (k : Fin m) :
    mixedWeight m a b k =
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) -
        (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0) := rfl

open Finset in

theorem _root_.RHLean.Geometry.NativeTheta.Paired.antitone_mixedWeight (m : ℕ) {p q : ℕ} {a : Fin p → ℕ} {b : Fin q → ℕ}
    (ha : Antitone a) (hb : Antitone b) : Antitone (_root_.RHLean.Geometry.NativeTheta.Paired.mixedWeight m a b) := by
  intro k l hkl
  have hkl' : (k : ℕ) ≤ l := hkl
  simp only [_root_.RHLean.Geometry.NativeTheta.Paired.mixedWeight_apply]
  have hA : (if h : (l : ℕ) < p then (a ⟨l, h⟩ : ℤ) else 0) ≤
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) := by
    split_ifs <;> first
      | omega | positivity | exact le_rfl | exact_mod_cast ha (Fin.mk_le_mk.mpr hkl')
  have hB : (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0) ≤
      (if h : m - 1 - (l : ℕ) < q then (b ⟨m - 1 - l, h⟩ : ℤ) else 0) := by
    split_ifs <;> first
      | omega | positivity | exact le_rfl | exact_mod_cast hb (Fin.mk_le_mk.mpr (by omega))
  linarith

open Finset in

theorem _root_.RHLean.Geometry.NativeTheta.Paired.sum_dite_lt {m p : ℕ} (hp : p ≤ m) (f : Fin p → ℤ) :
    ∑ k : Fin m, (if h : (k : ℕ) < p then f ⟨k, h⟩ else 0) = ∑ k, f k := by
  have hfin := Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) m
  have hfin' := Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) p
  beta_reduce at hfin
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at hfin'
  rw [hfin, hfin']
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j _ hj
    simp only [Finset.mem_range] at hj
    simp [hj]

open Finset in

theorem _root_.RHLean.Geometry.NativeTheta.Paired.sum_dite_rev_lt {m q : ℕ} (hq : q ≤ m) (f : Fin q → ℤ) :
    ∑ k : Fin m, (if h : m - 1 - (k : ℕ) < q then f ⟨m - 1 - k, h⟩ else 0) = ∑ k, f k := by
  rw [← _root_.RHLean.Geometry.NativeTheta.Paired.sum_dite_lt hq f]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun k => ?_)
  have hk : ((Fin.revPerm k : Fin m) : ℕ) = m - 1 - k := by
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  simp only [hk]

open Finset in

theorem _root_.RHLean.Geometry.NativeTheta.Paired.sum_mixedWeight {m p q : ℕ} (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) :
    ∑ k, _root_.RHLean.Geometry.NativeTheta.Paired.mixedWeight m a b k = ∑ i, (a i : ℤ) - ∑ i, (b i : ℤ) := by
  have h1 := _root_.RHLean.Geometry.NativeTheta.Paired.sum_dite_lt (m := m) (by omega : p ≤ m)
    (fun i => (a i : ℤ))
  have h2 := _root_.RHLean.Geometry.NativeTheta.Paired.sum_dite_rev_lt (m := m) (by omega : q ≤ m)
    (fun i => (b i : ℤ))
  beta_reduce at h1 h2
  simp only [_root_.RHLean.Geometry.NativeTheta.Paired.mixedWeight_apply, Finset.sum_sub_distrib]
  rw [h1, h2]

open Finset in

theorem _root_.RHLean.Geometry.NativeTheta.Paired.casimir_value_mixedWeight {m p q : ℕ} (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) :
    ∑ k : Fin m, _root_.RHLean.Geometry.NativeTheta.Paired.mixedWeight m a b k * (_root_.RHLean.Geometry.NativeTheta.Paired.mixedWeight m a b k + m - 1 - 2 * (k : ℕ)) =
      (∑ i : Fin p, (a i : ℤ) * (a i + p - 1 - 2 * (i : ℕ)) + ((m : ℤ) - p) * ∑ i, (a i : ℤ)) +
      (∑ i : Fin q, (b i : ℤ) * (b i + q - 1 - 2 * (i : ℕ)) + ((m : ℤ) - q) * ∑ i, (b i : ℤ)) := by
  have hp : p ≤ m := by omega
  have hq : q ≤ m := by omega
  have h1 := _root_.RHLean.Geometry.NativeTheta.Paired.sum_dite_lt hp
    (fun i : Fin p => (a i : ℤ) * (a i + m - 1 - 2 * (i : ℕ)))
  have h2 := _root_.RHLean.Geometry.NativeTheta.Paired.sum_dite_rev_lt hq
    (fun j : Fin q => (b j : ℤ) * (b j + m - 1 - 2 * (j : ℕ)))
  beta_reduce at h1 h2
  have hpt : ∀ k : Fin m, _root_.RHLean.Geometry.NativeTheta.Paired.mixedWeight m a b k *
        (_root_.RHLean.Geometry.NativeTheta.Paired.mixedWeight m a b k + m - 1 - 2 * (k : ℕ)) =
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) * (a ⟨k, h⟩ + m - 1 - 2 * (k : ℕ)) else 0) +
      (if h : m - 1 - (k : ℕ) < q then
        (b ⟨m - 1 - k, h⟩ : ℤ) * (b ⟨m - 1 - k, h⟩ + m - 1 - 2 * (m - 1 - (k : ℕ) : ℕ))
        else 0) := by
    intro k
    have hk := k.isLt
    have hc : ((m - 1 - (k : ℕ) : ℕ) : ℤ) = (m : ℤ) - 1 - (k : ℕ) := by omega
    rw [_root_.RHLean.Geometry.NativeTheta.Paired.mixedWeight_apply]
    split_ifs <;> first | omega | (rw [hc]; ring) | ring
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, h1, h2,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1 <;> refine Finset.sum_congr rfl (fun i _ => ?_) <;> ring

end RHLean.Geometry.NativeTheta.Paired

open MvPolynomial

namespace RHLean.Geometry.NativeTheta

section RowAdd

variable {K σ ι : Type*} [Field K] [DecidableEq σ] [Fintype ι]

noncomputable def rowAddTerm (K : Type*) [Field K] (u w : ι → σ) (s : σ) : MvPolynomial σ K :=
  ∑ k, if s = w k then X (u k) else 0

noncomputable def rowAddGeneric (u w : ι → σ) :
    MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun s => Polynomial.C (X s) + Polynomial.X * Polynomial.C (rowAddTerm K u w s)

theorem eval_rowAddGeneric (u w : ι → σ) (t : K) (P : MvPolynomial σ K) :
    Polynomial.eval (C t) (rowAddGeneric u w P) =
      bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul]
    congr 1
    simp [rowAddGeneric, rowAddTerm, Finset.mul_sum, Polynomial.eval_finsetSum]
    simp only [mul_comm]

theorem eval_zero_rowAddGeneric (u w : ι → σ) (P : MvPolynomial σ K) :
    Polynomial.eval 0 (rowAddGeneric u w P) = P := by
  have h := eval_rowAddGeneric u w (0 : K) P
  simpa using h

theorem rowAddGeneric_rowAddTerm (u w : ι → σ) (huw : ∀ k l, u k ≠ w l) (s : σ) :
    rowAddGeneric u w (rowAddTerm K u w s) = Polynomial.C (rowAddTerm K u w s) := by
  have h0 : ∀ k, rowAddTerm K u w (u k) = 0 := fun k => by
    simp [rowAddTerm, huw k]
  conv_lhs => rw [rowAddTerm]
  conv_rhs => rw [rowAddTerm]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · simp [rowAddGeneric, h0]
  · simp

theorem sum_X_mul_pderiv_X (u w : ι → σ) (s : σ) :
    ∑ k, X (u k) * pderiv (w k) (X s : MvPolynomial σ K) = rowAddTerm K u w s := by
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · simp [h]
  · simp [pderiv_X_of_ne h]

theorem derivative_rowAddGeneric (u w : ι → σ) (huw : ∀ k l, u k ≠ w l)
    (P : MvPolynomial σ K) :
    Polynomial.derivative (rowAddGeneric u w P) =
      rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p s hp =>
    have h : ∑ k, X (u k) * pderiv (w k) (p * X s) =
        (∑ k, X (u k) * pderiv (w k) p) * X s + p * rowAddTerm K u w s := by
      rw [← sum_X_mul_pderiv_X, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [h, map_add, map_mul (rowAddGeneric u w), map_mul (rowAddGeneric u w),
      map_mul (rowAddGeneric u w), Polynomial.derivative_mul, hp,
      rowAddGeneric_rowAddTerm u w huw]
    have hX : Polynomial.derivative (rowAddGeneric u w (X s : MvPolynomial σ K)) =
        Polynomial.C (rowAddTerm K u w s) := by
      simp [rowAddGeneric]
    rw [hX]

end RowAdd

theorem rowAdd_invariant_iff {K σ ι : Type*} [Field K] [CharZero K] [DecidableEq σ] [Fintype ι]
    (u w : ι → σ)
    (huw : ∀ k l, u k ≠ w l) (P : MvPolynomial σ K) :
    List.TFAE [∀ t : ℤ, bind₁ (fun s => X s + ∑ k, if s = w k then C (t : K) * X (u k) else 0) P = P,
      ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P = P,
      ∑ k, X (u k) * pderiv (w k) P = 0] := by
  tfae_have 2 → 1 := fun h t => h t
  tfae_have 1 → 3 := by
    intro h
    have hc : rowAddGeneric u w P = Polynomial.C P := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hinj : Function.Injective fun t : ℤ => (C (t : K) : MvPolynomial σ K) :=
        fun a b hab => Int.cast_injective (C_injective σ K hab)
      refine Set.infinite_of_injective_forall_mem hinj fun t => ?_
      simp only [Set.mem_ofPred_eq, Polynomial.eval_C]
      rw [eval_rowAddGeneric, h t]
    have hd := derivative_rowAddGeneric u w huw P
    rw [hc, Polynomial.derivative_C] at hd
    rw [← eval_zero_rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P), ← hd, Polynomial.eval_zero]
  tfae_have 3 → 2 := by
    intro h t
    have hd := derivative_rowAddGeneric u w huw P
    rw [h, map_zero] at hd
    have hc := Polynomial.eq_C_of_derivative_eq_zero hd
    rw [← eval_rowAddGeneric]
    conv_rhs => rw [← eval_zero_rowAddGeneric u w P]
    rw [hc, Polynomial.eval_C, Polynomial.eval_C]
  tfae_finish

end RHLean.Geometry.NativeTheta

open MvPolynomial

namespace RHLean.Geometry.NativeTheta

theorem eval_rowOps_eq {K σ : Type*} [Field K] [DecidableEq σ] {p n : ℕ} (z : Fin p × Fin n → σ)
    (hz : Function.Injective z) (P : MvPolynomial σ K)
    (hinv : ∀ a b : Fin p, a < b → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (i : ℕ) (c : Fin p × Fin p → K) (x : σ → K) (T : Finset (Fin p × Fin p))
    (hT : ∀ q ∈ T, (q.1 : ℕ) < i ∧ i ≤ (q.2 : ℕ)) :
    eval (fun s => x s + ∑ q ∈ T, ∑ k, if s = z (q.2, k) then c q * x (z (q.1, k)) else 0) P
      = eval x P := by
  have hb : ∀ (y : σ → K) (f : σ → MvPolynomial σ K) (Q : MvPolynomial σ K),
      eval y (bind₁ f Q) = eval (fun s => eval y (f s)) Q :=
    fun y f Q => eval₂Hom_bind₁ _ _ _ _
  revert hT
  refine Finset.induction_on T ?_ ?_
  · intro _
    simp
  · intro q T hq ih hT
    have hq' := hT q (Finset.mem_insert_self q T)
    have hab : q.1 < q.2 := Fin.lt_def.2 (lt_of_lt_of_le hq'.1 hq'.2)
    set y : σ → K := fun s => x s + ∑ q' ∈ T, ∑ k, if s = z (q'.2, k) then c q' * x (z (q'.1, k)) else 0
      with hy_def
    have hy : ∀ k, y (z (q.1, k)) = x (z (q.1, k)) := by
      intro k
      rw [hy_def]
      simp only [add_eq_left]
      refine Finset.sum_eq_zero fun q' hq'T => Finset.sum_eq_zero fun k' _ => ?_
      rw [ite_eq_right]
      intro h
      have h2 := congrArg Prod.fst (hz h)
      have h3 := hT q' (Finset.mem_insert_of_mem hq'T)
      have : (q.1 : ℕ) < q'.2 := lt_of_lt_of_le hq'.1 h3.2
      simp only at h2
      rw [h2] at this
      exact lt_irrefl _ this
    have hfun : (fun s => x s + ∑ q' ∈ insert q T, ∑ k,
        if s = z (q'.2, k) then c q' * x (z (q'.1, k)) else 0) =
        fun s => eval y (X s + ∑ k, if s = z (q.2, k) then C (c q) * X (z (q.1, k)) else 0) := by
      funext s
      have he : ∀ k, eval y (if s = z (q.2, k) then C (c q) * X (z (q.1, k)) else 0) =
          if s = z (q.2, k) then c q * x (z (q.1, k)) else 0 := by
        intro k
        split_ifs
        · simp [hy]
        · simp
      rw [map_add, eval_X, map_sum, Finset.sum_congr rfl fun k _ => he k, Finset.sum_insert hq, hy_def]
      ring
    rw [hfun, ← hb, hinv q.1 q.2 hab (c q), ih fun q' h => hT q' (Finset.mem_insert_of_mem h)]

theorem eval_scale_eq {K σ : Type*} [Field K] (w : σ → ℕ) (P : MvPolynomial σ K) (x : σ → K)
    (t : K) :
    eval (fun s => t ^ w s * x s) P =
      (∑ m ∈ P.support, Polynomial.monomial (∑ s ∈ m.support, w s * m s)
        (P.coeff m * ∏ s ∈ m.support, x s ^ m s)).eval t := by
  rw [eval_eq, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_monomial]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  ring

theorem column_degree_le {K σ : Type*} [Field K] [CharZero K] [DecidableEq σ] {p n : ℕ} (z : Fin p × Fin n → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ K) (lam : Fin p → ℕ)
    (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = lam a)
    (hinv : ∀ a b : Fin p, a < b → ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (S : Finset (Fin n)) : ∀ m ∈ P.support,
      ∑ a, ∑ k ∈ S, m (z (a, k)) ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin p => (a : ℕ) < S.card), lam a := by
  classical
  intro m0 hm0
  by_cases hpr : p ≤ S.card
  · have hfil : Finset.univ.filter (fun a : Fin p => (a : ℕ) < S.card) = Finset.univ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact lt_of_lt_of_le a.isLt hpr
    rw [hfil]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← hrow a m0 hm0]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  push Not at hpr
  let Z : Finset σ := (Finset.univ ×ˢ S).image z
  let w : σ → ℕ := fun s => if s ∈ Z then 1 else 0
  have hwz : ∀ a k, w (z (a, k)) = if k ∈ S then 1 else 0 := by
    intro a k
    show (if z (a, k) ∈ Finset.image z (Finset.univ ×ˢ S) then 1 else 0) = _
    have hm : z (a, k) ∈ Finset.image z (Finset.univ ×ˢ S) ↔ k ∈ S := by
      rw [hz.mem_finset_image]
      simp
    by_cases hk : k ∈ S
    · rw [ite_eq_left (hm.2 hk), ite_eq_left hk]
    · rw [ite_eq_right (fun h => hk (hm.1 h)), ite_eq_right hk]
  have he : ∀ m : σ →₀ ℕ, ∑ s ∈ m.support, w s * m s = ∑ a, ∑ k ∈ S, m (z (a, k)) := by
    intro m
    have h1 : ∑ s ∈ m.support, w s * m s = ∑ s ∈ m.support, if s ∈ Z then m s else 0 := by
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [w]
      split_ifs <;> simp
    have h2 : ∑ s ∈ m.support ∩ Z, m s = ∑ s ∈ Z, m s := by
      refine Finset.sum_subset Finset.inter_subset_right fun s hsZ hs => ?_
      by_contra h
      exact hs (Finset.mem_inter.2 ⟨Finsupp.mem_support_iff.2 h, hsZ⟩)
    rw [h1, Finset.sum_ite_mem, h2, Finset.sum_image hz.injOn, Finset.sum_product]
  have hlow : ∀ m ∈ P.support, ∑ a ∈ Finset.univ.filter (fun a : Fin p => (a : ℕ) < S.card),
      ∑ k ∈ S, m (z (a, k)) ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin p => (a : ℕ) < S.card), lam a := by
    intro m hm
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← hrow a m hm]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  by_contra hcon
  push Not at hcon
  set j := ∑ a, ∑ k ∈ S, m0 (z (a, k)) with hj
  let R : MvPolynomial σ K :=
    ∑ m ∈ P.support.filter (fun m => ∑ a, ∑ k ∈ S, m (z (a, k)) = j), monomial m (P.coeff m)
  have hR0 : R.coeff m0 ≠ 0 := by
    have hmem : m0 ∈ P.support.filter (fun m => ∑ a, ∑ k ∈ S, m (z (a, k)) = j) :=
      Finset.mem_filter.2 ⟨hm0, rfl⟩
    simp only [R, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq' _ _ _, ite_eq_left hmem]
    exact mem_support_iff.1 hm0
  let top : Fin S.card → Fin p := Fin.castLE hpr.le
  have htop : Function.Injective top := Fin.castLE_injective _
  let ee : Fin S.card → Fin n := S.orderEmbOfFin rfl
  have hee : ∀ k ∈ S, ∃ i, ee i = k := by
    intro k hk
    have : k ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hk
    exact this
  let D : MvPolynomial σ K :=
    (Matrix.of fun a b : Fin S.card => (X (z (top a, ee b)) : MvPolynomial σ K)).det
  have hevD : ∀ y : σ → K, eval y D = (Matrix.of fun a b : Fin S.card => y (z (top a, ee b))).det := by
    intro y
    simp only [D]
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [RingHom.mapMatrix_apply]
  have hD : D ≠ 0 := by
    let x0 : σ → K := fun s => if ∃ a : Fin S.card, s = z (top a, ee a) then 1 else 0
    have hx0 : ∀ a b, x0 (z (top a, ee b)) = if a = b then 1 else 0 := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simp only [x0]
        exact ite_eq_left ⟨a, rfl⟩
      · simp only [x0, ite_eq_right hab]
        rw [ite_eq_right]
        rintro ⟨a', h⟩
        have h' := hz h
        simp only [Prod.mk.injEq] at h'
        exact hab ((htop h'.1).trans ((S.orderEmbOfFin rfl).injective h'.2).symm)
    intro h0
    have h1 := hevD x0
    rw [h0, map_zero] at h1
    have h2 : (Matrix.of fun a b : Fin S.card => x0 (z (top a, ee b))) = 1 := by
      ext a b
      rw [Matrix.of_apply, hx0, Matrix.one_apply]
    rw [h2, Matrix.det_one] at h1
    exact zero_ne_one h1
  let Q : (σ → K) → Polynomial K := fun y => ∑ m ∈ P.support,
    Polynomial.monomial (∑ s ∈ m.support, w s * m s) (P.coeff m * ∏ s ∈ m.support, y s ^ m s)
  have hQcoeff : ∀ y : σ → K, (Q y).coeff j = ∑ m ∈ P.support,
      if ∑ a, ∑ k ∈ S, m (z (a, k)) = j then P.coeff m * ∏ s ∈ m.support, y s ^ m s else 0 := by
    intro y
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, he]
  have key : ∀ x : σ → K, eval x D ≠ 0 → eval x R = 0 := by
    intro x hdet
    let M : Matrix (Fin S.card) (Fin S.card) K := Matrix.of fun a b => x (z (top a, ee b))
    have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 (by rw [← hevD]; exact hdet)
    let v : Fin p → Fin S.card → K := fun b i => x (z (b, ee i))
    let c : Fin p × Fin p → K := fun q =>
      if h : (q.1 : ℕ) < S.card then -(Matrix.vecMul (v q.2) M⁻¹) ⟨q.1, h⟩ else 0
    let B : Finset (Fin p) := Finset.univ.filter fun b : Fin p => S.card ≤ (b : ℕ)
    let T : Finset (Fin p × Fin p) := (Finset.univ.image top) ×ˢ B
    have hT : ∀ q ∈ T, (q.1 : ℕ) < S.card ∧ S.card ≤ (q.2 : ℕ) := by
      intro q hq
      simp only [T, B, Finset.mem_product, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_filter] at hq
      obtain ⟨⟨a, ha⟩, hb⟩ := hq
      refine ⟨?_, hb⟩
      rw [← ha]
      exact a.isLt
    let op : (σ → K) → σ → K := fun y s =>
      y s + ∑ q ∈ T, ∑ k, if s = z (q.2, k) then c q * y (z (q.1, k)) else 0
    let sc : K → (σ → K) → σ → K := fun t y s => t ^ w s * y s
    have hcomm : ∀ t y, op (sc t y) = sc t (op y) := by
      intro t y
      funext s
      simp only [op, sc]
      rw [mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with h
      · rw [h, hwz, hwz]
        ring
      · simp
    have hsum : ∀ b : Fin p, ∀ i, ∑ a, (Matrix.vecMul (v b) M⁻¹) a * M a i = v b i := by
      intro b i
      have h := congrFun (show Matrix.vecMul (Matrix.vecMul (v b) M⁻¹) M = v b by
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hMu, Matrix.vecMul_one]) i
      simpa [Matrix.vecMul, dotProduct] using h
    have hx'0 : ∀ b : Fin p, S.card ≤ (b : ℕ) → ∀ k ∈ S, op x (z (b, k)) = 0 := by
      intro b hb k hk
      obtain ⟨i, rfl⟩ := hee k hk
      have hinner : ∀ q : Fin p × Fin p, (∑ k, if z (b, ee i) = z (q.2, k)
          then c q * x (z (q.1, k)) else 0) = if b = q.2 then c q * x (z (q.1, ee i)) else 0 := by
        intro q
        simp only [hz.eq_iff, Prod.mk.injEq, ite_and]
        split_ifs with h
        · simp
        · simp
      simp only [op]
      rw [Finset.sum_congr rfl fun q _ => hinner q, Finset.sum_product]
      have hbB : b ∈ B := Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩
      simp only [Finset.sum_ite_eq, hbB, ite_true]
      rw [Finset.sum_image fun a _ a' _ h => htop h]
      have hc : ∀ a : Fin S.card, c (top a, b) = -(Matrix.vecMul (v b) M⁻¹) a := by
        intro a
        simp only [c]
        rw [dite_eq_left (show ((top a : Fin p) : ℕ) < S.card from a.isLt)]
        rfl
      simp only [hc, neg_mul, Finset.sum_neg_distrib]
      have := hsum b i
      simp only [M, v, Matrix.of_apply] at this
      rw [this]
      ring
    have hQ : Q x = Q (op x) := by
      refine Polynomial.funext fun t => ?_
      rw [← eval_scale_eq w P x t, ← eval_scale_eq w P (op x) t]
      change eval (sc t x) P = eval (sc t (op x)) P
      rw [← hcomm]
      exact (eval_rowOps_eq z hz P hinv S.card c (sc t x) T hT).symm
    have hRx : eval x R = (Q x).coeff j := by
      rw [hQcoeff, ← Finset.sum_filter]
      simp only [R, map_sum, eval_monomial, Finsupp.prod]
    rw [hRx, hQ, hQcoeff]
    refine Finset.sum_eq_zero fun m hm => ?_
    split_ifs with hmj
    · have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun a : Fin p => (a : ℕ) < S.card) (fun a => ∑ k ∈ S, m (z (a, k)))
      have hup : ∑ a ∈ Finset.univ.filter (fun a : Fin p => ¬ (a : ℕ) < S.card),
          ∑ k ∈ S, m (z (a, k)) ≠ 0 := by
        intro h0
        have := hlow m hm
        omega
      obtain ⟨a, ha, ha0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hup
      obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha0
      have hs : z (a, k) ∈ m.support := Finsupp.mem_support_iff.2 hk0
      have hza : op x (z (a, k)) = 0 :=
        hx'0 a (not_lt.1 (Finset.mem_filter.1 ha).2) k hk
      rw [Finset.prod_eq_zero hs (by rw [hza, zero_pow hk0]), mul_zero]
    · rfl
  have hRD : R * D = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hdet : eval x D = 0
    · rw [hdet, mul_zero]
    · rw [key x hdet, zero_mul]
  have hR : R = 0 := (mul_eq_zero.1 hRD).resolve_right hD
  exact hR0 (by rw [hR]; rfl)

end RHLean.Geometry.NativeTheta

open MvPolynomial Matrix

namespace RHLean.Geometry.NativeTheta

namespace UnipotentInvariant

variable {K : Type*} [Field K] {p : ℕ}

def rowAdd (a b : Fin p) (t : K) (M : Matrix (Fin p) (Fin p) K) : Matrix (Fin p) (Fin p) K :=
  Matrix.of fun i k => M i k + if i = b then t * M a k else 0

def BiInvariant (f : Matrix (Fin p) (Fin p) K → K) : Prop :=
  (∀ a b : Fin p, a < b → ∀ t M, f (rowAdd a b t M) = f M) ∧
  (∀ a b : Fin p, a < b → ∀ t M, f (rowAdd a b t M)ᵀ = f Mᵀ)

theorem BiInvariant.transpose {f : Matrix (Fin p) (Fin p) K → K} (h : BiInvariant f) :
    BiInvariant fun M => f Mᵀ :=
  ⟨h.2, fun a b hab t M => by simpa using h.1 a b hab t M⟩

def leadMinor (i : Fin p) (M : Matrix (Fin p) (Fin p) K) : K :=
  (Matrix.of fun a b : Fin (i.val + 1) => M (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)).det

theorem leadMinor_transpose (i : Fin p) (M : Matrix (Fin p) (Fin p) K) :
    leadMinor i Mᵀ = leadMinor i M := by
  unfold leadMinor
  rw [← det_transpose]
  rfl

theorem leadMinor_rowAdd (i a b : Fin p) (hab : a < b) (t : K) (M : Matrix (Fin p) (Fin p) K) :
    leadMinor i (rowAdd a b t M) = leadMinor i M := by
  unfold leadMinor
  by_cases hb : b.val < i.val + 1
  · have ha : a.val < i.val + 1 := lt_trans hab hb
    have hne : (⟨b.val, hb⟩ : Fin (i.val + 1)) ≠ ⟨a.val, ha⟩ := by
      intro h
      have : b.val = a.val := Fin.mk.inj h
      exact absurd hab (by simp [Fin.lt_def, this])
    rw [← det_updateRow_add_smul_self
      (Matrix.of fun a b : Fin (i.val + 1) => M (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)) hne t]
    congr 1
    ext u v
    by_cases hu : u = ⟨b.val, hb⟩
    · subst hu
      simp [rowAdd, Fin.castLE]
    · have : Fin.castLE i.isLt u ≠ b := by
        intro h
        apply hu
        ext
        simpa using congrArg Fin.val h
      simp [rowAdd, updateRow_ne hu, this]
  · congr 1
    ext u v
    have : Fin.castLE i.isLt u ≠ b := by
      intro h
      apply hb
      rw [← h]
      exact u.isLt
    simp [rowAdd, this]

theorem biInvariant_leadMinor (i : Fin p) : BiInvariant (K := K) (leadMinor i) :=
  ⟨leadMinor_rowAdd i, fun a b hab t M => by
    rw [leadMinor_transpose, leadMinor_transpose, leadMinor_rowAdd i a b hab]⟩

theorem BiInvariant.what₂ {f : Matrix (Fin p) (Fin p) K → K} (h : BiInvariant f) (n : Fin p)
    (t : Fin p → K) (M : Matrix (Fin p) (Fin p) K) (S : Finset (Fin p)) (hS : ∀ b ∈ S, n < b) :
    f (Matrix.of fun b k => M b k + if b ∈ S then t b * M n k else 0) = f M := by
  induction S using Finset.induction_on with
  | empty =>
    congr 1
    ext b k
    simp
  | insert b S hb ih =>
    have hn : n ∉ S := fun hh => lt_irrefl _ (hS n (Finset.mem_insert_of_mem hh))
    rw [← ih fun b hb => hS b (Finset.mem_insert_of_mem hb),
      ← h.1 n b (hS b (Finset.mem_insert_self _ _)) (t b)
        (Matrix.of fun b k => M b k + if b ∈ S then t b * M n k else 0)]
    congr 1
    ext u k
    by_cases hu : u = b
    · subst hu
      simp [rowAdd, hb, hn]
    · simp [rowAdd, hu]

theorem exists_clear_col (n : Fin p) (M : Matrix (Fin p) (Fin p) K) (hn : M n n ≠ 0) :
    ∃ M' : Matrix (Fin p) (Fin p) K, (∀ f, BiInvariant f → f M' = f M) ∧
      (∀ b, n < b → M' b n = 0) ∧ (∀ b k, b ≤ n → M' b k = M b k) ∧
      (∀ b k, M n k = 0 → M' b k = M b k) := by
  refine ⟨Matrix.of fun b k => M b k +
      if b ∈ Finset.Ioi n then (- M b n / M n n) * M n k else 0, fun f hf => ?_, ?_, ?_, ?_⟩
  · exact hf.what₂ n (fun b => - M b n / M n n) M _ (by simp)
  · intro b hb
    simp only [of_apply, Finset.mem_Ioi, hb, ite_true]
    field_simp
    ring
  · intro b k hb
    simp [not_lt.mpr hb]
  · intro b k hk
    simp [hk]

theorem exists_cleared (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) (n : ℕ) :
    ∃ M' : Matrix (Fin p) (Fin p) K, (∀ f, BiInvariant f → f M' = f M) ∧
      ∀ i j : Fin p, i ≠ j → (i.val < n ∨ j.val < n) → M' i j = 0 := by
  induction n with
  | zero => exact ⟨M, fun _ _ => rfl, by simp⟩
  | succ n ih =>
    obtain ⟨M₀, h₀, hz₀⟩ := ih
    by_cases hn : n < p
    swap
    · exact ⟨M₀, h₀, fun i j hij _ => hz₀ i j hij (Or.inl (by omega))⟩
    set N : Fin p := ⟨n, hn⟩ with hN
    have hpiv : M₀ N N ≠ 0 := by
      intro h0
      apply hM N
      rw [← h₀ _ (biInvariant_leadMinor N)]
      unfold leadMinor
      apply det_eq_zero_of_row_eq_zero (Fin.last n)
      intro j
      simp only [of_apply]
      by_cases hj : j = Fin.last n
      · subst hj
        exact h0
      · apply hz₀
        · intro h
          apply hj
          ext
          simpa using (congrArg Fin.val h).symm
        · right
          exact Fin.val_lt_last hj
    obtain ⟨M₁, h₁, a₁, b₁, c₁⟩ := exists_clear_col N M₀ hpiv
    have hpiv₁ : M₁ᵀ N N ≠ 0 := by
      rw [transpose_apply, b₁ N N le_rfl]
      exact hpiv
    obtain ⟨M₂, h₂, a₂, b₂, c₂⟩ := exists_clear_col N M₁ᵀ hpiv₁
    have hz₁ : ∀ i j : Fin p, i ≠ j → (i.val < n ∨ j.val < n) → M₁ i j = 0 := by
      intro i j hij h
      rcases h with h | h
      · rw [b₁ i j (by simp [Fin.le_def, hN]; omega)]
        exact hz₀ i j hij (Or.inl h)
      · rw [c₁ i j (hz₀ N j (by intro hh; rw [← hh] at h; simp [hN] at h) (Or.inr h))]
        exact hz₀ i j hij (Or.inr h)
    have hcol : ∀ i : Fin p, i ≠ N → M₁ i N = 0 := by
      intro i hi
      rcases lt_or_gt_of_ne hi with h | h
      · exact hz₁ i N hi (Or.inl h)
      · exact a₁ i h
    refine ⟨M₂ᵀ, fun f hf => ?_, ?_⟩
    · have := h₂ _ hf.transpose
      simp only [transpose_transpose] at this
      rw [this, h₁ f hf, h₀ f hf]
    · intro i j hij h
      rw [transpose_apply]
      by_cases hj : j ≤ N
      · rw [b₂ j i hj, transpose_apply]
        rcases eq_or_lt_of_le hj with hj | hj
        · subst hj
          exact hcol i hij
        · exact hz₁ i j hij (Or.inr hj)
      · have hj' : N < j := not_le.mp hj
        have hi : i.val < n + 1 := by
          rcases h with h | h
          · exact h
          · exact absurd hj' (by simp [Fin.lt_def, hN]; omega)
        by_cases hiN : i = N
        · subst hiN
          exact a₂ j hj'
        · rw [c₂ j i (hcol i hiN), transpose_apply]
          refine hz₁ i j hij (Or.inl ?_)
          have : i.val ≠ n := fun hh => hiN (Fin.ext hh)
          omega

theorem exists_diagonal (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) :
    ∃ d : Fin p → K, ∀ f, BiInvariant f → f (diagonal d) = f M := by
  obtain ⟨M', h, hz⟩ := exists_cleared M hM p
  refine ⟨fun i => M' i i, fun f hf => ?_⟩
  rw [← h f hf]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij, hz i j hij (Or.inl i.isLt)]

theorem leadMinor_diagonal (i : Fin p) (d : Fin p → K) :
    leadMinor i (diagonal d) = ∏ a ∈ Finset.Iic i, d a := by
  unfold leadMinor
  have : (Matrix.of fun a b : Fin (i.val + 1) =>
      diagonal d (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)) =
      diagonal fun a => d (Fin.castLE i.isLt a) := by
    ext a b
    simp [diagonal_apply]
  rw [this, det_diagonal]
  refine Finset.prod_bij (fun a _ => Fin.castLE i.isLt a) ?_ ?_ ?_ ?_
  · intro a _
    simp only [Finset.mem_Iic, Fin.le_def, Fin.val_castLE]
    omega
  · intro a _ b _ h
    exact Fin.castLE_injective _ h
  · intro b hb
    simp only [Finset.mem_Iic, Fin.le_def] at hb
    exact ⟨⟨b.val, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl

theorem prod_leadMinor_diagonal (d : Fin p → K) (c : Fin p → ℕ) :
    ∏ i, leadMinor i (diagonal d) ^ c i = ∏ a, d a ^ ∑ i ∈ Finset.Ici a, c i := by
  simp only [leadMinor_diagonal, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_comm' ?_
  intro x y
  simp

theorem BiInvariant.eq_mul_prod {f : Matrix (Fin p) (Fin p) K → K} (hf : BiInvariant f)
    (c : Fin p → ℕ)
    (hd : ∀ d, f (diagonal d) = f 1 * ∏ a, d a ^ ∑ i ∈ Finset.Ici a, c i)
    (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) :
    f M = f 1 * ∏ i, leadMinor i M ^ c i := by
  obtain ⟨d, h⟩ := exists_diagonal M hM
  rw [← h f hf, hd, ← prod_leadMinor_diagonal]
  simp only [h _ (biInvariant_leadMinor _)]

variable {σ : Type*} [DecidableEq σ]

noncomputable def setBlock (z : Fin p × Fin p → σ) (x : σ → K) (M : Matrix (Fin p) (Fin p) K) :
    σ → K :=
  Function.extend z (fun w => M w.1 w.2) x

omit [Field K] [DecidableEq σ] in
theorem setBlock_apply {z : Fin p × Fin p → σ} (hz : Function.Injective z) (x : σ → K)
    (M : Matrix (Fin p) (Fin p) K) (w : Fin p × Fin p) : setBlock z x M (z w) = M w.1 w.2 :=
  hz.extend_apply _ _ _

omit [Field K] [DecidableEq σ] in
theorem setBlock_of_not {z : Fin p × Fin p → σ} (x : σ → K)
    (M : Matrix (Fin p) (Fin p) K) {s : σ} (hs : ¬ ∃ w, z w = s) : setBlock z x M s = x s :=
  Function.extend_apply' _ _ _ hs

omit [DecidableEq σ] in
theorem eval_bind₁' (y : σ → K) (g : σ → MvPolynomial σ K) (P : MvPolynomial σ K) :
    eval y (bind₁ g P) = eval (fun s => eval y (g s)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P s hP => simp [hP]

theorem biInvariant_eval {z : Fin p × Fin p → σ} (hz : Function.Injective z)
    (P : MvPolynomial σ K)
    (hr : ∀ a b : Fin p, a < b → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (hc : ∀ k l : Fin p, k < l → ∀ t : K,
      bind₁ (fun s => X s + ∑ a, if s = z (a, l) then C t * X (z (a, k)) else 0) P = P)
    (x : σ → K) : BiInvariant fun M => eval (setBlock z x M) P := by
  constructor
  · intro a b hab t M
    beta_reduce
    conv_rhs => rw [← hr a b hab t, eval_bind₁']
    congr 2
    funext s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨⟨u, v⟩, rfl⟩ := hs
      simp only [setBlock_apply hz, map_add, eval_X, map_sum, hz.eq_iff, Prod.mk.injEq,
        apply_ite (eval (setBlock z x M)), map_mul, eval_C, map_zero, rowAdd, of_apply]
      by_cases hu : u = b <;> simp [hu]
    · have : ∀ w, s ≠ z w := fun w h => hs ⟨w, h.symm⟩
      simp [setBlock_of_not _ _ hs, this]
  · intro a b hab t M
    beta_reduce
    conv_rhs => rw [← hc a b hab t, eval_bind₁']
    congr 2
    funext s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨⟨u, v⟩, rfl⟩ := hs
      simp only [setBlock_apply hz, map_add, eval_X, map_sum, hz.eq_iff, Prod.mk.injEq,
        apply_ite (eval (setBlock z x Mᵀ)), map_mul, eval_C, map_zero, rowAdd, of_apply,
        transpose_apply]
      by_cases hu : v = b <;> simp [hu]
    · have : ∀ w, s ≠ z w := fun w h => hs ⟨w, h.symm⟩
      simp [setBlock_of_not _ _ hs, this]

theorem eval_setBlock_diagonal {z : Fin p × Fin p → σ} (hz : Function.Injective z)
    (P : MvPolynomial σ K) (l : Fin p → ℕ)
    (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = l a) (x : σ → K) (d : Fin p → K) :
    eval (setBlock z x (diagonal d)) P = eval (setBlock z x 1) P * ∏ a, d a ^ l a := by
  let w : σ → K := setBlock z 1 (Matrix.of fun a _ => d a)
  have hw : ∀ s, setBlock z x (diagonal d) s = setBlock z x 1 s * w s := by
    intro s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨⟨u, v⟩, rfl⟩ := hs
      simp only [w, setBlock_apply hz, diagonal_apply, one_apply, of_apply]
      split_ifs <;> simp
    · simp [w, setBlock_of_not _ _ hs]
  rw [eval_eq, eval_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [hw, mul_pow, Finset.prod_mul_distrib, mul_assoc]
  congr 2
  have h1 : ∏ s ∈ m.support, w s ^ m s = ∏ s ∈ Finset.univ.image z, w s ^ m s := by
    refine Finset.prod_congr_of_eq_on_inter ?_ ?_ fun _ _ _ => rfl
    · intro s _ hs
      have hs' : ¬ ∃ w, z w = s := by simpa using hs
      simp [w, setBlock_of_not _ _ hs']
    · intro s _ hs
      rw [Finsupp.notMem_support_iff.mp hs, pow_zero]
  rw [h1, Finset.prod_image fun _ _ _ _ h => hz h, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← hrow a m hm, ← Finset.prod_pow_eq_pow_sum]
  simp [w, setBlock_apply hz]

end UnipotentInvariant

open UnipotentInvariant in

theorem eq_mul_prod_minors {K σ : Type*} [Field K] [CharZero K] [DecidableEq σ] {p : ℕ} (z : Fin p × Fin p → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ K) (c : Fin p → ℕ)
    (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = ∑ i ∈ Finset.Ici a, c i)
    (hr : ∀ a b : Fin p, a < b → ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (hc : ∀ k l : Fin p, k < l → ∀ t : K, bind₁ (fun s => X s + ∑ a, if s = z (a, l) then C t * X (z (a, k)) else 0) P = P) :
    ∃ Q : MvPolynomial σ K, (∀ w, z w ∉ Q.vars) ∧
      P = Q * ∏ i : Fin p, (Matrix.of fun a b : Fin (i.val + 1) => (X (z (Fin.castLE i.isLt a, Fin.castLE i.isLt b)) : MvPolynomial σ K)).det ^ c i := by
  let g : σ → MvPolynomial σ K :=
    Function.extend z (fun w => C ((1 : Matrix (Fin p) (Fin p) K) w.1 w.2)) X
  let Δ : Fin p → MvPolynomial σ K := fun i => (Matrix.of fun a b : Fin (i.val + 1) =>
    (X (z (Fin.castLE i.isLt a, Fin.castLE i.isLt b)) : MvPolynomial σ K)).det
  have hΔ : ∀ (x : σ → K) i, eval x (Δ i) = leadMinor i (Matrix.of fun a b => x (z (a, b))) := by
    intro x i
    simp only [Δ, leadMinor]
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp
  have hg : ∀ x : σ → K, eval x (bind₁ g P) = eval (setBlock z x 1) P := by
    intro x
    rw [eval_bind₁']
    congr 2
    funext s
    by_cases hs : ∃ w, z w = s
    · obtain ⟨w, rfl⟩ := hs
      simp [g, setBlock_apply hz, hz.extend_apply]
    · simp [g, setBlock_of_not _ _ hs, Function.extend_apply' _ _ _ hs]
  refine ⟨bind₁ g P, ?_, ?_⟩
  · intro w hw
    obtain ⟨s, -, hs'⟩ := mem_vars_bind₁ g P hw
    by_cases hs : ∃ w, z w = s
    · obtain ⟨w', rfl⟩ := hs
      simp [g, hz.extend_apply] at hs'
    · simp only [g, Function.extend_apply' _ _ _ hs, vars_X, Finset.mem_singleton] at hs'
      exact hs ⟨w, hs'⟩
  · have hne : ∏ i, Δ i ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun i _ h => ?_
      have := hΔ (setBlock z 0 1) i
      rw [h, map_zero] at this
      have h1 : (Matrix.of fun a b => setBlock z (0 : σ → K) 1 (z (a, b))) = diagonal fun _ => 1 := by
        ext a b
        simp [setBlock_apply hz]
      rw [h1, leadMinor_diagonal] at this
      simp at this
    apply mul_left_cancel₀ hne
    apply MvPolynomial.funext
    intro x
    change eval x (_ * P) = eval x (_ * (_ * ∏ i, Δ i ^ c i))
    simp only [map_mul, map_prod, map_pow, hΔ, hg]
    by_cases h : ∀ i, leadMinor i (Matrix.of fun a b => x (z (a, b))) ≠ 0
    · congr 1
      have hx : setBlock z x (Matrix.of fun a b => x (z (a, b))) = x := by
        funext s
        by_cases hs : ∃ w, z w = s
        · obtain ⟨w, rfl⟩ := hs
          simp [setBlock_apply hz]
        · exact setBlock_of_not _ _ hs
      have := (biInvariant_eval hz P hr hc x).eq_mul_prod c
        (eval_setBlock_diagonal hz P _ hrow x) _ h
      simpa only [hx] using this
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul, zero_mul]

end RHLean.Geometry.NativeTheta
