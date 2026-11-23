import Mathlib

/-!
# Integral adjugate perpendicular vectors and their exact size bound

The vector is constructed using a determinant and adjugate, so no division
or chosen inverse enters the integral lattice. The factorial size estimate
is the one consumed by the source finite harmonic family.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/`
`FormPerpVectorMemOfIntegral.lean`, the Covector, Size and Degree sections.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators Nat

namespace RHLean.Geometry.NativeTheta.Perpendicular

section Covector

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

def pairingMatrix (ε : ι → Module.Dual R M) (e' : ι → M) : Matrix ι ι R :=
  Matrix.of fun a' a => ε a (e' a')

def perpVector (ε : ι → Module.Dual R M) (e' : ι → M) (g : M) : M :=
  (pairingMatrix ε e').det • g
    - ∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a'

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem pairingMatrix_apply (ε : ι → Module.Dual R M) (e' : ι → M) (a' a : ι) :
    pairingMatrix ε e' a' a = ε a (e' a') := rfl

theorem apply_perpVector (ε : ι → Module.Dual R M) (e' : ι → M) (g : M) (c : ι) :
    ε c (perpVector ε e' g) = 0 := by
  have key : ∀ a, ∑ a', (pairingMatrix ε e').adjugate a a' * ε a g * ε c (e' a')
      = ε a g * ((pairingMatrix ε e').det * if a = c then 1 else 0) := by
    intro a
    have h := congrFun (congrFun (Matrix.adjugate_mul (pairingMatrix ε e')) a) c
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [pairingMatrix_apply]; ring
  simp only [perpVector, map_sub, map_sum, map_smul, smul_eq_mul, key]
  simp [mul_comm]

theorem perpVector_of_apply_eq_zero (ε : ι → Module.Dual R M) (e' : ι → M) {g : M}
    (hg : ∀ a, ε a g = 0) : perpVector ε e' g = (pairingMatrix ε e').det • g := by
  simp [perpVector, hg]

theorem map_perpVector {S N : Type*} [CommRing S] [AddCommGroup N] [Module S N] {ρ : R →+* S}
    (ψ : M →ₛₗ[ρ] N) (ε : ι → Module.Dual R M) (η : ι → Module.Dual S N) (e' : ι → M) (g : M)
    (he : ∀ a a', η a (ψ (e' a')) = ρ (ε a (e' a'))) (hg : ∀ a, η a (ψ g) = ρ (ε a g)) :
    ψ (perpVector ε e' g) = perpVector η (fun a => ψ (e' a)) (ψ g) := by
  have hm : pairingMatrix η (fun a => ψ (e' a)) = ρ.mapMatrix (pairingMatrix ε e') := by
    ext a' a; simp [he]
  simp only [perpVector, map_sub, map_sum, LinearMap.map_smulₛₗ, hm, ← RingHom.map_det,
    ← RingHom.map_adjugate, hg, map_mul]
  simp

section Integral

variable {A : Type*} [CommRing A] [Algebra A R]

theorem det_pairingMatrix_mem_range (ε : ι → Module.Dual R M) (e' : ι → M)
    (he : ∀ a a', ε a (e' a') ∈ (algebraMap A R).range) :
    (pairingMatrix ε e').det ∈ (algebraMap A R).range := by
  choose x hx using he
  have hm : pairingMatrix ε e' = (algebraMap A R).mapMatrix (Matrix.of fun a' a => x a a') := by
    ext a' a; simp [hx]
  exact ⟨(Matrix.of fun a' a => x a a').det, by rw [hm, RingHom.map_det]⟩

theorem perpVector_mem [Module A M] [IsScalarTower A R M] (L : Submodule A M)
    (ε : ι → Module.Dual R M) {e' : ι → M} {g : M} (he' : ∀ a, e' a ∈ L) (hgL : g ∈ L)
    (he : ∀ a a', ε a (e' a') ∈ (algebraMap A R).range)
    (hg : ∀ a, ε a g ∈ (algebraMap A R).range) : perpVector ε e' g ∈ L := by
  choose x hx using he
  choose y hy using hg
  have hm : pairingMatrix ε e' = (algebraMap A R).mapMatrix (Matrix.of fun a' a => x a a') := by
    ext a' a; simp [hx]
  rw [perpVector, hm, ← RingHom.map_det, ← RingHom.map_adjugate]
  refine L.sub_mem ?_ (L.sum_mem fun a _ => L.sum_mem fun a' _ => ?_)
  · rw [algebraMap_smul]; exact L.smul_mem _ hgL
  · rw [← hy, RingHom.mapMatrix_apply, Matrix.map_apply, ← map_mul, algebraMap_smul]
    exact L.smul_mem _ (he' a')

end Integral

end Covector

section Size

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem seminorm_sum_le {G κ : Type*} [AddCommGroup G] (ν : AddGroupSeminorm G)
    (s : Finset κ) (x : κ → G) {C : ℝ} (hx : ∀ k ∈ s, ν (x k) ≤ C) :
    ν (∑ k ∈ s, x k) ≤ s.card * C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.card_insert_of_notMem hk]
    have h1 := map_add_le_add ν (x k) (∑ k ∈ s, x k)
    have h2 := hx k (Finset.mem_insert_self _ _)
    have h3 := ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    push_cast
    linarith

private theorem ringSeminorm_prod_le {κ : Type*} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (s : Finset κ) (x : κ → R) {C : ℝ} (hx : ∀ k ∈ s, ν (x k) ≤ C) :
    ν (∏ k ∈ s, x k) ≤ C ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h1
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.card_insert_of_notMem hk, pow_succ']
    have h2 := hx k (Finset.mem_insert_self _ _)
    have h3 := ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    exact (map_mul_le_mul ν _ _).trans
      (mul_le_mul h2 h3 (apply_nonneg ν _) ((apply_nonneg ν _).trans h2))

theorem ringSeminorm_det_le {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : RingSeminorm R)
    (h1 : ν 1 ≤ 1) (H : Matrix ι ι R) {C : ℝ} (hH : ∀ i j, ν (H i j) ≤ C) :
    ν H.det ≤ (Fintype.card ι)! * C ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  have := seminorm_sum_le ν.toAddGroupSeminorm Finset.univ
    (fun σ : Equiv.Perm ι => Equiv.Perm.sign σ • ∏ i, H (σ i) i) (C := C ^ Fintype.card ι) (by
      intro σ _
      have h := ringSeminorm_prod_le ν h1 Finset.univ (fun i => H (σ i) i) fun i _ => hH _ _
      rw [Finset.card_univ] at h
      change ν _ ≤ _
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]; exact h
      · rw [hs, Units.neg_smul, one_smul, map_neg_eq_map]; exact h)
  rwa [Finset.card_univ, Fintype.card_perm] at this

theorem ringSeminorm_adjugate_le {n : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {C : ℝ} (hH : ∀ i j, ν (H i j) ≤ C)
    (i j : Fin (n + 1)) : ν (H.adjugate i j) ≤ n ! * C ^ n := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have h := ringSeminorm_det_le ν h1 (H.submatrix j.succAbove i.succAbove) (C := C)
    fun _ _ => hH _ _
  rw [Fintype.card_fin] at h
  rcases neg_one_pow_eq_or R ((j : ℕ) + i) with hs | hs
  · rw [hs, one_mul]; exact h
  · rw [hs, neg_one_mul, map_neg_eq_map]; exact h

theorem seminorm_perpVector_le {p : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (μ : AddGroupSeminorm M) (hsmul : ∀ (x : R) (v : M), μ (x • v) ≤ ν x * μ v)
    (ε : Fin p → Module.Dual R M) (e' : Fin p → M) (g : M) {C r : ℝ}
    (he : ∀ a a', ν (ε a (e' a')) ≤ C) (hg : ∀ a, ν (ε a g) ≤ C)
    (he' : ∀ a, μ (e' a) ≤ r) (hgr : μ g ≤ r) :
    μ (perpVector ε e' g) ≤ (p + 1)! * C ^ p * r := by
  have hdet := ringSeminorm_det_le ν h1 (pairingMatrix ε e') (C := C) fun i j => he j i
  rw [Fintype.card_fin] at hdet
  have hA : μ ((pairingMatrix ε e').det • g) ≤ p ! * C ^ p * r :=
    (hsmul _ _).trans (mul_le_mul hdet hgr (apply_nonneg μ _) ((apply_nonneg ν _).trans hdet))
  have hB : μ (∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
      ≤ p * (p ! * C ^ p * r) := by
    cases p with
    | zero => simp
    | succ n =>
      have h := seminorm_sum_le μ Finset.univ
        (fun a => ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
        (C := ((n + 1 : ℕ) : ℝ) * (n ! * C ^ n * C * r)) (by
          intro a _
          have h' := seminorm_sum_le μ Finset.univ
            (fun a' => ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
            (C := n ! * C ^ n * C * r) (by
              intro a' _
              have hadj := ringSeminorm_adjugate_le ν h1 (pairingMatrix ε e') (C := C)
                (fun i j => he j i) a a'
              have hm : ν ((pairingMatrix ε e').adjugate a a' * ε a g) ≤ n ! * C ^ n * C :=
                (map_mul_le_mul ν _ _).trans
                  (mul_le_mul hadj (hg a) (apply_nonneg ν _) ((apply_nonneg ν _).trans hadj))
              exact (hsmul _ _).trans
                (mul_le_mul hm (he' a') (apply_nonneg μ _) ((apply_nonneg ν _).trans hm)))
          rwa [Finset.card_univ, Fintype.card_fin] at h')
      rw [Finset.card_univ, Fintype.card_fin] at h
      refine h.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]; push_cast; ring
  have hsub := map_sub_le_add μ ((pairingMatrix ε e').det • g)
    (∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
  rw [perpVector, Nat.factorial_succ]
  push_cast
  linarith

end Size

section Degree

open MvPolynomial

variable {S τ : Type*} [CommRing S]

theorem totalDegree_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (MvPolynomial τ S)) {d : ℕ} (hH : ∀ i j, (H i j).totalDegree ≤ d) :
    H.det.totalDegree ≤ Fintype.card ι * d := by
  rw [Matrix.det_apply]
  refine totalDegree_finsetSum_le fun σ _ => ?_
  have h : (∏ i, H (σ i) i).totalDegree ≤ Fintype.card ι * d :=
    (totalDegree_finsetProd _ _).trans <| by
      simpa using Finset.sum_le_card_nsmul Finset.univ (fun i => (H (σ i) i).totalDegree) d
        fun i _ => hH _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact h
  · rw [hs, Units.neg_smul, one_smul, totalDegree_neg]; exact h

theorem totalDegree_perpVector_le {p : ℕ} {κ : Type*}
    (ε : Fin p → Module.Dual (MvPolynomial τ S) (κ → MvPolynomial τ S))
    (e' : Fin p → κ → MvPolynomial τ S) (g : κ → MvPolynomial τ S) {d m : ℕ}
    (he : ∀ a a', (ε a (e' a')).totalDegree ≤ d) (hg : ∀ a, (ε a g).totalDegree ≤ d)
    (he' : ∀ a k, (e' a k).totalDegree ≤ m) (hgm : ∀ k, (g k).totalDegree ≤ m) (k : κ) :
    (perpVector ε e' g k).totalDegree ≤ p * d + m := by
  have hdet := totalDegree_det_le (pairingMatrix ε e') (d := d) fun i j => he j i
  rw [Fintype.card_fin] at hdet
  simp only [perpVector, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (add_le_add hdet (hgm k))
  · refine totalDegree_finsetSum_le fun a _ => totalDegree_finsetSum_le fun a' _ => ?_
    refine (totalDegree_mul _ _).trans (add_le_add ?_ (he' a' k))
    cases p with
    | zero => exact a.elim0
    | succ n =>
      refine (totalDegree_mul _ _).trans ?_
      rw [Nat.succ_mul]
      refine add_le_add ?_ (hg a)
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      have h := totalDegree_det_le ((pairingMatrix ε e').submatrix a'.succAbove a.succAbove)
        (d := d) fun _ _ => he _ _
      rw [Fintype.card_fin] at h
      rcases neg_one_pow_eq_or (MvPolynomial τ S) ((a' : ℕ) + a) with hs | hs
      · rw [hs, one_mul]; exact h
      · rw [hs, neg_one_mul, totalDegree_neg]; exact h

end Degree

end RHLean.Geometry.NativeTheta.Perpendicular

end
