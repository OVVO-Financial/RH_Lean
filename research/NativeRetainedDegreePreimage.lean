import «research.NativeWheelLevelAttachment»
import Mathlib.RingTheory.Coprime.Lemmas

/-! Exact degree-clearing on the retained physical star, rather than on
all ambient coefficient coordinates. The root constraint is retained.
This is a finite preimage calculation; it does not assume a signed
asymptotic bound. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Matrix

namespace RHLean.Analysis.AlpogeThin.SlotProjector.RetainedDegree

/-- Every repeated slot in a physical layer must satisfy the finite
degree condition. The greatest required exponent is attained. -/
def layerMax {r : ℕ} (A : Fin (r+1) → Finset ℕ)
    (g : Fin (r+1) → ℕ → ℕ) (i : Fin (r+1)) : ℕ :=
  (A i).sup (g i)

theorem layer_dvd_iff {r : ℕ} (A : Fin (r+1) → Finset ℕ)
    (g : Fin (r+1) → ℕ → ℕ) (i : Fin (r+1)) (hA : (A i).Nonempty)
    (N z : ℤ) :
    (∀ k ∈ A i, N^(g i k) ∣ z) ↔ N^(layerMax A g i) ∣ z := by
  constructor
  · intro h
    obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup (A i) hA (g i)
    rw [layerMax, he]
    exact h k hk
  · intro h k hk
    exact (pow_dvd_pow N (Finset.le_sup hk : g i k ≤ layerMax A g i)).trans h

theorem leaf_read {r : ℕ} (A : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (u : Fin r → ℤ) (i : Fin r) (k : ↥(A i.succ)) :
    (columns A D).mulVec u ⟨i.succ,k⟩ = (D i.succ:ℤ)*u i := by
  classical
  change (∑ j, starColumn D j i.succ k.val * u j) = _
  rw [Finset.sum_eq_single i]
  · simp [starColumn]
  · intro j _ hj
    have hn : i.succ ≠ j.succ := fun he => hj ((Fin.succ_injective r he).symm)
    simp [starColumn, hn]
  · simp

theorem root_read {r : ℕ} (A : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (u : Fin r → ℤ) (k : ↥(A 0)) :
    (columns A D).mulVec u ⟨0,k⟩ = -(D 0:ℤ)*(∑ i, u i) := by
  change (∑ j, starColumn D j 0 k.val * u j) = _
  simp only [starColumn, (Fin.succ_ne_zero _).symm, ite_false, ite_true, zero_sub,
    Finset.mul_sum]

/-- The precise preimage condition on the original star columns at a
level coprime to the admitted depth primes. No ambient polynomial
basis is counted in the retained rank. -/
theorem physical_clearing_iff {r : ℕ} (A : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (g : Fin (r+1) → ℕ → ℕ)
    (hA : ∀ i, (A i).Nonempty) (N : ℤ)
    (hc : ∀ i, IsCoprime N (D i:ℤ)) (u : Fin r → ℤ) :
    (∀ z : Address A, N^(g z.1 z.2.val) ∣ (columns A D).mulVec u z) ↔
      (∀ j : Fin r, N^(layerMax A g j.succ) ∣ u j) ∧
      N^(layerMax A g 0) ∣ ∑ j, u j := by
  have root (k : ↥(A 0)) :
      N^(g 0 k.val) ∣ (columns A D).mulVec u ⟨0,k⟩ ↔
        N^(g 0 k.val) ∣ ∑ j, u j := by
    rw [root_read, neg_mul, dvd_neg]
    exact (hc 0).pow_left.dvd_mul_left_iff
  have leaf (j : Fin r) (k : ↥(A j.succ)) :
      N^(g j.succ k.val) ∣ (columns A D).mulVec u ⟨j.succ,k⟩ ↔
        N^(g j.succ k.val) ∣ u j := by
    rw [leaf_read]
    exact (hc j.succ).pow_left.dvd_mul_left_iff
  constructor
  · intro H
    refine ⟨fun j => (layer_dvd_iff A g j.succ (hA _) N _).1
      (fun k hk => (leaf j ⟨k,hk⟩).1 (H ⟨j.succ,⟨k,hk⟩⟩)), ?_⟩
    exact (layer_dvd_iff A g 0 (hA 0) N _).1
      (fun k hk => (root ⟨k,hk⟩).1 (H ⟨0,⟨k,hk⟩⟩))
  · rintro ⟨L,R⟩ ⟨i,k⟩
    revert k
    refine Fin.cases ?_ (fun j => ?_) i
    · intro k
      exact (root k).2 ((layer_dvd_iff A g 0 (hA 0) N _).2 R k.val k.property)
    · intro k
      exact (leaf j k).2 ((layer_dvd_iff A g j.succ (hA _) N _).2 (L j) k.val k.property)

section Rooted

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Unimodular coordinates: record the total in the pivot and keep the
other original leaf coordinates. -/
def rooted (p : I) (u : I → ℤ) : I → ℤ :=
  fun i => if i=p then ∑ j, u j else u i

def unrooted (p : I) (v : I → ℤ) : I → ℤ :=
  fun i => if i=p then v p - ∑ j ∈ Finset.univ.erase p, v j else v i

theorem rooted_unrooted (p : I) (v : I → ℤ) : rooted p (unrooted p v) = v := by
  funext i
  by_cases hi : i=p
  · subst i
    rw [rooted, ite_eq_left rfl, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    simp only [unrooted, ite_true]
    have h : (∑ j ∈ Finset.univ.erase p, (if j=p then v p - ∑ k ∈ Finset.univ.erase p, v k else v j)) =
        ∑ j ∈ Finset.univ.erase p, v j :=
      Finset.sum_congr rfl fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj)
    rw [h]
    ring
  · simp [rooted, unrooted, hi]

theorem unrooted_rooted (p : I) (u : I → ℤ) : unrooted p (rooted p u) = u := by
  funext i
  by_cases hi : i=p
  · subst i
    simp only [unrooted, ite_true, rooted]
    have h : (∑ j ∈ Finset.univ.erase p, (if j=p then ∑ k, u k else u j)) =
        ∑ j ∈ Finset.univ.erase p, u j :=
      Finset.sum_congr rfl fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj)
    rw [h, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    ring
  · simp [rooted, unrooted, hi]

/-- The pivot has the least exponent. In the total coordinate the
root constraint then changes only this one exponent. -/
def rootedDegree (E : I → ℕ) (m : ℕ) (p : I) (i : I) : ℕ :=
  if i=p then max m (E p) else E i

theorem rooted_dvd_iff (N : ℤ) (E : I → ℕ) (m : ℕ) (p : I)
    (hp : ∀ i, E p ≤ E i) (u : I → ℤ) :
    ((∀ i, N^(E i) ∣ u i) ∧ N^m ∣ ∑ i, u i) ↔
      ∀ i, N^(rootedDegree E m p i) ∣ rooted p u i := by
  constructor
  · rintro ⟨h,hroot⟩ i
    by_cases hi : i=p
    · subst i
      have hsum : N^(E p) ∣ ∑ j, u j :=
        Finset.dvd_sum fun j _ => (pow_dvd_pow N (hp j)).trans (h j)
      rw [rootedDegree, rooted, ite_eq_left rfl, ite_eq_left rfl]
      rcases le_total m (E p) with hle | hle
      · rwa [max_eq_right hle]
      · rwa [max_eq_left hle]
    · simpa [rootedDegree, rooted, hi] using h i
  · intro h
    have htotal : N^(max m (E p)) ∣ ∑ j, u j := by
      simpa [rootedDegree, rooted] using h p
    refine ⟨fun i => ?_, (pow_dvd_pow N (le_max_left _ _)).trans htotal⟩
    by_cases hi : i=p
    · subst i
      have hsum : N^(E p) ∣ ∑ j ∈ Finset.univ.erase p, u j := by
        apply Finset.dvd_sum
        intro j hj
        have hjp := Finset.ne_of_mem_erase hj
        exact (pow_dvd_pow N (hp j)).trans (by
          simpa [rootedDegree, rooted, hjp] using h j)
      have hu : N^(E p) ∣ (∑ j, u j) - ∑ j ∈ Finset.univ.erase p, u j :=
        dvd_sub ((pow_dvd_pow N (le_max_right _ _)).trans htotal) hsum
      rwa [← Finset.add_sum_erase _ _ (Finset.mem_univ p), add_sub_cancel_right] at hu
    · simpa [rootedDegree, rooted, hi] using h i

/-- The exact full retained preimage, parametrized by one integral
coefficient vector. In particular, this construction does not drop a
single original star column. -/
theorem rooted_preimage (N : ℤ) (E : I → ℕ) (m : ℕ) (p : I)
    (hp : ∀ i, E p ≤ E i) (u : I → ℤ) :
    ((∀ i, N^(E i) ∣ u i) ∧ N^m ∣ ∑ i, u i) ↔
      ∃ w : I → ℤ, u = unrooted p (fun i => N^(rootedDegree E m p i)*w i) := by
  rw [rooted_dvd_iff N E m p hp]
  constructor
  · intro h
    choose w hw using h
    refine ⟨w, ?_⟩
    have he : rooted p u = fun i => N^(rootedDegree E m p i)*w i := funext hw
    rw [← he, unrooted_rooted]
  · rintro ⟨w,rfl⟩ i
    rw [rooted_unrooted]
    exact dvd_mul_right _ _

/-- The matrix of the inverse rooted coordinates; changing the pivot
row costs determinant one. -/
def unrootMatrix (p : I) : Matrix I I ℤ :=
  (1 : Matrix I I ℤ).updateRow p (fun j => if j=p then 1 else -1)

theorem unrootMatrix_det (p : I) : (unrootMatrix p).det = 1 := by
  classical
  let c : I → ℤ := fun j => if j=p then 1 else -1
  have he : (∑ j, c j • (fun k : I => (1 : Matrix I I ℤ) j k)) = c := by
    funext k
    simp [Finset.sum_apply, Matrix.one_apply, mul_ite]
  have h := Matrix.det_updateRow_sum (1 : Matrix I I ℤ) p c
  change ((1 : Matrix I I ℤ).updateRow p
    (∑ j, c j • (fun k : I => (1 : Matrix I I ℤ) j k))).det = _ at h
  rw [he] at h
  simpa [unrootMatrix, c] using h

theorem unrootMatrix_mulVec (p : I) (v : I → ℤ) :
    (unrootMatrix p).mulVec v = unrooted p v := by
  classical
  funext i
  by_cases hi : i=p
  · subst i
    change (∑ j, unrootMatrix p p j * v j) = _
    have h (j : I) : unrootMatrix p p j = if j=p then 1 else -1 := by
      rw [unrootMatrix, Matrix.updateRow_self]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    simp only [h, ite_true, one_mul, unrooted]
    have he : (∑ j ∈ Finset.univ.erase p, (if j=p then 1 else -1)*v j) =
        -(∑ j ∈ Finset.univ.erase p, v j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_right (Finset.ne_of_mem_erase hj), neg_one_mul]
    rw [he, sub_eq_add_neg]
  · change (∑ j, unrootMatrix p i j * v j) = _
    have h (j : I) : unrootMatrix p i j = (1 : Matrix I I ℤ) i j := by
      rw [unrootMatrix, Matrix.updateRow_ne hi]
    simp [h, Matrix.one_apply, unrooted, hi, ite_mul]

def preimageFrame (N : ℤ) (E : I → ℕ) (m : ℕ) (p : I) : Matrix I I ℤ :=
  unrootMatrix p * Matrix.diagonal (fun i => N^(rootedDegree E m p i))

theorem preimageFrame_image (N : ℤ) (E : I → ℕ) (m : ℕ) (p : I)
    (hp : ∀ i, E p ≤ E i) (u : I → ℤ) :
    ((∀ i, N^(E i) ∣ u i) ∧ N^m ∣ ∑ i, u i) ↔
      ∃ w : I → ℤ, u = (preimageFrame N E m p).mulVec w := by
  rw [rooted_preimage N E m p hp]
  have hd (w : I → ℤ) : (Matrix.diagonal (fun i => N^(rootedDegree E m p i))).mulVec w =
      fun i => N^(rootedDegree E m p i)*w i :=
    funext fun i => Matrix.mulVec_diagonal _ _ i
  simp only [preimageFrame, ← Matrix.mulVec_mulVec, unrootMatrix_mulVec, hd]

theorem rootedDegree_sum (E : I → ℕ) (m : ℕ) (p : I) :
    (∑ i, rootedDegree E m p i) = (∑ i, E i) + (m-E p) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    ← Finset.add_sum_erase Finset.univ E (Finset.mem_univ p)]
  have he : (∑ i ∈ Finset.univ.erase p, rootedDegree E m p i) =
      ∑ i ∈ Finset.univ.erase p, E i :=
    Finset.sum_congr rfl fun i hi => ite_eq_right (Finset.ne_of_mem_erase hi)
  rw [he]
  simp only [rootedDegree, ite_true]
  omega

/-- Sharp clearing determinant: only the root excess above the least
leaf exponent is paid in addition to the leaf exponents. -/
theorem preimageFrame_det (N : ℤ) (E : I → ℕ) (m : ℕ) (p : I) :
    (preimageFrame N E m p).det = N^((∑ i, E i)+(m-E p)) := by
  rw [preimageFrame, Matrix.det_mul, unrootMatrix_det, one_mul,
    Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, rootedDegree_sum]

end Rooted

/-- The actual retained physical star preimage and its exact determinant,
on one frame and on the same original slot matrices. -/
theorem physical_preimage {r : ℕ} (A : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (g : Fin (r+1) → ℕ → ℕ)
    (hA : ∀ i, (A i).Nonempty) (N : ℤ)
    (hc : ∀ i, IsCoprime N (D i:ℤ)) (p : Fin r)
    (hp : ∀ i : Fin r, layerMax A g p.succ ≤ layerMax A g i.succ) :
    let E := fun i : Fin r => layerMax A g i.succ
    let m := layerMax A g 0
    let B := preimageFrame N E m p
    (∀ u : Fin r → ℤ,
      (∀ z : Address A, N^(g z.1 z.2.val) ∣ (columns A D).mulVec u z) ↔
        ∃ w : Fin r → ℤ, u = B.mulVec w) ∧
      B.det = N^((∑ i, E i)+(m-E p)) := by
  dsimp only
  refine ⟨fun u => (physical_clearing_iff A D g hA N hc u).trans
    (preimageFrame_image N _ _ p hp u), preimageFrame_det N _ _ p⟩

end RHLean.Analysis.AlpogeThin.SlotProjector.RetainedDegree
