import «research.NativeMeasuredSlotProjector»
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The local index and translated frame of the measured high first-prime sections.
All translates at a partner site use its original integer slot numbers. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin.SlotProjector

/-- Reduction of all measured star pairings on one finite lattice of slot
functions. The different depth requirements are imposed at the same prime. -/
def residueRead {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (p : ℕ) (depth : Fin r → ℕ) :
    (Address S → ℤ) →+ ((i : Fin r) → ZMod (p^depth i)) where
  toFun z i := ((Matrix.vecMul z (columns S D) i : ℤ) : ZMod (p^depth i))
  map_zero' := by funext i; simp
  map_add' z w := by funext i; simp [Matrix.add_vecMul]

/-- The index of joint divisibility is exact, including unequal depths.
Enforcing it solely by restriction pays the full gross prime power. -/
theorem residueRead_index {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i)
    (cop : Pairwise (fun i j => (D i).Coprime (D j))) (p : ℕ) (hp : p.Prime)
    (depth : Fin r → ℕ) :
    (residueRead S D p depth).ker.index = p^(∑ i, depth i) := by
  classical
  let F := residueRead S D p depth
  let (i : Fin r) : NeZero (p^depth i) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨Y, hY⟩ := left_inverse S D hS hD cop
  have onto : Function.Surjective F := by
    intro y
    choose v hv using fun i => ZMod.intCast_surjective (y i)
    refine ⟨Matrix.vecMul v Y, funext fun i => ?_⟩
    change ((Matrix.vecMul (Matrix.vecMul v Y) (columns S D) i : ℤ) : ZMod (p^depth i)) = _
    rw [Matrix.vecMul_vecMul, hY, Matrix.vecMul_one]
    exact hv i
  change F.ker.index = _
  rw [AddSubgroup.index_ker, F.range_eq_top_of_surjective onto, AddSubgroup.card_top]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card, Finset.prod_pow_eq_pow_sum]

/-- At a positive first-prime partner with host coordinate s, Frobenius
determines the top uniquely. Thus the fibre is a set of actual primes. -/
def partnerPrimes {H : Type*} [AddCommGroup H] [DecidableEq H]
    (tops : Finset H) (primes : Finset ℕ) (frob : ℕ → H) (s : H) : Finset ℕ :=
  primes.filter (fun p => s - frob p ∈ tops)

/-- One star with k cuts has k-1 independent columns. Across physical sites
the exact missing count is one per occupied site, for any pattern of collisions. -/
theorem partnerPrimes_rank {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops : Finset H) (primes : Finset ℕ) (frob : ℕ → H) :
    (∑ s : H, ((partnerPrimes tops primes frob s).card - 1)) +
      (Finset.univ.filter (fun s : H => (partnerPrimes tops primes frob s).Nonempty)).card =
      tops.card * primes.card := by
  classical
  let N := fun s => (partnerPrimes tops primes frob s).card
  have card (p : ℕ) : (Finset.univ.filter (fun s : H => s - frob p ∈ tops)).card = tops.card := by
    have hs : Finset.univ.filter (fun s : H => s - frob p ∈ tops) =
        tops.map (Equiv.addRight (frob p)).toEmbedding := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h
        exact ⟨s - frob p, h, sub_add_cancel _ _⟩
      · rintro ⟨t, ht, rfl⟩
        simpa using ht
    rw [hs, Finset.card_map]
  have total : ∑ s : H, N s = tops.card * primes.card := by
    simp only [N, partnerPrimes, Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _p ∈ primes, tops.card := Finset.sum_congr rfl fun p _ =>
        (by simpa only [Finset.card_filter] using card p)
      _ = _ := by simp [Nat.mul_comm]
  rw [← total, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : (partnerPrimes tops primes frob s).Nonempty
  · have := hs.card_pos
    simp only [hs, ite_true, N]
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs, N]

/-- Insert a band address at its actual integer coordinate. -/
private def slotInclusion {I J : Type*} [DecidableEq J] (f : I ↪ J) : Matrix J I ℝ :=
  fun k i => if k = f i then 1 else 0

private theorem inclusion_gram {I J : Type*} [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : I ↪ J) : (slotInclusion f).transpose * slotInclusion f = 1 := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.mul_apply, slotInclusion, ite_mul]
  · simp [Matrix.mul_apply, slotInclusion, ite_mul, Matrix.one_apply, h, f.injective.ne h]

/-- All widths at a partner site embed into one interval by forgetting
the layer index. Each row keeps its original quotient-slot number. -/
def physicalAddress {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) :
    Address (bands h v) ↪ ↥(Finset.Iic ⌊h 0⌋₊) :=
  (Classical.choose (original_addresses h v hne)).toEmbedding.trans
    { toFun := fun k => ⟨k.val, Finset.mem_Iic.mpr (Finset.mem_Ioc.mp k.property).2⟩
      inj' := fun _ _ he => Subtype.ext (congrArg Subtype.val he) }

theorem physicalAddress_val {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (a : Address (bands h v)) :
    (physicalAddress h v hne a).val = a.2.val :=
  Classical.choose_spec (original_addresses h v hne) a

/-- The measured integral columns in a fixed counting metric for every
width on this site. Rows outside the original band have zero coefficient. -/
def physicalColumns {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) :
    Matrix (↥(Finset.Iic ⌊h 0⌋₊)) (Fin r) ℝ :=
  slotInclusion (physicalAddress h v hne) * (columns (bands h v) D).map (Int.castRingHom ℝ)

private theorem physical_gram {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i) :
    let B := physicalColumns h v hne D
    IsUnit (B.transpose * B).det := by
  classical
  let S := bands h v
  let A := columns S D
  let f := Int.castRingHom ℝ
  let C := A.map f
  let E := slotInclusion (physicalAddress h v hne)
  have red : (E*C).transpose * (E*C) = C.transpose * C := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc E.transpose E C,
      inclusion_gram, Matrix.one_mul]
  have mapGram : f (A.transpose*A).det = (C.transpose*C).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]
    rfl
  let s := fun i => (S i).card * D i^2
  have hs (i) : 0 < s i := Nat.mul_pos (Finset.card_pos.mpr (hne i)) (pow_pos (hD i) _)
  have hmass : 0 < mass s :=
    Finset.sum_pos (fun i _ => Finset.prod_pos fun j _ => hs j) Finset.univ_nonempty
  have det : (A.transpose*A).det = (mass s : ℕ) := columns_det S D hne hD
  change IsUnit ((E*C).transpose * (E*C)).det
  rw [red, ← mapGram, det]
  apply isUnit_iff_ne_zero.mpr
  change ((mass s : ℕ) : ℝ) ≠ 0
  exact_mod_cast hmass.ne'

/-- The adjoint in the induced Gram metric on the domain. -/
def slotAdjoint {J : Type*} [Fintype J] {r : ℕ} (B : Matrix J (Fin r) ℝ) :
    Matrix (Fin r) J ℝ := (B.transpose*B)⁻¹ * B.transpose

private theorem gramProjection {J : Type*} [Fintype J] {r : ℕ} (B : Matrix J (Fin r) ℝ)
    (hg : IsUnit (B.transpose*B).det) :
    let A := slotAdjoint B
    let P := B*A
    (B.transpose*B)*A = B.transpose ∧ A*B = 1 ∧
      P.transpose = P ∧ P*P = P ∧ P.trace = (r:ℝ) := by
  classical
  let G := B.transpose*B
  let A := slotAdjoint B
  have adj : G*A = B.transpose := G.mul_nonsing_inv_cancel_left B.transpose hg
  have inv : A*B = 1 := by
    change (G⁻¹*B.transpose)*B = 1
    rw [Matrix.mul_assoc]
    exact G.nonsing_inv_mul hg
  refine ⟨adj, inv, ?_, ?_, ?_⟩
  · simp only [slotAdjoint, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  · change (B*A)*(B*A) = B*A
    calc
      _ = B*(A*B)*A := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [inv, Matrix.mul_one]
  · change (B*A).trace = _
    rw [Matrix.trace_mul_comm, inv, Matrix.trace_one, Fintype.card_fin]

private theorem trace_square {J : Type*} [Fintype J] (P : Matrix J J ℝ)
    (symm : P.transpose = P) : (P*P).trace = ∑ i, ∑ j, (P i j)^2 := by
  change (∑ i, ∑ j, P i j * P j i) = _
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have he : P j i = P i j := congrFun (congrFun symm i) j
  rw [he, sq]

/-- Cauchy-Schwarz on entries works even when admissible widths at
different translates truncate a different number of original slots. -/
private theorem trace_projector_sum {I J : Type*} [Fintype J] (T : Finset I)
    (P : I → Matrix J J ℝ) (r : ℕ) (hP : ∀ t ∈ T,
      (P t).transpose = P t ∧ P t*P t = P t ∧ (P t).trace = (r:ℝ)) :
    let F := ∑ t ∈ T, P t
    F.transpose = F ∧ F.trace = (T.card:ℝ)*r ∧
      (F*F).trace ≤ (T.card:ℝ)^2*r := by
  classical
  let F := ∑ t ∈ T, P t
  have symm : F.transpose = F := by
    rw [F, Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun t ht => (hP t ht).1
  have en (t) (ht : t ∈ T) : (∑ i, ∑ j, (P t i j)^2) = (r:ℝ) := by
    rw [← trace_square _ (hP t ht).1, (hP t ht).2.1, (hP t ht).2.2]
  refine ⟨symm, ?_, ?_⟩
  · rw [Matrix.trace_sum, Finset.sum_congr rfl fun t ht => (hP t ht).2.2]
    simp
  · change (F*F).trace ≤ _
    rw [trace_square F symm]
    calc
      _ ≤ ∑ i, ∑ j, (T.card:ℝ) * ∑ t ∈ T, (P t i j)^2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        simpa only [F, Matrix.sum_apply] using
          (sq_sum_le_card_mul_sum_sq (s := T) (f := fun t => P t i j))
      _ = (T.card:ℝ) * ∑ t ∈ T, ∑ i, ∑ j, (P t i j)^2 := by
        simp only [Finset.mul_sum]
        calc
          _ = ∑ i, ∑ t ∈ T, ∑ j, (T.card:ℝ)*(P t i j)^2 :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
      _ = _ := by rw [Finset.sum_congr rfl en]; simp [sq, mul_assoc]

/-- The translates containing a fixed partner, paired with the original
lift index. A second occurrence at the same site does not add to its rank. -/
def siteRows {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (T : Finset H) (n : ℕ) (s : H) : Finset (H × Fin n) :=
  (Finset.univ.filter (fun u : H =>
    alpogeNativeProjectionE1 s ∈ alpogeNativeProjectionThickColours T u 0)) ×ˢ Finset.univ

theorem siteRows_card {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (T : Finset H) (n : ℕ) (s : H) : (siteRows T n s).card = T.card*n := by
  rw [siteRows, Finset.card_product, alpogeNativeThickColour_translate_count, Finset.card_univ,
    Fintype.card_fin]

private theorem trace_square_pos {J : Type*} [Fintype J] (F : Matrix J J ℝ)
    (symm : F.transpose = F) (pos : 0 < F.trace) : 0 < (F*F).trace := by
  classical
  rw [trace_square _ symm]
  have ex : ∃ i, 0 < F i i := by
    by_contra! hn
    exact pos.not_ge (Finset.sum_nonpos fun i _ => hn i)
  obtain ⟨i, hi⟩ := ex
  have entry := Finset.single_le_sum (s := Finset.univ) (f := fun j => (F i j)^2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  exact ((sq_pos_of_pos hi).trans_le entry).trans_le (Finset.single_le_sum
    (s := Finset.univ) (f := fun k => ∑ j, (F k j)^2)
    (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- Frame bound on the measured high first-prime subspaces. All translates
and lifts at a given site enter the same matrix on the same integers.
The normalizing weights are one in the induced slot metric. The effective
rank counts the retained directions once per physical site. -/
theorem translated_frame {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (sites T : Finset H) (n : ℕ) (r : ↥sites → ℕ)
    (h : (s : ↥sites) → Fin (r s+1) → ℝ)
    (width : H × Fin n → ↥sites → ℝ) (D : (s : ↥sites) → Fin (r s+1) → ℕ)
    (hD : ∀ s i, 0 < D s i)
    (hne : ∀ s : ↥sites, ∀ a : ↥(siteRows T n s.val),
      ∀ i, (bands (h s) (width a.val s) i).Nonempty) :
    let B := fun (s : ↥sites) (a : ↥(siteRows T n s.val)) =>
      physicalColumns (h s) (width a.val s) (hne s a) (D s)
    let F := Matrix.blockDiagonal' fun s : ↥sites =>
      ∑ a : ↥(siteRows T n s.val), B s a * slotAdjoint (B s a)
    let k := ((T.card*n:ℕ):ℝ)
    let d := ∑ s : ↥sites, (r s:ℝ)
    (∀ s a, (B s a).transpose * B s a * slotAdjoint (B s a) = (B s a).transpose ∧
        slotAdjoint (B s a) * B s a = 1) ∧
      F.trace = k*d ∧ (F*F).trace ≤ k^2*d ∧
      (0 < k → 0 < d → d ≤ F.trace^2 / (F*F).trace) := by
  classical
  intro B F k d
  let P := fun (s : ↥sites) (a : ↥(siteRows T n s.val)) => B s a * slotAdjoint (B s a)
  let block := fun s : ↥sites => ∑ a, P s a
  have facts (s : ↥sites) (a : ↥(siteRows T n s.val)) :=
    gramProjection (B s a) (physical_gram (h s) (width a.val s) (hne s a) (D s) (hD s))
  have bound (s : ↥sites) : (block s).transpose = block s ∧ (block s).trace = k*r s ∧
      (block s*block s).trace ≤ k^2*r s := by
    simpa only [block, k, Finset.card_univ, Fintype.card_coe, siteRows_card] using
      trace_projector_sum Finset.univ (P s) (r s) (fun a _ => (facts s a).2.2)
  have tr : F.trace = k*d := by
    change (Matrix.blockDiagonal' block).trace = _
    rw [Matrix.trace_blockDiagonal', show k*d = ∑ s, k*(r s:ℝ) from Finset.mul_sum ..]
    exact Finset.sum_congr rfl fun s _ => (bound s).2.1
  have tr2 : (F*F).trace ≤ k^2*d := by
    change (Matrix.blockDiagonal' block * Matrix.blockDiagonal' block).trace ≤ _
    rw [← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal',
      show k^2*d = ∑ s, k^2*(r s:ℝ) from Finset.mul_sum ..]
    exact Finset.sum_le_sum fun s _ => (bound s).2.2
  refine ⟨fun s a => ⟨(facts s a).1, (facts s a).2.1⟩, tr, tr2, ?_⟩
  intro hk hd
  have symm : F.transpose = F := by
    change (Matrix.blockDiagonal' block).transpose = Matrix.blockDiagonal' block
    rw [Matrix.blockDiagonal'_transpose]
    exact congrArg Matrix.blockDiagonal' (funext fun s => (bound s).1)
  apply (le_div_iff₀ (trace_square_pos F symm (tr.symm ▸ mul_pos hk hd))).2
  calc
    _ ≤ d * (k^2*d) := mul_le_mul_of_nonneg_left tr2 hd.le
    _ = _ := by rw [tr]; ring

end RHLean.Analysis.AlpogeThin.SlotProjector
