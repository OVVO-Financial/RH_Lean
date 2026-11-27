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

private theorem translate_card {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops : Finset H) (v : H) :
    (Finset.univ.filter (fun s : H => s - v ∈ tops)).card = tops.card := by
  have hs : Finset.univ.filter (fun s : H => s - v ∈ tops) =
      tops.map (Equiv.addRight v).toEmbedding := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hs
      exact ⟨s-v, hs, sub_add_cancel _ _⟩
    · rintro ⟨t, ht, rfl⟩
      simpa using ht
  rw [hs, Finset.card_map]

/-- One star with k cuts has k-1 independent columns. Across physical sites
the exact missing count is one per occupied site, for any pattern of collisions. -/
theorem partnerPrimes_rank {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops : Finset H) (primes : Finset ℕ) (frob : ℕ → H) :
    (∑ s : H, ((partnerPrimes tops primes frob s).card - 1)) +
      (Finset.univ.filter (fun s : H => (partnerPrimes tops primes frob s).Nonempty)).card =
      tops.card * primes.card := by
  classical
  let N := fun s => (partnerPrimes tops primes frob s).card
  have total : ∑ s : H, N s = tops.card * primes.card := by
    simp only [N, partnerPrimes, Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _p ∈ primes, tops.card := Finset.sum_congr rfl fun p _ =>
        (by simpa only [Finset.card_filter] using translate_card tops (frob p))
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
    simp [Matrix.mul_apply, slotInclusion]
  · simp [Matrix.mul_apply, slotInclusion, h, Ne.symm h]

/-- All widths at a partner site embed into one interval by forgetting
the layer index. Each row keeps its original quotient-slot number. -/
def physicalAddress {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) :
    Address (bands h v) ↪ ↥(Finset.Iic ⌊h 0⌋₊) :=
  (Classical.choose (original_addresses h v hne)).toEmbedding.trans
    { toFun := fun k => ⟨k.val, Finset.mem_Iic.mpr (Finset.mem_Ioc.mp k.property).2⟩
      inj' := fun _ _ he => Subtype.ext (congrArg (fun x : ↥(Finset.Iic ⌊h 0⌋₊) => x.val) he) }

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
    change (∑ t ∈ T, P t).transpose = ∑ t ∈ T, P t
    rw [Matrix.transpose_sum]
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

/-- The occupied first-prime sites in the dyadic host. -/
def occupied {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops : Finset H) (primes : Finset ℕ) (frob : ℕ → H) : Finset H :=
  Finset.univ.filter (fun s => (partnerPrimes tops primes frob s).Nonempty)

def primeAt {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops : Finset H) (primes : Finset ℕ) (frob : ℕ → H)
    (s : ↥(occupied tops primes frob)) :
    Fin ((partnerPrimes tops primes frob s.val).card - 1 + 1) ↪o ℕ :=
  (partnerPrimes tops primes frob s.val).orderEmbOfFin
    (Nat.sub_add_cancel (Finset.card_pos.mpr (Finset.mem_filter.mp s.property).2)).symm

private theorem primeAt_mem {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops : Finset H) (primes : Finset ℕ) (frob : ℕ → H)
    (s : ↥(occupied tops primes frob)) (i) :
    primeAt tops primes frob s i ∈ partnerPrimes tops primes frob s.val :=
  Finset.orderEmbOfFin_mem ..

/-- Each fixed prime enters once for each original top over all occupied
sites. Arbitrary weights, in particular depth times log p, retain their sign. -/
theorem primeAt_sum {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops : Finset H) (primes : Finset ℕ) (frob : ℕ → H) (f : ℕ → ℝ) :
    (∑ s : ↥(occupied tops primes frob), ∑ i, f (primeAt tops primes frob s i)) =
      tops.card * ∑ p ∈ primes, f p := by
  classical
  let V := occupied tops primes frob
  let L := partnerPrimes tops primes frob
  have enumerate (s : ↥V) : (∑ i, f (primeAt tops primes frob s i)) = ∑ p ∈ L s.val, f p := by
    let e := (L s.val).orderIsoOfFin
      (Nat.sub_add_cancel (Finset.card_pos.mpr (Finset.mem_filter.mp s.property).2)).symm
    exact (e.toEquiv.sum_comp fun p => f p.val).trans (Finset.sum_coe_sort _ _)
  have empty (s : H) (hs : s ∉ V) : L s = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    exact fun hv => hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
  calc
    _ = ∑ s : ↥V, ∑ p ∈ L s.val, f p := Finset.sum_congr rfl fun s _ => enumerate s
    _ = ∑ s ∈ V, ∑ p ∈ L s, f p := Finset.sum_coe_sort _ _
    _ = ∑ s : H, ∑ p ∈ L s, f p := Finset.sum_subset (Finset.subset_univ _) fun s _ hs =>
      by rw [empty s hs, Finset.sum_empty]
    _ = _ := by
      simp only [L, partnerPrimes, Finset.sum_filter]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, translate_card]

/-- Logarithmic increase in covolume measured on the same slots before
and after the actual wheel powers are applied. -/
def logVolume {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ) : ℝ :=
  let B := columns S D
  let A := columns S (fun _ => 1)
  (Real.log (((B.transpose*B).det:ℤ):ℝ) - Real.log (((A.transpose*A).det:ℤ):ℝ))/2

private theorem volume_loss {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) (L : ℝ)
    (cap : ∀ i, (D i:ℝ) ≤ Real.exp L) :
    (∑ i, Real.log (D i:ℝ)) - logVolume S D ∈ Set.Icc 0 L := by
  classical
  let A := columns S (fun _ => 1)
  let B := columns S D
  have pos (d : Fin (r+1) → ℕ) (hd : ∀ i, 0 < d i) :
      0 < ((((columns S d).transpose * columns S d).det:ℤ):ℝ) := by
    rw [columns_det S d hS hd, Int.cast_natCast]
    exact_mod_cast (Finset.sum_pos (s := Finset.univ)
      (f := fun i : Fin (r+1) => ∏ j ∈ Finset.univ.erase i, (S j).card * d j^2)
      (fun i _ => Finset.prod_pos (fun j _ => Nat.mul_pos (Finset.card_pos.mpr (hS j))
        (pow_pos (hd j) _))) Finset.univ_nonempty)
  have ha := pos (fun _ => 1) (fun _ => Nat.zero_lt_one)
  have hb := pos D hD
  have hp : 0 < ∏ i, (D i:ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hD i
  obtain ⟨lo, hi⟩ := columns_gain S D hS hD (Real.exp L) cap
  have low := Real.log_le_log hb lo
  have high := Real.log_le_log (mul_pos (sq_pos_of_pos hp) ha) hi
  rw [Real.log_mul (sq_pos_of_pos hp).ne' ha.ne', Real.log_pow,
    Real.log_prod (fun i _ => by exact_mod_cast (hD i).ne')] at low high
  rw [Real.log_mul (sq_pos_of_pos (Real.exp_pos L)).ne' hb.ne', Real.log_pow,
    Real.log_exp] at high
  dsimp only [logVolume]
  constructor <;> linarith

/-- On the original dyadic host all high first primes of the thick colour
are selected directly from the cutoff. -/
def highThickPrimes (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (x : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊x⌋₊).filter fun p => Real.sqrt x ≤ (p:ℝ) ∧ (p:ℝ)+1 ≤ x ∧
    (alpogeNativeHostData e q d).frob p =
      alpogeNativeProjectionE1 ((alpogeNativeHostData e q d).frob p).2

private theorem row_mem {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (T : Finset H) (n : ℕ) (s : H) (a : H × Fin n) :
    a ∈ siteRows T n s ↔ (((0,1) : AlpogeNativeE0),s) ∈ alpogeNativeThickPositiveSites T a.1 := by
  simp [siteRows, alpogeNativeProjectionThickColours, alpogeNativeThickPositiveSites,
    alpogeNativeProjectionE1]

/-- Supply the layers, admissions, and translated projectors from the
original top heights, Frobenius values, and measured width of each row.
Each omitted direction is charged once per occupied site and active row.
The number of lifts enters both sums with the same multiplicity. -/
theorem highThick_frame (ε : ℝ) (he : 0 < ε) (he1 : ε ≤ 1) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ (e q d n E : ℕ) [Fact q.Prime] [Fact d.Prime]
      (tops T : Finset (AlpogeNativeDyadicH e)) (a : AlpogeNativeDyadicH e → ℝ)
      (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
      let b := Real.exp (x^ε)
      let c := ⌊Real.sqrt x⌋₊
      let P := highThickPrimes e q d x
      let g := fun p => ((alpogeNativeHostData e q d).frob p).2
      let V := occupied tops P g
      let r := fun s : ↥V => (partnerPrimes tops P g s.val).card - 1
      let p := primeAt tops P g
      let cut := fun (s : ↥V) (i : Fin (r s+1)) => a (s.val-g (p s i))/(p s i:ℝ)
      let power := fun l : ℕ => l^(⌊(c:ℝ)*x⌋₊/l-c)
      let D := fun (s : ↥V) (i : Fin (r s+1)) => power (p s i)
      let width := fun (j : AlpogeNativeDyadicH e × Fin n) (s : ↥V) => w j.1 j.2 ((0,1),s.val)
      let S := fun (s : ↥V) (j : ↥(siteRows T n s.val)) => bands (cut s) (width j.val s)
      let k := ((T.card*n:ℕ):ℝ)
      let rank := ∑ s : ↥V, (r s:ℝ)
      0 < E → (∀ t ∈ tops, a t ∈ Set.Icc (x*b) ((x+1)*b)) →
      (∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u j ρ ∈ Set.Icc b (b*(1+1/x))) →
      ∃ hS : ∀ s j i, (S s j i).Nonempty,
        let B := fun (s : ↥V) (j : ↥(siteRows T n s.val)) =>
          physicalColumns (cut s) (width j.val s) (hS s j) (D s)
        let F := Matrix.blockDiagonal' fun s : ↥V => ∑ j, B s j * slotAdjoint (B s j)
        (∀ s j, (B s j).transpose*B s j * slotAdjoint (B s j) = (B s j).transpose ∧
          slotAdjoint (B s j)*B s j = 1) ∧
        F.trace = k*rank ∧ (F*F).trace ≤ k^2*rank ∧
        (0 < k → 0 < rank → rank ≤ F.trace^2/(F*F).trace) ∧
        (k*(tops.card*(∑ l ∈ P, Real.log (power l:ℝ))) -
          ∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), logVolume (S s j) (D s)) ∈
            Set.Icc 0 ((V.card:ℝ)*k*((c:ℝ)*Real.sqrt x*Real.log x)) ∧
        ∀ s j (U : Finset ℕ),
          (∑ l ∈ U, ((allowance (fun i => (S s j i).card * D s i^2) E).factorization l:ℝ)*
            Real.log l)/(E:ℝ) ≤ x^4 := by
  classical
  filter_upwards [dyadic_rpow_le_exp_eventually 3 ε he, Filter.eventually_ge_atTop (10:ℝ)]
    with x hlarge hx
  intro e q d n E _ _ tops T a w b c P g V r p cut power D width S k rank hE ha hw
  have hx1 : 1 ≤ x := by linarith
  have hb4 : 4*x^2 ≤ b := by
    rw [show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast] at hlarge
    exact (show 4*x^2 ≤ x^3 by nlinarith only
      [mul_nonneg (show 0 ≤ x-4 by linarith) (sq_nonneg x)]).trans hlarge
  have info (s : ↥V) (i : Fin (r s+1)) :
      (p s i).Prime ∧ Real.sqrt x ≤ (p s i:ℝ) ∧ (p s i:ℝ)+1 ≤ x ∧
      (alpogeNativeHostData e q d).frob (p s i) = alpogeNativeProjectionE1 (g (p s i)) ∧
      s.val - g (p s i) ∈ tops := by
    have hp := Finset.mem_filter.mp (primeAt_mem tops P g s i)
    have hi := Finset.mem_filter.mp hp.1
    exact ⟨(Nat.mem_primesLE.mp hi.1).2, hi.2.1, hi.2.2.1, hi.2.2.2, hp.2⟩
  have hp s i := (info s i).1
  have high s i := (info s i).2.1
  have band s i := (info s i).2.2.1
  have px s i : (p s i:ℝ) ≤ x := by linarith only [band s i]
  have height s i := ha _ (info s i).2.2.2.2
  have hD s i : 0 < D s i := pow_pos (hp s i).pos _
  have partner (s : ↥V) (i : Fin (r s+1)) :
      alpogeNativePartner (s.val-g (p s i)) ((alpogeNativeHostData e q d).frob (p s i)) =
        (((0,1) : AlpogeNativeE0),s.val) := by
    have heq : s.val - (s.val-g (p s i)) = g (p s i) := by abel
    rw [(info s i).2.2.2.1]
    simpa only [add_zero, heq] using
      alpogeNativeProjectionThick_partner s.val 0 (s.val-g (p s i))
  have hS (s : ↥V) (j : ↥(siteRows T n s.val)) (i) : (S s j i).Nonempty := by
    have hwidth := hw j.val.1 j.val.2 _ ((row_mem T n s.val j.val).1 j.property)
    exact (firstPrime_slots e q d (r s) (p s) (fun i => s.val-g (p s i)) a (w j.val.1 j.val.2)
      x b hx1 hb4 (hp s) (p s).strictMono (band s) (height s) _ (partner s)
      ((Real.exp_pos _).le.trans hwidth.1) hwidth.2 i).2.1
  obtain ⟨adj, tr, tr2, eff⟩ := translated_frame V T n r cut width D hD hS
  refine ⟨hS, adj, tr, tr2, eff, ?_, ?_⟩
  · let L := (c:ℝ)*Real.sqrt x*Real.log x
    let gross := fun s : ↥V => ∑ i, Real.log (D s i:ℝ)
    let loss := fun (s : ↥V) (j : ↥(siteRows T n s.val)) => gross s - logVolume (S s j) (D s)
    have one (s : ↥V) (j : ↥(siteRows T n s.val)) : loss s j ∈ Set.Icc 0 L :=
      volume_loss (S s j) (D s) (hS s j) (hD s) L fun i =>
        MeasuredCut.wheel_factor_le (p s i) c x (hp s i) hx1 (high s i) (px s i)
    have total : (∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), loss s j) =
        k*(tops.card*(∑ l ∈ P, Real.log (power l:ℝ))) -
          ∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), logVolume (S s j) (D s) := by
      simp only [loss, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        siteRows_card, nsmul_eq_mul, ← Finset.mul_sum]
      exact congrArg (fun z : ℝ => k*z - _) (primeAt_sum tops P g (fun l => Real.log (power l:ℝ)))
    rw [← total]
    refine ⟨Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun j _ => (one s j).1, ?_⟩
    calc
      _ ≤ ∑ s : ↥V, ∑ _j : ↥(siteRows T n s.val), L :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun j _ => (one s j).2
      _ = _ := by simp [k, siteRows_card, mul_assoc, L]
  · intro s j U
    exact squareClock_price (r s) E (p s) (fun i => a (s.val-g (p s i))) (width j.val s) x ε
      hx he1 hE (hp s) (p s).strictMono (high s) (px s) (fun i => (height s i).2) U (hS s j)

end RHLean.Analysis.AlpogeThin.SlotProjector
