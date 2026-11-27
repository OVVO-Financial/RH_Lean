import «research.NativeMeasuredCutGram»
import «research.NativeWheelFitProjector»

/-! Integral sections on the quotient slots of one high first-prime thick fibre.
The scalar product counts actual integer slots. The finite test and the real
Gram use the same columns. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin.SlotProjector

/-- Consecutive differences of the quotient-slot intervals. The last interval
uses the original upward rounding at the translated partner. -/
def bands {m : ℕ} (h : Fin (m+1) → ℝ) (v : ℝ) : Fin (m+1) → Finset ℕ :=
  Fin.lastCases (Finset.Ioc ⌈v⌉₊ ⌊h (Fin.last m)⌋₊)
    (fun i => Finset.Ioc ⌊h i.succ⌋₊ ⌊h i.castSucc⌋₊)

private theorem rounded (h l : ℝ) (n : ℕ) (hl : 0 ≤ l) (hg : 4 ≤ h-l)
    (hn : l-1 ≤ (n:ℝ)) (hn' : (n:ℝ) ≤ l+1) :
    let S := Finset.Ioc n ⌊h⌋₊
    S.Nonempty ∧ h-l-2 ≤ (S.card:ℝ) ∧ (S.card:ℝ) ≤ h-l+1 := by
  have ha := Nat.lt_floor_add_one h
  have hb := Nat.floor_le (show 0 ≤ h by linarith)
  have hc : (n:ℝ) < (⌊h⌋₊:ℝ) := by linarith
  have hlt : n < ⌊h⌋₊ := by exact_mod_cast hc
  dsimp only
  refine ⟨⟨⌊h⌋₊, Finset.mem_Ioc.mpr ⟨hlt, le_rfl⟩⟩, ?_⟩
  rw [Nat.card_Ioc, Nat.cast_sub hlt.le]
  constructor <;> linarith

/-- Quantitative separation of the original high first-prime cuts gives
nonempty integral layers. Every layer is inside the respective original
quotient-slot test, with at most two slots lost to endpoint rounding. -/
theorem firstPrime_slots (e q d m : ℕ) [Fact q.Prime] [Fact d.Prime]
    (p : Fin (m+1) → ℕ) (t : Fin (m+1) → AlpogeNativeDyadicH e)
    (a : AlpogeNativeDyadicH e → ℝ) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b : ℝ) (hx : 1 ≤ x) (hb : 4*x^2 ≤ b) (hp : ∀ i, (p i).Prime)
    (ho : StrictMono p) (hband : ∀ i, (p i:ℝ)+1 ≤ x)
    (ha : ∀ i, a (t i) ∈ Set.Icc (x*b) ((x+1)*b))
    (site : AlpogeNativeE0 × AlpogeNativeDyadicH e)
    (hs : ∀ i, alpogeNativePartner (t i) ((alpogeNativeHostData e q d).frob (p i)) = site)
    (hv : 0 ≤ w site) (hw : w site ≤ b*(1+1/x)) :
    let U := fun i => nativeDyadicLocalSourceAtom e q d (p i) (a (t i)) (t i) w 1
    let S := bands (fun i => a (t i)/(p i:ℝ)) (w site)
    ∀ i, S i ⊆ RankOne.slots (a (t i)) (w site) (p i) ∧ (S i).Nonempty ∧
      b/x^2 ≤ MeasuredCut.layers U i ∧
      MeasuredCut.layers U i-2 ≤ ((S i).card:ℝ) ∧
      ((S i).card:ℝ) ≤ MeasuredCut.layers U i+1 := by
  let h := fun i => a (t i)/(p i:ℝ)
  let U := fun i => nativeDyadicLocalSourceAtom e q d (p i) (a (t i)) (t i) w 1
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hx2 : 0 < x^2 := sq_pos_of_pos hx0
  have hb0 : 0 < b := by linarith
  have hfour : 4 ≤ b/x^2 := (le_div_iff₀ hx2).2 hb
  have hp0 i : 0 < (p i:ℝ) := by exact_mod_cast (hp i).pos
  have hpx i : (p i:ℝ) ≤ x := by linarith only [hband i]
  have bottom i : b/x^2 ≤ h i - w site := by
    have one : w site * (p i:ℝ) ≤ x*b-b/x := calc
      _ ≤ (b*(1+1/x))*(x-1) := mul_le_mul hw (by linarith only [hband i]) (hp0 i).le (by positivity)
      _ = _ := by field [hx0.ne']
    have two : b/x^2*(p i:ℝ) ≤ b/x := calc
      _ ≤ b/x^2*x := mul_le_mul_of_nonneg_left (hpx i) (by positivity)
      _ = _ := by field [hx0.ne']
    apply le_sub_iff_add_le.mpr
    apply (le_div_iff₀ (hp0 i)).2
    rw [add_mul]
    linarith only [one, two, (ha i).1]
  have eqU i : U i = h i - w site := by
    have pos : 0 ≤ h i - w site := le_trans (by positivity : 0 ≤ b/x^2) (bottom i)
    change max (a (t i) / ((p i ^ 1 : ℕ):ℝ) -
      w (alpogeNativePartner (t i) ((1:ℕ) • (alpogeNativeHostData e q d).frob (p i)))) 0 = _
    simpa only [pow_one, one_nsmul, hs i] using max_eq_left pos
  have gap (j : Fin m) : b/x^2 ≤ h j.castSucc - h j.succ := by
    let i := j.castSucc
    let k := j.succ
    have hik : p i < p k := ho (show i < k from Fin.castSucc_lt_succ)
    have hk : (p i:ℝ)+1 ≤ p k := by exact_mod_cast Nat.succ_le_of_lt hik
    have coeff : 1 ≤ x*((p k:ℝ)-p i)-p i := by
      have := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ (p k:ℝ)-p i by linarith only [hk]) hx0.le
      linarith only [this, hband i]
    have sign := (nativeDyadic_sameWidth_firstPrime_signed e q d (p i) (p k) (t i) (t k)
      w x b (a (t i)) (a (t k)) hb0 (hp i).pos hik (hband k) (ha i) (ha k)
      ((hs i).trans (hs k).symm) (by rwa [hs k])).2.1
    change b*(x*((p k:ℝ)-p i)-p i) ≤ (p i:ℝ)*p k*(U i-U k) at sign
    rw [eqU, eqU, sub_sub_sub_cancel_right] at sign
    have low := (mul_le_mul_of_nonneg_left coeff hb0.le).trans sign
    have cap : (p i:ℝ)*p k ≤ x^2 := (mul_le_mul (hpx i) (hpx k) (hp0 k).le hx0.le).trans_eq (sq x).symm
    apply (le_of_mul_le_mul_left _ (mul_pos (hp0 i) (hp0 k)))
    calc
      (p i:ℝ)*p k*(b/x^2) ≤ x^2*(b/x^2) := mul_le_mul_of_nonneg_right cap (by positivity)
      _ = b := by field [hx0.ne']
      _ ≤ _ := by simpa only [mul_one] using low
  change ∀ i, bands h (w site) i ⊆ RankOne.slots (a (t i)) (w site) (p i) ∧
    (bands h (w site) i).Nonempty ∧ b/x^2 ≤ MeasuredCut.layers U i ∧
    MeasuredCut.layers U i-2 ≤ ((bands h (w site) i).card:ℝ) ∧
    ((bands h (w site) i).card:ℝ) ≤ MeasuredCut.layers U i+1
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · let k := Fin.last m
    have hr := rounded (h k) (w site) ⌈w site⌉₊ hv (hfour.trans (bottom k))
      (by linarith only [Nat.le_ceil (w site)]) (Nat.ceil_lt_add_one hv).le
    change bands h (w site) k ⊆ _ ∧ _ ∧ _ ∧ _ ∧ _
    simpa [k, bands, RankOne.slots, MeasuredCut.layers, eqU, h] using
      And.intro (Finset.Subset.refl (Finset.Ioc ⌈w site⌉₊ ⌊h k⌋₊))
        (And.intro hr.1 (And.intro (bottom k) hr.2))
  · have hlow : 0 ≤ h j.succ := by linarith only [bottom j.succ, hfour, hv]
    have hn : ⌈w site⌉₊ ≤ ⌊h j.succ⌋₊ := by
      have hf := Nat.lt_floor_add_one (h j.succ)
      have hc := Nat.ceil_lt_add_one hv
      exact_mod_cast (show (⌈w site⌉₊:ℝ) ≤ (⌊h j.succ⌋₊:ℝ) by linarith only [bottom j.succ, hfour, hf, hc])
    have hr := rounded (h j.castSucc) (h j.succ) ⌊h j.succ⌋₊ hlow (hfour.trans (gap j))
      (by linarith only [Nat.lt_floor_add_one (h j.succ)]) (by linarith only [Nat.floor_le hlow])
    have sub : Finset.Ioc ⌊h j.succ⌋₊ ⌊h j.castSucc⌋₊ ⊆
        Finset.Ioc ⌈w site⌉₊ ⌊h j.castSucc⌋₊ := fun k hk =>
      Finset.mem_Ioc.mpr ⟨hn.trans_lt (Finset.mem_Ioc.mp hk).1, (Finset.mem_Ioc.mp hk).2⟩
    change bands h (w site) j.castSucc ⊆ _ ∧ _ ∧ _ ∧ _ ∧ _
    simpa [bands, RankOne.slots, MeasuredCut.layers, eqU, sub_sub_sub_cancel_right, h] using
      And.intro sub (And.intro hr.1 (And.intro (gap j) hr.2))

/-- An integral section takes one constant value on each actual layer. -/
def starColumn {m : ℕ} (D : Fin (m+1) → ℕ) (j : Fin m) (i : Fin (m+1)) (_k : ℕ) : ℤ :=
  (if i = j.succ then (D j.succ:ℤ) else 0) - (if i = 0 then (D 0:ℤ) else 0)

/-- Pair a slot function with each section, by summing only over its support. -/
def read {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
    (z : Fin (m+1) → ℕ → ℤ) (j : Fin m) : ℤ :=
  (D j.succ:ℤ) * ∑ k ∈ S j.succ, z j.succ k -
    (D 0:ℤ) * ∑ k ∈ S 0, z 0 k

/-- A single integral function simultaneously prescribes all star pairings.
It is supported at one genuine quotient slot per layer. -/
theorem integral_dual {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i)
    (hc : Pairwise (fun i j => (D i).Coprime (D j))) (y : Fin m → ℤ) :
    ∃ z : Fin (m+1) → ℕ → ℤ, (∀ j, read S D z j = y j) ∧
      ∀ i, ∃ k ∈ S i, ∀ l, l ≠ k → z i l = 0 := by
  obtain ⟨v, u, hu⟩ := nativeDyadic_firstPrime_wheel_block_dual (fun i : Fin m => D i.succ)
    (D 0) (fun i => (hD _).ne') (fun i => hc (Fin.succ_ne_zero i).symm)
    (fun _ _ h => hc (fun he => h (Fin.succ_injective m he))) y
  choose k hk using hS
  let c : Fin (m+1) → ℤ := Fin.cases v u
  refine ⟨fun i l => if k i = l then c i else 0, ?_, ?_⟩
  · intro j
    simpa [read, hk, c] using hu j
  · exact fun i => ⟨k i, hk i, fun l hl => by simp [Ne.symm hl]⟩

/-- Real Gram from integer pairings on the same slots and the same sections. -/
theorem measured_gram {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ) :
    (fun i j : Fin m => (read S D (starColumn D j) i : ℝ)) =
      MeasuredCut.gram (fun i => ((S i).card:ℝ)*(D i:ℝ)^2) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [read, starColumn, MeasuredCut.gram, Matrix.diagonal_apply, Matrix.mul_apply, pow_two]
    <;> ring
  · simp [read, starColumn, MeasuredCut.gram, Matrix.diagonal_apply, Matrix.mul_apply, hij, pow_two]
    <;> ring

/-- The top determinant of the orthogonal projector has a single Gram
denominator for every pair of integral test matrices, in every ambient dimension. -/
theorem projector_det {m : ℕ} {J : Type*} [Fintype J] (B : Matrix J (Fin m) ℤ)
    (U V : Matrix (Fin m) J ℤ) (hG : (B.transpose * B).det ≠ 0) :
    let A := B.map (Int.castRingHom ℚ)
    let P := A * (A.transpose*A)⁻¹ * A.transpose
    (((B.transpose*B).det:ℤ):ℚ) * (U.map (Int.castRingHom ℚ)*P*(V.map (Int.castRingHom ℚ)).transpose).det =
      (((U*B).det*(V*B).det:ℤ):ℚ) := by
  classical
  dsimp only
  let f := Int.castRingHom ℚ
  let A := B.map f
  let G := A.transpose*A
  have mapProd (W : Matrix (Fin m) J ℤ) :
      f (W*B).det = (W.map f*A).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]
  have mapGram : f (B.transpose*B).det = G.det := mapProd B.transpose
  have hG' : IsUnit G.det := isUnit_iff_ne_zero.mpr (by
    rw [← mapGram]
    change (((B.transpose*B).det:ℤ):ℚ) ≠ 0
    exact_mod_cast hG)
  change f (B.transpose*B).det * (U.map f*(A*G⁻¹*A.transpose)*(V.map f).transpose).det =
    f ((U*B).det*(V*B).det)
  have grouping : U.map f*(A*G⁻¹*A.transpose)*(V.map f).transpose =
      (U.map f*A)*G⁻¹*(V.map f*A).transpose := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [grouping, map_mul, mapGram, mapProd U, mapProd V, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  linear_combination (U.map f*A).det*(V.map f*A).det * G.det_nonsing_inv_mul_det hG'

/-- A quotient address records the prime direction and the actual integer
in its band. No volume or local height is supplied to this definition. -/
abbrev Address {m : ℕ} (S : Fin (m+1) → Finset ℕ) := (i : Fin (m+1)) × {k // k ∈ S i}

def columns {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ) :
    Matrix (Address S) (Fin m) ℤ := fun a j => starColumn D j a.1 a.2.val

private theorem dot_read {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
    (z : Fin (m+1) → ℕ → ℤ) (j : Fin m) :
    ∑ x : Address S, z x.1 x.2.val * columns S D x j = read S D z j := by
  classical
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ i, (∑ k ∈ S i, z i k) * starColumn D j i 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      change (∑ k : ↥(S i), z i k.val * starColumn D j i 0) = _
      rw [← Finset.sum_mul, Finset.sum_coe_sort (S i) (z i)]
    _ = _ := by simp [starColumn, read, mul_sub, mul_ite, Finset.sum_sub_distrib, mul_comm]

/-- The CRT functionals are a simultaneous integral left inverse to the
actual matrix. In particular its columns span a saturated sublattice. -/
theorem left_inverse {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i)
    (hc : Pairwise (fun i j => (D i).Coprime (D j))) :
    ∃ Y : Matrix (Fin m) (Address S) ℤ, Y * columns S D = 1 := by
  classical
  choose z hz using fun i : Fin m => integral_dual S D hS hD hc ((1 : Matrix (Fin m) (Fin m) ℤ) i)
  refine ⟨fun i x => z i x.1 x.2.val, ?_⟩
  ext i j
  exact (dot_read S D (z i) j).trans ((hz i).1 j)

/-- Integer squared covolume as a sum of the products omitting one layer.
This expression applies to any number of layers, including one. -/
def mass {m : ℕ} (s : Fin (m+1) → ℕ) : ℕ :=
  ∑ i, ∏ j ∈ Finset.univ.erase i, s j

theorem mass_det {m : ℕ} (s : Fin (m+1) → ℕ) (hs : ∀ i, 0 < s i) :
    (mass s:ℝ) = (MeasuredCut.gram fun i => (s i:ℝ)).det := by
  classical
  rw [MeasuredCut.gram_det _ (fun i => by exact_mod_cast hs i), Finset.mul_sum]
  unfold mass
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.prod_erase_mul _ (fun j => (s j:ℝ)) (Finset.mem_univ i), mul_assoc,
    mul_inv_cancel₀ (show (s i:ℝ) ≠ 0 by exact_mod_cast (hs i).ne'), mul_one]

theorem columns_det {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) :
    ((columns S D).transpose * columns S D).det =
      (mass fun i => (S i).card * D i ^ 2 : ℕ) := by
  classical
  let s := fun i => (S i).card * D i ^ 2
  have hs i : 0 < s i := Nat.mul_pos (Finset.card_pos.mpr (hS i)) (pow_pos (hD i) _)
  let f := Int.castRingHom ℝ
  have hg : f.mapMatrix ((columns S D).transpose * columns S D) =
      MeasuredCut.gram (fun i => (s i:ℝ)) := by
    ext i j
    have hj := congrFun (congrFun (measured_gram S D) i) j
    change (((∑ x : Address S, columns S D x i * columns S D x j):ℤ):ℝ) = _
    rw [show (∑ x : Address S, columns S D x i * columns S D x j) = read S D (starColumn D j) i by
      simpa only [columns, mul_comm] using dot_read S D (starColumn D j) i]
    simpa [s] using hj
  apply Int.cast_injective (α := ℝ)
  change f _ = _
  rw [RingHom.map_det, hg, ← mass_det s hs]
  simp [f]

/-- The common denominator is attained by integral tests on the same slot
columns. Thus the determinant clearing factor is exact on their lattice. -/
theorem attained_price {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i)
    (hc : Pairwise (fun i j => (D i).Coprime (D j))) :
    let g := mass fun i => (S i).card * D i^2
    let B := (columns S D).map (Int.castRingHom ℚ)
    let P := B * (B.transpose*B)⁻¹ * B.transpose
    ∃ Y : Matrix (Fin m) (Address S) ℤ,
      let T := Y.map (Int.castRingHom ℚ)
      Y * columns S D = 1 ∧ (T*P*T.transpose).det = (g:ℚ)⁻¹ := by
  classical
  let s := fun i => (S i).card * D i^2
  have hs i : 0 < s i := Nat.mul_pos (Finset.card_pos.mpr (hS i)) (pow_pos (hD i) _)
  have hp : 0 < mass s := Finset.sum_pos (fun i _ => Finset.prod_pos (fun j _ => hs j)) Finset.univ_nonempty
  obtain ⟨Y, hY⟩ := left_inverse S D hS hD hc
  have hg := columns_det S D hS hD
  have hne : ((columns S D).transpose*columns S D).det ≠ 0 := by
    rw [hg]
    exact_mod_cast hp.ne'
  have test := projector_det (columns S D) Y Y hne
  dsimp only at test ⊢
  refine ⟨Y, hY, ?_⟩
  rw [hY, Matrix.det_one, mul_one, Int.cast_one, hg, Int.cast_natCast] at test
  exact (eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using test))

/-- Bounding each measured layer bounds the actual clearing determinant.
The exponent is the number of nonpivot columns. -/
theorem mass_le {m : ℕ} (s : Fin (m+1) → ℕ) (L : ℝ) (h : ∀ i, (s i:ℝ) ≤ L) :
    (mass s:ℝ) ≤ (m+1:ℕ)*L^m := by
  classical
  unfold mass
  push_cast
  calc
    _ ≤ ∑ i : Fin (m+1), L ^ m := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∏ _j ∈ (Finset.univ : Finset (Fin (m+1))).erase i, L :=
          Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg (s j)) (fun j _ => h j)
        _ = _ := by simp
    _ = _ := by simp

/-- An integer clearing both the full determinant and the rank-one tests
raised to the row exponent. -/
def allowance {m : ℕ} (s : Fin (m+1) → ℕ) (E : ℕ) : ℕ :=
  mass s * (∏ j : Fin m, (s 0+s j.succ))^E

theorem allowance_dvd {m : ℕ} (s : Fin (m+1) → ℕ) (E : ℕ) :
    mass s ∣ allowance s E ∧ ∀ i : Fin m, (s 0+s i.succ)^E ∣ allowance s E := by
  classical
  exact ⟨dvd_mul_right _ _, fun i => (pow_dvd_pow_of_dvd
    (Finset.dvd_prod_of_mem (fun j : Fin m => s 0+s j.succ) (Finset.mem_univ i)) E).trans
      (dvd_mul_left _ _)⟩

/-- Total normalized price of a common allowance at every finite place,
including primes outside the admitted wheel. The rank exponent occurs
only in the full-row share after normalization. -/
theorem allowance_price {m : ℕ} (s : Fin (m+1) → ℕ) (hs : ∀ i, 0 < s i)
    (L : ℝ) (h : ∀ i, (s i:ℝ) ≤ L) (E : ℕ) (hE : 0 < E) (T : Finset ℕ) :
    (∑ p ∈ T, ((allowance s E).factorization p:ℝ)*Real.log p)/(E:ℝ) ≤
      (Real.log (m+1:ℕ) + (m:ℝ)*Real.log L)/(E:ℝ) + (m:ℝ)*Real.log (2*L) := by
  classical
  have hL : 0 < L := (show 0 < (s 0:ℝ) by exact_mod_cast hs 0).trans_le (h 0)
  have hg : 0 < mass s := Finset.sum_pos (fun i _ => Finset.prod_pos (fun j _ => hs j)) Finset.univ_nonempty
  let d := fun j : Fin m => s 0+s j.succ
  have hd j : 0 < d j := Nat.add_pos_left (hs 0) _
  have hprod : 0 < ∏ j, d j := Finset.prod_pos fun j _ => hd j
  have hpR : (0:ℝ) < ∏ j, (d j:ℝ) := by exact_mod_cast hprod
  have hE' : (0:ℝ) < E := by exact_mod_cast hE
  have hlog := Real.log_le_log (show (0:ℝ) < mass s by exact_mod_cast hg) (mass_le s L h)
  rw [Real.log_mul (by positivity) (pow_ne_zero _ hL.ne'), Real.log_pow] at hlog
  have hrow : (∑ j, Real.log (d j:ℝ)) ≤ (m:ℝ)*Real.log (2*L) := calc
    _ ≤ ∑ _j : Fin m, Real.log (2*L) := Finset.sum_le_sum fun j _ =>
      Real.log_le_log (by exact_mod_cast hd j) (by dsimp [d]; push_cast; linarith only [h 0,h j.succ])
    _ = _ := by simp
  have cost := WheelFit.finite_row_budget (allowance s E) T
  change _ ≤ Real.log ((mass s * (∏ j, d j)^E : ℕ):ℝ) at cost
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod,
    Real.log_mul (Nat.cast_ne_zero.mpr hg.ne') (pow_ne_zero _ hpR.ne'),
    Real.log_pow, Real.log_prod (fun j _ => Nat.cast_ne_zero.mpr (hd j).ne')] at cost
  apply (div_le_iff₀ hE').2
  rw [add_mul, div_mul_cancel₀ _ hE'.ne']
  linarith only [cost, hlog, mul_le_mul_of_nonneg_left hrow hE'.le, mul_comm (E:ℝ) ((m:ℝ)*Real.log (2*L))]

/-- On the original fibre the counted cardinality and the admitted prime
power bound the same column norm used by the Gram clearing factor. -/
theorem firstPrime_norm_cap (m c : ℕ) (p : Fin (m+1) → ℕ) (a : Fin (m+1) → ℝ)
    (v x b : ℝ) (hx : 1 ≤ x) (hb : 0 ≤ b) (ha : ∀ i, a i ≤ (x+1)*b)
    (hp : ∀ i, (p i).Prime) (hhigh : ∀ i, Real.sqrt x ≤ p i) (hband : ∀ i, (p i:ℝ) ≤ x) :
    let S := bands (fun i => a i/(p i:ℝ)) v
    let D := fun i => p i ^ (⌊(c:ℝ)*x⌋₊ / p i - c)
    ∀ i, ((S i).card:ℝ)*(D i:ℝ)^2 ≤ (x+1)*b*Real.exp ((c:ℝ)*Real.sqrt x*Real.log x)^2 := by
  let h := fun i => a i/(p i:ℝ)
  have hxb : 0 ≤ (x+1)*b := mul_nonneg (by linarith) hb
  have bound (i) : (⌊h i⌋₊:ℝ) ≤ (x+1)*b := by
    by_cases hi : 0 ≤ h i
    · apply (Nat.floor_le hi).trans
      apply (div_le_iff₀ (show (0:ℝ) < p i by exact_mod_cast (hp i).pos)).2
      exact (ha i).trans (le_mul_of_one_le_right hxb (by exact_mod_cast (hp i).one_le))
    · simpa only [Nat.floor_of_nonpos (le_of_not_ge hi), Nat.cast_zero] using hxb
  have card (i) : ((bands h v i).card:ℝ) ≤ (x+1)*b := by
    have hi : (bands h v i).card ≤ ⌊h i⌋₊ := by
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [bands, Nat.sub_le]
    exact (show ((bands h v i).card:ℝ) ≤ (⌊h i⌋₊:ℝ) by exact_mod_cast hi).trans (bound i)
  dsimp only
  exact fun i => mul_le_mul (card i) (pow_le_pow_left₀ (Nat.cast_nonneg _)
    (MeasuredCut.wheel_factor_le (p i) c x (hp i) hx (hhigh i) (hband i)) 2) (sq_nonneg _) hxb

end RHLean.Analysis.AlpogeThin.SlotProjector
