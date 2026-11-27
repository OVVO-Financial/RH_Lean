import «research.NativeMeasuredCutGram»
import «research.NativeRankOneEulerRepayment»

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
def section {m : ℕ} (D : Fin (m+1) → ℕ) (j : Fin m) (i : Fin (m+1)) (_k : ℕ) : ℤ :=
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
  · exact fun i => ⟨k i, hk i, fun l hl => if_neg (Ne.symm hl)⟩

/-- Real Gram from integer pairings on the same slots and the same sections. -/
theorem measured_gram {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ) :
    (fun i j : Fin m => (read S D (section D j) i : ℝ)) =
      MeasuredCut.gram (fun i => ((S i).card:ℝ)*(D i:ℝ)^2) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [read, section, MeasuredCut.gram, Matrix.diagonal_apply, Matrix.mul_apply, pow_two]
    <;> ring
  · simp [read, section, MeasuredCut.gram, Matrix.diagonal_apply, Matrix.mul_apply, hij, pow_two]
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
    exact_mod_cast hG)
  change f (B.transpose*B).det * (U.map f*(A*G⁻¹*A.transpose)*(V.map f).transpose).det =
    f ((U*B).det*(V*B).det)
  have grouping : U.map f*(A*G⁻¹*A.transpose)*(V.map f).transpose =
      (U.map f*A)*G⁻¹*(V.map f*A).transpose := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [grouping, map_mul, mapGram, mapProd U, mapProd V, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  linear_combination (U.map f*A).det*(V.map f*A).det * G.det_nonsing_inv_mul_det hG'

end RHLean.Analysis.AlpogeThin.SlotProjector
