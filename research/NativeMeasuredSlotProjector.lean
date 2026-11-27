import RHLean.Analysis.AlpogeThin.NativeDyadicCostWindows
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

/-- One CRT representative lies in a fundamental interval. For a coordinate
test every resulting coefficient is nonnegative and at most one plus the
product of the admitted prime powers. The resulting dual norm is measured
in the same counting metric as the columns. -/
theorem bounded_dual {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i)
    (hc : Pairwise (fun i j => (D i).Coprime (D j))) (j : Fin m) :
    ∃ z : Fin (m+1) → ℕ → ℤ,
      (∀ i, read S D z i = if j=i then 1 else 0) ∧
      (∑ i, ∑ k ∈ S i, (z i k:ℝ)^2) ≤ (m+1:ℕ)*(1+∏ i, (D i:ℝ))^2 := by
  classical
  let y := fun i : Fin m => if j=i then (1:ℤ) else 0
  obtain ⟨v, u, hu⟩ := nativeDyadic_firstPrime_wheel_block_dual (fun i : Fin m => D i.succ)
    (D 0) (fun i => (hD _).ne') (fun i => hc (Fin.succ_ne_zero i).symm)
    (fun _ _ h => hc (fun he => h (Fin.succ_injective m he))) y
  let M := ∏ i : Fin m, (D i.succ:ℤ)
  let v' := v % M
  have Mpos : 0 < M := Finset.prod_pos fun i _ => by exact_mod_cast hD i.succ
  have v0 : 0 ≤ v' := Int.emod_nonneg _ Mpos.ne'
  have vM : v' ≤ M := (Int.emod_lt_of_pos v Mpos).le
  have Dpos (i) : 0 < (D i:ℤ) := by exact_mod_cast hD i
  have md (i : Fin m) : (D i.succ:ℤ) ∣ M :=
    Finset.dvd_prod_of_mem (fun k : Fin m => (D k.succ:ℤ)) (Finset.mem_univ i)
  have dv i : (D i.succ:ℤ) ∣ y i+(D 0:ℤ)*v' := by
    obtain ⟨l, hl⟩ := md i
    refine ⟨u i-(D 0:ℤ)*l*(v/M), ?_⟩
    have q : v' + M*(v/M) = v := Int.emod_add_mul_ediv v M
    linear_combination -hu i + (D 0:ℤ)*q - (D 0:ℤ)*(v/M)*hl
  choose u' prop using dv
  let c : Fin (m+1) → ℤ := Fin.cases v' u'
  have bound (i) : 0 ≤ c i ∧ c i ≤ 1+(D 0:ℤ)*M := by
    refine Fin.cases ?_ (fun k => ?_) i
    · have h := le_mul_of_one_le_left Mpos.le (by exact_mod_cast hD 0 : (1:ℤ) ≤ D 0)
      exact ⟨v0, by change v' ≤ _; linarith only [vM,h]⟩
    · have hy : 0 ≤ y k ∧ y k ≤ 1 := by dsimp [y]; split <;> simp
      have hz : 0 ≤ u' k := by
        apply nonneg_of_mul_nonneg_right _ (Dpos k.succ)
        rw [← prop k]
        exact add_nonneg hy.1 (mul_nonneg (Dpos 0).le v0)
      have hle := le_mul_of_one_le_left hz (show (1:ℤ) ≤ D k.succ by exact_mod_cast hD k.succ)
      have hupp := mul_le_mul_of_nonneg_left vM (Dpos 0).le
      exact ⟨hz, by change u' k ≤ _; linarith only [hle,prop k,hy.2,hupp]⟩
  choose a ha using hS
  let z := fun i k => if a i = k then c i else 0
  refine ⟨z, fun i => ?_, ?_⟩
  · dsimp [read,z]
    simpa [ha,c,y] using (show (D i.succ:ℤ)*u' i-(D 0:ℤ)*v' = y i by linarith only [prop i])
  · have HM : (∏ i, (D i:ℝ)) = (D 0:ℝ)*(M:ℝ) := by simp [M,Fin.prod_univ_succ]
    calc
      _ = ∑ i, (c i:ℝ)^2 := by simp [z, ha, ite_pow]
      _ ≤ ∑ _i : Fin (m+1), (1+∏ i, (D i:ℝ))^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (by exact_mod_cast (bound i).1)
        rw [HM]
        exact_mod_cast (bound i).2
      _ = _ := by simp

/-- Real Gram from integer pairings on the same slots and the same sections. -/
theorem measured_gram {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ) :
    (fun i j : Fin m => (read S D (starColumn D j) i : ℝ)) =
      MeasuredCut.gram (fun i => ((S i).card:ℝ)*(D i:ℝ)^2) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [read, starColumn, MeasuredCut.gram, Matrix.mul_apply, (Fin.succ_ne_zero i).symm, pow_two]
    ring
  · simp [read, starColumn, MeasuredCut.gram, Matrix.mul_apply, (Fin.succ_ne_zero j).symm, hij, pow_two]
    ring

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

private theorem place_test {m : ℕ} {J : Type*} [Fintype J] (p : ℕ) [Fact p.Prime]
    (ι : ℂ →+* PadicAlgCl p) (B : Matrix J (Fin m) ℤ) (U : Matrix (Fin m) J ℂ)
    (hU : ∀ i k, ‖ι (U i k)‖ ≤ 1) :
    ‖ι (U*B.map (Int.castRingHom ℂ)).det‖ ≤ 1 := by
  classical
  apply WheelFit.integral_det
  intro i j
  rw [Matrix.mul_apply, map_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro k _
  change ‖ι (U i k*((B k j:ℤ):ℂ))‖ ≤ 1
  rw [map_mul, map_intCast, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)).trans (hU i k)

/-- At each prime and every complex-to-p-adic embedding, the same single
determinant clears arbitrary locally integral tests. The second row is
tested at the conjugate embedding. -/
theorem place_bound {m : ℕ} {J : Type*} [Fintype J] (p : ℕ) [Fact p.Prime]
    (ι : ℂ →+* PadicAlgCl p) (B : Matrix J (Fin m) ℤ) (U V : Matrix (Fin m) J ℂ)
    (hg : (B.transpose*B).det ≠ 0) (hu : ∀ i k, ‖ι (U i k)‖ ≤ 1)
    (hv : ∀ i k, ‖(ι.comp (starRingEnd ℂ)) (V i k)‖ ≤ 1) :
    let A := B.map (Int.castRingHom ℂ)
    let P := A*(A.transpose*A)⁻¹*A.transpose
    ‖ι ((((B.transpose*B).det:ℤ):ℂ)*(U*P*(V.map (starRingEnd ℂ)).transpose).det)‖ ≤ 1 := by
  classical
  let f := Int.castRingHom ℂ
  let A := B.map f
  let G := A.transpose*A
  let W := V.map (starRingEnd ℂ)
  have hcast : f (B.transpose*B).det = G.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]
    rfl
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (by
    rw [← hcast]
    change (((B.transpose*B).det:ℤ):ℂ) ≠ 0
    exact_mod_cast hg)
  have H : (((B.transpose*B).det:ℤ):ℂ) * (U*(A*G⁻¹*A.transpose)*W.transpose).det =
      (U*A).det*(W*A).det := by
    change f _ * _ = _
    rw [hcast, show U*(A*G⁻¹*A.transpose)*W.transpose = (U*A)*G⁻¹*(W*A).transpose by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc], Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    linear_combination (U*A).det*(W*A).det * G.det_nonsing_inv_mul_det hG
  dsimp only
  change ‖ι (_ * (U*(A*G⁻¹*A.transpose)*W.transpose).det)‖ ≤ 1
  rw [H, map_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (place_test p ι B W hv)).trans (place_test p ι B U hu)

/-- A quotient address records the prime direction and the actual integer
in its band. No volume or local height is supplied to this definition. -/
abbrev Address {m : ℕ} (S : Fin (m+1) → Finset ℕ) := (i : Fin (m+1)) × {k // k ∈ S i}

/-- Forgetting the band label is an integral coordinate permutation onto
the original outer quotient interval. The counting metric therefore needs
no extra multiplicity or change-of-lattice payment at this step. -/
theorem original_addresses {m : ℕ} (h : Fin (m+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) :
    ∃ e : Address (bands h v) ≃ ↥(Finset.Ioc ⌈v⌉₊ ⌊h 0⌋₊), ∀ a, (e a).val = a.2.val := by
  classical
  let H := fun i => ⌊h i⌋₊
  have anti : StrictAnti H := Fin.strictAnti_iff_succ_lt.2 fun i => by
    obtain ⟨k,hk⟩ := hne i.castSucc
    have hki : k ∈ Finset.Ioc (H i.succ) (H i.castSucc) := by simpa [H,bands] using hk
    exact (Finset.mem_Ioc.mp hki).1.trans_le (Finset.mem_Ioc.mp hki).2
  have edge : ⌈v⌉₊ ≤ H (Fin.last m) := by
    obtain ⟨k,hk⟩ := hne (Fin.last m)
    have hk' : k ∈ Finset.Ioc ⌈v⌉₊ (H (Fin.last m)) := by simpa [H,bands] using hk
    exact (Finset.mem_Ioc.mp hk').1.le.trans (Finset.mem_Ioc.mp hk').2
  have ends (i : Fin (m+1)) : ∀ k ∈ bands h v i, ⌈v⌉₊ < k ∧ k ≤ H i := by
    refine Fin.lastCases ?_ (fun a => ?_) i
    · intro k hk
      exact Finset.mem_Ioc.mp (by simpa [H,bands] using hk : k ∈ Finset.Ioc ⌈v⌉₊ (H (Fin.last m)))
    · intro k hk
      have hki : k ∈ Finset.Ioc (H a.succ) (H a.castSucc) := by simpa [H,bands] using hk
      have hlow := edge.trans (anti.antitone (Fin.le_last a.succ))
      exact ⟨hlow.trans_lt (Finset.mem_Ioc.mp hki).1,(Finset.mem_Ioc.mp hki).2⟩
  let F (a : Address (bands h v)) : ↥(Finset.Ioc ⌈v⌉₊ ⌊h 0⌋₊) :=
    ⟨a.2.val, Finset.mem_Ioc.mpr ⟨(ends _ _ a.2.property).1,
      (ends _ _ a.2.property).2.trans (anti.antitone (Fin.zero_le _))⟩⟩
  have apart {i j : Fin (m+1)} (hij : i < j) {k : ℕ} (hi : k ∈ bands h v i) (hj : k ∈ bands h v j) : False := by
    have hlast : i ≠ Fin.last m := (hij.trans_le (Fin.le_last j)).ne
    obtain ⟨a,ha⟩ := Fin.eq_castSucc_of_ne_last hlast
    have hle : a.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp (show a.castSucc < j by rwa [ha])
    rw [← ha] at hi
    have hak : k ∈ Finset.Ioc (H a.succ) (H a.castSucc) := by simpa [H,bands] using hi
    exact (Finset.mem_Ioc.mp hak).1.not_ge ((ends _ _ hj).2.trans (anti.antitone hle))
  have inj : Function.Injective F := by
    rintro ⟨i,k⟩ ⟨j,l⟩ he
    have hk : k.val = l.val := congrArg Subtype.val he
    have eqi : i=j := le_antisymm (le_of_not_gt fun h => apart h l.property (hk ▸ k.property))
      (le_of_not_gt fun h => apart h k.property (hk.symm ▸ l.property))
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext hk)
  have sur : Function.Surjective F := by
    intro k
    let T := Finset.univ.filter (fun i => k.val ≤ H i)
    have h0 : (0 : Fin (m+1)) ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_Ioc.mp k.property).2⟩
    let i := T.max' ⟨0,h0⟩
    have himem : i ∈ T := Finset.max'_mem _ _
    have htop := (Finset.mem_filter.mp himem).2
    have mem : k.val ∈ bands h v i := by
      by_cases he : i = Fin.last m
      · rw [he] at htop ⊢
        simpa [H,bands] using Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp k.property).1,htop⟩
      · obtain ⟨j,hj⟩ := Fin.eq_castSucc_of_ne_last he
        have low : H j.succ < k.val := by
          by_contra! bad
          have hmem : j.succ ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad⟩
          have hle : j.succ ≤ i := Finset.le_max' T _ hmem
          exact (show j.castSucc < j.succ from Fin.castSucc_lt_succ).not_ge (hj.symm ▸ hle)
        rw [← hj] at htop ⊢
        simpa [H,bands] using Finset.mem_Ioc.mpr ⟨low,htop⟩
    exact ⟨⟨i,⟨k.val,mem⟩⟩,Subtype.ext rfl⟩
  exact ⟨Equiv.ofBijective F ⟨inj,sur⟩,fun _ => rfl⟩

def columns {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ) :
    Matrix (Address S) (Fin m) ℤ := fun a j => starColumn D j a.1 a.2.val

theorem dot_read {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
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

/-- Every integral section pairing in the measured layer metric. -/
theorem columns_gram {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ) :
    (Int.castRingHom ℝ).mapMatrix ((columns S D).transpose * columns S D) =
      MeasuredCut.gram (fun i => (((S i).card * D i^2 : ℕ):ℝ)) := by
  ext i j
  have hj := congrFun (congrFun (measured_gram S D) i) j
  change (((∑ x : Address S, columns S D x i * columns S D x j):ℤ):ℝ) = _
  rw [show (∑ x : Address S, columns S D x i * columns S D x j) = read S D (starColumn D j) i by
    simpa only [columns, mul_comm] using dot_read S D (starColumn D j) i]
  simpa using hj

theorem columns_det {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) :
    ((columns S D).transpose * columns S D).det =
      (mass fun i => (S i).card * D i ^ 2 : ℕ) := by
  classical
  let s := fun i => (S i).card * D i ^ 2
  have hs i : 0 < s i := Nat.mul_pos (Finset.card_pos.mpr (hS i)) (pow_pos (hD i) _)
  let f := Int.castRingHom ℝ
  have hg : f.mapMatrix ((columns S D).transpose * columns S D) =
      MeasuredCut.gram (fun i => (s i:ℝ)) := columns_gram S D
  apply Int.cast_injective (α := ℝ)
  change f _ = _
  rw [RingHom.map_det, hg, ← mass_det s hs]
  simp [s]

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
  exact eq_inv_of_mul_eq_one_right test

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
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [bands]
    exact (show ((bands h v i).card:ℝ) ≤ (⌊h i⌋₊:ℝ) by exact_mod_cast hi).trans (bound i)
  dsimp only
  exact fun i => mul_le_mul (card i) (pow_le_pow_left₀ (Nat.cast_nonneg _)
    (MeasuredCut.wheel_factor_le (p i) c x (hp i) hx (hhigh i) (hband i)) 2) (sq_nonneg _) hxb

private theorem cofactor {m : ℕ} (w : Fin (m+1) → ℝ) (hw : ∀ i, 0 < w i) :
    (MeasuredCut.gram w).det = ∑ i, ∏ j ∈ Finset.univ.erase i, w j := by
  rw [MeasuredCut.gram_det w hw, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.prod_erase_mul _ w (Finset.mem_univ i), mul_assoc, mul_inv_cancel₀ (hw i).ne', mul_one]

private theorem scaled_le {m : ℕ} (w v : Fin (m+1) → ℝ) (c d : ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (hc : 0 ≤ c) (h : ∀ i, c*w i ≤ d*v i) :
    c^m*(MeasuredCut.gram w).det ≤ d^m*(MeasuredCut.gram v).det := by
  classical
  rw [cofactor w hw, cofactor v hv, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have H := Finset.prod_le_prod₀ (s := Finset.univ.erase i)
    (fun j _ => mul_nonneg hc (hw j).le) (fun j _ => h j)
  simpa [Finset.prod_mul_distrib] using H

/-- Relative cost of changing from real cut lengths to actual integer
slot counts in the same Gram. The prime weights can already be present. -/
theorem rounded_gram {m : ℕ} (w D : Fin (m+1) → ℝ) (S : Fin (m+1) → Finset ℕ)
    (r : ℝ) (hr : 4 ≤ r) (hw : ∀ i, r ≤ w i) (hD : ∀ i, 0 < D i)
    (lo : ∀ i, w i-2 ≤ ((S i).card:ℝ)) (hi : ∀ i, ((S i).card:ℝ) ≤ w i+1) :
    let old := (MeasuredCut.gram (fun i => w i * D i^2)).det
    let newVol := (MeasuredCut.gram (fun i => ((S i).card:ℝ) * D i^2)).det
    (1-2/r)^m * old ≤ newVol ∧ newVol ≤ (1+1/r)^m * old := by
  have hr0 : 0 < r := by linarith
  have hp i := mul_pos (hr0.trans_le (hw i)) (sq_pos_of_pos (hD i))
  have hq i := mul_pos (show 0 < ((S i).card:ℝ) by linarith only [lo i, hw i, hr]) (sq_pos_of_pos (hD i))
  have hlow i : (1-2/r)*w i ≤ ((S i).card:ℝ) := by
    have HH := mul_le_mul_of_nonneg_left (hw i) (by positivity : (0:ℝ) ≤ 2/r)
    rw [div_mul_cancel₀ _ hr0.ne'] at HH
    linarith only [HH, lo i]
  have hhigh i : ((S i).card:ℝ) ≤ (1+1/r)*w i := by
    have HH := mul_le_mul_of_nonneg_left (hw i) (by positivity : (0:ℝ) ≤ 1/r)
    rw [div_mul_cancel₀ _ hr0.ne'] at HH
    linarith only [HH, hi i]
  constructor
  · simpa using scaled_le _ _ (1-2/r) 1 hp hq (sub_nonneg.mpr ((div_le_one hr0).2 (by linarith)))
      (fun i => by simpa only [one_mul, ← mul_assoc] using mul_le_mul_of_nonneg_right (hlow i) (sq_nonneg (D i)))
  · simpa using scaled_le _ _ 1 (1+1/r) hq hp zero_le_one
      (fun i => by simpa only [one_mul, ← mul_assoc] using mul_le_mul_of_nonneg_right (hhigh i) (sq_nonneg (D i)))

/-- Aggregate admission and the price of its one omitted direction in the
integer Gram determinants of precisely the slot sections used for testing. -/
theorem columns_gain {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) (K : ℝ) (hK : ∀ i, (D i:ℝ) ≤ K) :
    let A := columns S (fun _ => 1)
    let B := columns S D
    let before := (((A.transpose*A).det:ℤ):ℝ)
    let after := (((B.transpose*B).det:ℤ):ℝ)
    after ≤ (∏ i, (D i:ℝ))^2 * before ∧ (∏ i, (D i:ℝ))^2 * before ≤ K^2 * after := by
  dsimp only
  rw [columns_det S D hS hD, columns_det S (fun _ => 1) hS (fun _ => Nat.zero_lt_one)]
  simp only [Int.cast_natCast, one_pow, mul_one]
  rw [mass_det _ (fun i => Nat.mul_pos (Finset.card_pos.mpr (hS i)) (pow_pos (hD i) _)),
    mass_det _ (fun i => Finset.card_pos.mpr (hS i))]
  push_cast
  exact MeasuredCut.admission_bounds _ _ K (fun i => by exact_mod_cast Finset.card_pos.mpr (hS i))
    (fun i => ⟨by exact_mod_cast hD i, hK i⟩)

/-- At the square-clock scale the entire joint clearing price of a single
fibre, including its rank-one tests, is at most x^4. -/
theorem squareClock_price (m E : ℕ) (p : Fin (m+1) → ℕ) (a : Fin (m+1) → ℝ)
    (v x ε : ℝ) (hx : 10 ≤ x) (hε : ε ≤ 1) (hE : 0 < E)
    (hp : ∀ i, (p i).Prime) (ho : StrictMono p) (high : ∀ i, Real.sqrt x ≤ p i)
    (band : ∀ i, (p i:ℝ) ≤ x) (ha : ∀ i, a i ≤ (x+1)*Real.exp (x^ε))
    (T : Finset ℕ) :
    let c := ⌊Real.sqrt x⌋₊
    let S := bands (fun i => a i/(p i:ℝ)) v
    let D := fun i => p i^(⌊(c:ℝ)*x⌋₊ / p i - c)
    (∀ i, (S i).Nonempty) →
      (∑ l ∈ T, ((allowance (fun i => (S i).card * D i^2) E).factorization l:ℝ)*Real.log l)/(E:ℝ) ≤ x^4 := by
  classical
  let b := Real.exp (x^ε)
  let c := ⌊Real.sqrt x⌋₊
  let S := bands (fun i => a i/(p i:ℝ)) v
  let D := fun i => p i^(⌊(c:ℝ)*x⌋₊ / p i - c)
  let s := fun i => (S i).card * D i^2
  change (∀ i, (S i).Nonempty) → _
  intro hS
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hcount : m+1 ≤ ⌊x⌋₊ := by
    have hi := Finset.card_le_card_of_injOn (s := Finset.univ)
      (t := Finset.Icc 1 ⌊x⌋₊) p (fun i _ => Finset.mem_Icc.mpr ⟨(hp i).one_le, Nat.le_floor (band i)⟩)
      (fun _ _ _ _ h => ho.injective h)
    simpa using hi
  have hm : (m:ℝ) ≤ x := (show (m:ℝ) ≤ (⌊x⌋₊:ℝ) by exact_mod_cast Nat.le_of_succ_le hcount).trans
    (Nat.floor_le hx0.le)
  let L := (x+1)*b*Real.exp ((c:ℝ)*Real.sqrt x*Real.log x)^2
  have hL : 0 < L := by dsimp [L,b]; positivity
  have hnorm (i) : (s i:ℝ) ≤ L := by
    simpa [s,D,S,L,c,b] using firstPrime_norm_cap m c p a v x b hx1 (Real.exp_pos _).le ha hp high band i
  have H := allowance_price s (fun i => Nat.mul_pos (Finset.card_pos.mpr (hS i))
    (pow_pos (pow_pos (hp i).pos _) _)) L hnorm E hE T
  apply H.trans
  have hcx : (c:ℝ)*Real.sqrt x ≤ x :=
    (mul_le_mul_of_nonneg_right (Nat.floor_le (Real.sqrt_nonneg x)) (Real.sqrt_nonneg x)).trans_eq
      (Real.mul_self_sqrt hx0.le)
  have hlogx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hpow : x^ε ≤ x := by simpa using Real.rpow_le_rpow_of_exponent_le hx1 hε
  have logL : Real.log L ≤ 4*x^2 := by
    dsimp [L,b]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_pow, Real.log_exp]
    have hterm := mul_le_mul hcx hlogx (Real.log_nonneg hx1) hx0.le
    have he : Real.log (x+1) ≤ x := by linarith only [Real.log_le_sub_one_of_pos (show 0 < x+1 by linarith)]
    calc
      _ ≤ x+x+2*(x*x) := add_le_add (add_le_add he hpow) (mul_le_mul_of_nonneg_left hterm (by norm_num))
      _ ≤ _ := by nlinarith only [mul_nonneg hx0.le (show 0 ≤ x-1 by linarith)]
  have logm : Real.log (m+1:ℕ) ≤ m := by
    simpa using Real.log_le_sub_one_of_pos (show (0:ℝ) < (m+1:ℕ) by positivity)
  have hE1 : (1:ℝ) ≤ E := by exact_mod_cast hE
  have Ediv : (Real.log (m+1:ℕ)+(m:ℝ)*Real.log L)/(E:ℝ) ≤ (m:ℝ)+(m:ℝ)*(4*x^2) :=
    (div_le_div_of_nonneg_right (add_le_add logm (mul_le_mul_of_nonneg_left logL (Nat.cast_nonneg m)))
      (Nat.cast_nonneg E)).trans (div_le_self (by positivity) hE1)
  have htwo : Real.log (2*L) ≤ 1+4*x^2 := by
    rw [Real.log_mul (by norm_num) hL.ne']
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2), logL]
  calc
    _ ≤ ((m:ℝ)+(m:ℝ)*(4*x^2)) + (m:ℝ)*(1+4*x^2) :=
      add_le_add Ediv (mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg m))
    _ = (m:ℝ)*(2+8*x^2) := by ring
    _ ≤ x*(2+8*x^2) := mul_le_mul_of_nonneg_right hm (by positivity)
    _ ≤ x^4 := by
      have h1 := mul_nonneg (show 0 ≤ x-10 by linarith) (pow_nonneg hx0.le 3)
      have h2 := mul_nonneg hx0.le (show 0 ≤ x^2-1 by nlinarith only [sq_nonneg (x-1),hx])
      nlinarith only [h1, h2]

open Filter in
/-- Even polynomially many such fibre prices are affordable in the
compact per-direction budget on the native exponential-width clock. -/
theorem squareClock_budget (ε J K : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (f a t : ℝ), 1 ≤ f → Real.exp (x^ε) ≤ a →
      0 < t → t ≤ x^K → x^J*x^4 ≤ f*a*(Real.log (Real.exp (x^ε)))^3/t := by
  filter_upwards [dyadic_rpow_le_exp_eventually (J+4+K) ε hε, eventually_ge_atTop (1:ℝ)]
    with x h hx
  intro f a t hf ha ht htk
  have hx0 := zero_lt_one.trans_le hx
  have hεx : 1 ≤ x^ε := Real.one_le_rpow hx hε.le
  rw [Real.rpow_add hx0, Real.rpow_add hx0, show x^(4:ℝ) = x^(4:ℕ) from Real.rpow_natCast x 4] at h
  rw [Real.log_exp, le_div_iff₀ ht]
  calc
    _ ≤ x^J*x^4*x^K := mul_le_mul_of_nonneg_left htk (by positivity)
    _ ≤ a := h.trans ha
    _ ≤ f*a := le_mul_of_one_le_left ((Real.exp_pos _).le.trans ha) hf
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hf) ((Real.exp_pos _).le.trans ha))
      (one_le_pow₀ hεx)

/-- The denominator of the projector onto one of the very same columns
is the sum of its two measured integer masses. -/
theorem line_det {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ) (j : Fin m) :
    let B : Matrix (Address S) (Fin 1) ℤ := fun x _ => columns S D x j
    (B.transpose*B).det = (((S 0).card*D 0^2 + (S j.succ).card*D j.succ^2:ℕ):ℤ) := by
  classical
  dsimp only
  rw [Matrix.det_fin_one]
  change (∑ x : Address S, starColumn D j x.1 x.2.val * columns S D x j) = _
  rw [dot_read]
  simp [read, starColumn, (Fin.succ_ne_zero j).symm, pow_two]
  ring

open Filter in
/-- Uniform at every sufficiently large real anchor. For every eligible
ordered high first-prime fibre the integral dual attains the projector
determinant, admission retains the stated prime product on these columns,
and the joint finite price is at most x^4. -/
theorem firstPrime_projector (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ x : ℝ in atTop, ∀ (m E : ℕ) (p : Fin (m+1) → ℕ)
      (t : Fin (m+1) → AlpogeNativeDyadicH e) (a : AlpogeNativeDyadicH e → ℝ)
      (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) (site : AlpogeNativeE0 × AlpogeNativeDyadicH e),
      let b := Real.exp (x^ε)
      let c := ⌊Real.sqrt x⌋₊
      let S := bands (fun i => a (t i)/(p i:ℝ)) (w site)
      let D := fun i => p i^(⌊(c:ℝ)*x⌋₊/p i-c)
      let s := fun i => (S i).card*D i^2
      let A := columns S (fun _ => 1)
      let B := columns S D
      let Bq := B.map (Int.castRingHom ℚ)
      let P := Bq*(Bq.transpose*Bq)⁻¹*Bq.transpose
      let before := (((A.transpose*A).det:ℤ):ℝ)
      let after := (((B.transpose*B).det:ℤ):ℝ)
      0 < E → (∀ i, (p i).Prime) → StrictMono p → (∀ i, Real.sqrt x ≤ p i) →
      (∀ i, (p i:ℝ)+1 ≤ x) → (∀ i, a (t i) ∈ Set.Icc (x*b) ((x+1)*b)) →
      (∀ i, alpogeNativePartner (t i) ((alpogeNativeHostData e q d).frob (p i)) = site) →
      0 ≤ w site → w site ≤ b*(1+1/x) →
      (∃ Y : Matrix (Fin m) (Address S) ℤ,
        let T := Y.map (Int.castRingHom ℚ)
        Y*B=1 ∧ (T*P*T.transpose).det = ((mass s:ℕ):ℚ)⁻¹) ∧
      (after ≤ (∏ i, (D i:ℝ))^2*before ∧
        (∏ i, (D i:ℝ))^2*before ≤ Real.exp ((c:ℝ)*Real.sqrt x*Real.log x)^2*after) ∧
      ∀ T : Finset ℕ, (∑ l ∈ T, ((allowance s E).factorization l:ℝ)*Real.log l)/(E:ℝ) ≤ x^4 := by
  filter_upwards [dyadic_rpow_le_exp_eventually 3 ε hε, eventually_ge_atTop (10:ℝ)]
    with x hb hx
  intro m E p t a w site
  dsimp only
  intro hE hp ho high band ha hsite hv hw
  let b := Real.exp (x^ε)
  let c := ⌊Real.sqrt x⌋₊
  let S := bands (fun i => a (t i)/(p i:ℝ)) (w site)
  let D := fun i => p i^(⌊(c:ℝ)*x⌋₊/p i-c)
  have hx1 : 1 ≤ x := by linarith
  have hb' : 4*x^2 ≤ b := by
    rw [show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast] at hb
    exact (show 4*x^2 ≤ x^3 by nlinarith only [mul_nonneg (show 0 ≤ x-4 by linarith) (sq_nonneg x)]).trans hb
  have hS (i) : (S i).Nonempty := (firstPrime_slots e q d m p t a w x b hx1 hb' hp ho band ha site hsite hv hw i).2.1
  have hD (i) : 0 < D i := pow_pos (hp i).pos _
  have cop : Pairwise (fun i j => (D i).Coprime (D j)) := fun i j hij =>
    Nat.coprime_pow_primes _ _ (hp i) (hp j) (ho.injective.ne hij)
  have px (i) : (p i:ℝ) ≤ x := by linarith only [band i]
  exact ⟨attained_price S D hS hD cop, columns_gain S D hS hD _
    (fun i => MeasuredCut.wheel_factor_le (p i) c x (hp i) hx1 (high i) (px i)), fun T =>
    squareClock_price m E p (fun i => a (t i)) (w site) x ε hx hε1 hE hp ho high px (fun i => (ha i).2) T hS⟩

private theorem clearing_bound (p : ℕ) [Fact p.Prime] (ι : ℂ →+* PadicAlgCl p)
    (a C k : ℕ) (ha : 0 < a) (hC : 0 < C) (hk : 0 < k) (hd : a^k ∣ C)
    (z : ℂ) (hz : ‖ι ((a:ℂ)*z)‖ ≤ 1) :
    ‖ι z‖ ≤ Real.exp (((C.factorization p:ℝ)*Real.log p)/(k:ℝ)) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have pn : padicNorm p (a:ℚ) = ((p:ℚ)^a.factorization p)⁻¹ := by
    rw [padicNorm.eq_zpow_of_nonzero (Nat.cast_ne_zero.mpr ha.ne'), padicValRat.of_nat,
      Nat.factorization_def _ (Fact.out : p.Prime), zpow_neg, zpow_natCast]
  have normA : ‖ι (a:ℂ)‖ = ((p:ℝ)^a.factorization p)⁻¹ := by
    simpa [pn] using WheelFit.place_rat p ι (a:ℚ)
  rw [map_mul, norm_mul, normA, inv_mul_eq_div] at hz
  have hf := (Nat.factorization_le_iff_dvd (pow_pos ha k).ne' hC.ne').2 hd p
  have he : k*a.factorization p ≤ C.factorization p := by simpa [Nat.factorization_pow] using hf
  have hc : (k:ℝ)*(a.factorization p:ℝ) ≤ (C.factorization p:ℝ) := by exact_mod_cast he
  calc
    _ ≤ (p:ℝ)^a.factorization p := (div_le_one (pow_pos hp _)).1 hz
    _ = Real.exp ((a.factorization p:ℝ)*Real.log p) := by rw [Real.exp_nat_mul,Real.exp_log hp]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      apply (le_div_iff₀ (show (0:ℝ)<k by exact_mod_cast hk)).mpr
      calc
        _ = ((k:ℝ)*(a.factorization p:ℝ))*Real.log p := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.log_natCast_nonneg p)

/-- Tested determinant for an integral matrix of sections and two
arbitrary tables of complex rows. -/
def testedDet {m : ℕ} {J : Type*} [Fintype J] (B : Matrix J (Fin m) ℤ)
    (U V : Matrix (Fin m) J ℂ) : ℂ :=
  let A := B.map (Int.castRingHom ℂ)
  (U*(A*(A.transpose*A)⁻¹*A.transpose)*(V.map (starRingEnd ℂ)).transpose).det

/-- Price a rational change of the two test lattices. The two clearing
integers enter once each per determinant dimension. -/
theorem transport_integral {m : ℕ} {J : Type*} [Fintype J] (p : ℕ) [Fact p.Prime]
    (ι : ℂ →+* PadicAlgCl p) (B : Matrix J (Fin m) ℤ) (U V : Matrix (Fin m) J ℂ)
    (a b : ℕ) (hg : (B.transpose*B).det ≠ 0)
    (hu : ∀ i k, ‖ι ((a:ℂ)*U i k)‖ ≤ 1)
    (hv : ∀ i k, ‖(ι.comp (starRingEnd ℂ)) ((b:ℂ)*V i k)‖ ≤ 1) :
    ‖ι ((((B.transpose*B).det:ℤ):ℂ)*((a:ℂ)*(b:ℂ))^m*testedDet B U V)‖ ≤ 1 := by
  classical
  have H := place_bound p ι B ((a:ℂ) • U) ((b:ℂ) • V) hg hu hv
  have bar : ((b:ℂ) • V).map (starRingEnd ℂ) = (b:ℂ) • V.map (starRingEnd ℂ) := by
    ext i j
    change (starRingEnd ℂ) ((b:ℂ)*V i j) = (b:ℂ)*((starRingEnd ℂ) (V i j))
    rw [map_mul,map_natCast]
  dsimp only at H
  rw [bar, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, Matrix.det_smul, Fintype.card_fin] at H
  simpa only [testedDet, mul_comm (b:ℂ) (a:ℂ), mul_assoc] using H

/-- One explicit local allowance works simultaneously for the full
projector and every class-scaled line in it at every embedding. Its
finite sums have the upper bound in allowance_price. -/
theorem common_place {m : ℕ} (S : Fin (m+1) → Finset ℕ) (D : Fin (m+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) (E p : ℕ) (hE : 0 < E)
    [Fact p.Prime] (ι : ℂ →+* PadicAlgCl p) :
    let s := fun i => (S i).card*D i^2
    let γ := ((allowance s E).factorization p:ℝ)*Real.log p/(E:ℝ)
    let B := columns S D
    (∀ U V : Matrix (Fin m) (Address S) ℂ, (∀ i k, ‖ι (U i k)‖ ≤ 1) →
      (∀ i k, ‖(ι.comp (starRingEnd ℂ)) (V i k)‖ ≤ 1) →
      ‖ι (testedDet B U V)‖ ≤ Real.exp ((E:ℝ)*γ)) ∧
    ∀ (j : Fin m) (h : ℕ) (U V : Matrix (Fin 1) (Address S) ℂ),
      (∀ i k, ‖ι (U i k)‖ ≤ 1) → (∀ i k, ‖(ι.comp (starRingEnd ℂ)) (V i k)‖ ≤ 1) →
      ‖ι ((h:ℂ)*testedDet (fun x (_ : Fin 1) => B x j) U V)‖ ≤ Real.exp γ := by
  classical
  let s := fun i => (S i).card*D i^2
  have hs i : 0 < s i := Nat.mul_pos (Finset.card_pos.mpr (hS i)) (pow_pos (hD i) _)
  have hg : 0 < mass s := Finset.sum_pos (fun i _ => Finset.prod_pos (fun j _ => hs j)) Finset.univ_nonempty
  have hc : 0 < allowance s E := Nat.mul_pos hg (pow_pos (Finset.prod_pos fun j _ => Nat.add_pos_left (hs 0) _) _)
  have he : (0:ℝ) < E := by exact_mod_cast hE
  constructor
  · intro U V hu hv
    have eqg := columns_det S D hS hD
    have hn : ((columns S D).transpose*columns S D).det ≠ 0 := by
      rw [eqg]
      exact_mod_cast hg.ne'
    have H := place_bound p ι (columns S D) U V hn hu hv
    dsimp only at H
    rw [eqg, Int.cast_natCast] at H
    have decl := clearing_bound p ι (mass s) (allowance s E) 1 hg hc Nat.zero_lt_one
      (by simpa using (allowance_dvd s E).1) (testedDet (columns S D) U V) H
    change ‖ι (testedDet (columns S D) U V)‖ ≤
      Real.exp ((E:ℝ)*(((allowance s E).factorization p:ℝ)*Real.log p/(E:ℝ)))
    rw [mul_div_cancel₀ _ he.ne']
    simpa only [Nat.cast_one, div_one] using decl
  · intro j h U V hu hv
    let B : Matrix (Address S) (Fin 1) ℤ := fun x _ => columns S D x j
    have eqg : (B.transpose*B).det = (s 0+s j.succ:ℕ) := line_det S D j
    have hpos : 0 < s 0+s j.succ := Nat.add_pos_left (hs 0) _
    have hn : (B.transpose*B).det ≠ 0 := by rw [eqg]; exact_mod_cast hpos.ne'
    have H := place_bound p ι B U V hn hu hv
    dsimp only at H
    rw [eqg, Int.cast_natCast] at H
    apply clearing_bound p ι (s 0+s j.succ) (allowance s E) E hpos hc hE ((allowance_dvd s E).2 j)
    rw [mul_left_comm, map_mul, norm_mul]
    rw [map_natCast]
    exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) h)).trans H

/-- Shared-anchor arithmetic certificate. For x=65, b=100000 and
beta=50000 the complete cutoff is 130. The three high cuts at 31,47,59
give unit clearing factors at 131. A thick order and three thin orders
have total factorial valuation 1917 at that very prime. -/
theorem cutoff131 :
    let top := 65*100000
    let D := fun p : ℕ => p^(520/p-8)
    let s₀ := (top/31-top/47)*D 31^2
    let s₁ := (top/47-top/59)*D 47^2
    let s₂ := (top/59-100000)*D 59^2
    top/50000=130 ∧ (s₀*s₁+s₀*s₂+s₁*s₂)%131=17 ∧
      (s₀+s₁)%131=109 ∧ (s₀+s₂)%131=33 ∧
      ((Nat.factorial 100000).factorization 131 + 3*(Nat.factorial 50000).factorization 131)=1917 := by
  let _ : Fact (Nat.Prime 131) := ⟨by norm_num⟩
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rw [Nat.factorization_def _ Fact.out, Nat.factorization_def _ Fact.out,
    padicValNat_factorial (by decide : Nat.log 131 100000 < 3),
    padicValNat_factorial (by decide : Nat.log 131 50000 < 3)]
  decide

end RHLean.Analysis.AlpogeThin.SlotProjector
