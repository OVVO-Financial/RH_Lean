import RHLean.Analysis.AlpogeThin.NativeDyadicShiftedWidthRows

/-!
# Prime admission on the measured thick cuts

At one translated positive site the active first-prime cuts are nested intervals.
Use their disjoint layers as integral coordinates, with their measured lengths as
the diagonal metric. Scaling coordinate i by the prime power counted on the wheel
gives columns Dᵢ eᵢ - D₀ e₀. The same lengths enter the comparison before and
after prime admission. The determinant loses at most one prime power per fibre.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis.AlpogeThin.MeasuredCut

/-- In a star of coordinate differences, the shared pivot contributes to every
entry of the Gram matrix and each nonpivot coordinate to a single diagonal entry. -/
def gram {m : ℕ} (s : Fin (m+1) → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun i => s i.succ) +
    Matrix.replicateCol Unit (fun _ => s 0) * Matrix.replicateRow Unit (fun _ => 1)

/-- The squared covolume, including the zero-column case of a singleton fibre. -/
theorem gram_det {m : ℕ} (s : Fin (m+1) → ℝ) (hs : ∀ i, 0 < s i) :
    (gram s).det = (∏ i, s i) * ∑ i, (s i)⁻¹ := by
  classical
  let A := Matrix.diagonal (fun i : Fin m => s i.succ)
  let u := fun i : Fin m => s 0 / s i.succ
  let oneRow := Matrix.replicateRow Unit (fun _ : Fin m => (1 : ℝ))
  have factor : gram s = A * (1 + Matrix.replicateCol Unit u * oneRow) := by
    rw [Matrix.mul_add, Matrix.mul_one]
    apply congrArg (A + ·)
    ext i j
    simp [A, u, oneRow, Matrix.diagonal_mul, Matrix.mul_apply, (hs i.succ).ne',
      div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc]
  rw [factor, Matrix.det_mul, show A.det = ∏ i : Fin m, s i.succ from Matrix.det_diagonal]
  change _ * (1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit (fun _ => (1:ℝ))).det = _
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow, Fin.prod_univ_succ s,
    Fin.sum_univ_succ (fun i => (s i)⁻¹)]
  simp only [dotProduct, u, one_mul, div_eq_mul_inv, ← Finset.mul_sum]
  field_simp [(hs 0).ne'] <;> ring

/-- For the same physical layer lengths, admission changes the squared
covolume by the product of all squared prime factors, up to one omitted
factor. The bounds are independent of the smallest layer length. -/
theorem admission_bounds {m : ℕ} (w D : Fin (m+1) → ℝ) (K : ℝ)
    (hw : ∀ i, 0 < w i) (hD : ∀ i, 1 ≤ D i ∧ D i ≤ K) :
    let old := (gram w).det
    let newVol := (gram (fun i => w i * D i ^ 2)).det
    let total := (∏ i, D i) ^ 2 * old
    newVol ≤ total ∧ total ≤ K ^ 2 * newVol := by
  classical
  dsimp only
  have hDpos i : 0 < D i := zero_lt_one.trans_le (hD i).1
  have hnew i : 0 < w i * D i ^ 2 := mul_pos (hw i) (sq_pos_of_pos (hDpos i))
  have hprod : ∏ i, (w i * D i ^ 2) = (∏ i, w i) * (∏ i, D i) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
  let cap := (∏ i, w i) * (∏ i, D i) ^ 2
  have hcap : 0 ≤ cap := mul_nonneg (Finset.prod_nonneg fun i _ => (hw i).le) (sq_nonneg _)
  have hsum : (∑ i, (w i * D i ^ 2)⁻¹) ≤ ∑ i, (w i)⁻¹ := by
    apply Finset.sum_le_sum
    intro i _
    apply inv_anti₀ (hw i)
    exact le_mul_of_one_le_right (hw i).le (one_le_pow₀ (hD i).1)
  have hrev : (∑ i, (w i)⁻¹) ≤ K ^ 2 * ∑ i, (w i * D i ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (hw i) (hnew i), one_mul]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hDpos i).le (hD i).2 2) (hw i).le).trans_eq
      (mul_comm _ _)
  rw [gram_det w hw, gram_det _ hnew, hprod]
  constructor
  · calc
      _ ≤ cap * ∑ i, (w i)⁻¹ := mul_le_mul_of_nonneg_left hsum hcap
      _ = _ := by dsimp [cap]; ring
  · calc
      _ = cap * ∑ i, (w i)⁻¹ := by dsimp [cap]; ring
      _ ≤ cap * (K ^ 2 * ∑ i, (w i * D i ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hrev hcap
      _ = _ := by dsimp [cap]; ring

/-- These lengths are the differences of consecutive nested measured cuts,
with the shortest cut supplying the final layer. -/
def layers {m : ℕ} (U : Fin (m+1) → ℝ) : Fin (m+1) → ℝ :=
  Fin.lastCases (U (Fin.last m)) (fun i => U i.castSucc - U i.succ)

/-- One charged prime power is affordable in the high band, regardless
of how many distinct addresses belong to the same measured fibre. -/
theorem wheel_factor_le (p c : ℕ) (x : ℝ) (hp : p.Prime) (hx : 1 ≤ x)
    (hhigh : Real.sqrt x ≤ p) (hpx : (p:ℝ) ≤ x) :
    ((p ^ (⌊(c:ℝ)*x⌋₊ / p - c) : ℕ) : ℝ) ≤
      Real.exp ((c:ℝ) * Real.sqrt x * Real.log x) := by
  let N := ⌊(c:ℝ)*x⌋₊
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hN : (N:ℝ) ≤ (c:ℝ)*x := Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  have hquot : ((N/p:ℕ):ℝ) * p ≤ N := by exact_mod_cast Nat.div_mul_le_self N p
  have hroot : x ≤ Real.sqrt x * (p:ℝ) := calc
    _ = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt (by linarith)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hhigh (Real.sqrt_nonneg x)
  have hdepth : ((N/p-c:ℕ):ℝ) ≤ (c:ℝ)*Real.sqrt x := calc
    _ ≤ ((N/p:ℕ):ℝ) := by exact_mod_cast Nat.sub_le (N/p) c
    _ ≤ _ := le_of_mul_le_mul_right (hquot.trans (hN.trans
      ((mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg c)).trans_eq (mul_assoc _ _ _).symm))) hp0
  change ((p ^ (N / p - c) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_pow]
  apply (Real.log_le_iff_le_exp (pow_pos hp0 _)).mp
  rw [Real.log_pow]
  exact mul_le_mul hdepth (Real.log_le_log hp0 hpx) (Real.log_natCast_nonneg _) (by positivity)

/-- At any single original thick partner, the wheel prime powers furnish a
simultaneous integral dual and a measured determinant comparison. Prime
order and the physical collar imply all layer lengths are positive. -/
theorem firstPrime_fibre (e q d c m : ℕ) [Fact q.Prime] [Fact d.Prime]
    (p : Fin (m+1) → ℕ) (t : Fin (m+1) → AlpogeNativeDyadicH e)
    (a : AlpogeNativeDyadicH e → ℝ) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b : ℝ) (hx : 1 ≤ x) (hb : 0 < b) (hprime : ∀ i, (p i).Prime)
    (horder : StrictMono p) (hhigh : ∀ i, Real.sqrt x ≤ p i)
    (hband : ∀ i, (p i:ℝ)+1 ≤ x)
    (ha : ∀ i, a (t i) ∈ Set.Icc (x*b) ((x+1)*b))
    (site : AlpogeNativeE0 × AlpogeNativeDyadicH e)
    (hs : ∀ i, alpogeNativePartner (t i) ((alpogeNativeHostData e q d).frob (p i)) = site)
    (hw : w site ≤ b*(1+1/x)) :
    let U := fun i => nativeDyadicLocalSourceAtom e q d (p i) (a (t i)) (t i) w 1
    let D := fun i => p i ^ (⌊(c:ℝ)*x⌋₊ / p i - c)
    let old := (gram (layers U)).det
    let newVol := (gram (fun i => layers U i * (D i:ℝ)^2)).det
    let total := (∏ i, (D i:ℝ))^2 * old
    (∀ i, 0 < layers U i) ∧
      (∀ y : Fin m → ℤ, ∃ (v : ℤ) (u : Fin m → ℤ), ∀ i,
        (D i.succ:ℤ) * u i - (D 0:ℤ) * v = y i) ∧
      newVol ≤ total ∧ total ≤ Real.exp ((c:ℝ)*Real.sqrt x*Real.log x)^2 * newVol := by
  classical
  dsimp only
  let U := fun i => nativeDyadicLocalSourceAtom e q d (p i) (a (t i)) (t i) w 1
  let D := fun i => p i ^ (⌊(c:ℝ)*x⌋₊ / p i - c)
  have decreasing : StrictAnti U := by
    intro i j hij
    exact sub_pos.mp (nativeDyadic_sameWidth_firstPrime_signed e q d (p i) (p j)
      (t i) (t j) w x b (a (t i)) (a (t j)) hb (hprime i).pos (horder hij)
      (hband j) (ha i) (ha j) ((hs i).trans (hs j).symm) (by rwa [hs j])).2.2
  have pos (i) : 0 < U i := by
    have hp0 : 0 < (p i:ℝ) := by exact_mod_cast (hprime i).pos
    have hx0 := zero_lt_one.trans_le hx
    have hcap : w site * p i < x*b := calc
      _ ≤ (b*(1+1/x))*(x-1) := mul_le_mul hw (by linarith only [hband i]) hp0.le (by positivity)
      _ = x*b-b/x := by field [hx0.ne']
      _ < _ := sub_lt_self _ (div_pos hb hx0)
    have hcut := sub_pos.mpr ((lt_div_iff₀ hp0).2 (hcap.trans_le (ha i).1))
    change 0 < max (a (t i) / ((p i ^ 1 : ℕ):ℝ) -
      w (alpogeNativePartner (t i) ((1:ℕ) • (alpogeNativeHostData e q d).frob (p i)))) 0
    simpa only [pow_one, one_nsmul, hs i] using
      (hcut.trans_le (le_max_left (a (t i) / (p i:ℝ) - w site) 0))
  have hlen (i) : 0 < layers U i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [layers] using pos (Fin.last m)
    · simpa [layers] using sub_pos.mpr (decreasing (Fin.castSucc_lt_succ j))
  have hD (i) : 0 < D i := pow_pos (hprime i).pos _
  have cop : Pairwise (fun i j => (D i).Coprime (D j)) := fun i j hij =>
    Nat.coprime_pow_primes _ _ (hprime i) (hprime j) (horder.injective.ne hij)
  refine ⟨hlen, ?_, admission_bounds (layers U) (fun i => (D i:ℝ)) _ hlen (fun i => ⟨?_, ?_⟩)⟩
  · exact nativeDyadic_firstPrime_wheel_block_dual (fun i : Fin m => D i.succ) (D 0)
      (fun i => (hD _).ne') (fun i => cop (Fin.succ_ne_zero i).symm)
      (fun _ _ h => cop (fun he => h (Fin.succ_injective m he)))
  · exact_mod_cast hD i
  · exact wheel_factor_le (p i) c x (hprime i) hx (hhigh i) (by linarith only [hband i])

end RHLean.Analysis.AlpogeThin.MeasuredCut
