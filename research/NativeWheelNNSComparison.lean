import «research.NativeAnchoredSlotMetric»
import «research.NativePrincipalCrossingBalance»
import RHLean.Analysis.PartialMomentSchurTarget

/-! Partial moments on the integral wheel and on the common integer address space
of its translates. The logarithmic and signed arithmetic reads have separate columns. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector
namespace WheelNNS

/-- Reassemble the four partial moments in the original counting measure. -/
def coDiv {J ι : Type*} [Fintype J] (X : Matrix J ι ℝ) : Matrix ι ι ℝ :=
  finiteCLPM Finset.univ (fun _ => 1) X 0 + finiteCUPM Finset.univ (fun _ => 1) X 0 -
    finiteDLPM Finset.univ (fun _ => 1) X 0 - finiteDUPM Finset.univ (fun _ => 1) X 0

theorem coDiv_eq {J ι : Type*} [Fintype J] (X : Matrix J ι ℝ) :
    coDiv X = X.transpose * X := by
  rw [coDiv, ← finiteTargetSecondMoment_eq_partial_reassembly]
  ext i j
  simp [finiteTargetSecondMoment, Matrix.mul_apply]

/-- Inserting the original rows at their integer addresses preserves every mixed entry,
including one between a section and a signed arithmetic observation. -/
theorem insert_gram {I J ι : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (e : I ↪ J) (X : Matrix I ι ℝ) : coDiv (slotInclusion e * X) = coDiv X := by
  classical
  rw [coDiv_eq, coDiv_eq, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (slotInclusion e).transpose (slotInclusion e) X, inclusion_gram,
    Matrix.one_mul]

/-- Index all translates in a single observation matrix at a partner. In particular
the off-diagonal blocks pair the same integer slot on the two translates. -/
def translated {J U ι : Type*} (B : U → Matrix J ι ℝ) : Matrix J (U × ι) ℝ :=
  fun z j => B j.1 z j.2

theorem translated_pair {r : ℕ} {U : Type*} (h : Fin (r+1) → ℝ) (v : U → ℝ)
    (hne : ∀ u i, (bands h (v u) i).Nonempty) (D : Fin (r+1) → ℕ)
    (u u' : U) (i j : Fin r) :
    coDiv (translated fun t => physicalColumns h (v t) (hne t) D) (u,i) (u',j) =
      ((physicalColumns h (v u) (hne u) D).transpose * physicalColumns h (v u') (hne u') D) i j := by
  rw [coDiv_eq]
  rfl

/-- Exact identification with the integral Gram determinant used to charge the
finite projector, on every retained translate and with its original prime powers. -/
theorem physical_det {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) :
    (coDiv (physicalColumns h v hne D)).det =
      ((((columns (bands h v) D).transpose * columns (bands h v) D).det : ℤ) : ℝ) := by
  rw [physicalColumns, insert_gram, coDiv_eq]
  symm
  let A := columns (bands h v) D
  let f := Int.castRingHom ℝ
  change f (A.transpose*A).det = ((A.map f).transpose*A.map f).det
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]
  rfl

theorem complementary_volume {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i) :
    complementaryLog (bands h v) D =
      -(Real.log (coDiv (physicalColumns h v hne D)).det -
        Real.log (coDiv (physicalColumns h v hne (fun _ => 1))).det)/2 := by
  rw [complementaryLog_eq _ _ hne hD, physical_det, physical_det]
  unfold logVolume
  ring

/-- The mean of a star retains the orientation of its root and leaf. -/
theorem first_moment {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ) (j : Fin r) :
    finiteTargetFirstMoment Finset.univ (fun _ => 1) ((columns S D).map (Int.castRingHom ℝ)) 0 j =
      (D j.succ:ℝ)*(S j.succ).card - (D 0:ℝ)*(S 0).card := by
  have hi := dot_read S D (fun _ _ => 1) j
  simp only [one_mul, read, Finset.sum_const, nsmul_eq_mul, mul_one] at hi
  change (∑ x : Address S, 1 * (((columns S D x j:ℤ):ℝ) - 0)) = _
  simp only [sub_zero, one_mul]
  exact_mod_cast hi

/-- Read the first moment separately from the target-invariant covariance. -/
theorem oriented_schur {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (t : Fin r → ℝ) (i j : Fin r) :
    let X := (columns S D).map (Int.castRingHom ℝ)
    finiteTargetScaledSchur Finset.univ (fun _ => 1) X t i j =
      (Fintype.card (Address S):ℝ)*coDiv X i j -
      ((D i.succ:ℝ)*(S i.succ).card - (D 0:ℝ)*(S 0).card)*
      ((D j.succ:ℝ)*(S j.succ).card - (D 0:ℝ)*(S 0).card) := by
  intro X
  rw [finiteTargetScaledSchur_target_invariant _ _ X 0 t]
  change finiteTotalWeight _ _ * finiteTargetSecondMoment _ _ X 0 i j -
    finiteTargetFirstMoment _ _ X 0 i * finiteTargetFirstMoment _ _ X 0 j = _
  rw [first_moment, first_moment, finiteTargetSecondMoment_eq_partial_reassembly]
  simp [coDiv, finiteTotalWeight]

/-- Every nonempty retained layer contains the upper slot of its own prime cut. -/
theorem boundary_mem {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (i : Fin (r+1)) : ⌊h i⌋₊ ∈ bands h v i := by
  have top {l u : ℕ} (he : (Finset.Ioc l u).Nonempty) : u ∈ Finset.Ioc l u := by
    obtain ⟨k, hk⟩ := he
    have hku := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr ⟨hku.1.trans_le hku.2, le_rfl⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [bands] using top (show (Finset.Ioc ⌈v⌉₊ ⌊h (Fin.last r)⌋₊).Nonempty by
      simpa [bands] using hne (Fin.last r))
  · simpa [bands] using top (show (Finset.Ioc ⌊h j.succ⌋₊ ⌊h j.castSucc⌋₊).Nonempty by
      simpa [bands] using hne j.castSucc)

/-- The original numerator and the integer endpoint recover the served prime,
even though the ambient coordinates of the projector are quotient integers. -/
theorem decode_boundary (a : ℝ) (p : ℕ) (hp : 0 < p) (ha : (p:ℝ)*((p:ℝ)+1) ≤ a) :
    ⌊a/(⌊a/(p:ℝ)⌋₊:ℝ)⌋₊ = p := by
  have pos : (0:ℝ) < p := by exact_mod_cast hp
  have one : 0 < (p:ℝ)+1 := by positivity
  have a0 : 0 ≤ a := le_trans (by positivity) ha
  let k : ℕ := ⌊a/(p:ℝ)⌋₊
  have lo : (k:ℝ) ≤ a/p := Nat.floor_le (div_nonneg a0 pos.le)
  have hi : a/p < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have gap : a/((p:ℝ)+1)+1 ≤ a/p := by
    apply (le_div_iff₀ pos).2
    rw [add_mul, div_mul_eq_mul_div, ← le_sub_iff_add_le, div_le_iff₀ one]
    nlinarith only [ha]
  have right : a/((p:ℝ)+1) < k := by linarith
  have kpos : (0:ℝ) < k := lt_of_le_of_lt (div_nonneg a0 one.le) right
  apply Nat.floor_eq_iff (div_nonneg a0 kpos.le) |>.2
  constructor
  · exact (le_div_iff₀ kpos).2 (by simpa [mul_comm] using (le_div_iff₀ pos).1 lo)
  · exact (div_lt_iff₀ kpos).2 (by simpa [mul_comm] using (div_lt_iff₀ one).1 right)

/-- Sample the observable once at the actual upper endpoint of each layer. -/
def boundaryObs {r : ℕ} (a h : Fin (r+1) → ℝ) (v : ℝ) (f : ℕ → ℝ)
    (z : Address (bands h v)) : ℝ :=
  if z.2.val = ⌊h z.1⌋₊ then f ⌊a z.1/(z.2.val:ℝ)⌋₊ else 0

/-- Original integral sections, the prime logarithm, and a separately oriented
prime test embedded into the same integer slot space. -/
def observed {r : ℕ} (a h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) (f : ℕ → ℝ) :
    Matrix (↥(Finset.Iic ⌊h 0⌋₊)) (Fin r ⊕ Bool) ℝ :=
  slotInclusion (physicalAddress h v hne) * fun z =>
    Sum.elim (fun j => (columns (bands h v) D z j : ℝ))
      (fun b => if b then boundaryObs a h v f z else boundaryObs a h v (fun p => Real.log p) z)

theorem observed_star {r : ℕ} (a h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) (f : ℕ → ℝ)
    (z : ↥(Finset.Iic ⌊h 0⌋₊)) (i : Fin r) :
    observed a h v hne D f z (.inl i) = physicalColumns h v hne D z i := rfl

/-- An off-diagonal entry of the augmented Co–Div matrix equals the signed
prime read on this translate. No logarithm or sign is squared. -/
theorem boundary_pair {r : ℕ} (a : Fin (r+1) → ℝ) (p : Fin (r+1) → ℕ)
    (hp : ∀ i, 0 < p i) (ha : ∀ i, (p i:ℝ)*((p i:ℝ)+1) ≤ a i)
    (v : ℝ) (hne : ∀ i, (bands (fun j => a j/(p j:ℝ)) v i).Nonempty)
    (D : Fin (r+1) → ℕ) (f : ℕ → ℝ) :
    coDiv (observed a (fun j => a j/(p j:ℝ)) v hne D f) (.inr false) (.inr true) =
      ∑ i, Real.log (p i)*f (p i) := by
  rw [observed, insert_gram, coDiv_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Sum.elim_inr, Bool.false_eq_true, if_false, if_true]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  let h := fun j => a j/(p j:ℝ)
  let k : ↥(bands h v i) := ⟨⌊h i⌋₊, boundary_mem h v hne i⟩
  change (∑ z : ↥(bands h v i), boundaryObs a h v (fun l => Real.log l) ⟨i,z⟩ *
    boundaryObs a h v f ⟨i,z⟩) = _
  rw [Finset.sum_eq_single k]
  · simp [boundaryObs, k, h, decode_boundary _ _ (hp i) (ha i)]
  · intro z _ hz
    have ne : z.val ≠ ⌊h i⌋₊ := fun eq => hz (Subtype.ext eq)
    simp [boundaryObs, ne]
  · simp

end WheelNNS
end RHLean.Analysis.AlpogeThin.SlotProjector
