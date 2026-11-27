import «research.NativeWheelIntervalRecovery»
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
  calc
    _ = finiteTargetSecondMoment Finset.univ (fun _ => 1) (fun z i => X z i) 0 :=
      (finiteTargetSecondMoment_eq_partial_reassembly Finset.univ (fun _ => 1) (fun z i => X z i) 0).symm
    _ = _ := by ext i j; simp [finiteTargetSecondMoment,Matrix.mul_apply]

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

/-- Entrywise Co–Div equals the independently measured wheel metric for
the full arithmetic mask, including its off-diagonal root pairings. -/
theorem physical_metric {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) :
    coDiv (physicalColumns h v hne D) =
      MeasuredCut.gram (fun i => (((bands h v i).card * D i^2 : ℕ):ℝ)) := by
  rw [physicalColumns, insert_gram, coDiv_eq, ← columns_gram (bands h v) D,
    RingHom.mapMatrix_apply, Matrix.map_mul]
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
  rw [first_moment, first_moment, coDiv_eq]
  simp [finiteTargetSecondMoment, finiteTotalWeight, Matrix.mul_apply]

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
  refine (Nat.floor_eq_iff (div_nonneg a0 kpos.le)).2 ⟨?_, ?_⟩
  · exact (le_div_iff₀ kpos).2 (by simpa [mul_comm] using (le_div_iff₀ pos).1 lo)
  · exact (div_lt_iff₀ kpos).2 (by simpa [mul_comm] using (div_lt_iff₀ one).1 right)

/-- Sample the observable once at the actual upper endpoint of each layer. -/
def boundaryObs {r : ℕ} (a h : Fin (r+1) → ℝ) (v : ℝ) (f : ℕ → ℝ)
    (z : Address (bands h v)) : ℝ :=
  if z.2.val = ⌊h z.1⌋₊ then f ⌊a z.1/(z.2.val:ℝ)⌋₊ else 0

private def layerObservations {r : ℕ} (a h : Fin (r+1) → ℝ) (v : ℝ)
    (D : Fin (r+1) → ℕ) (f : ℕ → ℝ) : Matrix (Address (bands h v)) (Fin r ⊕ Bool) ℝ :=
  fun z => Sum.elim (fun j => (columns (bands h v) D z j : ℝ))
    (fun b => if b then boundaryObs a h v f z else boundaryObs a h v (fun p => Real.log p) z)

/-- Original integral sections, the prime logarithm, and a separately oriented
prime test embedded into the same integer slot space. -/
def observed {r : ℕ} (a h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (D : Fin (r+1) → ℕ) (f : ℕ → ℝ) :
    Matrix (↥(Finset.Iic ⌊h 0⌋₊)) (Fin r ⊕ Bool) ℝ :=
  slotInclusion (physicalAddress h v hne) * layerObservations a h v D f

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
  change (∑ z : Address (bands (fun j => a j/(p j:ℝ)) v),
    boundaryObs a _ v (fun l => Real.log l) z * boundaryObs a _ v f z) = _
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


/-- All original lifts and translates on the actual high-thick prime family.
The same constructed slot population works for every signed prime test. -/
theorem highThick_reads (e q d n : ℕ) [Fact q.Prime] [Fact d.Prime] (x b : ℝ)
    (tops T : Finset (AlpogeNativeDyadicH e)) (a : AlpogeNativeDyadicH e → ℝ)
    (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hx : 1 ≤ x) (hb : 4*x^2 ≤ b)
    (ha : ∀ t ∈ tops, a t ∈ Set.Icc (x*b) ((x+1)*b))
    (hw : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u j ρ ∈ Set.Icc b (b*(1+1/x))) :
    let P := highThickPrimes e q d x
    let g := fun p => ((alpogeNativeHostData e q d).frob p).2
    let V := occupied tops P g
    let p := primeAt tops P g
    let num := fun (s : ↥V) i => a (s.val-g (p s i))
    let cut := fun (s : ↥V) i => num s i/(p s i:ℝ)
    let c := ⌊Real.sqrt x⌋₊
    let D := fun (s : ↥V) i => (p s i)^(⌊(c:ℝ)*x⌋₊/(p s i)-c)
    let width := fun (s : ↥V) (j : ↥(siteRows T n s.val)) => w j.val.1 j.val.2 ((0,1),s.val)
    ∃ hS : ∀ s j i, (bands (cut s) (width s j) i).Nonempty, ∀ f : ℕ → ℝ,
      (∑ s : ↥V, ∑ j : ↥(siteRows T n s.val),
        coDiv (observed (num s) (cut s) (width s j) (hS s j) (D s) f) (.inr false) (.inr true)) =
        ((T.card*n:ℕ):ℝ)*(tops.card*(∑ l ∈ P, Real.log l*f l)) := by
  classical
  intro P g V p num cut c D width
  have info := highThick_primeAt e q d x tops
  have height s i := ha _ (info s i).2.2.2.2
  have hbpos : 0 ≤ b := le_trans (by positivity) hb
  have bx : x ≤ b := by nlinarith only [hb, hx, sq_nonneg (x-1)]
  have hS (s : ↥V) (j : ↥(siteRows T n s.val)) (i) : (bands (cut s) (width s j) i).Nonempty := by
    have wid := hw j.val.1 j.val.2 _ ((siteRows_mem_iff T n s.val j.val).1 j.property)
    exact (firstPrime_slots e q d _ (p s) (fun i => s.val-g (p s i)) a (w j.val.1 j.val.2)
      x b hx hb (fun i => (info s i).1) (p s).strictMono (fun i => (info s i).2.2.1)
      (height s) _ (fun i => (info s i).2.2.2.1) (hbpos.trans wid.1) wid.2 i).2.1
  refine ⟨hS, fun f => ?_⟩
  have big (s : ↥V) (i) : (p s i:ℝ)*((p s i:ℝ)+1) ≤ num s i := by
    have bound : (p s i:ℝ)+1 ≤ x := (info s i).2.2.1
    exact (mul_le_mul (by linarith : (p s i:ℝ) ≤ x) (bound.trans bx) (by positivity)
      (zero_le_one.trans hx)).trans (height s i).1
  have row (s : ↥V) (j : ↥(siteRows T n s.val)) := boundary_pair (num s) (p s)
    (fun i => (info s i).1.pos) (big s) (width s j) (hS s j) (D s) f
  simp_rw [show ∀ s j, coDiv (observed (num s) (cut s) (width s j) (hS s j) (D s) f)
    (.inr false) (.inr true) = ∑ i, Real.log (p s i)*f (p s i) from row]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, siteRows_card, nsmul_eq_mul,
    ← Finset.mul_sum]
  exact congrArg (fun z : ℝ => ((T.card*n:ℕ):ℝ)*z) (primeAt_sum tops P g (fun l => Real.log l*f l))

/-- Use the same physical test at every translate to recover the part of a
moving interval served by the wheel. The remaining prime log mass and the
full interval length are explicit, including both endpoint conventions. -/
theorem moving_balance (P : Finset ℕ) (M : ℕ) (a v : ℝ) :
    let R := PrincipalCofactor.retainedFirstPrimes M
    let hit := fun p : ℕ => p ∈ R ∧ a/(v+1) ≤ (p:ℝ) ∧ (p:ℝ) < a/v
    PrincipalCofactor.movingExcess M a v =
      (∑ p ∈ P, Real.log p * (if hit p then 1 else 0)) +
      (∑ p ∈ (R.filter (fun p : ℕ => a/(v+1) ≤ (p:ℝ) ∧ (p:ℝ) < a/v)) \ P, Real.log p) -
      (a/v-a/(v+1)) := by
  classical
  intro R hit
  let U := R.filter (fun p : ℕ => a/(v+1) ≤ (p:ℝ) ∧ (p:ℝ) < a/v)
  have eq : (∑ p ∈ P, Real.log p*(if hit p then 1 else 0)) = ∑ p ∈ U ∩ P, Real.log p := by
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : hit p
    · have mem : p ∈ U := Finset.mem_filter.mpr h
      simp [h,mem]
    · have mem : p ∉ U := fun hp => h (Finset.mem_filter.mp hp)
      simp [h,mem]
  have rest : U \ (U ∩ P) = U \ P := by ext p; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have all := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) (show U ∩ P ⊆ U from Finset.inter_subset_left)
  rw [rest] at all
  change (∑ p ∈ U, Real.log p)-(a/v-a/(v+1)) = _
  rw [eq]
  change (∑ p ∈ U, Real.log p) - _ =
    ((∑ p ∈ U ∩ P, Real.log p) + ∑ p ∈ U \ P, Real.log p) - _
  linarith only [all]

/-- Partition the original parent interval at the upper slot of an admitted
prime. Both children retain their actual quotient coordinates. -/
abbrev SplitSlots (l c u : ℕ) := (↥(Finset.Ioc l c)) ⊕ (↥(Finset.Ioc c u))

def splitAddress (l c u : ℕ) (hl : l ≤ c) (hu : c ≤ u) : SplitSlots l c u ≃ ↥(Finset.Ioc l u) where
  toFun z := match z with
    | .inl k => ⟨k.val, Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp k.property).1,
      (Finset.mem_Ioc.mp k.property).2.trans hu⟩⟩
    | .inr k => ⟨k.val, Finset.mem_Ioc.mpr ⟨hl.trans_lt (Finset.mem_Ioc.mp k.property).1,
      (Finset.mem_Ioc.mp k.property).2⟩⟩
  invFun k := if h : k.val ≤ c then .inl ⟨k.val, Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp k.property).1,h⟩⟩
    else .inr ⟨k.val, Finset.mem_Ioc.mpr ⟨lt_of_not_ge h,(Finset.mem_Ioc.mp k.property).2⟩⟩
  left_inv z := by
    cases z with
    | inl k => simp [(Finset.mem_Ioc.mp k.property).2]
    | inr k => simp [not_le.mpr (Finset.mem_Ioc.mp k.property).1]
  right_inv k := by by_cases edge : k.val ≤ c <;> simp [edge]

/-- The anchor is constant on the parent. The recovered jump is multiplied by
the original Euler power on the upper child. -/
def splitColumns (l c u d : ℕ) : Matrix (SplitSlots l c u) Bool ℝ :=
  fun z b => if b then z.elim (fun _ => 0) (fun _ => (d:ℝ)) else 1

private theorem split_entries (l c u d : ℕ) :
    let G := coDiv (splitColumns l c u d)
    let L : ℝ := (c-l:ℕ)
    let R : ℝ := (u-c:ℕ)
    G false false = L+R ∧ G false true = R*d ∧ G true true = R*(d:ℝ)^2 := by
  intro G L R
  simp [G, L, R, coDiv_eq, Matrix.mul_apply, splitColumns, Fintype.sum_sum_type, pow_two]

/-- Complete one-admission price on a changing mask. The determinant is in the
parent counting metric. The Schur pivot removes the retained anchor only over
the reals. The integral index is computed before any such orthogonalization. -/
theorem admission_price (a : ℝ) (p e l u : ℕ) (hp : p.Prime)
    (hl : l < ⌊a/(p:ℝ)⌋₊) (hu : ⌊a/(p:ℝ)⌋₊ < u) :
    let c := ⌊a/(p:ℝ)⌋₊
    let d := p^e
    let L : ℝ := (c-l:ℕ)
    let R : ℝ := (u-c:ℕ)
    let G := coDiv (slotInclusion (splitAddress l c u hl.le hu.le).toEmbedding * splitColumns l c u d)
    G false true = R*d ∧
    G true true - G false true^2/G false false = (d:ℝ)^2*L*R/(L+R) ∧
    G false false*G true true - G false true^2 = (d:ℝ)^2*L*R ∧
    (anchoredRecovery (fun _ : Fin 1 => (d:ℤ))).toAddMonoidHom.range.index = d := by
  intro c d L R G
  have left : 0 < L := by dsimp [L,c]; exact_mod_cast Nat.sub_pos_of_lt hl
  have right : 0 < R := by dsimp [R,c]; exact_mod_cast Nat.sub_pos_of_lt hu
  have pos := add_pos left right
  have ident : G = coDiv (splitColumns l c u d) := insert_gram _ _
  obtain ⟨h0,h1,h2⟩ := split_entries l c u d
  change (coDiv (splitColumns l c u d)) false false = L+R at h0
  change (coDiv (splitColumns l c u d)) false true = R*d at h1
  change (coDiv (splitColumns l c u d)) true true = R*(d:ℝ)^2 at h2
  rw [ident, h0, h1, h2]
  refine ⟨rfl, ?_, by ring, ?_⟩
  · field_simp [pos.ne']; ring
  · simpa using (anchoredRecovery_index (fun _ : Fin 1 => d) (fun _ => pow_pos hp.pos e)).2


/-- At zero target the bare star has a uniform sign across each slot row.
Its two divergent partial-moment matrices vanish even when a signed prime
read on precisely these slots is nonzero. -/
theorem star_divergent_zero {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ) :
    let X := (columns S D).map (Int.castRingHom ℝ)
    finiteDLPM Finset.univ (fun _ => 1) X 0 = 0 ∧ finiteDUPM Finset.univ (fun _ => 1) X 0 = 0 := by
  intro X
  have signs (z : Address S) : (∀ j, X z j ≤ 0) ∨ (∀ j, 0 ≤ X z j) := by
    by_cases root : z.1 = 0
    · left
      intro j
      change ((starColumn D j z.1 z.2.val:ℤ):ℝ) ≤ 0
      simp [starColumn,root,(Fin.succ_ne_zero j).symm]
    · right
      intro j
      change 0 ≤ ((starColumn D j z.1 z.2.val:ℤ):ℝ)
      by_cases leaf : z.1 = j.succ <;> simp [starColumn,root,leaf]
  have upper {z : ℝ} (hz : z ≤ 0) : partialUpper z 0 = 0 := by
    unfold partialUpper
    split_ifs <;> linarith
  have lower {z : ℝ} (hz : 0 ≤ z) : partialLower z 0 = 0 := by simp [partialLower, not_lt.mpr hz]
  constructor
  · ext i j
    apply Finset.sum_eq_zero
    intro z _
    rcases signs z with h|h
    · simp [upper (h j)]
    · simp [lower (h i)]
  · ext i j
    apply Finset.sum_eq_zero
    intro z _
    rcases signs z with h|h
    · simp [upper (h i)]
    · simp [lower (h j)]

/-- Dot products with every layer-constant section characterize the projection
of the endpoint observation. No prime mass is inserted at the other slots. -/
theorem boundary_against_layers {r : ℕ} (a : Fin (r+1) → ℝ) (p : Fin (r+1) → ℕ)
    (hp : ∀ i, 0 < p i) (ha : ∀ i, (p i:ℝ)*((p i:ℝ)+1) ≤ a i)
    (v : ℝ) (hne : ∀ i, (bands (fun j => a j/(p j:ℝ)) v i).Nonempty)
    (f : ℕ → ℝ) (b : Fin (r+1) → ℝ) :
    let h := fun i => a i/(p i:ℝ)
    (∑ z : Address (bands h v), boundaryObs a h v f z*b z.1) = ∑ i, f (p i)*b i := by
  intro h
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  let k : ↥(bands h v i) := ⟨⌊h i⌋₊, boundary_mem h v hne i⟩
  rw [Finset.sum_eq_single k]
  · simp [boundaryObs,k,h,decode_boundary _ _ (hp i) (ha i)]
  · intro z _ hz
    have ne : z.val ≠ ⌊h i⌋₊ := fun eq => hz (Subtype.ext eq)
    simp [boundaryObs,ne]
  · simp

/-- Projection onto the entire layer-constant space, which contains the
stars and the retained anchor, averages the sparse signed read over each
original layer. Pairing with any layer section leaves the read unchanged. -/
theorem boundary_projection {r : ℕ} (a : Fin (r+1) → ℝ) (p : Fin (r+1) → ℕ)
    (hp : ∀ i, 0 < p i) (ha : ∀ i, (p i:ℝ)*((p i:ℝ)+1) ≤ a i)
    (v : ℝ) (hne : ∀ i, (bands (fun j => a j/(p j:ℝ)) v i).Nonempty)
    (f : ℕ → ℝ) (b : Fin (r+1) → ℝ) :
    let h := fun i => a i/(p i:ℝ)
    let S := bands h v
    (∑ z : Address S, (boundaryObs a h v f z - f (p z.1)/(S z.1).card)*b z.1) = 0 := by
  intro h S
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [boundary_against_layers a p hp ha v hne f b, Fintype.sum_sigma]
  apply sub_eq_zero.mpr
  refine Finset.sum_congr rfl fun i _ => ?_
  have pos : ((S i).card:ℝ) ≠ 0 := by exact_mod_cast (hne i).card_pos.ne'
  simp [pos, mul_comm, mul_left_comm, div_eq_mul_inv]

/-- If both the logarithm and the contrast use an endpoint, the anchored
layer projection sees at most one slot's fraction of each nonnegative
crossing. With a layer-constant signed test the full read survives, as
computed in `boundary_against_layers`. -/
theorem sparse_projection_price {r : ℕ} (a : Fin (r+1) → ℝ) (p : Fin (r+1) → ℕ)
    (hp : ∀ i, 0 < p i) (ha : ∀ i, (p i:ℝ)*((p i:ℝ)+1) ≤ a i)
    (v : ℝ) (hne : ∀ i, (bands (fun j => a j/(p j:ℝ)) v i).Nonempty)
    (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f (p i)) {m : ℝ} (hm : 0 < m)
    (hmS : ∀ i, m ≤ ((bands (fun j => a j/(p j:ℝ)) v i).card:ℝ)) :
    let h := fun i => a i/(p i:ℝ)
    let S := bands h v
    (∑ z : Address S, boundaryObs a h v (fun l => Real.log l) z*(f (p z.1)/(S z.1).card)) ≤
      (∑ i, Real.log (p i)*f (p i))/m := by
  intro h S
  rw [boundary_against_layers a p hp ha v hne (fun l => Real.log l) (fun i => f (p i)/(S i).card),
    Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_left (mul_nonneg (Real.log_natCast_nonneg _) (hf i)) hm (hmS i)

/-- With that single multiplier, each original clipped log-prime interval is
a pairing against an actual integral image section on the same quotient slots. -/
theorem broad_physical_read {r : ℕ} (p : Fin (r+1) → ℕ) (num : Fin (r+1) → ℝ)
    (hp : ∀ i, (p i).Prime) (hn : ∀ i, (p i:ℝ)*((p i:ℝ)+1) ≤ num i)
    (width : ℝ) (hS : ∀ i, (bands (fun j => num j/(p j:ℝ)) width i).Nonempty)
    (d : Fin r → ℕ) (M K : ℕ) (s : ℝ) (m : ℕ) (hm : broadClearing p d M K s ∣ m) :
    let h := fun i => num i/(p i:ℝ)
    let a := PrincipalCofactor.evenEndpoint M
    let v := fun k => PrincipalCofactor.oddCofactor k+s
    ∃ A : ℕ → Fin (r+1) → ℤ, ∀ k ∈ Finset.Ico 1 K,
      (∑ z : Address (bands h width), boundaryObs num h width (fun l => Real.log l) z *
        ((onSlots (bands h width) (anchoredRecovery (fun j => (d j:ℤ)) (A k)) z:ℤ):ℝ)) =
        (m:ℝ)*(∑ i, Real.log (p i) * (if p i ∈ PrincipalCofactor.retainedFirstPrimes M ∧
          a/(v k+1) ≤ (p i:ℝ) ∧ (p i:ℝ) < a/v k then 1 else 0)) := by
  intro h a v
  obtain ⟨A,recov⟩ := broad_recovered p d M K s m hm
  refine ⟨A, fun k hk => ?_⟩
  change (∑ z : Address (bands h width), boundaryObs num h width (fun l => Real.log l) z *
    (((anchoredRecovery (fun j => (d j:ℤ)) (A k)) z.1:ℤ):ℝ)) = _
  rw [boundary_against_layers num p (fun i => (hp i).pos) hn width hS (fun l => Real.log l)
    (fun i => (((anchoredRecovery (fun j => (d j:ℤ)) (A k)) i:ℤ):ℝ)),recov k hk,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change Real.log (p i) * (((m:ℤ)*intervalTest p (lowerCut M a (v k)) (upperCut M a (v k)) i:ℤ):ℝ) = _
  simp only [Int.cast_mul,Int.cast_natCast,intervalTest,clipped_hit M (p i) (hp i)]
  split_ifs <;> push_cast <;> ring

/-- One collection of integral preimages and one denominator realize the
physical log-prime reads of every broad cell at every ancestor on the
original wheel. The underlying prime powers do not change with the ancestor. -/
theorem history_physical_read {r : ℕ} (p : Fin (r+1) → ℕ) (num : Fin (r+1) → ℝ)
    (hp : ∀ i, (p i).Prime) (hn : ∀ i, (p i:ℝ)*((p i:ℝ)+1) ≤ num i)
    (width : ℝ) (hS : ∀ i, (bands (fun j => num j/(p j:ℝ)) width i).Nonempty)
    (d : Fin r → ℕ) (N : ℕ) (x s : ℝ) :
    let h := fun i => num i/(p i:ℝ)
    let M := fun j : ℕ => N/2^j
    let a := fun j => PrincipalCofactor.evenEndpoint (M j)
    let K := fun j => ⌈Real.sqrt (a j/Real.sqrt x)⌉₊
    let v := fun k => PrincipalCofactor.oddCofactor k+s
    let m := historyClearing p d x s N
    ∃ A : ℕ → ℕ → Fin (r+1) → ℤ, ∀ j, 16 ≤ M j → ∀ k ∈ Finset.Ico 1 (K j),
      (∑ z : Address (bands h width), boundaryObs num h width (fun l => Real.log l) z *
        ((onSlots (bands h width) (anchoredRecovery (fun i => (d i:ℤ)) (A j k)) z:ℤ):ℝ)) =
        (m:ℝ)*(∑ i, Real.log (p i)*(if p i ∈ PrincipalCofactor.retainedFirstPrimes (M j) ∧
          a j/(v k+1) ≤ (p i:ℝ) ∧ (p i:ℝ) < a j/v k then 1 else 0)) := by
  classical
  intro h M a K v m
  have read (j : ℕ) (hj : 16 ≤ M j) := broad_physical_read p num hp hn width hS d (M j) (K j) s m
    (ancestor_dvd_history p d x s j N hj)
  exact ⟨fun j => if hj : 16 ≤ M j then (read j hj).choose else 0,
    fun j hj => by simpa only [dite_eq_left hj] using (read j hj).choose_spec⟩

/-- Use the Riesz vector of the measured wheel normal as principal mode.
The logarithm is sampled once on a layer, and the signed contrast is constant
on that layer. This gives its exact target-independent residual against an
affine interval length, with both principal readings present. -/
theorem signed_normal_balance {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D p : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) (f : ℕ → ℝ) (length : ℝ) (target : Bool → ℝ) :
    let q := fun i => (wheelNormal D i:ℝ)
    let n := fun i => ((S i).card:ℝ)
    let w := fun i => (q i)^2/n i
    let X := fun i (col : Bool) => if col then n i*f (p i)/q i else Real.log (p i)/q i
    let E := dualEnergy S D
    (∑ i, Real.log (p i)*f (p i))-length =
      finiteTargetScaledSchur Finset.univ w X target false true/E +
      ((∑ i, q i*Real.log (p i)/n i)*(∑ i, q i*f (p i)))/E-length := by
  intro q n w X E
  have q0 (i) : q i ≠ 0 := by
    dsimp [q,wheelNormal]
    exact_mod_cast (Finset.prod_pos (fun j _ => hD j) : 0 < ∏ j ∈ Finset.univ.erase i, D j).ne'
  have n0 (i) : n i ≠ 0 := by dsimp [n]; exact_mod_cast (hS i).card_pos.ne'
  have energy : finiteTotalWeight Finset.univ w = E := rfl
  have left : finiteTargetFirstMoment Finset.univ w X 0 false = ∑ i, q i*Real.log (p i)/n i := by
    apply Finset.sum_congr rfl
    intro i _
    change w i*(Real.log (p i)/q i-0)=_
    dsimp only [w]
    field_simp [q0 i,n0 i]; ring
  have right : finiteTargetFirstMoment Finset.univ w X 0 true = ∑ i, q i*f (p i) := by
    apply Finset.sum_congr rfl
    intro i _
    change w i*(n i*f (p i)/q i-0)=_
    dsimp only [w]
    field_simp [q0 i,n0 i]; ring
  have pair : finiteTargetSecondMoment Finset.univ w X 0 false true = ∑ i, Real.log (p i)*f (p i) := by
    apply Finset.sum_congr rfl
    intro i _
    change w i*(Real.log (p i)/q i-0)*(n i*f (p i)/q i-0)=_
    dsimp only [w]
    field_simp [q0 i,n0 i]; ring
  have positive : 0 < E := dualEnergy_pos S D hS hD
  rw [finiteTargetScaledSchur_target_invariant _ _ X 0 target]
  change _ = (finiteTotalWeight _ w*finiteTargetSecondMoment _ w X 0 false true -
    finiteTargetFirstMoment _ w X 0 false*finiteTargetFirstMoment _ w X 0 true)/E+_-length
  rw [energy,left,right,pair]
  field_simp [positive.ne']; ring

/-- Marginal volume of a real Euler admission on a block which already has its
original depths D. In the independently measured layer metric, replacing the
cardinality of layer i by its product with D_i squared counts exactly the
old Gram. This comparison works even for a singleton block. -/
theorem marginal_volume {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D F : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) (hF : ∀ i, 0 < F i)
    (x : ℝ) (hx : 0 < x) (cap : ∀ i, (F i:ℝ) ≤ x) :
    (∑ i, Real.log (F i:ℝ)) -
      (logVolume S (fun i => D i*F i)-logVolume S D) ∈ Set.Icc 0 (Real.log x) := by
  let s := fun i => (S i).card * D i^2
  let b := fun i => s i*(F i)^2
  have positive i : 0 < s i := Nat.mul_pos (hS i).card_pos (pow_pos (hD i) _)
  have bp i : 0 < b i := Nat.mul_pos (positive i) (pow_pos (hF i) _)
  have omitPos (g : Fin (r+1) → ℕ) (hg : ∀ i, 0 < g i) (j : Fin (r+1)) :
      0 < ∏ i ∈ Finset.univ.erase j, g i := Finset.prod_pos fun i _ => hg i
  have mp (g : Fin (r+1) → ℕ) (hg : ∀ i, 0 < g i) : 0 < (mass g:ℝ) := by
    exact_mod_cast (Finset.sum_pos (fun i _ => omitPos g hg i) Finset.univ_nonempty)
  let P := ∏ i, (F i:ℝ)
  have pp : 0 < P := Finset.prod_pos fun i _ => by exact_mod_cast hF i
  have bounds (j : Fin (r+1)) :
      (∏ i ∈ Finset.univ.erase j, (b i:ℝ)) ≤ P^2*(∏ i ∈ Finset.univ.erase j, (s i:ℝ)) ∧
      P^2*(∏ i ∈ Finset.univ.erase j, (s i:ℝ)) ≤ x^2*(∏ i ∈ Finset.univ.erase j, (b i:ℝ)) := by
    let z := ∏ i ∈ Finset.univ.erase j, (b i:ℝ)
    have id : P^2*(∏ i ∈ Finset.univ.erase j, (s i:ℝ)) = z*(F j:ℝ)^2 := by
      dsimp only [P,z,b]
      simp only [Nat.cast_mul,Nat.cast_pow,Finset.prod_mul_distrib,Finset.prod_pow]
      rw [← Finset.prod_erase_mul Finset.univ (fun i => (F i:ℝ)) (Finset.mem_univ j)]
      ring
    have zp : 0 ≤ z := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    have one : (1:ℝ) ≤ F j := by exact_mod_cast hF j
    have sq : (1:ℝ) ≤ (F j:ℝ)^2 := by nlinarith only [one,sq_nonneg ((F j:ℝ)-1)]
    rw [id]
    exact ⟨le_mul_of_one_le_right zp sq,(mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (cap j) 2) zp).trans_eq (mul_comm _ _)⟩
  have lo : (mass b:ℝ) ≤ P^2*(mass s:ℝ) := by
    simp only [mass,Nat.cast_sum,Nat.cast_prod,Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (bounds j).1
  have hi : P^2*(mass s:ℝ) ≤ x^2*(mass b:ℝ) := by
    simp only [mass,Nat.cast_sum,Nat.cast_prod,Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => (bounds j).2
  have l := Real.log_le_log (mp b bp) lo
  have u := Real.log_le_log (mul_pos (sq_pos_of_pos pp) (mp s positive)) hi
  rw [Real.log_mul (sq_pos_of_pos pp).ne' (mp s positive).ne',Real.log_pow] at l u
  rw [Real.log_mul (sq_pos_of_pos hx).ne' (mp b bp).ne',Real.log_pow] at u
  have sum : Real.log P = ∑ i, Real.log (F i:ℝ) := Real.log_prod (fun i _ => by exact_mod_cast (hF i).ne')
  rw [sum] at l u
  norm_num1 at l u
  have id : (fun i => (S i).card*(D i*F i)^2)=b := by funext i; dsimp [b,s]; ring
  dsimp only [logVolume]
  rw [columns_det S (fun i => D i*F i) hS (fun i => Nat.mul_pos (hD i) (hF i)),
    columns_det S D hS hD,id]
  simp only [Int.cast_natCast]
  change _ - ((Real.log (mass b:ℝ)-_)/2-(Real.log (mass s:ℝ)-_)/2) ∈ _
  exact ⟨by linarith only [l],by linarith only [u]⟩

/-- One extra prime power precisely on the original recovered interval
test. The principal log-boundary read lies above this marginal volume;
its possible excess is at most the log of the largest allowed prime. -/
theorem interval_volume {r : ℕ} (p : Fin (r+1) → ℕ) (num : Fin (r+1) → ℝ)
    (hp : ∀ i, (p i).Prime) (ha : ∀ i, (p i:ℝ)*((p i:ℝ)+1) ≤ num i)
    (width : ℝ) (hS : ∀ i, (bands (fun j => num j/(p j:ℝ)) width i).Nonempty)
    (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i) (L U x : ℝ) (hx : 1 ≤ x) (hpx : ∀ i, (p i:ℝ) ≤ x) :
    let h := fun i => num i/(p i:ℝ)
    let S := bands h width
    let F := fun i => if L ≤ (p i:ℝ) ∧ (p i:ℝ) < U then p i else 1
    (∑ z : Address S, boundaryObs num h width (fun l => Real.log l) z*(intervalTest p L U z.1:ℝ)) -
      (logVolume S (fun i => D i*F i)-logVolume S D) ∈ Set.Icc 0 (Real.log x) := by
  intro h S F
  rw [boundary_against_layers num p (fun i => (hp i).pos) ha width hS (fun l => Real.log l)
    (fun i => (intervalTest p L U i:ℝ))]
  have id i : Real.log (p i)*(intervalTest p L U i:ℝ)=Real.log (F i:ℝ) := by
    by_cases hit : L ≤ (p i:ℝ) ∧ (p i:ℝ) < U <;> simp [intervalTest,F,hit]
  simp_rw [id]
  exact marginal_volume S D F hS hD (fun i => by dsimp [F]; split <;> first | exact (hp i).pos | decide)
    x (zero_lt_one.trans_le hx) (fun i => by
      dsimp [F]; split
      · exact hpx i
      · simpa only [Nat.cast_one] using hx)

/-- Block-diagonal sum of marginal wheel covolumes at all occupied sites and
translates. A selected prime is admitted once above its original depth. -/
def translatedMarginal {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
    (tops T : Finset H) (P : Finset ℕ) (g : ℕ → H) (n : ℕ) (a : H → ℝ)
    (width : H × Fin n → H → ℝ) (power : ℕ → ℕ) (hit : ℕ → Prop) [DecidablePred hit] : ℝ :=
  let p := primeAt tops P g
  let h := fun (s : ↥(occupied tops P g)) i => a (s.val-g (p s i))/(p s i:ℝ)
  ∑ s : ↥(occupied tops P g), ∑ j : ↥(siteRows T n s.val),
    (logVolume (bands (h s) (width j.val s.val))
      (fun i => power (p s i)*(if hit (p s i) then p s i else 1)) -
     logVolume (bands (h s) (width j.val s.val)) (fun i => power (p s i)))

/-- Bounds for the very same marginal volume. Its upper comparison comes
from joint determinant divisibility. The lower comparison uses the original
interval length and an independent theta estimate with prescribed relative
precision. The mass outside the measured prime family occurs on both sides. -/
theorem metric_sandwich (e q d n : ℕ) [Fact q.Prime] [Fact d.Prime] (tops T : Finset (AlpogeNativeDyadicH e))
    (a : AlpogeNativeDyadicH e → ℝ)
    (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b δ : ℝ) (hx : 1 ≤ x) (hb : 4*x^2 ≤ b) (hδ : 0 < δ)
    (ht : tops.Nonempty) (hT : T.Nonempty) (hn : 0 < n)
    (ha : ∀ t ∈ tops, a t ∈ Set.Icc (x*b) ((x+1)*b))
    (hw : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u j ρ ∈ Set.Icc b (b*(1+1/x))) :
    let P := highThickPrimes e q d x
    let g := fun p => ((alpogeNativeHostData e q d).frob p).2
    let V := occupied tops P g
    let c := ⌊Real.sqrt x⌋₊
    let power := fun p : ℕ => p^(⌊(c:ℝ)*x⌋₊/p-c)
    let width := fun (j : AlpogeNativeDyadicH e × Fin n) (y : AlpogeNativeDyadicH e) => w j.1 j.2 ((0,1),y)
    let k := ((T.card*n:ℕ):ℝ)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) (v : ℝ), 2 ≤ M → 1 ≤ v →
      let A := PrincipalCofactor.evenEndpoint M
      let I := (PrincipalCofactor.retainedFirstPrimes M).filter (fun l : ℕ => A/(v+1) ≤ (l:ℝ) ∧ (l:ℝ) < A/v)
      let outside := ∑ l ∈ I \ P, Real.log l
      let base := A/v-A/(v+1)
      let measured := translatedMarginal tops T P g n a width power (fun l => l ∈ I)/(k*tops.card)
      let error := 2*(δ*M+C+Real.log 4*Real.sqrt M)
      let cost := ((V.card:ℝ)/tops.card)*Real.log x
      (measured+outside-base ≤ PrincipalCofactor.movingExcess M A v ∧
        PrincipalCofactor.movingExcess M A v ≤ measured+outside-base+cost) ∧
      base-outside-error-cost ≤ measured ∧ measured ≤ base-outside+error := by
  classical
  intro P g V c power width k
  obtain ⟨C,hC,env⟩ := PrincipalCofactor.discrepancy_envelope hδ
  refine ⟨C,hC,fun M v hM hv => ?_⟩
  intro A I outside base measured error cost
  let p := primeAt tops P g
  let cut := fun (y : ↥V) i => a (y.val-g (p y i))/(p y i:ℝ)
  obtain ⟨hS,_⟩ := highThick_reads e q d n x b tops T a w hx hb ha hw
  have info := highThick_primeAt e q d x tops
  let F := fun (y : ↥V) i => if p y i ∈ I then p y i else 1
  let source := ∑ l ∈ P, Real.log l*(if l ∈ I then 1 else 0)
  let raw := translatedMarginal tops T P g n a width power (fun l => l ∈ I)
  let S := fun (y : ↥V) (j : ↥(siteRows T n y.val)) => bands (cut y) (width j.val y.val)
  let loss := fun (y : ↥V) (j : ↥(siteRows T n y.val)) =>
    (∑ i, Real.log (F y i:ℝ)) - (logVolume (S y j) (fun i => power (p y i)*F y i) -
      logVolume (S y j) (fun i => power (p y i)))
  have band (y : ↥V) (j : ↥(siteRows T n y.val)) : loss y j ∈ Set.Icc 0 (Real.log x) := by
    have pos (i) : 0 < F y i := by dsimp [F]; split <;> first | exact (info y i).1.pos | decide
    have cap (i) : (F y i:ℝ) ≤ x := by
      dsimp [F]; split <;> push_cast <;> first | exact hx | linarith only [(info y i).2.2.1]
    exact marginal_volume (S y j) _ (F y) (hS y j) (fun i => pow_pos (info y i).1.pos _) pos x
      (zero_lt_one.trans_le hx) cap
  have fs (y : ↥V) i : Real.log (F y i:ℝ) = Real.log (p y i)*(if p y i ∈ I then 1 else 0) := by
    by_cases hit : p y i ∈ I <;> simp [F,hit]
  have total : (∑ y : ↥V, ∑ j : ↥(siteRows T n y.val), loss y j) = k*(tops.card*source)-raw := by
    simp only [loss,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
      siteRows_card,nsmul_eq_mul,← Finset.mul_sum]
    simp_rw [fs]
    simpa only [raw,translatedMarginal,Finset.sum_sub_distrib] using
      congrArg (fun z : ℝ => k*z-raw) (primeAt_sum tops P g (fun l => Real.log l*(if l ∈ I then 1 else 0)))
  have lower : 0 ≤ k*(tops.card*source)-raw := by
    rw [← total]; exact Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun j _ => (band y j).1
  have upper : k*(tops.card*source)-raw ≤ (V.card:ℝ)*(k*Real.log x) := by
    rw [← total]
    calc
      _ ≤ ∑ y : ↥V, ∑ _j : ↥(siteRows T n y.val), Real.log x :=
        Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun j _ => (band y j).2
      _ = _ := by simp [k,siteRows_card]
  have kt : 0 < k := by change 0 < ((T.card*n:ℕ):ℝ); exact_mod_cast Nat.mul_pos hT.card_pos hn
  have tt : (0:ℝ) < tops.card := by exact_mod_cast ht.card_pos
  have denom := mul_pos kt tt
  have id : source-measured=(k*(tops.card*source)-raw)/(k*tops.card) := by
    change source-raw/(k*tops.card)=_
    field_simp [kt.ne',tt.ne']
  have rati : (V.card:ℝ)*(k*Real.log x)/(k*tops.card)=cost := by
    dsimp [cost]; field_simp [kt.ne',tt.ne']
  have zero : 0 ≤ source-measured := by rw [id]; exact div_nonneg lower denom.le
  have finite : source-measured ≤ cost := by rw [id,← rati]; exact div_le_div_of_nonneg_right upper denom.le
  have compare : PrincipalCofactor.movingExcess M A v = source+outside-base := by
    simpa only [source,outside,base,I,Finset.mem_filter] using moving_balance P M A v
  have posA : 0 ≤ A := by dsimp [A,PrincipalCofactor.evenEndpoint]; positivity
  have approx : |PrincipalCofactor.movingExcess M A v| ≤ error := by
    rw [← PrincipalCofactor.moving_eq M posA (zero_lt_one.trans_le hv)]
    dsimp only [error]
    exact (abs_sub _ _).trans (by linarith only [env M v hM hv,env M (v+1) hM (by linarith)])
  rw [compare] at approx ⊢
  exact ⟨⟨by linarith only [zero],by linarith only [finite]⟩,by linarith only [(abs_le.mp approx).1,finite],
    by linarith only [(abs_le.mp approx).2,zero]⟩

/-- On the actual translated wheel, the complete signed step, including all
odd endpoint readings, is bounded from the history side by the same measured
marginal volumes, the unserved primes and the full affine lengths. One
common shift suffices. Its rounding price is one per dyadic ancestor. -/
theorem measured_history_step (e q d n : ℕ) [Fact q.Prime] [Fact d.Prime] (tops T : Finset (AlpogeNativeDyadicH e))
    (a : AlpogeNativeDyadicH e → ℝ)
    (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b : ℝ) (hx : 1 ≤ x) (hb : 4*x^2 ≤ b)
    (ht : tops.Nonempty) (hT : T.Nonempty) (hn : 0 < n)
    (ha : ∀ t ∈ tops, a t ∈ Set.Icc (x*b) ((x+1)*b))
    (hw : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u j ρ ∈ Set.Icc b (b*(1+1/x)))
    (M K R : ℕ) (hm : 2 ≤ M) :
    let P := highThickPrimes e q d x
    let g := fun l => ((alpogeNativeHostData e q d).frob l).2
    let c := ⌊Real.sqrt x⌋₊
    let power := fun p : ℕ => p^(⌊(c:ℝ)*x⌋₊/p-c)
    let width := fun (j : AlpogeNativeDyadicH e × Fin n) (y : AlpogeNativeDyadicH e) => w j.1 j.2 ((0,1),y)
    let scale := ((T.card*n:ℕ):ℝ)*tops.card
    let A := PrincipalCofactor.evenEndpoint M
    let I := fun v : ℝ => (PrincipalCofactor.retainedFirstPrimes M).filter
      (fun l : ℕ => A/(v+1) ≤ (l:ℝ) ∧ (l:ℝ) < A/v)
    let measured := fun v : ℝ => translatedMarginal tops T P g n a width power (fun l => l ∈ I v)/scale
    let outside := fun v : ℝ => ∑ l ∈ I v \ P, Real.log l
    let base := fun v : ℝ => A/v-A/(v+1)
    ∃ s ∈ Set.Icc (0:ℝ) 1, -(∑ k ∈ Finset.Ico K R, PrincipalCofactor.primePairReading M k) ≤
      1-(∑ k ∈ Finset.Ico K R, (PrincipalCofactor.chord M k + PrincipalCofactor.cellWeight k *
        (measured (PrincipalCofactor.oddCofactor k+s)+outside (PrincipalCofactor.oddCofactor k+s)-
          base (PrincipalCofactor.oddCofactor k+s)))) := by
  intro P g c power width scale A I measured outside base
  obtain ⟨s,hs,shift⟩ := PrincipalCofactor.exists_common_shift_lower M K R hm
  obtain ⟨_,_,all⟩ := metric_sandwich e q d n tops T a w x b 1 hx hb (by norm_num) ht hT hn ha hw
  have per (k : ℕ) : let v := PrincipalCofactor.oddCofactor k+s
      measured v+outside v-base v ≤ PrincipalCofactor.movingExcess M A v := by
    intro v
    have one : 1 ≤ v := by dsimp [v,PrincipalCofactor.oddCofactor]; linarith only [hs.1,Nat.cast_nonneg (α := ℝ) k]
    exact (all M v hm one).1.1
  refine ⟨s,hs,?_⟩
  have bound := Finset.sum_le_sum (s := Finset.Ico K R) (fun (k : ℕ) _ =>
    add_le_add_right (mul_le_mul_of_nonneg_left (per k)
      (by dsimp [PrincipalCofactor.cellWeight,PrincipalCofactor.oddCofactor]; positivity :
        0 ≤ PrincipalCofactor.cellWeight k)) (PrincipalCofactor.chord M k))
  linarith only [bound,shift]

/-- The independent lower comparison at every fine cell together, uniform
in the very shift chosen for the broad cells. It charges the full affine
length, the actual marginal determinant and the omitted primes. -/
theorem fine_metric_lower (e q d n : ℕ) [Fact q.Prime] [Fact d.Prime] (tops T : Finset (AlpogeNativeDyadicH e))
    (a : AlpogeNativeDyadicH e → ℝ)
    (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b : ℝ) (hx : 1 ≤ x) (hb : 4*x^2 ≤ b)
    (ht : tops.Nonempty) (hT : T.Nonempty) (hn : 0 < n)
    (ha : ∀ t ∈ tops, a t ∈ Set.Icc (x*b) ((x+1)*b))
    (hw : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u j ρ ∈ Set.Icc b (b*(1+1/x)))
    (M K R : ℕ) (hm : 2 ≤ M) (one : 1 ≤ K) (kr : K ≤ R) (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    let P := highThickPrimes e q d x
    let g := fun l => ((alpogeNativeHostData e q d).frob l).2
    let c := ⌊Real.sqrt x⌋₊
    let power := fun p : ℕ => p^(⌊(c:ℝ)*x⌋₊/p-c)
    let width := fun (j : AlpogeNativeDyadicH e × Fin n) (y : AlpogeNativeDyadicH e) => w j.1 j.2 ((0,1),y)
    let scale := ((T.card*n:ℕ):ℝ)*tops.card
    let A := PrincipalCofactor.evenEndpoint M
    let I := fun v : ℝ => (PrincipalCofactor.retainedFirstPrimes M).filter
      (fun l : ℕ => A/(v+1) ≤ (l:ℝ) ∧ (l:ℝ) < A/v)
    let measured := fun v : ℝ => translatedMarginal tops T P g n a width power (fun l => l ∈ I v)/scale
    let outside := fun v : ℝ => ∑ l ∈ I v \ P, Real.log l
    let base := fun v : ℝ => A/v-A/(v+1)
    let count := ((occupied tops P g).card:ℝ)/tops.card
    (-(∑ k ∈ Finset.Ico K R, PrincipalCofactor.cellWeight k*
      (measured (PrincipalCofactor.oddCofactor k+s)+outside (PrincipalCofactor.oddCofactor k+s)-
        base (PrincipalCofactor.oddCofactor k+s)))) ≤
      A/(PrincipalCofactor.oddCofactor K)^2+(count*Real.log x)*(1+Real.log R) := by
  intro P g c power width scale A I measured outside base count
  let S := Finset.Ico K R
  let v := fun k => PrincipalCofactor.oddCofactor k+s
  let t := fun k => A/PrincipalCofactor.oddCofactor k
  let cost := count*Real.log x
  let m := fun k => measured (v k)+outside (v k)-base (v k)
  have A0 : 0 ≤ A := by dsimp [A,PrincipalCofactor.evenEndpoint]; positivity
  have cost0 : 0 ≤ cost := mul_nonneg (by dsimp [count]; positivity) (Real.log_nonneg hx)
  have dpos k : 0 < PrincipalCofactor.oddCofactor k := by dsimp [PrincipalCofactor.oddCofactor]; positivity
  have wpos k : 0 ≤ PrincipalCofactor.cellWeight k := by dsimp [PrincipalCofactor.cellWeight,PrincipalCofactor.oddCofactor]; positivity
  obtain ⟨_,_,all⟩ := metric_sandwich e q d n tops T a w x b 1 hx hb (by norm_num) ht hT hn ha hw
  have per (k : ℕ) : -m k ≤ base (v k)+cost := by
    have vk : 1 ≤ v k := by dsimp [v,PrincipalCofactor.oddCofactor]; linarith only [hs.1,Nat.cast_nonneg (α := ℝ) k]
    have earned : PrincipalCofactor.movingExcess M A (v k) ≤ m k+cost := (all M (v k) hm vk).1.2
    have mass : 0 ≤ ∑ l ∈ I (v k), Real.log (l:ℝ) := Finset.sum_nonneg fun l _ => Real.log_natCast_nonneg l
    change (∑ l ∈ I (v k), Real.log (l:ℝ))-base (v k) ≤ m k+cost at earned
    linarith only [earned,mass]
  have edge k : base (v k) ≤ t k-t (k+1) := by
    have left : PrincipalCofactor.oddCofactor k ≤ v k := le_add_of_nonneg_right hs.1
    have right : v k+1 ≤ PrincipalCofactor.oddCofactor (k+1) := by
      dsimp [v,PrincipalCofactor.oddCofactor]; push_cast; linarith only [hs.2]
    exact sub_le_sub (div_le_div_of_nonneg_left A0 (dpos k) left)
      (div_le_div_of_nonneg_left A0 (by linarith only [left,dpos k]) right)
  have point (k : ℕ) (hk : k ∈ S) :
      PrincipalCofactor.cellWeight k*(-m k) ≤ (1/PrincipalCofactor.oddCofactor K)*(t k-t (k+1))+(1/(k:ℝ))*cost := by
    have low : (K:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
    have step : PrincipalCofactor.oddCofactor k ≤ PrincipalCofactor.oddCofactor (k+1) := by
      dsimp [PrincipalCofactor.oddCofactor]; push_cast; linarith
    have monot : 0 ≤ t k-t (k+1) := sub_nonneg.mpr (div_le_div_of_nonneg_left A0 (dpos k) step)
    have den : PrincipalCofactor.oddCofactor K ≤ 2*(PrincipalCofactor.oddCofactor k+1) := by
      dsimp [PrincipalCofactor.oddCofactor]; linarith only [low,Nat.cast_nonneg (α := ℝ) k]
    have kn : 0 < (k:ℝ) := by exact_mod_cast one.trans (Finset.mem_Ico.mp hk).1
    have cheap : (k:ℝ) ≤ 2*(PrincipalCofactor.oddCofactor k+1) := by dsimp [PrincipalCofactor.oddCofactor]; linarith
    calc
      _ ≤ PrincipalCofactor.cellWeight k*((t k-t (k+1))+cost) :=
        mul_le_mul_of_nonneg_left ((per k).trans (add_le_add_right (edge k) _)) (wpos k)
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (dpos K) den) monot)
          (mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le kn cheap) cost0)
  have tel (B : ℕ) (ge : K ≤ B) : ∑ k ∈ Finset.Ico K B, (t k-t (k+1))=t K-t B := by
    induction B, ge using Nat.le_induction with
    | base => simp
    | succ B ge ih => rw [Finset.sum_Ico_succ_top ge,ih]; ring
  have harmonic : (∑ k ∈ S, 1/(k:ℝ)) ≤ 1+Real.log R :=
    (nativeTailReciprocalIco_le K R one).trans (harmonic_le_one_add_log R)
  change -(∑ k ∈ S, PrincipalCofactor.cellWeight k*m k) ≤ _
  calc
    _ = ∑ k ∈ S, PrincipalCofactor.cellWeight k*(-m k) := by simp [Finset.sum_neg_distrib]
    _ ≤ _ := Finset.sum_le_sum point
    _ = (1/PrincipalCofactor.oddCofactor K)*(t K-t R)+(∑ k ∈ S, 1/(k:ℝ))*cost := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,tel R kr]
    _ ≤ (1/PrincipalCofactor.oddCofactor K)*t K+(1+Real.log R)*cost :=
      add_le_add (mul_le_mul_of_nonneg_left (sub_le_self _ (div_nonneg A0 (dpos R).le)) (one_div_pos.mpr (dpos K)).le)
        (mul_le_mul_of_nonneg_right harmonic cost0)
    _ = _ := by dsimp only [t,cost]; ring

/-- Evaluate the physical metric lower estimate along the original halving
chain. Each ancestor keeps its common shift and all of its endpoint chords. -/
def signedMetricHistory (term : ℕ → ℝ → ℝ) (shift : ℕ → ℝ) (N : ℕ) : ℝ :=
  if _h : N < 16 then 0 else signedMetricHistory term shift (N/2)+1 -
    ∑ k ∈ Finset.Ico 1 ⌈Real.sqrt N⌉₊, (PrincipalCofactor.chord N k+
      PrincipalCofactor.cellWeight k*term N (PrincipalCofactor.oddCofactor k+shift N))
termination_by N
decreasing_by omega

/-- One-sided comparison for the complete original signed integer history. The sum
on the right is evaluated from actual marginal wheel covolumes, the outside
prime log mass, ordinary lengths and the original endpoint chords. -/
theorem principal_metric_upper (e q d n : ℕ) [Fact q.Prime] [Fact d.Prime] (tops T : Finset (AlpogeNativeDyadicH e))
    (a : AlpogeNativeDyadicH e → ℝ)
    (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b : ℝ) (hx : 1 ≤ x) (hb : 4*x^2 ≤ b)
    (ht : tops.Nonempty) (hT : T.Nonempty) (hn : 0 < n)
    (ha : ∀ t ∈ tops, a t ∈ Set.Icc (x*b) ((x+1)*b))
    (hw : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u j ρ ∈ Set.Icc b (b*(1+1/x))) :
    let P := highThickPrimes e q d x
    let g := fun l => ((alpogeNativeHostData e q d).frob l).2
    let c := ⌊Real.sqrt x⌋₊
    let power := fun p : ℕ => p^(⌊(c:ℝ)*x⌋₊/p-c)
    let width := fun (j : AlpogeNativeDyadicH e × Fin n) (y : AlpogeNativeDyadicH e) => w j.1 j.2 ((0,1),y)
    let scale := ((T.card*n:ℕ):ℝ)*tops.card
    let A := PrincipalCofactor.evenEndpoint
    let I := fun (M : ℕ) (v : ℝ) => (PrincipalCofactor.retainedFirstPrimes M).filter
      (fun l : ℕ => A M/(v+1) ≤ (l:ℝ) ∧ (l:ℝ) < A M/v)
    let measured := fun (M : ℕ) (v : ℝ) => translatedMarginal tops T P g n a width power (fun l => l ∈ I M v)/scale
    let outside := fun (M : ℕ) (v : ℝ) => ∑ l ∈ I M v \ P, Real.log l
    let base := fun (M : ℕ) (v : ℝ) => A M/v-A M/(v+1)
    ∃ C : ℝ, 0 < C ∧ ∃ shift : ℕ → ℝ, (∀ M, shift M ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ N, PrincipalCofactor.affineHistory N-PrincipalCofactor.weightedCrossings N ≤
        signedMetricHistory (fun M v => measured M v+outside M v-base M v) shift N) ∧
      ∀ y : ℝ, 1 ≤ y → alpogeNativeGzArithmetic y ≤
        signedMetricHistory (fun M v => measured M v+outside M v-base M v) shift ⌊y⌋₊+C*Real.sqrt y := by
  classical
  intro P g c power width scale A I measured outside base
  let term := fun M v => measured M v+outside M v-base M v
  let choose (M : ℕ) (large : 16 ≤ M) :=
    measured_history_step e q d n tops T a w x b hx hb ht hT hn ha hw M 1 ⌈Real.sqrt M⌉₊ (by omega)
  let shift := fun M => if hm : 16 ≤ M then (choose M hm).choose else 0
  obtain ⟨C,hC,actual⟩ := PrincipalCofactor.real_firstPrime_history_price
  have inRange (M : ℕ) : shift M ∈ Set.Icc (0:ℝ) 1 := by
    by_cases large : 16 ≤ M
    · simpa only [shift,dite_eq_left large] using (choose M large).choose_spec.1
    · simp [shift,large]
  have price (N : ℕ) : PrincipalCofactor.firstPrimeHistory N ≤ signedMetricHistory term shift N := by
    induction N using Nat.strong_induction_on with
    | h N ih =>
      by_cases tiny : N < 16
      · rw [PrincipalCofactor.firstPrimeHistory,PrincipalCofactor.sumHistory_small _ N tiny,signedMetricHistory]
        simp [tiny]
      · have large : 16 ≤ N := by omega
        have prev := ih (N/2) (by omega)
        have step := (choose N large).choose_spec.2
        have eq : shift N=(choose N large).choose := by simp [shift,large]
        have recursion : PrincipalCofactor.firstPrimeHistory N =
            PrincipalCofactor.firstPrimeHistory (N/2) -
            ∑ k ∈ Finset.Ico 1 ⌈Real.sqrt N⌉₊, PrincipalCofactor.primePairReading N k := by
          rw [PrincipalCofactor.firstPrimeHistory,PrincipalCofactor.sumHistory_step _ N tiny]
          simp only [PrincipalCofactor.primePairReading,
            PrincipalCofactor.oddPrimeReading,PrincipalCofactor.evenEndpoint,PrincipalCofactor.oddCofactor,
            show ∀ k : ℕ, 2*(k:ℝ)+1+1=2*k+2 by intro k; ring]
        rw [recursion,signedMetricHistory,dite_eq_right tiny,eq]
        exact (sub_le_sub_right prev _).trans (by linarith only [step])

  refine ⟨C,hC,shift,inRange,?_,?_⟩
  · intro N
    rw [PrincipalCofactor.affine_sub_weightedCrossings]
    exact price N
  · intro y hy
    exact (sub_le_iff_le_add'.mp (abs_le.mp (actual y hy)).2).trans
      (by linarith only [price ⌊y⌋₊])

end WheelNNS
end RHLean.Analysis.AlpogeThin.SlotProjector
