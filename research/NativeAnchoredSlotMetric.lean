import «research.NativeAnchoredSlotRecovery»

/-! Counting-metric prices of the physical anchor and of the line complementary
to the prime-weighted star. The latter is determined by an actual minimum. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector

/-- Counting energy of a layer-constant section on its original integer slots. -/
def slotEnergy {r : ℕ} (S : Fin (r+1) → Finset ℕ) (A : Fin (r+1) → ℝ) : ℝ :=
  ∑ i, ((S i).card:ℝ)*(A i)^2

/-- The integral anchor projector repeats the zeroth amplitude on all occupied
layers. Its real squared operator norm is attained by the zeroth layer indicator. -/
theorem anchor_norm {r : ℕ} (S : Fin (r+1) → Finset ℕ) (hS : (S 0).Nonempty) :
    let L := ∑ i, ((S i).card:ℝ)
    (∀ A : Fin (r+1) → ℝ, slotEnergy S (fun _ => A 0) ≤
      (L/(S 0).card) * slotEnergy S A) ∧
    ∃ A : Fin (r+1) → ℤ, 0 < slotEnergy S (fun i => (A i:ℝ)) ∧
      slotEnergy S (fun _ => (A 0:ℝ)) = (L/(S 0).card) * slotEnergy S (fun i => (A i:ℝ)) := by
  classical
  intro L
  have h0 : 0 < ((S 0).card:ℝ) := by exact_mod_cast hS.card_pos
  have total (a : ℝ) : slotEnergy S (fun _ => a) = L*a^2 := (Finset.sum_mul _ _ _).symm
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  constructor
  · intro A
    have one : ((S 0).card:ℝ)*(A 0)^2 ≤ slotEnergy S A :=
      Finset.single_le_sum (f := fun i : Fin (r+1) => ((S i).card:ℝ)*(A i)^2)
        (fun i _ => by positivity) (Finset.mem_univ 0)
    rw [total]
    calc
      _ = (L/(S 0).card) * (((S 0).card:ℝ)*(A 0)^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left one (div_nonneg hL h0.le)
  · let A := fun i : Fin (r+1) => if i = 0 then (1:ℤ) else 0
    have ha : slotEnergy S (fun i => (A i:ℝ)) = ((S 0).card:ℝ) := by
      simp [slotEnergy, A, apply_ite]
    refine ⟨A, ha.symm ▸ h0, ?_⟩
    rw [total, ha]
    simp [A, h0.ne']

/-- In the original height/width collar the squared norm of reading and
retaining the pivot grows only polynomially in x, independently of the wheel. -/
theorem firstPrime_anchor_price (e q d r : ℕ) [Fact q.Prime] [Fact d.Prime]
    (p : Fin (r+1) → ℕ) (t : Fin (r+1) → AlpogeNativeDyadicH e)
    (a : AlpogeNativeDyadicH e → ℝ) (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b : ℝ) (hx : 1 ≤ x) (hb : 4*x^2 ≤ b) (hp : ∀ i, (p i).Prime)
    (ho : StrictMono p) (hband : ∀ i, (p i:ℝ)+1 ≤ x)
    (ha : ∀ i, a (t i) ∈ Set.Icc (x*b) ((x+1)*b))
    (s : AlpogeNativeE0 × AlpogeNativeDyadicH e)
    (hs : ∀ i, alpogeNativePartner (t i) ((alpogeNativeHostData e q d).frob (p i)) = s)
    (hv : 0 ≤ w s) (hw : w s ≤ b*(1+1/x)) :
    let S := bands (fun i => a (t i)/(p i:ℝ)) (w s)
    ∀ l, (∑ i, ((S i).card:ℝ))/((S l).card:ℝ) ≤ 4*x^3 := by
  classical
  intro S l
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hx2 : 0 < x^2 := sq_pos_of_pos hx0
  have hb0 : 0 < b := by linarith
  have spec := firstPrime_slots e q d r p t a w x b hx hb hp ho hband ha s hs hv hw
  have hS (i) : (S i).Nonempty := (spec i).2.1
  obtain ⟨f,_⟩ := original_addresses (fun i => a (t i)/(p i:ℝ)) (w s) hS
  have len : (∑ i, (S i).card) = ⌊a (t 0)/(p 0:ℝ)⌋₊ - ⌈w s⌉₊ := by
    simpa only [Address, Fintype.card_sigma, Fintype.card_coe, Nat.card_Ioc] using Fintype.card_congr f
  have one : 1 ≤ (p 0:ℝ) := by exact_mod_cast (hp 0).one_le
  have hpos : 0 ≤ a (t 0) := (mul_pos hx0 hb0).le.trans (ha 0).1
  have upper : (∑ i, ((S i).card:ℝ)) ≤ (x+1)*b := by
    rw [← Nat.cast_sum, len]
    calc
      _ ≤ (⌊a (t 0)/(p 0:ℝ)⌋₊:ℝ) := by exact_mod_cast Nat.sub_le _ _
      _ ≤ a (t 0)/(p 0:ℝ) := Nat.floor_le (div_nonneg hpos (by linarith))
      _ ≤ a (t 0) := div_le_self hpos one
      _ ≤ _ := (ha 0).2
  have hcount : 0 < ((S l).card:ℝ) := by exact_mod_cast (hS l).card_pos
  have sep : b/x^2 - 2 ≤ ((S l).card:ℝ) := by
    linarith only [(spec l).2.2.1, (spec l).2.2.2.1]
  have h4 : 4 ≤ b/x^2 := (le_div_iff₀ hx2).2 hb
  have low : b ≤ (2*((S l).card:ℝ))*x^2 := (div_le_iff₀ hx2).1 (by linarith only [h4,sep])
  apply (div_le_iff₀ hcount).2
  calc
    _ ≤ (x+1)*b := upper
    _ ≤ (2*x)*b := mul_le_mul_of_nonneg_right (by linarith) hb0.le
    _ ≤ (2*x)*((2*((S l).card:ℝ))*x^2) := mul_le_mul_of_nonneg_left low (by positivity)
    _ = _ := by ring

/-- Sum the exact real log norms of the retained anchors over their actual
translated rows. One prime from each occupied block pays its anchor. The
prime/top incidence identity and Chebyshev's bound give a uniform square-root
cost after the original wheel-volume normalization. -/
theorem translated_anchor_total_price (e q d n : ℕ) [Fact q.Prime] [Fact d.Prime]
    (tops T : Finset (AlpogeNativeDyadicH e)) (a : AlpogeNativeDyadicH e → ℝ)
    (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b : ℝ) (hx : 10 ≤ x) (hb : 4*x^2 ≤ b) (ht : tops.Nonempty) (hT : T.Nonempty)
    (hn : 0 < n) (ha : ∀ t ∈ tops, a t ∈ Set.Icc (x*b) ((x+1)*b))
    (hw : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u j ρ ∈ Set.Icc b (b*(1+1/x))) :
    let c := ⌊Real.sqrt x⌋₊
    let k := ((T.card*n:ℕ):ℝ)
    let P := highThickPrimes e q d x
    let g := fun l => ((alpogeNativeHostData e q d).frob l).2
    let V := occupied tops P g
    let p := primeAt tops P g
    let S := fun (s : ↥V) (j : ↥(siteRows T n s.val)) =>
      bands (fun i => a (s.val-g (p s i))/(p s i:ℝ)) (w j.val.1 j.val.2 ((0,1),s.val))
    2*(∑ s : ↥V, ∑ j : ↥(siteRows T n s.val),
      Real.log ((∑ i, ((S s j i).card:ℝ))/((S s j 0).card:ℝ)))/((c:ℝ)*k*tops.card) ≤
        32*Real.log 4*Real.sqrt x := by
  classical
  intro c k P g V p S
  let r := fun s : ↥V => (partnerPrimes tops P g s.val).card-1
  let R := fun (s : ↥V) (j : ↥(siteRows T n s.val)) =>
    (∑ i, ((S s j i).card:ℝ))/((S s j 0).card:ℝ)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hsqrt : 2 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).2 (by linarith)
  have hfloor := Nat.lt_floor_add_one (Real.sqrt x)
  change Real.sqrt x < (c:ℝ)+1 at hfloor
  have hc : 0 < (c:ℝ) := by linarith
  have hk : 0 < k := by
    change 0 < ((T.card*n:ℕ):ℝ)
    exact_mod_cast Nat.mul_pos hT.card_pos hn
  have ht0 : 0 < (tops.card:ℝ) := by exact_mod_cast ht.card_pos
  have info := highThick_primeAt e q d x tops
  have per (s : ↥V) (j : ↥(siteRows T n s.val)) :
      Real.log (R s j) ≤ 8*∑ i, Real.log (p s i:ℝ) := by
    have width := hw j.val.1 j.val.2 _ ((siteRows_mem_iff T n s.val j.val).1 j.property)
    have prime i := (info s i).1
    have band i := (info s i).2.2.1
    have height i := ha _ (info s i).2.2.2.2
    have partner i := (info s i).2.2.2.1
    have price := firstPrime_anchor_price e q d (r s) (p s) (fun i => s.val-g (p s i))
      a (w j.val.1 j.val.2) x b hx1 hb prime (p s).strictMono band height _ partner
      (hb0.le.trans width.1) width.2 0
    have layer := (firstPrime_slots e q d (r s) (p s) (fun i => s.val-g (p s i)) a (w j.val.1 j.val.2)
      x b hx1 hb prime (p s).strictMono band height _ partner (hb0.le.trans width.1) width.2 0).2.1
    have h0 : 0 < ((S s j 0).card:ℝ) := by exact_mod_cast layer.card_pos
    have term : ((S s j 0).card:ℝ) ≤ ∑ i, ((S s j i).card:ℝ) :=
      Finset.single_le_sum (f := fun i => ((S s j i).card:ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ 0)
    have hlog := Real.log_le_log (Real.sqrt_pos.2 hx0) (info s 0).2.1
    rw [Real.log_sqrt hx0.le] at hlog
    calc
      Real.log (R s j) ≤ Real.log (4*x^3) := Real.log_le_log (div_pos (h0.trans_le term) h0) price
      _ ≤ 8*Real.log (p s 0:ℝ) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num only [Nat.cast_ofNat]
        linarith only [hlog, Real.log_le_log (by norm_num : (0:ℝ) < 4) (by linarith : 4 ≤ x)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun i => Real.log (p s i:ℝ))
        (fun i _ => Real.log_natCast_nonneg _) (Finset.mem_univ 0)) (by norm_num)
  have sums : ∑ l ∈ P, Real.log (l:ℝ) ≤ Real.log 4*x := by
    calc
      _ ≤ ∑ l ∈ Nat.primesLE ⌊x⌋₊, Real.log (l:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
          (fun l _ _ => Real.log_natCast_nonneg l)
      _ = Chebyshev.theta x := by rw [Chebyshev.theta, Nat.primesLE_eq_filter_Ioc_zero]
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x hx0.le
  have charge : (∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), Real.log (R s j)) ≤
      k*(8*(tops.card*(Real.log 4*x))) := by
    calc
      _ ≤ ∑ s : ↥V, ∑ _j : ↥(siteRows T n s.val), 8*∑ i, Real.log (p s i:ℝ) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun j _ => per s j
      _ = k*(8*(tops.card*∑ l ∈ P, Real.log (l:ℝ))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, siteRows_card, nsmul_eq_mul,
          ← Finset.mul_sum]
        exact congrArg (fun v : ℝ => k*(8*v)) (primeAt_sum tops P g (fun l => Real.log (l:ℝ)))
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left sums ht0.le) (by norm_num)) hk.le
  have scale : x ≤ 2*Real.sqrt x*(c:ℝ) := by
    nlinarith only [Real.mul_self_sqrt hx0.le, mul_le_mul_of_nonneg_left
      (show Real.sqrt x ≤ 2*(c:ℝ) by linarith) (Real.sqrt_nonneg x)]
  apply (div_le_iff₀ (mul_pos (mul_pos hc hk) ht0)).2
  calc
    _ ≤ 2*(k*(8*(tops.card*(Real.log 4*x)))) := mul_le_mul_of_nonneg_left charge (by norm_num)
    _ = ((16*Real.log 4)*k*tops.card)*x := by ring
    _ ≤ ((16*Real.log 4)*k*tops.card)*(2*Real.sqrt x*c) := mul_le_mul_of_nonneg_left scale (by positivity)
    _ = _ := by ring

/-- Cofactor of a measured star column matrix at each layer. -/
def wheelNormal {r : ℕ} (D : Fin (r+1) → ℕ) (i : Fin (r+1)) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, D j

def dualEnergy {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ) : ℝ :=
  ∑ i, (wheelNormal D i:ℝ)^2 / (S i).card

theorem dualEnergy_pos {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) : 0 < dualEnergy S D := by
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  have hn : 0 < wheelNormal D i := Finset.prod_pos fun j _ => hD j
  exact div_pos (sq_pos_of_pos (by exact_mod_cast hn)) (by exact_mod_cast (hS i).card_pos)

/-- Minimum in the measured metric on each affine hyperplane of the wheel normal.
The minimizer is exhibited. Taking level one measures a primitive completion. -/
theorem complementary_minimum {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) (t : ℝ) :
    (∀ A : Fin (r+1) → ℝ, (∑ i, (wheelNormal D i:ℝ)*A i) = t →
      t^2/dualEnergy S D ≤ slotEnergy S A) ∧
    ∃ A : Fin (r+1) → ℝ, (∑ i, (wheelNormal D i:ℝ)*A i) = t ∧
      slotEnergy S A = t^2/dualEnergy S D := by
  classical
  have positive := dualEnergy_pos S D hS hD
  have hw (i) : 0 < ((S i).card:ℝ) := by exact_mod_cast (hS i).card_pos
  constructor
  · intro A hA
    apply (div_le_iff₀ positive).2
    rw [← hA]
    unfold slotEnergy dualEnergy
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun i => (wheelNormal D i:ℝ)*A i)
      (f := fun i => ((S i).card:ℝ)*(A i)^2)
      (g := fun i => (wheelNormal D i:ℝ)^2/(S i).card)
    · intro i _; positivity
    · intro i _; positivity
    · intro i _
      apply le_of_eq
      field_simp [(hw i).ne']
  · let N := dualEnergy S D
    let A := fun i => (t/N) * ((wheelNormal D i:ℝ)/(S i).card)
    have level : (∑ i, (wheelNormal D i:ℝ)*A i) = (t/N)*N := by
      change _ = (t/N)*∑ i, (wheelNormal D i:ℝ)^2/(S i).card
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [A]
      ring
    have energy : slotEnergy S A = (t/N)^2*N := by
      change _ = (t/N)^2*∑ i, (wheelNormal D i:ℝ)^2/(S i).card
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [A]
      field_simp [(hw i).ne']
    refine ⟨A, level.trans (div_mul_cancel₀ _ positive.ne'), energy.trans ?_⟩
    change (t/N)^2*N = t^2/N
    field_simp [show N ≠ 0 from positive.ne']

theorem wheelNormal_star {r : ℕ} (D : Fin (r+1) → ℕ) (j : Fin r) :
    ∑ i, (wheelNormal D i:ℤ)*starColumn D j i 0 = 0 := by
  have same (i) : (wheelNormal D i:ℤ)*(D i:ℤ) = (∏ k, (D k:ℤ)) := by
    simpa [wheelNormal] using Finset.prod_erase_mul (Finset.univ : Finset (Fin (r+1)))
      (fun k => (D k:ℤ)) (Finset.mem_univ i)
  simp [starColumn, mul_sub, mul_ite, Finset.sum_sub_distrib, same]

def normalReading {r : ℕ} (D : Fin (r+1) → ℕ) (A : Fin (r+1) → ℤ) : ℤ :=
  ∑ i, (wheelNormal D i:ℤ)*A i

/-- On integral amplitudes the normal equation cuts out exactly the measured
star lattice. Pairwise coprimality recovers the original integer coefficients. -/
theorem wheel_star_kernel {r : ℕ} (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i)
    (cop : Pairwise (fun i j => (D i).Coprime (D j))) (A : Fin (r+1) → ℤ) :
    normalReading D A = 0 ↔ ∃ z : Fin r → ℤ, ∀ i, A i = ∑ j, starColumn D j i 0 * z j := by
  classical
  constructor
  · intro zero
    have hz (i : Fin (r+1)) : (D i:ℤ) ∣ A i := by
      have hcop : (D i).Coprime (wheelNormal D i) := (Nat.coprime_prod_left_iff.mpr
        (fun j hj => cop (Finset.mem_erase.mp hj).1)).symm
      apply hcop.isCoprime.dvd_of_dvd_mul_left
      let f := fun j => (wheelNormal D j:ℤ)*A j
      have rest : (D i:ℤ) ∣ ∑ j ∈ Finset.univ.erase i, f j := by
        apply Finset.dvd_sum
        intro j hj
        have div : D i ∣ wheelNormal D j := Finset.dvd_prod_of_mem D
          (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1.symm, Finset.mem_univ i⟩)
        exact dvd_mul_of_dvd_left (by exact_mod_cast div) _
      have eqn := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
      change ∑ j, f j = 0 at zero
      change (D i:ℤ) ∣ f i
      rw [show f i = -(∑ j ∈ Finset.univ.erase i, f j) by omega]
      exact dvd_neg.mpr rest
    choose u hu using hz
    let N := ∏ i, (D i:ℤ)
    have nonzero : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (hD i).ne'
    have same i : (wheelNormal D i:ℤ)*(D i:ℤ) = N := by
      simpa only [wheelNormal, Nat.cast_prod, N] using
        Finset.prod_erase_mul Finset.univ (fun j => (D j:ℤ)) (Finset.mem_univ i)
    have sumU : ∑ i, u i = 0 := by
      apply (mul_eq_zero.mp (show N*∑ i, u i = 0 by
        rw [Finset.mul_sum]
        simpa only [normalReading, hu, ← mul_assoc, same] using zero)).resolve_left nonzero
    rw [Fin.sum_univ_succ] at sumU
    refine ⟨fun j => u j.succ, fun i => Fin.cases ?_ (fun j => ?_) i⟩
    · rw [hu 0, show u 0 = -(∑ j : Fin r, u j.succ) by omega]
      simp [starColumn, (Fin.succ_ne_zero _).symm, neg_mul, mul_neg, Finset.mul_sum]
    · simp [starColumn, Fin.succ_ne_zero, ite_mul, hu]
  · rintro ⟨z,hz⟩
    unfold normalReading
    simp_rw [hz, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, wheelNormal_star, zero_mul, Finset.sum_const_zero]

/-- Read an integral section modulo the normal level of the constant column. -/
def wheelCongruence {r : ℕ} (D : Fin (r+1) → ℕ) :
    (Fin (r+1) → ℤ) →+ ZMod (∑ i, wheelNormal D i) where
  toFun A := (normalReading D A : ZMod _)
  map_zero' := by simp [normalReading]
  map_add' A B := by simp [normalReading, mul_add, Finset.sum_add_distrib]

/-- Ordinary index after adjoining the literal constant anchor to the original
wheel stars. A primitive completion has normal reading one instead. -/
theorem constant_extension_index {r : ℕ} (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i)
    (cop : Pairwise (fun i j => (D i).Coprime (D j))) :
    let δ := ∑ i, wheelNormal D i
    let F := wheelCongruence D
    F.ker.index = δ ∧ (∀ A, A ∈ F.ker ↔ ∃ (a : ℤ) (z : Fin r → ℤ),
      ∀ i, A i = a + ∑ j, starColumn D j i 0*z j) := by
  classical
  intro δ F
  have hd : 0 < δ := Finset.sum_pos (fun i _ => Finset.prod_pos (fun j _ => hD j)) Finset.univ_nonempty
  let : NeZero δ := ⟨hd.ne'⟩
  obtain ⟨w,hw,_⟩ := nativeDyadic_firstPrime_wheel_short_completion (0 : Fin (r+1)) D hD cop
  have onto : Function.Surjective F := by
    intro y
    obtain ⟨v,hv⟩ := ZMod.intCast_surjective y
    refine ⟨fun i => w i*v, ?_⟩
    change ((∑ i, (wheelNormal D i:ℤ)*(w i*v):ℤ):ZMod δ) = y
    simp only [← mul_assoc, ← Finset.sum_mul, wheelNormal, hw, one_mul, hv]
  constructor
  · rw [AddSubgroup.index_ker, F.range_eq_top_of_surjective onto, AddSubgroup.card_top]
    simp only [Nat.card_eq_fintype_card, ZMod.card, δ]
  · intro A
    change ((normalReading D A:ℤ):ZMod δ) = 0 ↔ _
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have shift (a : ℤ) : normalReading D (fun i => A i-a) = normalReading D A - (δ:ℤ)*a := by
      simp only [normalReading, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, δ, Nat.cast_sum]
    constructor
    · rintro ⟨a,ha⟩
      obtain ⟨z,hz⟩ := (wheel_star_kernel D hD cop (fun i => A i-a)).1 (by rw [shift, ha, sub_self])
      exact ⟨a,z,fun i => by have h := hz i; omega⟩
    · rintro ⟨a,z,hz⟩
      have h := (wheel_star_kernel D hD cop (fun i => A i-a)).2 ⟨z,fun i => by rw [hz i]; abel⟩
      exact ⟨a,sub_eq_zero.mp ((shift a).symm.trans h)⟩

/-- The projected length is evaluated independently through the dual norm.
Its relative log is the opposite of the measured star log covolume. -/
def complementaryLog {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ) : ℝ :=
  (Real.log (1/dualEnergy S D) - Real.log (1/dualEnergy S (fun _ => 1)))/2

private theorem erase_cost_cancel (u v t : ℝ) (ht : t ≠ 0) : u*v = (u*t)*(v/t) := by
  field_simp

theorem complementaryLog_eq {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) :
    complementaryLog S D = -logVolume S D := by
  classical
  let L := ∏ i, ((S i).card:ℝ)
  have hw (i) : 0 < ((S i).card:ℝ) := by exact_mod_cast (hS i).card_pos
  have hL : 0 < L := Finset.prod_pos fun i _ => hw i
  have det (d : Fin (r+1) → ℕ) (hd : ∀ i, 0 < d i) :
      ((((columns S d).transpose*columns S d).det:ℤ):ℝ) = L*dualEnergy S d := by
    rw [columns_det S d hS hd, Int.cast_natCast]
    simp only [mass, Nat.cast_sum, Nat.cast_prod, Nat.cast_mul, Nat.cast_pow, dualEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [L, wheelNormal, Nat.cast_prod, Finset.prod_mul_distrib, Finset.prod_pow]
    rw [← Finset.prod_erase_mul Finset.univ (fun k => ((S k).card:ℝ)) (Finset.mem_univ i)]
    exact erase_cost_cancel _ _ _ (hw i).ne'
  dsimp only [complementaryLog, logVolume]
  rw [det D hD, det _ (fun _ => Nat.zero_lt_one), Real.log_mul hL.ne' (dualEnergy_pos S D hS hD).ne',
    Real.log_mul hL.ne' (dualEnergy_pos S _ hS (fun _ => Nat.zero_lt_one)).ne']
  simp only [one_div, Real.log_inv]
  ring

/-- The constant anchor has normal level δ. Using it as the added column of
the wheel stars changes the relative archimedean volume by exactly the log
of the *relative* ordinary index, including the unit-wheel index r+1. -/
theorem constant_complement_price {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) :
    let δ := ∑ i, wheelNormal D i
    (Real.log ((δ:ℝ)^2/dualEnergy S D) -
      Real.log (((r+1:ℕ):ℝ)^2/dualEnergy S (fun _ => 1)))/2 =
      Real.log ((δ:ℝ)/(r+1:ℕ)) - logVolume S D := by
  intro δ
  have hd : 0 < δ := Finset.sum_pos (fun i _ => Finset.prod_pos fun j _ => hD j) Finset.univ_nonempty
  have hd' : (δ:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hr : ((r+1:ℕ):ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  have h1 := (dualEnergy_pos S _ hS (fun _ => Nat.zero_lt_one)).ne'
  have h2 := (dualEnergy_pos S D hS hD).ne'
  have opp := complementaryLog_eq S D hS hD
  simp only [complementaryLog, one_div, Real.log_inv] at opp
  rw [Real.log_div (pow_ne_zero _ hd') h2, Real.log_div (pow_ne_zero _ hr) h1,
    Real.log_div hd' hr, Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [opp]

end RHLean.Analysis.AlpogeThin.SlotProjector
