import «research.NativeAnchoredSlotMetric»

/-! The finite places and the real norm of projecting onto a primitive
integral completion along the original measured star lattice. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector

private theorem measured_smul {r : ℕ} (S : Fin (r+1) → Finset ℕ) (a : ℝ) (v : Fin (r+1) → ℝ) :
    slotEnergy S (fun i => a*v i) = a^2*slotEnergy S v := by
  unfold slotEnergy
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The same integral column saturates the original stars. Its projection
along the stars has a unit entry at every finite prime. Its squared real norm
is exactly the product of the column energy and the dual energy. -/
theorem primitive_splitting_cost {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i)
    (cop : Pairwise (fun i j => (D i).Coprime (D j))) :
    ∃ b : Fin (r+1) → ℤ, normalReading D b = 1 ∧
      (∀ A, ∃ z : Fin r → ℤ, ∀ i, A i = normalReading D A*b i + ∑ j, starColumn D j i 0*z j) ∧
      (∀ p : ℕ, p.Prime → ∃ i, ¬(p:ℤ) ∣ (wheelNormal D i:ℤ)*b i) ∧
      let eb := slotEnergy S (fun i => (b i:ℝ))
      let N := dualEnergy S D
      let h := fun A : Fin (r+1) → ℝ => ∑ i, (wheelNormal D i:ℝ)*A i
      let P := fun (A : Fin (r+1) → ℝ) i => h A*(b i:ℝ)
      (∀ A, slotEnergy S (P A) ≤ (eb*N)*slotEnergy S A) ∧
      (∃ A, 0 < slotEnergy S A ∧ slotEnergy S (P A) = (eb*N)*slotEnergy S A) ∧
      (∃ i, ((∑ j, wheelNormal D j : ℕ):ℝ)^2*((S i).card:ℝ) ≤
        (∑ j, ((S j).card:ℝ))*(eb*N)) := by
  classical
  obtain ⟨b,one,_⟩ := nativeDyadic_firstPrime_wheel_short_completion (0 : Fin (r+1)) D hD cop
  change normalReading D b = 1 at one
  refine ⟨b,one,?_,?_,?_⟩
  · intro A
    let t := normalReading D A
    have zero : normalReading D (fun i => A i-t*b i) = 0 := by
      have split : normalReading D (fun i => A i-t*b i) = t-t*normalReading D b := by
        unfold normalReading
        dsimp only [t, normalReading]
        simp only [mul_sub, Finset.sum_sub_distrib]
        apply congrArg ((∑ i, (wheelNormal D i:ℤ)*A i) - ·)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [split, one, mul_one, sub_self]
    obtain ⟨z,hz⟩ := (wheel_star_kernel D hD cop _).1 zero
    exact ⟨z, fun i => by have h := hz i; change A i-t*b i = _ at h; change A i=t*b i+_; omega⟩
  · intro p hp
    by_contra! hn
    have div : (p:ℤ) ∣ normalReading D b := Finset.dvd_sum fun i _ => hn i
    rw [one] at div
    have bad : p ∣ 1 := by exact_mod_cast div
    exact hp.not_dvd_one bad
  · intro eb N h P
    have hN : 0 < N := dualEnergy_pos S D hS hD
    have hb : 0 ≤ eb := Finset.sum_nonneg fun i _ => by exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have price A : slotEnergy S (P A) = (h A)^2*eb := measured_smul S _ _
    constructor
    · intro A
      have hz := ((div_le_iff₀ hN).mp ((complementary_minimum S D hS hD (h A)).1 A rfl))
      rw [price]
      calc
        _ ≤ (slotEnergy S A*N)*eb := mul_le_mul_of_nonneg_right hz hb
        _ = _ := by ring
    · obtain ⟨A,hA,hmin⟩ := (complementary_minimum S D hS hD 1).2
      change h A = 1 at hA
      change slotEnergy S A = 1^2/N at hmin
      refine ⟨⟨A, by rw [hmin]; positivity, ?_⟩, ?_⟩
      · rw [price, hA, hmin]
        field_simp [hN.ne']
      · have hit : ∃ i, b i ≠ 0 := by
          by_contra! hz
          simp [normalReading,hz] at one
        obtain ⟨i,hi⟩ := hit
        have sq : (1:ℝ) ≤ (b i:ℝ)^2 := by
          exact_mod_cast (show (1:ℤ) ≤ (b i)^2 by nlinarith only [sq_pos_of_ne_zero hi])
        have lo : ((S i).card:ℝ) ≤ eb := calc
          _ ≤ ((S i).card:ℝ)*(b i:ℝ)^2 := le_mul_of_one_le_right (Nat.cast_nonneg _) sq
          _ ≤ _ := Finset.single_le_sum (f := fun j => ((S j).card:ℝ)*(b j:ℝ)^2)
            (fun j _ => by positivity) (Finset.mem_univ i)
        let δ := ∑ j, wheelNormal D j
        have hz := (complementary_minimum S D hS hD (δ:ℝ)).1 (fun _ => 1) (by simp [δ])
        have lower := (div_le_iff₀ hN).mp hz
        simp only [slotEnergy, one_pow, mul_one] at lower
        refine ⟨i, ?_⟩
        calc
          _ ≤ ((∑ j, ((S j).card:ℝ))*N)*((S i).card:ℝ) := mul_le_mul_of_nonneg_right lower (Nat.cast_nonneg _)
          _ = (∑ j, ((S j).card:ℝ))*(((S i).card:ℝ)*N) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right lo hN.le)
            (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _)

/-- On every genuine nonpivot star the inexpensive pivot projector crosses
the original hyperplane by precisely this nonzero multiple of its index. -/
theorem anchor_on_wheel_star {r : ℕ} (D : Fin (r+1) → ℕ) (j : Fin r) :
    normalReading D (anchoredRecovery (fun _ => 0) (fun i => starColumn D j i 0)) =
      ((∑ i, wheelNormal D i : ℕ):ℤ) * (-(D 0:ℤ)) := by
  rw [anchoredRecovery_constant]
  simp only [normalReading, starColumn, ite_eq_right (Fin.succ_ne_zero j).symm, ite_true, zero_sub,
    ← Finset.sum_mul, Nat.cast_sum]

/-- Exact index of the jumps of the original star sections after forgetting
one anchor. Taking differences identifies the constant-extended star lattice
modulo the entire kernel of the jump map. -/
theorem wheel_star_jump_index {r : ℕ} (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i)
    (cop : Pairwise (fun i j => (D i).Coprime (D j))) :
    ∃ K : AddSubgroup (Fin r → ℤ), K.index = (∑ i, wheelNormal D i) ∧
      ∀ y, y ∈ K ↔ ∃ z : Fin r → ℤ, y = layerJump (fun i => ∑ j, starColumn D j i 0*z j) := by
  classical
  let J : (Fin (r+1) → ℤ) →+ (Fin r → ℤ) := {
    toFun := layerJump
    map_zero' := by funext j; simp [layerJump]
    map_add' A B := by funext j; simp only [layerJump, Pi.add_apply]; abel }
  let F := wheelCongruence D
  have h := constant_extension_index D hD cop
  have onto : Function.Surjective J := fun y => ⟨fromJumps 0 y, funext fun j => layerJump_fromJumps 0 y j⟩
  have ker : J.ker ≤ F.ker := by
    intro A hA
    change J A = 0 at hA
    have same : A = fun _ => A 0 := eq_of_anchor_jumps rfl fun j => by
      have hj := congrFun hA j
      change layerJump A j = 0 at hj
      change layerJump A j = A 0-A 0
      rw [hj, sub_self]
    apply (h.2 A).2
    refine ⟨A 0,fun _ => 0,fun i => ?_⟩
    simpa only [mul_zero, Finset.sum_const_zero, add_zero] using congrFun same i
  refine ⟨F.ker.map J, (F.ker.index_map_eq onto ker).trans h.1, ?_⟩
  intro y
  constructor
  · rintro ⟨A,hA,rfl⟩
    obtain ⟨a,z,vals⟩ := (h.2 A).1 hA
    refine ⟨z, funext fun j => ?_⟩
    change A j.succ - A j.castSucc = _ - _
    rw [vals j.succ, vals j.castSucc]
    abel
  · rintro ⟨z,rfl⟩
    refine ⟨fun i => ∑ j, starColumn D j i 0*z j, (h.2 _).2 ⟨0,z,fun _ => (zero_add _).symm⟩,rfl⟩

/-- Eliminating the anchor costs at least the entire positive log volume
of the same wheel block in its actual counting metric. -/
theorem logVolume_le_log_congruence {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i) :
    logVolume S D ≤ Real.log ((∑ i, wheelNormal D i : ℕ):ℝ) := by
  classical
  let δ := ∑ i, wheelNormal D i
  have hd : 0 < δ := Finset.sum_pos (fun i _ => Finset.prod_pos fun j _ => hD j) Finset.univ_nonempty
  have dual : dualEnergy S D ≤ (δ:ℝ)^2 * dualEnergy S (fun _ => 1) := by
    unfold dualEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : (wheelNormal D i:ℝ) ≤ (δ:ℝ) := by
      exact_mod_cast (Finset.single_le_sum (f := wheelNormal D) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    have sq := pow_le_pow_left₀ (Nat.cast_nonneg (wheelNormal D i)) hi 2
    have lower := div_le_div_of_nonneg_right sq (Nat.cast_nonneg (S i).card : 0 ≤ ((S i).card:ℝ))
    simpa only [wheelNormal, Finset.prod_const_one, Nat.cast_one, one_pow, mul_one_div] using lower
  have hh := Real.log_le_log (dualEnergy_pos S D hS hD) dual
  rw [Real.log_mul (pow_ne_zero _ (by exact_mod_cast hd.ne')) (dualEnergy_pos S _ hS (fun _ => Nat.zero_lt_one)).ne',
    Real.log_pow] at hh
  have opp := complementaryLog_eq S D hS hD
  simp only [complementaryLog, one_div, Real.log_inv] at opp
  change logVolume S D ≤ Real.log (δ:ℝ)
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh,opp]

/-- One common amplitude vector at each physical site, shared by all its
translated rows. Eliminating the anchors gives one index factor per site.
The logarithm of this single global index bounds the *row average* of the
entire measured wheel gain. -/
theorem translated_star_jump_index {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (V T : Finset H) (n : ℕ) (r : ↥V → ℕ) (D : (s : ↥V) → Fin (r s+1) → ℕ)
    (hD : ∀ s i, 0 < D s i) (cop : ∀ s, Pairwise (fun i j => (D s i).Coprime (D s j))) :
    ∃ K : AddSubgroup ((s : ↥V) → Fin (r s) → ℤ),
      K.index = (∏ s : ↥V, ∑ i, wheelNormal (D s) i) ∧
      (∀ y, y ∈ K ↔ ∀ s, ∃ z : Fin (r s) → ℤ, y s = layerJump (fun i => ∑ j, starColumn (D s) j i 0*z j)) ∧
      ∀ (S : (s : ↥V) → ↥(siteRows T n s.val) → Fin (r s+1) → Finset ℕ),
        (∀ s j i, (S s j i).Nonempty) →
        (∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), logVolume (S s j) (D s)) ≤
          ((T.card*n:ℕ):ℝ)*Real.log (K.index:ℝ) := by
  classical
  choose B hidx hmem using fun s => wheel_star_jump_index (D s) (hD s) (cop s)
  let K := AddSubgroup.pi Set.univ B
  have idx : K.index = ∏ s : ↥V, ∑ i, wheelNormal (D s) i := by
    calc
      _ = ∏ s, (B s).index := by
        dsimp only [K]
        simp_rw [AddSubgroup.index, ← Nat.card_pi]
        refine Nat.card_congr ((Quotient.congrRight (fun x y => ?_)).trans (Setoid.piQuotientEquiv _).symm)
        rw [QuotientAddGroup.leftRel_pi]
      _ = _ := Finset.prod_congr rfl fun s _ => hidx s
  refine ⟨K,idx,?_,?_⟩
  · intro y
    constructor
    · intro h s
      exact (hmem s (y s)).1 (h s (Set.mem_univ s))
    · intro h s _
      exact (hmem s (y s)).2 (h s)
  · intro S hS
    have pos (s : ↥V) : 0 < ∑ i, wheelNormal (D s) i :=
      Finset.sum_pos (fun i _ => Finset.prod_pos fun j _ => hD s j) Finset.univ_nonempty
    rw [idx, Nat.cast_prod, Real.log_prod (fun s _ => by exact_mod_cast (pos s).ne')]
    calc
      _ ≤ ∑ s : ↥V, ∑ _j : ↥(siteRows T n s.val), Real.log ((∑ i, wheelNormal (D s) i : ℕ):ℝ) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun j _ => logVolume_le_log_congruence _ _ (hS s j) (hD s)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, siteRows_card,
                             nsmul_eq_mul, ← Finset.mul_sum]

end RHLean.Analysis.AlpogeThin.SlotProjector
