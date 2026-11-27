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

end RHLean.Analysis.AlpogeThin.SlotProjector
