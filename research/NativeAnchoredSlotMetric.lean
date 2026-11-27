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
      simp [slotEnergy, A, apply_ite, mul_ite]
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
    (∑ i, ((S i).card:ℝ))/((S 0).card:ℝ) ≤ 4*x^3 := by
  classical
  intro S
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
  have hcount : 0 < ((S 0).card:ℝ) := by exact_mod_cast (hS 0).card_pos
  have sep : b/x^2 - 2 ≤ ((S 0).card:ℝ) := by
    linarith only [(spec 0).2.2.1, (spec 0).2.2.2.1]
  have h4 : 4 ≤ b/x^2 := (le_div_iff₀ hx2).2 hb
  have low : b ≤ (2*((S 0).card:ℝ))*x^2 := (div_le_iff₀ hx2).1 (by linarith only [h4,sep])
  apply (div_le_iff₀ hcount).2
  calc
    _ ≤ (x+1)*b := upper
    _ ≤ (2*x)*b := mul_le_mul_of_nonneg_right (by linarith) hb0.le
    _ ≤ (2*x)*((2*((S 0).card:ℝ))*x^2) := mul_le_mul_of_nonneg_left low (by positivity)
    _ = _ := by ring

/-- Cofactor of a measured star column matrix at each layer. -/
def wheelNormal {r : ℕ} (D : Fin (r+1) → ℕ) (i : Fin (r+1)) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, D j

def dualEnergy {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ) : ℝ :=
  ∑ i, (wheelNormal D i:ℝ)^2 / (S i).card

private theorem dualEnergy_pos {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
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
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (f := fun i => ((S i).card:ℝ)*(A i)^2)
      (g := fun i => (wheelNormal D i:ℝ)^2/(S i).card)
    · intro i _; positivity
    · intro i _; positivity
    · intro i _
      apply le_of_eq
      field_simp [(hw i).ne'] <;> ring
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
      field_simp [(hw i).ne'] <;> ring
    refine ⟨A, level.trans (div_mul_cancel₀ _ positive.ne'), energy.trans ?_⟩
    change (t/N)^2*N = t^2/N
    field_simp [show N ≠ 0 from positive.ne']

theorem wheelNormal_star {r : ℕ} (D : Fin (r+1) → ℕ) (j : Fin r) :
    ∑ i, (wheelNormal D i:ℤ)*starColumn D j i 0 = 0 := by
  have same (i) : (wheelNormal D i:ℤ)*(D i:ℤ) = (∏ k, (D k:ℤ)) := by
    simpa [wheelNormal] using Finset.prod_erase_mul (Finset.univ : Finset (Fin (r+1)))
      (fun k => (D k:ℤ)) (Finset.mem_univ i)
  simp [starColumn, mul_sub, mul_ite, Finset.sum_sub_distrib, same]

/-- The projected length is evaluated independently through the dual norm.
Its relative log is the opposite of the measured star log covolume. -/
def complementaryLog {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ) : ℝ :=
  (Real.log (1/dualEnergy S D) - Real.log (1/dualEnergy S (fun _ => 1)))/2

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
    field_simp [(hw i).ne'] <;> ring
  unfold complementaryLog logVolume
  rw [det D hD, det _ (fun _ => Nat.zero_lt_one), Real.log_mul hL.ne' (dualEnergy_pos S D hS hD).ne',
    Real.log_mul hL.ne' (dualEnergy_pos S _ hS (fun _ => Nat.zero_lt_one)).ne']
  simp only [one_div, Real.log_inv]
  ring

end RHLean.Analysis.AlpogeThin.SlotProjector
