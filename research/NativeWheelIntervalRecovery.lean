import «research.NativeWheelNNSComparison»
import RHLean.Analysis.NativePNTSquarePrefixTailReciprocalBound

/-! Integral recovery of the layer-constant signed test on the original sorted
prime cuts. The two endpoint thresholds price all its boundary jumps. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector.WheelNNS

def intervalTest {r : ℕ} (p : Fin (r+1) → ℕ) (L U : ℝ) (i : Fin (r+1)) : ℤ :=
  if L ≤ (p i:ℝ) ∧ (p i:ℝ) < U then 1 else 0

def changes {r : ℕ} (p : Fin (r+1) → ℕ) (L U : ℝ) : Finset (Fin r) :=
  Finset.univ.filter (fun j => intervalTest p L U j.succ ≠ intervalTest p L U j.castSucc)

private def threshold {r : ℕ} (p : Fin (r+1) → ℕ) (t : ℝ) : Finset (Fin r) :=
  Finset.univ.filter (fun j => (p j.castSucc:ℝ) < t ∧ t ≤ (p j.succ:ℝ))

private theorem threshold_unique {r : ℕ} (p : Fin (r+1) → ℕ) (hp : Monotone p) (t : ℝ) :
    (threshold p t).card ≤ 1 := by
  have same (i j : Fin r) (hi : i ∈ threshold p t) (hj : j ∈ threshold p t) : ¬i < j := by
    intro lt
    have ord : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact lt
    have pv : (p i.succ:ℝ) ≤ p j.castSucc := by exact_mod_cast hp ord
    exact (not_lt_of_ge ((Finset.mem_filter.mp hi).2.2.trans pv)) (Finset.mem_filter.mp hj).2.1
  exact Finset.card_le_one.mpr fun i hi j hj => le_antisymm (le_of_not_gt (same j i hj hi))
    (le_of_not_gt (same i j hi hj))

theorem changes_card {r : ℕ} (p : Fin (r+1) → ℕ) (hp : Monotone p) (L U : ℝ) :
    (changes p L U).card ≤ 2 := by
  have sub : changes p L U ⊆ threshold p L ∪ threshold p U := by
    intro j hj
    have diff := (Finset.mem_filter.mp hj).2
    have ord : (p j.castSucc:ℝ) ≤ p j.succ := by exact_mod_cast hp (show j.castSucc < j.succ from Fin.castSucc_lt_succ).le
    simp only [Finset.mem_union,threshold,Finset.mem_filter,Finset.mem_univ,true_and]
    by_contra! no
    have ll : L ≤ (p j.succ:ℝ) ↔ L ≤ (p j.castSucc:ℝ) := by constructor <;> intro m <;> grind
    have uu : (p j.succ:ℝ) < U ↔ (p j.castSucc:ℝ) < U := by constructor <;> intro m <;> grind
    exact diff (by simp only [intervalTest,ll,uu])
  exact (Finset.card_le_card sub).trans ((Finset.card_union_le ..).trans
    (Nat.add_le_add (threshold_unique p hp L) (threshold_unique p hp U)))

/-- A test multiple belongs to the single, simultaneous anchored recovery
image exactly when all its changed boundaries divide that multiple. -/
theorem interval_clearing_iff {r : ℕ} (p : Fin (r+1) → ℕ) (L U : ℝ) (d : Fin r → ℕ) (m : ℕ) :
    (∃ A, anchoredRecovery (fun j => (d j:ℤ)) A = fun i => (m:ℤ)*intervalTest p L U i) ↔
      ∀ j ∈ changes p L U, d j ∣ m := by
  rw [anchoredRecovery_image]
  have localIff (j : Fin r) :
      ((d j:ℤ) ∣ layerJump (fun i => (m:ℤ)*intervalTest p L U i) j) ↔
        (j ∈ changes p L U → d j ∣ m) := by
    by_cases left : L ≤ (p j.castSucc:ℝ) ∧ (p j.castSucc:ℝ) < U <;>
      by_cases right : L ≤ (p j.succ:ℝ) ∧ (p j.succ:ℝ) < U <;>
      simp [layerJump,changes,intervalTest,left,right]
  exact forall_congr' localIff

def clearing {r : ℕ} (p : Fin (r+1) → ℕ) (L U : ℝ) (d : Fin r → ℕ) : ℕ :=
  ∏ j ∈ changes p L U, d j

theorem interval_recovered {r : ℕ} (p : Fin (r+1) → ℕ) (L U : ℝ) (d : Fin r → ℕ) :
    ∃ A, anchoredRecovery (fun j => (d j:ℤ)) A =
      fun i => (clearing p L U d:ℤ)*intervalTest p L U i :=
  (interval_clearing_iff ..).2 fun _ hj => Finset.dvd_prod_of_mem _ hj

private theorem clearing_price {r : ℕ} (p : Fin (r+1) → ℕ) (hp : Monotone p) (L U : ℝ)
    (d : Fin r → ℕ) (hd : ∀ j, 0 < d j) (B : ℝ) (hB : 0 ≤ B)
    (price : ∀ j, Real.log (d j:ℝ) ≤ B) : Real.log (clearing p L U d:ℝ) ≤ 2*B := by
  rw [clearing,Nat.cast_prod,Real.log_prod (fun j _ => by exact_mod_cast (hd j).ne')]
  calc
    _ ≤ ∑ _j ∈ changes p L U, B := Finset.sum_le_sum fun j _ => price j
    _ = ((changes p L U).card:ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast changes_card p hp L U) hB

/-- Price all the original moving interval tests on the same sorted prime
block and at the same shift. The weighted sum of their actual clearing
logs uses the original cofactor weights. This does not identify a rowwise
clearing sum with a single simultaneous denominator. -/
theorem weighted_interval_price {r : ℕ} (p : Fin (r+1) → ℕ) (hp : StrictMono p) (c R : ℕ)
    (x a shift : ℝ) (hx : 1 ≤ x) (hprime : ∀ i, (p i).Prime) (hhigh : ∀ i, Real.sqrt x ≤ p i)
    (hpx : ∀ i, (p i:ℝ) ≤ x) :
    let d := fun j : Fin r => (p j.succ)^(⌊(c:ℝ)*x⌋₊/(p j.succ)-c)
    let v := fun k => PrincipalCofactor.oddCofactor k+shift
    (∑ k ∈ Finset.Ico 1 R, PrincipalCofactor.cellWeight k*
      Real.log (clearing p (a/(v k+1)) (a/v k) d:ℝ)) ≤
      2*((c:ℝ)*Real.sqrt x*Real.log x)*(1+Real.log R) := by
  intro d v
  let B := (c:ℝ)*Real.sqrt x*Real.log x
  have B0 : 0 ≤ B := mul_nonneg (by positivity) (Real.log_nonneg hx)
  have hd j : 0 < d j := pow_pos (hprime _).pos _
  have price (j) : Real.log (d j:ℝ) ≤ B :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hd j)).2
      (MeasuredCut.wheel_factor_le _ c x (hprime _) hx (hhigh _) (hpx _))
  have bound k := clearing_price p hp.monotone (a/(v k+1)) (a/v k) d hd B B0 price
  have weight (k : ℕ) (hk : k ∈ Finset.Ico 1 R) : PrincipalCofactor.cellWeight k ≤ 1/(k:ℝ) := by
    have pos : 0 < (k:ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hk).1
    exact one_div_le_one_div_of_le pos (by dsimp [PrincipalCofactor.oddCofactor]; linarith :
      (k:ℝ) ≤ 2*(PrincipalCofactor.oddCofactor k+1))
  calc
    _ ≤ ∑ k ∈ Finset.Ico 1 R, (1/(k:ℝ))*(2*B) := by
      refine Finset.sum_le_sum fun k hk => ?_
      exact (mul_le_mul_of_nonneg_left (bound k) (by dsimp [PrincipalCofactor.cellWeight,
        PrincipalCofactor.oddCofactor]; positivity)).trans (mul_le_mul_of_nonneg_right (weight k hk) (by positivity))
    _ = (2*B)*(∑ k ∈ Finset.Ico 1 R, 1/(k:ℝ)) := by rw [← Finset.sum_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((nativeTailReciprocalIco_le 1 R le_rfl).trans (harmonic_le_one_add_log R)) (by positivity)


/-- Exact archimedean squared norm of the recovered interval in the original
slot metric. The logarithmic price includes the same finite multiplier and
the actual size of the parent interval. Empty tests have zero energy. -/
theorem interval_energy {r : ℕ} (h : Fin (r+1) → ℝ) (v : ℝ)
    (hne : ∀ i, (bands h v i).Nonempty) (p : Fin (r+1) → ℕ) (L U : ℝ) (d : Fin r → ℕ)
    (hd : ∀ j, 0 < d j) :
    let m := clearing p L U d
    let J := Finset.univ.filter fun i => L ≤ (p i:ℝ) ∧ (p i:ℝ) < U
    let S := bands h v
    let E := slotEnergy S (fun i => (m:ℝ)*(intervalTest p L U i:ℝ))
    E = (m:ℝ)^2*(∑ i ∈ J, ((S i).card:ℝ)) ∧
      Real.log (1+E) ≤ 2*Real.log (m:ℝ)+Real.log (1+(⌊h 0⌋₊-⌈v⌉₊:ℕ):ℝ) := by
  intro m J S E
  have pos : 0 < m := Finset.prod_pos fun j _ => hd j
  have eq : E = (m:ℝ)^2*(∑ i ∈ J, ((S i).card:ℝ)) := by
    dsimp only [E,slotEnergy,J]
    rw [Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hit : L ≤ (p i:ℝ) ∧ (p i:ℝ) < U <;> simp [intervalTest,hit,mul_comm]
  refine ⟨eq, ?_⟩
  obtain ⟨emb,_⟩ := original_addresses h v hne
  have len : (∑ i, (S i).card) = ⌊h 0⌋₊-⌈v⌉₊ := by
    simpa only [Address,Fintype.card_sigma,Fintype.card_coe,Nat.card_Ioc] using Fintype.card_congr emb
  have subset : (∑ i ∈ J, ((S i).card:ℝ)) ≤ ((⌊h 0⌋₊-⌈v⌉₊:ℕ):ℝ) := by
    rw [← len,Nat.cast_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) (fun _ _ _ => Nat.cast_nonneg _)
  have m1 : (1:ℝ) ≤ m := by exact_mod_cast pos
  have e0 : 0 ≤ E := by rw [eq]; positivity
  have m2 : (1:ℝ) ≤ (m:ℝ)^2 := by nlinarith only [m1,sq_nonneg ((m:ℝ)-1)]
  have norm : 1+E ≤ (m:ℝ)^2*(1+((⌊h 0⌋₊-⌈v⌉₊:ℕ):ℝ)) := by
    rw [eq,mul_add,mul_one]
    exact add_le_add m2 (mul_le_mul_of_nonneg_left subset (sq_nonneg _))
  calc
    _ ≤ _ := Real.log_le_log (by linarith : 0 < 1+E) norm
    _ = _ := by rw [Real.log_mul (by positivity) (by positivity),Real.log_pow]; norm_num

end RHLean.Analysis.AlpogeThin.SlotProjector.WheelNNS
