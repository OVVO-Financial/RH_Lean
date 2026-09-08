import RHLean.Analysis.EulerCRTRoughnessRecursion

/-!
# Finite counting on rough wheel intervals

The endpoint convention is `a < n <= b`.  The residue count and both
incomplete periods remain explicit; the estimate is uniform in the wheel.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- The reduced residue classes of a positive wheel, represented in `[0,W)`. -/
def roughWheelResidues (W : ℕ) : Finset ℕ :=
  (Finset.range W).filter fun r => Nat.Coprime r W

/-- The physical rough interval, with its lower endpoint excluded. -/
def roughWheelInterval (W a b : ℕ) : Finset ℕ :=
  (Finset.Ioc a b).filter fun n => Nat.Coprime n W

/-- Division and remainder inject the interval into its intersecting periods
times the reduced residue classes. -/
theorem card_roughWheelInterval_le_periods
    {W a b : ℕ} (hW : 0 < W) :
    (roughWheelInterval W a b).card ≤
      (b / W + 1 - a / W) * (roughWheelResidues W).card := by
  classical
  have hmaps : ∀ n ∈ roughWheelInterval W a b,
      (n / W, n % W) ∈
        (Finset.Icc (a / W) (b / W)).product (roughWheelResidues W) := by
    intro n hn
    obtain ⟨hnab, hnW⟩ := Finset.mem_filter.mp hn
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.mp hnab
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_Icc.mpr
        ⟨Nat.div_le_div_right han.le, Nat.div_le_div_right hnb⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (Nat.mod_lt n hW),
        by simpa only [Nat.coprime_mod_left_iff] using hnW⟩
  have hinj : Set.InjOn (fun n : ℕ => (n / W, n % W))
      (roughWheelInterval W a b : Set ℕ) := by
    intro m _hm n _hn hmn
    have hq := congrArg Prod.fst hmn
    have hr := congrArg Prod.snd hmn
    dsimp only at hq hr
    nlinarith [Nat.mod_add_div m W, Nat.mod_add_div n W]
  have hcard := Finset.card_le_card_of_injOn
    (fun n : ℕ => (n / W, n % W)) hmaps hinj
  simpa only [Finset.card_product, Nat.card_Icc] using hcard

/-- Actual finite counting: density times interval length plus at most two
incomplete residue periods.  In particular the error is displayed as a
function of the wheel, not hidden in an `O(1)` while the wheel varies. -/
theorem card_roughWheelInterval_le_density
    {W a b : ℕ} (hW : 0 < W) (hab : a ≤ b) :
    ((roughWheelInterval W a b).card : ℝ) ≤
      ((roughWheelResidues W).card : ℝ) / W * ((b : ℝ) - a) +
        2 * (roughWheelResidues W).card := by
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hq : a / W ≤ b / W := Nat.div_le_div_right hab
  have hcard : ((roughWheelInterval W a b).card : ℝ) ≤
      (((b / W : ℕ) : ℝ) + 1 - ((a / W : ℕ) : ℝ)) *
        (roughWheelResidues W).card := by
    have hcast : ((roughWheelInterval W a b).card : ℝ) ≤
        (((b / W + 1 - a / W) * (roughWheelResidues W).card : ℕ) : ℝ) := by
      exact_mod_cast card_roughWheelInterval_le_periods (a := a) (b := b) hW
    rw [Nat.cast_mul, Nat.cast_sub (by omega : a / W ≤ b / W + 1),
      Nat.cast_add, Nat.cast_one] at hcast
    exact hcast
  have ha : (a : ℝ) < ((a / W : ℕ) : ℝ) * W + W := by
    exact_mod_cast (show a < a / W * W + W by
      nlinarith [Nat.mod_add_div a W, Nat.mod_lt a hW])
  have hb : ((b / W : ℕ) : ℝ) * W ≤ (b : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self b W
  have hcancel : (((b : ℝ) - a) / W) * W = (b : ℝ) - a :=
    div_mul_cancel₀ _ hWR.ne'
  have hlength : ((b / W : ℕ) : ℝ) + 1 - ((a / W : ℕ) : ℝ) ≤
      ((b : ℝ) - a) / W + 2 := by
    nlinarith
  calc
    ((roughWheelInterval W a b).card : ℝ) ≤
        (((b / W : ℕ) : ℝ) + 1 - ((a / W : ℕ) : ℝ)) *
          (roughWheelResidues W).card := hcard
    _ ≤ (((b : ℝ) - a) / W + 2) * (roughWheelResidues W).card :=
      mul_le_mul_of_nonneg_right hlength (by positivity)
    _ = _ := by ring

/-- The signed interval is exactly the sum on the counted physical carrier. -/
theorem roughInterval_eq_sum_roughWheelInterval
    (W a b : ℕ) (hab : a ≤ b) :
    roughInterval W a b = ∑ n ∈ roughWheelInterval W a b, (μ n : ℤ) := by
  have hset : Finset.Ico (a + 1) (b + 1) = Finset.Ioc a b := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  unfold roughInterval roughMertens
  rw [← Finset.sum_Ico_eq_sub _ (Nat.add_le_add_right hab 1), hset]
  simp only [roughMoebius, roughWheelInterval, Finset.sum_filter]

/-- The first absolute value is taken after the exact wheel cancellation. -/
theorem abs_roughInterval_le_density
    {W a b : ℕ} (hW : 0 < W) (hab : a ≤ b) :
    |(roughInterval W a b : ℝ)| ≤
      ((roughWheelResidues W).card : ℝ) / W * ((b : ℝ) - a) +
        2 * (roughWheelResidues W).card := by
  rw [roughInterval_eq_sum_roughWheelInterval W a b hab]
  push_cast
  calc
    |∑ n ∈ roughWheelInterval W a b, (μ n : ℝ)| ≤
        ∑ n ∈ roughWheelInterval W a b, |(μ n : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ roughWheelInterval W a b, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    _ = ((roughWheelInterval W a b).card : ℝ) := by simp
    _ ≤ _ := card_roughWheelInterval_le_density hW hab

theorem roughWheelResidues_card_six : (roughWheelResidues 6).card = 2 := by
  decide

theorem roughWheelResidues_card_thirty : (roughWheelResidues 30).card = 8 := by
  decide

theorem roughWheelResidues_card_twoTen : (roughWheelResidues 210).card = 48 := by
  decide

/-- The requested `6`-rough finite count, including an explicit endpoint cost. -/
theorem card_roughWheelInterval_six (a b : ℕ) (hab : a ≤ b) :
    ((roughWheelInterval 6 a b).card : ℝ) ≤ ((b : ℝ) - a) / 3 + 4 := by
  have h := card_roughWheelInterval_le_density (W := 6) (by norm_num) hab
  rw [roughWheelResidues_card_six] at h
  norm_num at h
  linarith

end RHLean.Analysis
