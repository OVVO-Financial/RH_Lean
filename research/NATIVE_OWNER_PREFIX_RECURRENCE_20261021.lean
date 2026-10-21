import Mathlib

/-!
# Conditional full-prefix consumer for the original square-root owner Gram

The arithmetic hypothesis `OwnerBound` is explicit and remains unproved.
The finite norm includes 1: without this normalization the generic theorem
is false for unit-step sequences that vanish on the initial prefix.
The diagonal is paid by an all-integer harmonic sum; no prime density theorem
or external Mertens exponent is imported.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis.OwnerPrefix

def endpoint (R : ℕ) : ℕ := R ^ 2 - 1

def primeOwners (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (endpoint R)).filter Nat.Prime

def transport (M : ℕ → ℝ) (R : ℕ) : ℝ :=
  ∑ p ∈ primeOwners R, M (endpoint R / p)

def diagonal (M : ℕ → ℝ) (R : ℕ) : ℝ :=
  ∑ p ∈ primeOwners R, M (endpoint R / p) ^ 2

/-- The complete signed smooth/transport Gram, with the owner diagonal removed.
No value `M (endpoint R)` enters this definition. -/
def compensation (M A : ℕ → ℝ) (R : ℕ) : ℝ :=
  A R ^ 2 - 2 * A R * transport M R + transport M R ^ 2 - diagonal M R

def prefixValues (M : ℕ → ℝ) (B : ℕ) : Finset ℝ := by
  classical
  exact insert 1 ((Finset.Ico 1 B).image fun n => |M n| / Real.sqrt (n : ℝ))

theorem prefixValues_nonempty (M : ℕ → ℝ) (B : ℕ) :
    (prefixValues M B).Nonempty := by
  classical
  exact ⟨1, by simp [prefixValues]⟩

def prefixAmplitude (M : ℕ → ℝ) (B : ℕ) : ℝ :=
  (prefixValues M B).max' (prefixValues_nonempty M B)

theorem one_le_prefixAmplitude (M : ℕ → ℝ) (B : ℕ) :
    1 ≤ prefixAmplitude M B := by
  classical
  exact Finset.le_max' _ _ (by simp [prefixValues])

theorem prefixAmplitude_nonneg (M : ℕ → ℝ) (B : ℕ) :
    0 ≤ prefixAmplitude M B :=
  zero_le_one.trans (one_le_prefixAmplitude M B)

theorem abs_le_prefixAmplitude_mul_sqrt (M : ℕ → ℝ) {B n : ℕ}
    (hn : 1 ≤ n) (hnB : n < B) :
    |M n| ≤ prefixAmplitude M B * Real.sqrt (n : ℝ) := by
  classical
  have hmem : |M n| / Real.sqrt (n : ℝ) ∈ prefixValues M B := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨n, Finset.mem_Ico.mpr ⟨hn, hnB⟩, rfl⟩
  have hmax : |M n| / Real.sqrt (n : ℝ) ≤ prefixAmplitude M B :=
    Finset.le_max' _ _ hmem
  have hs : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  exact (div_le_iff₀ hs).mp hmax

theorem prefixAmplitude_le (M : ℕ → ℝ) {B : ℕ} {C : ℝ}
    (hC : 1 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n → n < B →
      |M n| ≤ C * Real.sqrt (n : ℝ)) :
    prefixAmplitude M B ≤ C := by
  classical
  unfold prefixAmplitude
  apply Finset.max'_le
  intro x hx
  change x ∈ insert 1 ((Finset.Ico 1 B).image
    fun n => |M n| / Real.sqrt (n : ℝ)) at hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · simpa only [hx] using hC
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hn1, hnB⟩ := Finset.mem_Ico.mp hn
    have hs : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
    exact (div_le_iff₀ hs).mpr (hbound n hn1 hnB)

theorem prefixAmplitude_mono (M : ℕ → ℝ) :
    Monotone (prefixAmplitude M) := by
  intro B C hBC
  apply prefixAmplitude_le M (one_le_prefixAmplitude M C)
  intro n hn hnB
  exact abs_le_prefixAmplitude_mul_sqrt M hn (hnB.trans_le hBC)

/-- The literal, unpadded finite maximum; its domain records nonemptiness. -/
def rawPrefixAmplitude (M : ℕ → ℝ) (B : ℕ) (hB : 2 ≤ B) : ℝ := by
  classical
  let s := (Finset.Ico 1 B).image fun n => |M n| / Real.sqrt (n : ℝ)
  have hs : s.Nonempty := by
    refine ⟨|M 1| / Real.sqrt (1 : ℝ), ?_⟩
    exact Finset.mem_image.mpr ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, by norm_num⟩
  exact s.max' hs

/-- For the actual Mertens normalization, adjoining 1 does not change E(B). -/
theorem prefixAmplitude_eq_raw (M : ℕ → ℝ) (B : ℕ) (hB : 2 ≤ B)
    (hunit : |M 1| = 1) :
    prefixAmplitude M B = rawPrefixAmplitude M B hB := by
  classical
  have hmem : (1 : ℝ) ∈ (Finset.Ico 1 B).image
      (fun n => |M n| / Real.sqrt (n : ℝ)) := by
    refine Finset.mem_image.mpr ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, ?_⟩
    simp [hunit]
  unfold prefixAmplitude rawPrefixAmplitude prefixValues
  simp only [Finset.insert_eq_of_mem hmem]

def OwnerBound (M A : ℕ → ℝ) (κ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R →
    compensation M A R ≤ C * (R : ℝ) ^ (κ + ε) *
      ((endpoint R : ℝ) + diagonal M R)

theorem square_eq_diagonal_add_compensation (M A : ℕ → ℝ)
    {R : ℕ} (hdecomp : M (endpoint R) = A R - transport M R) :
    M (endpoint R) ^ 2 = diagonal M R + compensation M A R := by
  rw [hdecomp]
  unfold compensation
  ring

theorem diagonal_nonneg (M : ℕ → ℝ) (R : ℕ) :
    0 ≤ diagonal M R := by
  unfold diagonal
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem owner_cofactor_bounds {R p : ℕ} (hR : 2 ≤ R)
    (hp : p ∈ primeOwners R) :
    1 ≤ endpoint R / p ∧ endpoint R / p < R := by
  have hpI := (Finset.mem_filter.mp hp).1
  obtain ⟨hRp, hpX⟩ := Finset.mem_Ioc.mp hpI
  have hp0 : 0 < p := by omega
  constructor
  · exact Nat.div_pos hpX hp0
  · apply (Nat.div_lt_iff_lt_mul hp0).mpr
    have hXlt : endpoint R < R ^ 2 := by
      unfold endpoint
      exact Nat.sub_lt (by positivity) (by norm_num)
    have hmul : R ^ 2 ≤ R * p := by
      simpa only [pow_two] using Nat.mul_le_mul_left R hRp.le
    exact hXlt.trans_le hmul

/-- The prime reciprocal sum is bounded by a full harmonic sum. -/
theorem owner_reciprocal_le_log (R : ℕ) (hR : 2 ≤ R) :
    (∑ p ∈ primeOwners R, (p : ℝ)⁻¹) ≤ 1 + 2 * Real.log (R : ℝ) := by
  have hsub : primeOwners R ⊆ Finset.Icc 1 (R ^ 2) := by
    intro p hp
    obtain ⟨hRp, hpX⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, hpX.trans (Nat.sub_le _ _)⟩
  have hsum : (∑ p ∈ primeOwners R, (p : ℝ)⁻¹) ≤
      ∑ p ∈ Finset.Icc 1 (R ^ 2), (p : ℝ)⁻¹ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hh : (∑ p ∈ Finset.Icc 1 (R ^ 2), (p : ℝ)⁻¹) ≤
      1 + 2 * Real.log (R : ℝ) := by
    have hh₀ : (∑ p ∈ Finset.Icc 1 (R ^ 2), (p : ℝ)⁻¹) ≤
        1 + Real.log ((R ^ 2 : ℕ) : ℝ) := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast] using harmonic_le_one_add_log (R ^ 2)
    have hlog : Real.log ((R ^ 2 : ℕ) : ℝ) = 2 * Real.log (R : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    rw [hlog] at hh₀
    exact hh₀
  exact hsum.trans hh

theorem diagonal_le_log (M : ℕ → ℝ) (R : ℕ) (hR : 2 ≤ R) :
    diagonal M R ≤ (endpoint R : ℝ) * prefixAmplitude M R ^ 2 *
      (1 + 2 * Real.log (R : ℝ)) := by
  have hterm : ∀ p ∈ primeOwners R,
      M (endpoint R / p) ^ 2 ≤
        (endpoint R : ℝ) * prefixAmplitude M R ^ 2 * (p : ℝ)⁻¹ := by
    intro p hp
    obtain ⟨hc1, hcR⟩ := owner_cofactor_bounds hR hp
    have hm := abs_le_prefixAmplitude_mul_sqrt M hc1 hcR
    have hsq : M (endpoint R / p) ^ 2 ≤
        prefixAmplitude M R ^ 2 * ((endpoint R / p : ℕ) : ℝ) := by
      have h := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (prefixAmplitude_nonneg M R) (Real.sqrt_nonneg _))).mpr hm
      simpa only [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using h
    have hp0 : 0 < (p : ℝ) := by
      have hRp := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      exact_mod_cast (show 0 < p by omega)
    have hdiv : ((endpoint R / p : ℕ) : ℝ) ≤ (endpoint R : ℝ) / (p : ℝ) := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast Nat.div_mul_le_self (endpoint R) p
    calc
      M (endpoint R / p) ^ 2 ≤
          prefixAmplitude M R ^ 2 * ((endpoint R / p : ℕ) : ℝ) := hsq
      _ ≤ prefixAmplitude M R ^ 2 * ((endpoint R : ℝ) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (sq_nonneg _)
      _ = (endpoint R : ℝ) * prefixAmplitude M R ^ 2 * (p : ℝ)⁻¹ := by ring
  calc
    diagonal M R ≤ ∑ p ∈ primeOwners R,
        (endpoint R : ℝ) * prefixAmplitude M R ^ 2 * (p : ℝ)⁻¹ :=
      Finset.sum_le_sum hterm
    _ = (endpoint R : ℝ) * prefixAmplitude M R ^ 2 *
        (∑ p ∈ primeOwners R, (p : ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ (endpoint R : ℝ) * prefixAmplitude M R ^ 2 *
        (1 + 2 * Real.log (R : ℝ)) :=
      mul_le_mul_of_nonneg_left (owner_reciprocal_le_log R hR) (by positivity)

theorem diagonal_le_rpow (M : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (R : ℕ) (hR : 2 ≤ R) :
    diagonal M R ≤ (1 + 2 / ε) * (endpoint R : ℝ) *
      (R : ℝ) ^ ε * prefixAmplitude M R ^ 2 := by
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
  have hpow : 1 ≤ (R : ℝ) ^ ε := Real.one_le_rpow hR1 hε.le
  have hlog := Real.log_le_rpow_div (Nat.cast_nonneg R) hε
  have hlogbound : 1 + 2 * Real.log (R : ℝ) ≤
      (1 + 2 / ε) * (R : ℝ) ^ ε := by
    calc
      1 + 2 * Real.log (R : ℝ) ≤
          (R : ℝ) ^ ε + 2 * ((R : ℝ) ^ ε / ε) := by linarith
      _ = (1 + 2 / ε) * (R : ℝ) ^ ε := by ring
  calc
    diagonal M R ≤ (endpoint R : ℝ) * prefixAmplitude M R ^ 2 *
        (1 + 2 * Real.log (R : ℝ)) := diagonal_le_log M R hR
    _ ≤ (endpoint R : ℝ) * prefixAmplitude M R ^ 2 *
        ((1 + 2 / ε) * (R : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left hlogbound (by positivity)
    _ = (1 + 2 / ε) * (endpoint R : ℝ) *
        (R : ℝ) ^ ε * prefixAmplitude M R ^ 2 := by ring

/-- One positive epsilon is spent on the owner premise and one on the harmonic
diagonal. Taking the square root gives precisely the displayed epsilon. -/
theorem endpoint_amplitude_bound (M A : ℕ → ℝ) {κ ε C : ℝ}
    (hκ : 0 ≤ κ) (hε : 0 < ε) (hC : 0 ≤ C)
    (hdecomp : ∀ R : ℕ, 2 ≤ R → M (endpoint R) = A R - transport M R)
    (howner : ∀ R : ℕ, 2 ≤ R → compensation M A R ≤
      C * (R : ℝ) ^ (κ + ε) * ((endpoint R : ℝ) + diagonal M R)) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℕ, 2 ≤ R →
      |M (endpoint R)| ≤
        K * (R : ℝ) ^ (κ / 2 + ε) * prefixAmplitude M R * (R : ℝ) := by
  let k : ℝ := 1 + 2 / ε
  have hk : 0 ≤ k := by dsimp [k]; positivity
  let K₀ : ℝ := (C + 1) * (1 + k)
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  let K : ℝ := K₀ + 1
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro R hR
  let e := prefixAmplitude M R
  let x : ℝ := endpoint R
  let d := diagonal M R
  let p : ℝ := (R : ℝ) ^ ε
  let q : ℝ := (R : ℝ) ^ (κ + ε)
  let l : ℝ := (R : ℝ) ^ (κ / 2 + ε)
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
  have hR0 : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 0 < R by omega)
  have he1 : 1 ≤ e := one_le_prefixAmplitude M R
  have he0 : 0 ≤ e := by linarith
  have he2 : 1 ≤ e ^ 2 := by
    simpa only [one_pow] using (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) he0).mpr he1
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have hd0 : 0 ≤ d := diagonal_nonneg M R
  have hp1 : 1 ≤ p := Real.one_le_rpow hR1 hε.le
  have hq1 : 1 ≤ q := Real.one_le_rpow hR1 (by linarith)
  have hl0 : 0 ≤ l := Real.rpow_nonneg (Nat.cast_nonneg R) _
  have hpe : 1 ≤ p * e ^ 2 := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ p * e ^ 2 := mul_le_mul hp1 he2 (by norm_num) (by linarith)
  have hxpe : x ≤ x * p * e ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hpe hx0
    nlinarith
  have hd : d ≤ k * x * p * e ^ 2 :=
    diagonal_le_rpow M hε R hR
  have hxd : x + d ≤ (1 + k) * x * p * e ^ 2 := by nlinarith
  have hdq : d ≤ q * d := by
    have h := mul_le_mul_of_nonneg_right hq1 hd0
    simpa only [one_mul] using h
  have hqp : q * p = l ^ 2 := by
    calc
      q * p = (R : ℝ) ^ ((κ + ε) + ε) :=
        (Real.rpow_add hR0 _ _).symm
      _ = (R : ℝ) ^ ((κ / 2 + ε) + (κ / 2 + ε)) := by congr 1; ring
      _ = l * l := Real.rpow_add hR0 _ _
      _ = l ^ 2 := by ring
  have hxR : x ≤ (R : ℝ) ^ 2 := by
    dsimp [x, endpoint]
    exact_mod_cast (Nat.sub_le (R ^ 2) 1)
  have henergy : M (endpoint R) ^ 2 ≤ K₀ * (l * e * (R : ℝ)) ^ 2 := by
    calc
      M (endpoint R) ^ 2 = d + compensation M A R :=
        square_eq_diagonal_add_compensation M A (hdecomp R hR)
      _ ≤ d + C * q * (x + d) := add_le_add (le_refl d) (howner R hR)
      _ ≤ (C + 1) * q * (x + d) := by
        nlinarith [hdq, mul_nonneg (by linarith : 0 ≤ q) hx0]
      _ ≤ (C + 1) * q * ((1 + k) * x * p * e ^ 2) :=
        mul_le_mul_of_nonneg_left hxd (by positivity)
      _ = K₀ * x * l ^ 2 * e ^ 2 := by rw [← hqp]; dsimp [K₀]; ring
      _ = x * (K₀ * l ^ 2 * e ^ 2) := by ring
      _ ≤ (R : ℝ) ^ 2 * (K₀ * l ^ 2 * e ^ 2) :=
        mul_le_mul_of_nonneg_right hxR (by positivity)
      _ = K₀ * (l * e * (R : ℝ)) ^ 2 := by ring
  have hKsq : K₀ ≤ K ^ 2 := by dsimp [K]; nlinarith [sq_nonneg K₀]
  have hsquared : M (endpoint R) ^ 2 ≤ (K * l * e * (R : ℝ)) ^ 2 := by
    calc
      M (endpoint R) ^ 2 ≤ K₀ * (l * e * (R : ℝ)) ^ 2 := henergy
      _ ≤ K ^ 2 * (l * e * (R : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hKsq (sq_nonneg _)
      _ = (K * l * e * (R : ℝ)) ^ 2 := by ring
  have hsquared' : |M (endpoint R)| ^ 2 ≤ (K * l * e * (R : ℝ)) ^ 2 := by
    simpa only [sq_abs] using hsquared
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hsquared'

/-- Unit increments give the exact integer interval cost. -/
theorem abs_sub_le_of_unit_step (M : ℕ → ℝ)
    (hstep : ∀ n : ℕ, 1 ≤ n → |M (n + 1) - M n| ≤ 1)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |M b - M a| ≤ ((b - a : ℕ) : ℝ) := by
  induction b with
  | zero => omega
  | succ b ih =>
      by_cases hlast : a = b + 1
      · subst a
        simp
      · have hab' : a ≤ b := by omega
        calc
          |M (b + 1) - M a| =
              |(M b - M a) + (M (b + 1) - M b)| := by congr 1; ring
          _ ≤ |M b - M a| + |M (b + 1) - M b| := abs_add_le _ _
          _ ≤ ((b - a : ℕ) : ℝ) + 1 :=
            add_le_add (ih hab') (hstep b (by omega))
          _ = (((b + 1) - a : ℕ) : ℝ) := by
            exact_mod_cast (show b - a + 1 = b + 1 - a by omega)

/-- The next completed square has root at most `2 sqrt(n)` and is at distance
at most `2 sqrt(n)`. This is used only for positive integer n. -/
theorem upper_square_geometry {n B : ℕ} (hn : 1 ≤ n) (hnB : n < B ^ 2) :
    let R := Nat.sqrt n + 1
    2 ≤ R ∧ R ≤ B ∧ n ≤ endpoint R ∧
      (R : ℝ) ≤ 2 * Real.sqrt (n : ℝ) ∧
      ((endpoint R - n : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  let r := Nat.sqrt n
  have hr1 : 1 ≤ r := Nat.sqrt_pos.mpr (by omega)
  have hr2 : r ^ 2 ≤ n := Nat.sqrt_le' n
  have hnnext : n < (r + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hR2 : 2 ≤ r + 1 := by omega
  have hRB : r + 1 ≤ B := by
    by_contra h
    have hBr : B ≤ r := by omega
    have hsq : B ^ 2 ≤ r ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hBr hBr
    omega
  have hsq : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
  have hendpoint : endpoint (r + 1) = r ^ 2 + 2 * r := by
    unfold endpoint
    rw [hsq]
    omega
  have hnend : n ≤ endpoint (r + 1) := by
    rw [hendpoint]
    rw [hsq] at hnnext
    omega
  have hgap : endpoint (r + 1) - n ≤ 2 * r := by rw [hendpoint]; omega
  have hr2R : (r : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hr2
  have hrsqrt : (r : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa only [Real.sqrt_sq_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) from Nat.cast_nonneg r)]
      using Real.sqrt_le_sqrt hr2R
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hRreal : ((r + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    push_cast
    linarith
  have hgapreal : ((endpoint (r + 1) - n : ℕ) : ℝ) ≤
      2 * Real.sqrt (n : ℝ) := by
    have h : ((endpoint (r + 1) - n : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by
      exact_mod_cast hgap
    linarith
  exact ⟨hR2, hRB, hnend, hRreal, hgapreal⟩

/-- Every original square endpoint controls the entire new prefix. -/
theorem prefix_amplitude_le_of_endpoint (M : ℕ → ℝ) {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hstep : ∀ n : ℕ, 1 ≤ n → |M (n + 1) - M n| ≤ 1)
    (hendpoint : ∀ R : ℕ, 2 ≤ R → |M (endpoint R)| ≤
      C * (R : ℝ) ^ a * prefixAmplitude M R * (R : ℝ))
    (B : ℕ) (hB : 2 ≤ B) :
    prefixAmplitude M (B ^ 2) ≤
      (2 * C + 2) * (B : ℝ) ^ a * prefixAmplitude M B := by
  let Z := (B : ℝ) ^ a * prefixAmplitude M B
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show 1 ≤ B by omega)
  have hBp : 1 ≤ (B : ℝ) ^ a := Real.one_le_rpow hB1 ha
  have hE := one_le_prefixAmplitude M B
  have hZ : 1 ≤ Z := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ Z := mul_le_mul hBp hE (by norm_num) (by positivity)
  have hZ0 : 0 ≤ Z := by linarith
  apply prefixAmplitude_le M
  · have hzbound : 1 ≤ (2 * C + 2) * Z := by
      nlinarith [mul_nonneg hC hZ0]
    simpa only [Z, mul_assoc] using hzbound
  · intro n hn hnB
    let R := Nat.sqrt n + 1
    obtain ⟨hR2, hRB, hnend, hRreal, hgapreal⟩ := upper_square_geometry hn hnB
    have hinterval := abs_sub_le_of_unit_step M hstep hn hnend
    have hdiff : |M n - M (endpoint R)| ≤ 2 * Real.sqrt (n : ℝ) := by
      rw [abs_sub_comm]
      exact hinterval.trans hgapreal
    have hRp : (R : ℝ) ^ a ≤ (B : ℝ) ^ a :=
      Real.rpow_le_rpow (Nat.cast_nonneg R) (by exact_mod_cast hRB) ha
    have hEp : prefixAmplitude M R ≤ prefixAmplitude M B :=
      prefixAmplitude_mono M hRB
    have hcoeff : C * (R : ℝ) ^ a * prefixAmplitude M R ≤ C * Z := by
      have hmul : (R : ℝ) ^ a * prefixAmplitude M R ≤
          (B : ℝ) ^ a * prefixAmplitude M B :=
        mul_le_mul hRp hEp (prefixAmplitude_nonneg M R)
          (Real.rpow_nonneg (Nat.cast_nonneg B) a)
      calc
        C * (R : ℝ) ^ a * prefixAmplitude M R =
            C * ((R : ℝ) ^ a * prefixAmplitude M R) := by ring
        _ ≤ C * ((B : ℝ) ^ a * prefixAmplitude M B) :=
          mul_le_mul_of_nonneg_left hmul hC
        _ = C * Z := rfl
    have hend : |M (endpoint R)| ≤ C * Z * (R : ℝ) :=
      (hendpoint R hR2).trans
        (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg R))
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    have hsZ : Real.sqrt (n : ℝ) ≤ Z * Real.sqrt (n : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hZ hs0
    calc
      |M n| = |M (endpoint R) + (M n - M (endpoint R))| := by congr 1; ring
      _ ≤ |M (endpoint R)| + |M n - M (endpoint R)| := abs_add_le _ _
      _ ≤ C * Z * (R : ℝ) + 2 * Real.sqrt (n : ℝ) := add_le_add hend hdiff
      _ ≤ C * Z * (2 * Real.sqrt (n : ℝ)) + 2 * Real.sqrt (n : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hRreal (mul_nonneg hC hZ0)) (le_refl _)
      _ ≤ C * Z * (2 * Real.sqrt (n : ℝ)) + 2 * (Z * Real.sqrt (n : ℝ)) := by
        linarith
      _ = ((2 * C + 2) * (B : ℝ) ^ a * prefixAmplitude M B) *
          Real.sqrt (n : ℝ) := by dsimp [Z]; ring

/-- Conditional full-prefix recurrence. The only arithmetic estimate assumed
is the displayed complete signed owner bound. -/
theorem prefix_amplitude_recurrence (M A : ℕ → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hdecomp : ∀ R : ℕ, 2 ≤ R → M (endpoint R) = A R - transport M R)
    (hstep : ∀ n : ℕ, 1 ≤ n → |M (n + 1) - M n| ≤ 1)
    (howner : OwnerBound M A κ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 2 ≤ B →
      prefixAmplitude M (B ^ 2) ≤
        C * (B : ℝ) ^ (κ / 2 + ε) * prefixAmplitude M B := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := howner ε hε
  obtain ⟨K, hK, hend⟩ := endpoint_amplitude_bound M A hκ hε hC.le hdecomp hbound
  refine ⟨2 * K + 2, by linarith, ?_⟩
  intro B hB
  exact prefix_amplitude_le_of_endpoint M (by linarith) hK.le hstep hend B hB

/-- Global real power envelope, including every positive integer. -/
def PowerBound (M : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |M n| ≤ C * (n : ℝ) ^ a

/-- Exponent-level control with arbitrary positive exponent loss. -/
def GrowthAtMost (M : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → PowerBound M (a + ε)

theorem prefixAmplitude_le_of_power (M : ℕ → ℝ) {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n → |M n| ≤ C * (n : ℝ) ^ (a + 1 / 2))
    (B : ℕ) (hB : 2 ≤ B) :
    prefixAmplitude M B ≤ (C + 1) * (B : ℝ) ^ a := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show 1 ≤ B by omega)
  have hBp : 1 ≤ (B : ℝ) ^ a := Real.one_le_rpow hB1 ha
  have hBp0 : 0 ≤ (B : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg B) a
  apply prefixAmplitude_le M
  · nlinarith [mul_nonneg hC hBp0]
  · intro n hn hnB
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnp : (n : ℝ) ^ a ≤ (B : ℝ) ^ a :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnB.le) ha
    calc
      |M n| ≤ C * (n : ℝ) ^ (a + 1 / 2) := hbound n hn
      _ = C * (n : ℝ) ^ a * Real.sqrt (n : ℝ) := by
        rw [Real.rpow_add hn0, Real.sqrt_eq_rpow]
        ring
      _ ≤ C * (B : ℝ) ^ a * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnp hC)
          (Real.sqrt_nonneg _)
      _ ≤ ((C + 1) * (B : ℝ) ^ a) * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hBp0)
          (Real.sqrt_nonneg _)

/-- A full-prefix recurrence transfers any available exponent theta >= 1/2.
The recurrence is required for every B, not merely for a sparse chain. -/
theorem growthAtMost_of_prefix_recurrence (M : ℕ → ℝ) {γ θ : ℝ}
    (hγ : 0 ≤ γ) (hθ : (1 : ℝ) / 2 ≤ θ)
    (hrec : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 2 ≤ B →
      prefixAmplitude M (B ^ 2) ≤
        C * (B : ℝ) ^ (γ + ε) * prefixAmplitude M B)
    (hgrowth : GrowthAtMost M θ) :
    GrowthAtMost M (1 / 4 + θ / 2 + γ / 2) := by
  intro ε hε
  obtain ⟨C, hC, hCB⟩ := hrec ε hε
  obtain ⟨D, hD, hDn⟩ := hgrowth ε hε
  let a : ℝ := θ - 1 / 2 + ε
  let s : ℝ := γ + ε + a
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hDa : ∀ n : ℕ, 1 ≤ n → |M n| ≤ D * (n : ℝ) ^ (a + 1 / 2) := by
    intro n hn
    have heq : a + 1 / 2 = θ + ε := by dsimp [a]; ring
    rw [heq]
    exact hDn n hn
  refine ⟨C * (D + 1) * (2 : ℝ) ^ s, by positivity, ?_⟩
  intro n hn
  let B := Nat.sqrt n + 1
  have hnB : n < B ^ 2 := Nat.lt_succ_sqrt' n
  obtain ⟨hB2, _, _, hBroot, _⟩ := upper_square_geometry hn hnB
  have hEB : prefixAmplitude M B ≤ (D + 1) * (B : ℝ) ^ a :=
    prefixAmplitude_le_of_power M ha hD hDa B hB2
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hscale : ((2 * Real.sqrt (n : ℝ)) ^ s) * Real.sqrt (n : ℝ) =
      (2 : ℝ) ^ s * (n : ℝ) ^ ((1 / 4 + θ / 2 + γ / 2) + ε) := by
    have heq : (1 / 2 : ℝ) * s + 1 / 2 =
        (1 / 4 + θ / 2 + γ / 2) + ε := by dsimp [s, a]; ring
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _)]
    simp only [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (Nat.cast_nonneg n), mul_assoc,
      ← Real.rpow_add hn0, heq]
  have hBs : (B : ℝ) ^ s ≤ (2 * Real.sqrt (n : ℝ)) ^ s :=
    Real.rpow_le_rpow (Nat.cast_nonneg B) hBroot hs
  calc
    |M n| ≤ prefixAmplitude M (B ^ 2) * Real.sqrt (n : ℝ) :=
      abs_le_prefixAmplitude_mul_sqrt M hn hnB
    _ ≤ (C * (B : ℝ) ^ (γ + ε) * prefixAmplitude M B) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right (hCB B hB2) (Real.sqrt_nonneg _)
    _ ≤ (C * (B : ℝ) ^ (γ + ε) * ((D + 1) * (B : ℝ) ^ a)) *
        Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEB (by positivity)) (Real.sqrt_nonneg _)
    _ = C * (D + 1) * (B : ℝ) ^ s * Real.sqrt (n : ℝ) := by
      have hpow : (B : ℝ) ^ s = (B : ℝ) ^ (γ + ε) * (B : ℝ) ^ a :=
        Real.rpow_add hB0 (γ + ε) a
      rw [hpow]
      ring
    _ ≤ C * (D + 1) * (2 * Real.sqrt (n : ℝ)) ^ s * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBs (by positivity)) (Real.sqrt_nonneg _)
    _ = (C * (D + 1) * (2 : ℝ) ^ s) *
        (n : ℝ) ^ ((1 / 4 + θ / 2 + γ / 2) + ε) := by
      calc
        C * (D + 1) * (2 * Real.sqrt (n : ℝ)) ^ s * Real.sqrt (n : ℝ) =
            (C * (D + 1)) *
              (((2 * Real.sqrt (n : ℝ)) ^ s) * Real.sqrt (n : ℝ)) := by ring
        _ = _ := by rw [hscale]; ring

/-- The quantitative exponent consumer. Its sole new arithmetic input is
`OwnerBound`; this theorem does not assert that hypothesis. -/
theorem growthAtMost_of_ownerBound (M A : ℕ → ℝ) {κ θ : ℝ}
    (hκ : 0 ≤ κ) (hθ : (1 : ℝ) / 2 ≤ θ)
    (hdecomp : ∀ R : ℕ, 2 ≤ R → M (endpoint R) = A R - transport M R)
    (hstep : ∀ n : ℕ, 1 ≤ n → |M (n + 1) - M n| ≤ 1)
    (howner : OwnerBound M A κ) (hgrowth : GrowthAtMost M θ) :
    GrowthAtMost M ((1 + 2 * θ + κ) / 4) := by
  have h := growthAtMost_of_prefix_recurrence M (γ := κ / 2) (by linarith) hθ
    (prefix_amplitude_recurrence M A hκ hdecomp hstep howner) hgrowth
  have heq : (1 : ℝ) / 4 + θ / 2 + (κ / 2) / 2 = (1 + 2 * θ + κ) / 4 := by ring
  simpa only [heq] using h

/-- Conditional calibration: a quarter-power owner loss gives 3/4 in one step
from a supplied 7/8 bound. Neither input is proved by this consumer. -/
theorem three_quarters_of_quarter_owner_bound (M A : ℕ → ℝ)
    (hdecomp : ∀ R : ℕ, 2 ≤ R → M (endpoint R) = A R - transport M R)
    (hstep : ∀ n : ℕ, 1 ≤ n → |M (n + 1) - M n| ≤ 1)
    (howner : OwnerBound M A (1 / 4)) (hgrowth : GrowthAtMost M (7 / 8)) :
    GrowthAtMost M (3 / 4) := by
  have h := growthAtMost_of_ownerBound M A (κ := 1 / 4) (θ := 7 / 8)
    (by norm_num) (by norm_num) hdecomp hstep howner hgrowth
  norm_num at h ⊢
  exact h

end RHLean.Analysis.OwnerPrefix
