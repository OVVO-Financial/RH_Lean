import «research.NYMAN_FLAT_TAPER_RETURN_20261104»

/-!
Finite original-source core of 20261117-coordinator-2309-EST/DUAL1-DUAL2,
accepted with scope in 20261118-referee-0413-EST/DP. Exact floor pairing
improves the earlier-profile leakage from 5N/12 to N/4. Geometric recovery
then proves a uniform lower bound for every finite number of profiles.
The complete arithmetic upper estimate and the infinite return remain open.
-/

set_option autoImplicit false

noncomputable section
open Finset
open scoped BigOperators

namespace RHLean.Analysis

def nymanDualProfile (K m : Nat) : Real :=
  nymanCorrectionFloor (12 * K)
    (fun k => if k ∈ Ioc (6 * K) (8 * K) then 1
      else if k ∈ Ioc (10 * K) (12 * K) then -1 else 0) m

def nymanDualPair (f : Nat -> Real) (k : Nat) : Real :=
  f (3 * k) - (3 / 2 : Real) * f (2 * k)

def nymanDualSamples (K : Nat) : Finset Nat := Ioc (3 * K) (3 * K + K / 20)

def nymanDualWindow (K : Nat) : Finset Nat :=
  (nymanDualSamples K).image (fun k => 2 * k) ∪
    (nymanDualSamples K).image (fun k => 3 * k)

def nymanDualWindows (K n : Nat) : Finset Nat :=
  (range n).biUnion (fun i => nymanDualWindow (4 ^ i * K))

def nymanDualSum (K n : Nat) (t : Nat -> Real) (m : Nat) : Real :=
  ∑ i ∈ range n, t i * nymanDualProfile (4 ^ i * K) m

def nymanDualEnergy (s : Finset Nat) (f : Nat -> Real) : Real :=
  ∑ m ∈ s, f m ^ 2 / ((m : Real) * (m + 1))

private def band (a b m : Nat) : Real := ∑ k ∈ Ioc a b, ((m / k : Nat) : Real)

private theorem profile_source (K m : Nat) (hK : 1 <= K) :
    nymanDualProfile K m = band (6 * K) (8 * K) m - band (10 * K) (12 * K) m := by
  have hsum (a b : Nat) (ha : 1 <= a) (hb : b <= 12 * K) (w : Real) :
      (∑ k ∈ Icc 2 (12 * K),
        (if k ∈ Ioc a b then w else 0) * ((m / k : Nat) : Real)) = w * band a b m := by
    have hs : (∑ k ∈ Ioc a b,
        (if k ∈ Ioc a b then w else 0) * ((m / k : Nat) : Real)) =
        ∑ k ∈ Icc 2 (12 * K),
          (if k ∈ Ioc a b then w else 0) * ((m / k : Nat) : Real) := by
      apply Finset.sum_subset
      · intro k hk
        have := Finset.mem_Ioc.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro k _ hk
        simp [hk]
    rw [← hs, band, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp [hk]
  have he : nymanDualProfile K m =
      (∑ k ∈ Icc 2 (12 * K),
        (if k ∈ Ioc (6 * K) (8 * K) then (1 : Real) else 0) * (m / k : Nat)) +
      ∑ k ∈ Icc 2 (12 * K),
        (if k ∈ Ioc (10 * K) (12 * K) then (-1 : Real) else 0) * (m / k : Nat) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h1 : k ∈ Ioc (6 * K) (8 * K)
    · have h2 : k ∉ Ioc (10 * K) (12 * K) := by
        simp only [Finset.mem_Ioc] at h1 ⊢
        omega
      simp [h1, h2]
    · simp [h1]
  rw [he, hsum (6 * K) (8 * K) (by omega) (by omega),
    hsum (10 * K) (12 * K) (by omega) (by omega)]
  ring

private theorem floor_pair_bounds (m k : Nat) :
    -1 <= 2 * ((3 * m / k : Nat) : Real) - 3 * ((2 * m / k : Nat) : Real) ∧
    2 * ((3 * m / k : Nat) : Real) - 3 * ((2 * m / k : Nat) : Real) <= 2 := by
  by_cases hk : k = 0
  · simp [hk]
  have hp : 0 < k := by omega
  have h2 := Nat.div_add_mod (2 * m) k
  have h3 := Nat.div_add_mod (3 * m) k
  have r2 := Nat.mod_lt (2 * m) hp
  have r3 := Nat.mod_lt (3 * m) hp
  have hlo : 3 * (2 * m / k) <= 2 * (3 * m / k) + 1 := by
    by_contra hn
    have hh : 2 * (3 * m / k) + 2 <= 3 * (2 * m / k) := by omega
    nlinarith [Nat.mul_le_mul_right k hh]
  have hhi : 2 * (3 * m / k) <= 3 * (2 * m / k) + 2 := by
    by_contra hn
    have hh : 3 * (2 * m / k) + 3 <= 2 * (3 * m / k) := by omega
    nlinarith [Nat.mul_le_mul_right k hh]
  have hlor : 3 * ((2 * m / k : Nat) : Real) <= 2 * ((3 * m / k : Nat) : Real) + 1 := by
    exact_mod_cast hlo
  have hhir : 2 * ((3 * m / k : Nat) : Real) <= 3 * ((2 * m / k : Nat) : Real) + 2 := by
    exact_mod_cast hhi
  constructor <;> linarith

/-- Both original bands are retained. The bound is uniform in the output m. -/
theorem nyman_dual_profile_leakage (K m : Nat) (hK : 1 <= K) :
    |nymanDualPair (nymanDualProfile K) m| <= 3 * K := by
  have hband (a b : Nat) (hlen : b - a = 2 * K) :
      -2 * (K : Real) <= 2 * band a b (3 * m) - 3 * band a b (2 * m) ∧
      2 * band a b (3 * m) - 3 * band a b (2 * m) <= 4 * K := by
    have he : 2 * band a b (3 * m) - 3 * band a b (2 * m) =
        ∑ k ∈ Ioc a b, (2 * ((3 * m / k : Nat) : Real) - 3 * ((2 * m / k : Nat) : Real)) := by
      simp only [band, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [he]
    constructor
    · have hh := Finset.sum_le_sum (s := Ioc a b) (fun k _ => (floor_pair_bounds m k).1)
      simpa [hlen] using hh
    · have hh := Finset.sum_le_sum (s := Ioc a b) (fun k _ => (floor_pair_bounds m k).2)
      simpa [hlen] using hh
  have h1 := hband (6 * K) (8 * K) (by omega)
  have h2 := hband (10 * K) (12 * K) (by omega)
  rw [nymanDualPair, profile_source K (3 * m) hK, profile_source K (2 * m) hK, abs_le]
  constructor <;> linarith

private theorem band_zero (a b m : Nat) (hm : m <= a) : band a b m = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have := (Finset.mem_Ioc.mp hk).1
  simp [Nat.div_eq_of_lt (show m < k by omega)]

private theorem profile_zero (K m : Nat) (hK : 1 <= K) (hm : m <= 6 * K) :
    nymanDualProfile K m = 0 := by
  rw [profile_source K m hK, band_zero _ _ _ hm, band_zero _ _ _ (by omega)]
  ring

private theorem profile_ramp (K m : Nat) (hK : 1 <= K)
    (hlo : 6 * K <= m) (hhi : m <= 8 * K) :
    nymanDualProfile K m = (m : Real) - 6 * K := by
  have hs : band (6 * K) m m = band (6 * K) (8 * K) m := by
    apply Finset.sum_subset
    · intro k hk
      have := Finset.mem_Ioc.mp hk
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro k hk hn
      simp only [Finset.mem_Ioc] at hk hn
      simp [Nat.div_eq_of_lt (show m < k by omega)]
  rw [profile_source K m hK, ← hs, band_zero _ _ _ (by omega)]
  have he : band (6 * K) m m = ∑ _k ∈ Ioc (6 * K) m, (1 : Real) := by
    apply Finset.sum_congr rfl
    intro k hk
    have := Finset.mem_Ioc.mp hk
    rw [Nat.div_eq_of_lt_le (by omega) (by omega)]
    norm_num
  rw [he]
  simp only [Finset.sum_const, Finset.card_Ioc, nsmul_eq_mul, mul_one, sub_zero]
  rw [Nat.cast_sub hlo]
  push_cast
  ring

private theorem profile_plateau (K m : Nat) (hK : 1 <= K)
    (hlo : 8 * K <= m) (hhi : m <= 10 * K) : nymanDualProfile K m = 2 * K := by
  rw [profile_source K m hK, band_zero _ _ _ hhi]
  have he : band (6 * K) (8 * K) m = ∑ _k ∈ Ioc (6 * K) (8 * K), (1 : Real) := by
    apply Finset.sum_congr rfl
    intro k hk
    have := Finset.mem_Ioc.mp hk
    rw [Nat.div_eq_of_lt_le (by omega) (by omega)]
    norm_num
  rw [he]
  simp [show 8 * K - 6 * K = 2 * K by omega]

private theorem pair_self (K k : Nat) (hK : 1 <= K) (hk : k ∈ nymanDualSamples K) :
    (9 / 5 : Real) * K <= nymanDualPair (nymanDualProfile K) k := by
  have hm := Finset.mem_Ioc.mp hk
  have hd := Nat.div_mul_le_self K 20
  have hr := profile_ramp K (2 * k) hK (by omega) (by omega)
  have hp := profile_plateau K (3 * k) hK (by omega) (by omega)
  have hu : 20 * k <= 61 * K := by omega
  have hur : 20 * (k : Real) <= 61 * K := by exact_mod_cast hu
  rw [nymanDualPair, hp, hr]
  push_cast
  linarith

private theorem energy_nonneg (s : Finset Nat) (f : Nat -> Real) :
    0 <= nymanDualEnergy s f := by
  apply Finset.sum_nonneg
  intro m _
  positivity

private theorem paired_sample (K : Nat) (hK : 40 <= K) (s : Finset Nat)
    (f : Nat -> Real) (d : Real) (hd : 0 <= d) (hsub : nymanDualWindow K ⊆ s)
    (hbudget : 18720 * (K : Real) * nymanDualEnergy s f <= d ^ 2) :
    ∃ k ∈ nymanDualSamples K, |nymanDualPair f k| <= d := by
  have hkpos : (0 : Real) < K := by exact_mod_cast (show 0 < K by omega)
  have hdiv := Nat.div_mul_le_self K 20
  have hcard : (nymanDualSamples K).card = K / 20 := by simp [nymanDualSamples]
  have hcardlo : (K : Real) <= 40 * (nymanDualSamples K).card := by
    rw [hcard]
    exact_mod_cast (show K <= 40 * (K / 20) by omega)
  have hdis : Disjoint ((nymanDualSamples K).image (fun k => 2 * k))
      ((nymanDualSamples K).image (fun k => 3 * k)) := by
    apply Finset.disjoint_left.mpr
    intro m hm2 hm3
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp hm2
    obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp hm3
    have hma := Finset.mem_Ioc.mp ha
    have hmb := Finset.mem_Ioc.mp hb
    omega
  have hden (m : Nat) (hm : m ∈ nymanDualWindow K) :
      0 < (m : Real) * (m + 1) ∧ (m : Real) * (m + 1) <= 144 * (K : Real)^2 := by
    have hbounds : 0 < m ∧ m <= 10 * K := by
      rcases Finset.mem_union.mp hm with hm | hm
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
        have := Finset.mem_Ioc.mp hk
        omega
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
        have := Finset.mem_Ioc.mp hk
        omega
    have hp : (0 : Real) < m := by exact_mod_cast hbounds.1
    have hu : (m : Real) <= 10 * K := by exact_mod_cast hbounds.2
    have hk1 : (1 : Real) <= K := by exact_mod_cast (show 1 <= K by omega)
    constructor
    · positivity
    · nlinarith
  have he : (∑ m ∈ nymanDualWindow K, f m ^ 2) <=
      144 * (K : Real)^2 * nymanDualEnergy s f := by
    calc
      _ <= ∑ m ∈ nymanDualWindow K,
          144 * (K : Real)^2 * (f m ^ 2 / ((m : Real) * (m + 1))) := by
        apply Finset.sum_le_sum
        intro m hm
        have hh := hden m hm
        calc
          _ = ((m : Real) * (m + 1)) * (f m ^ 2 / ((m : Real) * (m + 1))) := by
            have hnz := mul_ne_zero_iff.mp (ne_of_gt hh.1)
            field_simp [hnz.1, hnz.2]
          _ <= _ := mul_le_mul_of_nonneg_right hh.2 (by positivity)
      _ = 144 * (K : Real)^2 * nymanDualEnergy (nymanDualWindow K) f := by
        rw [nymanDualEnergy, Finset.mul_sum]
      _ <= _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro m _ _
        positivity
  have hp : (∑ k ∈ nymanDualSamples K, nymanDualPair f k ^ 2) <=
      468 * (K : Real)^2 * nymanDualEnergy s f := by
    have hsq : (∑ k ∈ nymanDualSamples K, nymanDualPair f k ^ 2) <=
        (13 / 4 : Real) * ∑ k ∈ nymanDualSamples K, (f (2 * k)^2 + f (3 * k)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      unfold nymanDualPair
      nlinarith [sq_nonneg (3 * f (3 * k) + 2 * f (2 * k))]
    have hi : (∑ k ∈ nymanDualSamples K, (f (2 * k)^2 + f (3 * k)^2)) =
        ∑ m ∈ nymanDualWindow K, f m ^ 2 := by
      rw [Finset.sum_add_distrib, nymanDualWindow, Finset.sum_union hdis]
      rw [Finset.sum_image (by intro a _ b _ hab; omega),
        Finset.sum_image (by intro a _ b _ hab; omega)]
    rw [hi] at hsq
    nlinarith
  by_contra hn
  push Not at hn
  have hpoint (k : Nat) (hk : k ∈ nymanDualSamples K) : d^2 < nymanDualPair f k ^ 2 := by
    have hh := hn k hk
    nlinarith [sq_abs (nymanDualPair f k), abs_nonneg (nymanDualPair f k)]
  have hs : (∑ _k ∈ nymanDualSamples K, d^2) <
      ∑ k ∈ nymanDualSamples K, nymanDualPair f k ^ 2 := by
    apply Finset.sum_lt_sum
    · intro k hk; exact (hpoint k hk).le
    · have hm : 3 * K + 1 ∈ nymanDualSamples K := by
        apply Finset.mem_Ioc.mpr
        omega
      exact ⟨3 * K + 1, hm, hpoint _ hm⟩
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hb := mul_le_mul_of_nonneg_left hbudget hkpos.le
  have hc := mul_le_mul_of_nonneg_right hcardlo (sq_nonneg d)
  nlinarith

private theorem later_zero (K i j k : Nat) (hK : 1 <= K) (hij : i < j)
    (hk : k ∈ nymanDualSamples (4 ^ i * K)) :
    nymanDualPair (nymanDualProfile (4 ^ j * K)) k = 0 := by
  have hm := Finset.mem_Ioc.mp hk
  have hd := Nat.div_mul_le_self (4 ^ i * K) 20
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (show i + 1 <= j by omega)
  have hpow : 1 <= 4 ^ a := by have := pow_pos (show 0 < (4 : Nat) by omega) a; omega
  have hscale : 4 * (4 ^ i * K) <= 4 ^ j * K := by
    rw [ha, pow_add, pow_succ]
    nlinarith [Nat.mul_le_mul_left (4 ^ i * 4 * K) hpow]
  have hq : 1 <= 4 ^ j * K := by
    have := pow_pos (show 0 < (4 : Nat) by omega) j
    nlinarith
  rw [nymanDualPair, profile_zero _ _ hq (by omega), profile_zero _ _ hq (by omega)]
  ring

private theorem pair_prefix (K n i k : Nat) (hK : 1 <= K) (hi : i < n)
    (hk : k ∈ nymanDualSamples (4 ^ i * K)) (t : Nat -> Real) :
    nymanDualPair (nymanDualSum K n t) k =
      (∑ j ∈ range i, t j * nymanDualPair (nymanDualProfile (4 ^ j * K)) k) +
      t i * nymanDualPair (nymanDualProfile (4 ^ i * K)) k := by
  have hall : nymanDualPair (nymanDualSum K n t) k =
      ∑ j ∈ range n, t j * nymanDualPair (nymanDualProfile (4 ^ j * K)) k := by
    simp only [nymanDualPair, nymanDualSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : (∑ j ∈ range (i + 1), t j * nymanDualPair (nymanDualProfile (4 ^ j * K)) k) =
      ∑ j ∈ range n, t j * nymanDualPair (nymanDualProfile (4 ^ j * K)) k := by
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro j _ hj
      have hj' : i < j := by simp only [Finset.mem_range] at hj; omega
      rw [later_zero K i j k hK hj' hk, mul_zero]
  rw [hall, ← hs, Finset.sum_range_succ]

private theorem geometric_three (i : Nat) : 2 * (∑ j ∈ range i, (3 : Real)^j) <= 3^i := by
  induction i with
  | zero => norm_num
  | succ i ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith

private theorem geometric_nine (n : Nat) : (∑ i ∈ range n, (9 / 16 : Real)^i) <= 16 / 7 := by
  have he : (∑ i ∈ range n, (9 / 16 : Real)^i) = (16 / 7) * (1 - (9 / 16 : Real)^n) := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [he]
  nlinarith [pow_nonneg (show (0 : Real) <= 9 / 16 by norm_num) n]

/-- Uniform all-head coercivity on the original paired observation union.
This improves DUAL1's 121N/808704000 to 7N/40960000, with N=12K.
The empty family is included. No arithmetic upper estimate is assumed. -/
theorem nyman_all_profile_coercivity (K n : Nat) (hK : 40 <= K) (t : Nat -> Real) :
    (21 / 10240000 : Real) * K * (∑ i ∈ range n, t i ^ 2) <=
      nymanDualEnergy (nymanDualWindows K n) (nymanDualSum K n t) := by
  let E := nymanDualEnergy (nymanDualWindows K n) (nymanDualSum K n t)
  let c := Real.sqrt (E / (12 * K))
  have hE : 0 <= E := energy_nonneg _ _
  have hkpos : (0 : Real) < K := by exact_mod_cast (show 0 < K by omega)
  have hc : 0 <= c := Real.sqrt_nonneg _
  have hcsq : 12 * (K : Real) * c^2 = E := by
    dsimp [c]
    rw [Real.sq_sqrt (by positivity)]
    field_simp [ne_of_gt hkpos]
  have hcoeff : ∀ i, i < n -> |t i| <= 1600 * c * (3 / 4 : Real)^i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      have hq : 40 <= 4 ^ i * K := by
        have := pow_pos (show 0 < (4 : Nat) by omega) i
        nlinarith
      have hsub : nymanDualWindow (4 ^ i * K) ⊆ nymanDualWindows K n := by
        intro m hm
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hm⟩
      have hp2 : ((2 : Real)^i)^2 = (4 : Real)^i := by
        rw [← pow_mul, Nat.mul_comm i 2, pow_mul]
        norm_num
      have hb : 18720 * ((4 ^ i * K : Nat) : Real) * E <=
          (480 * (2 : Real)^i * K * c)^2 := by
        calc
          _ <= 19200 * ((4 ^ i * K : Nat) : Real) * E := by
            nlinarith [mul_nonneg (show (0 : Real) <= (4 ^ i * K : Nat) by positivity) hE]
          _ = _ := by
            rw [← hcsq]
            push_cast
            simp only [mul_pow, hp2]
            ring
      obtain ⟨k, hsample, hobs⟩ := paired_sample (4 ^ i * K) hq _ _
        (480 * (2 : Real)^i * K * c) (by positivity) hsub hb
      have hself := pair_self (4 ^ i * K) k (by omega) hsample
      have hpref := pair_prefix K n i k (by omega) hi hsample t
      have hrest : |∑ j ∈ range i, t j * nymanDualPair (nymanDualProfile (4 ^ j * K)) k| <=
          2400 * (K : Real) * c * 3^i := by
        calc
          _ <= ∑ j ∈ range i, |t j * nymanDualPair (nymanDualProfile (4 ^ j * K)) k| :=
            Finset.abs_sum_le_sum_abs _ _
          _ <= ∑ j ∈ range i, 4800 * (K : Real) * c * 3^j := by
            apply Finset.sum_le_sum
            intro j hj
            have hji := Finset.mem_range.mp hj
            have ht := ih j hji (by omega)
            have hqj : 1 <= 4 ^ j * K := by
              have := pow_pos (show 0 < (4 : Nat) by omega) j
              nlinarith
            have hl := nyman_dual_profile_leakage (4 ^ j * K) k hqj
            have hpow : (4 : Real)^j * (3 / 4 : Real)^j = 3^j := by
              rw [← mul_pow]
              norm_num
            rw [abs_mul]
            calc
              _ <= (1600 * c * (3 / 4 : Real)^j) * (3 * ((4 ^ j * K : Nat) : Real)) :=
                mul_le_mul ht hl (abs_nonneg _) (by positivity)
              _ = 4800 * (K : Real) * c * ((4 : Real)^j * (3 / 4 : Real)^j) := by
                push_cast
                ring
              _ = _ := by rw [hpow]
          _ = 4800 * (K : Real) * c * (∑ j ∈ range i, (3 : Real)^j) := by
            rw [Finset.mul_sum]
          _ <= _ := by
            have hh := mul_le_mul_of_nonneg_left (geometric_three i)
              (show 0 <= 2400 * (K : Real) * c by positivity)
            nlinarith
      have htri : |t i| * nymanDualPair (nymanDualProfile (4 ^ i * K)) k <=
          |nymanDualPair (nymanDualSum K n t) k| +
          |∑ j ∈ range i, t j * nymanDualPair (nymanDualProfile (4 ^ j * K)) k| := by
        have hn : 0 <= nymanDualPair (nymanDualProfile (4 ^ i * K)) k := by
          have : (0 : Real) <= (4 ^ i * K : Nat) := by positivity
          linarith
        calc
          _ = |t i * nymanDualPair (nymanDualProfile (4 ^ i * K)) k| := by
            rw [abs_mul, abs_of_nonneg hn]
          _ = |nymanDualPair (nymanDualSum K n t) k -
              ∑ j ∈ range i, t j * nymanDualPair (nymanDualProfile (4 ^ j * K)) k| := by
            congr 1
            linarith
          _ <= _ := abs_sub _ _
      have h23 : (2 : Real)^i <= 3^i := by gcongr <;> norm_num
      have hobs' := mul_le_mul_of_nonneg_right h23
        (show 0 <= 480 * (K : Real) * c by positivity)
      have hlow := mul_le_mul_of_nonneg_left hself (abs_nonneg (t i))
      have hpower : (4 : Real)^i * (3 / 4 : Real)^i = 3^i := by
        rw [← mul_pow]
        norm_num
      have hpos : 0 < (4 : Real)^i * K := by positivity
      push_cast at hlow
      have hh : (4 : Real)^i * K * |t i| <= 1600 * (K : Real) * c * 3^i := by
        nlinarith
      have heq : 1600 * (K : Real) * c * 3^i =
          ((4 : Real)^i * K) * (1600 * c * (3 / 4 : Real)^i) := by
        calc
          _ = 1600 * (K : Real) * c * ((4 : Real)^i * (3 / 4 : Real)^i) := by rw [hpower]
          _ = _ := by ring
      rw [heq] at hh
      exact (mul_le_mul_left hpos).mp hh
  have hs : (∑ i ∈ range n, t i^2) <= (40960000 / 7 : Real) * c^2 := by
    calc
      _ <= ∑ i ∈ range n, 2560000 * c^2 * (9 / 16 : Real)^i := by
        apply Finset.sum_le_sum
        intro i hi
        have ht := hcoeff i (Finset.mem_range.mp hi)
        have hp : ((3 / 4 : Real)^i)^2 = (9 / 16 : Real)^i := by
          rw [← pow_mul, Nat.mul_comm i 2, pow_mul]
          norm_num
        have hsq : t i^2 <= (1600 * c * (3 / 4 : Real)^i)^2 := by
          nlinarith [sq_abs (t i), abs_nonneg (t i),
            show 0 <= 1600 * c * (3 / 4 : Real)^i by positivity]
        simpa only [mul_pow, hp, show (1600 : Real)^2 = 2560000 by norm_num] using hsq
      _ = 2560000 * c^2 * (∑ i ∈ range n, (9 / 16 : Real)^i) := by rw [Finset.mul_sum]
      _ <= _ := by
        have hh := mul_le_mul_of_nonneg_left (geometric_nine n)
          (show 0 <= 2560000 * c^2 by positivity)
        nlinarith
  have hh := mul_le_mul_of_nonneg_left hs hkpos.le
  change (21 / 10240000 : Real) * K * (∑ i ∈ range n, t i^2) <= E
  nlinarith

/-- Every restoration interaction is paid; no profile-only upper claim is made. -/
theorem nyman_all_profile_restored_lower (K n : Nat) (hK : 40 <= K)
    (t : Nat -> Real) (r : Nat -> Real) :
    (21 / 20480000 : Real) * K * (∑ i ∈ range n, t i^2) -
        nymanDualEnergy (nymanDualWindows K n) r <=
      nymanDualEnergy (nymanDualWindows K n) (fun m => nymanDualSum K n t m + r m) := by
  have hp := nyman_all_profile_coercivity K n hK t
  have hs : nymanDualEnergy (nymanDualWindows K n) (nymanDualSum K n t) / 2 -
      nymanDualEnergy (nymanDualWindows K n) r <=
      nymanDualEnergy (nymanDualWindows K n) (fun m => nymanDualSum K n t m + r m) := by
    unfold nymanDualEnergy
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro m _
    have hd : 0 <= (m : Real) * (m + 1) := by positivity
    have hb : nymanDualSum K n t m ^ 2 / 2 - r m ^ 2 <= (nymanDualSum K n t m + r m)^2 := by
      nlinarith [sq_nonneg (nymanDualSum K n t m + 2 * r m)]
    have hh := div_le_div_of_nonneg_right hb hd
    convert hh using 1 <;> ring
  linarith

end RHLean.Analysis
