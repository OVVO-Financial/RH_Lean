import «research.NYMAN_FLAT_TAPER_RETURN_20261104»

/-!
Uniform finite core of 20261117-analytic-1711-EST/CP1, independently accepted
in 20261117-referee-2013-EST/PR. All floor overlaps in both original bands
are retained. Sampling the three windows improves the paper constant.
Here N=12*K; no square-support or Mobius estimate is needed. This is a
profile LOWER bound, not a complete residual upper bound or an RH result.
-/

set_option autoImplicit false

noncomputable section
open Finset
open scoped BigOperators

namespace RHLean.Analysis

def nymanBandCount (a b m : Nat) : Nat :=
  ∑ k ∈ Ioc a b, m / k

def nymanTwoBandProfile (K m : Nat) : Real :=
  (nymanBandCount (6 * K) (8 * K) m : Real) -
    (nymanBandCount (10 * K) (12 * K) m : Real)

def nymanProfileWindow (K : Nat) : Finset Nat := Ioc (7 * K) (8 * K)

def nymanThreeProfileWindows (K : Nat) : Finset Nat :=
  nymanProfileWindow K ∪ nymanProfileWindow (4 * K) ∪
    nymanProfileWindow (16 * K)

def nymanWindowEnergy (s : Finset Nat) (f : Nat -> Real) : Real :=
  ∑ m ∈ s, f m ^ 2 / ((m : Real) * (m + 1))

def nymanThreeProfile (K : Nat) (t0 t1 t2 : Real) (m : Nat) : Real :=
  t0 * nymanTwoBandProfile K m + t1 * nymanTwoBandProfile (4 * K) m +
    t2 * nymanTwoBandProfile (16 * K) m

private theorem bandCount_zero (a b m : Nat) (hm : m <= a) :
    nymanBandCount a b m = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  exact Nat.div_eq_of_lt (by have := (Finset.mem_Ioc.mp hk).1; omega)

private theorem profile_zero (K m : Nat) (hm : m <= 6 * K) :
    nymanTwoBandProfile K m = 0 := by
  simp [nymanTwoBandProfile, bandCount_zero _ _ _ hm,
    bandCount_zero (10 * K) (12 * K) m (by omega)]

private theorem profile_self (K m : Nat) (hm : m ∈ nymanProfileWindow K) :
    nymanTwoBandProfile K m = (m : Real) - 6 * K := by
  have hmem := Finset.mem_Ioc.mp hm
  have hfirst : nymanBandCount (6 * K) (8 * K) m = m - 6 * K := by
    unfold nymanBandCount
    have hs : (∑ k ∈ Ioc (6 * K) m, m / k) =
        ∑ k ∈ Ioc (6 * K) (8 * K), m / k := by
      apply Finset.sum_subset
      · intro k hk
        have := Finset.mem_Ioc.mp hk
        exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
      · intro k hk hn
        have := Finset.mem_Ioc.mp hk
        have hmk : m < k := by
          simp only [Finset.mem_Ioc] at hn
          omega
        exact Nat.div_eq_of_lt hmk
    rw [← hs]
    calc
      _ = ∑ k ∈ Ioc (6 * K) m, (1 : Nat) := by
        apply Finset.sum_congr rfl
        intro k hk
        have := Finset.mem_Ioc.mp hk
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      _ = m - 6 * K := by simp
  rw [nymanTwoBandProfile, hfirst, bandCount_zero _ _ m (by omega)]
  push_cast [Nat.cast_sub (by omega : 6 * K <= m)]
  ring

private theorem profile_abs_le (K m : Nat) (hK : 1 <= K) :
    |nymanTwoBandProfile K m| <= m := by
  have hband (a b : Nat) (ha : 4 * K <= a) (hlen : b - a = 2 * K) :
      4 * K * nymanBandCount a b m <= 2 * K * m := by
    unfold nymanBandCount
    rw [Finset.mul_sum]
    calc
      _ <= ∑ k ∈ Ioc a b, m := by
        apply Finset.sum_le_sum
        intro k hk
        have hlow : 4 * K <= k := by have := Finset.mem_Ioc.mp hk; omega
        calc
          4 * K * (m / k) <= (m / k) * k := by nlinarith
          _ <= m := Nat.div_mul_le_self m k
      _ = 2 * K * m := by simp [hlen]
  have h1 := hband (6 * K) (8 * K) (by omega) (by omega)
  have h2 := hband (10 * K) (12 * K) (by omega) (by omega)
  have hs : nymanBandCount (6 * K) (8 * K) m +
      nymanBandCount (10 * K) (12 * K) m <= m := by nlinarith
  have hr : (nymanBandCount (6 * K) (8 * K) m : Real) +
      (nymanBandCount (10 * K) (12 * K) m : Real) <= m := by exact_mod_cast hs
  unfold nymanTwoBandProfile
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (nymanBandCount (6 * K) (8 * K) m),
    Nat.cast_nonneg (nymanBandCount (10 * K) (12 * K) m)]

/-- Exact transport to the original two-band correction floor, at N=12K.
The second amplitude is v-alpha, so both original bands are present. -/
theorem nyman_two_band_profile_source (K m : Nat) (hK : 1 <= K)
    (alpha v : Real) :
    nymanCorrectionFloor (12 * K)
      (fun k => if k ∈ Ioc (6 * K) (8 * K) then alpha
        else if k ∈ Ioc (10 * K) (12 * K) then v - alpha else 0) m =
      alpha * nymanTwoBandProfile K m +
        v * (nymanBandCount (10 * K) (12 * K) m : Real) := by
  have hsum (a b : Nat) (ha : 1 <= a) (hb : b <= 12 * K) (w : Real) :
      (∑ k ∈ Icc 2 (12 * K),
        (if k ∈ Ioc a b then w else 0) * ((m / k : Nat) : Real)) =
        w * (nymanBandCount a b m : Real) := by
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
    rw [← hs]
    simp only [nymanBandCount, Nat.cast_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp [hk]
  have hs1 := hsum (6 * K) (8 * K) (by omega) (by omega) alpha
  have hs2 := hsum (10 * K) (12 * K) (by omega) (by omega) (v - alpha)
  have he : nymanCorrectionFloor (12 * K)
      (fun k => if k ∈ Ioc (6 * K) (8 * K) then alpha
        else if k ∈ Ioc (10 * K) (12 * K) then v - alpha else 0) m =
      (∑ k ∈ Icc 2 (12 * K),
        (if k ∈ Ioc (6 * K) (8 * K) then alpha else 0) * ((m / k : Nat) : Real)) +
      ∑ k ∈ Icc 2 (12 * K),
        (if k ∈ Ioc (10 * K) (12 * K) then v - alpha else 0) *
          ((m / k : Nat) : Real) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h1 : k ∈ Ioc (6 * K) (8 * K)
    · have h2 : k ∉ Ioc (10 * K) (12 * K) := by
        simp only [Finset.mem_Ioc] at h1 ⊢
        omega
      simp [h1, h2]
    · simp [h1]
  rw [he, hs1, hs2, nymanTwoBandProfile]
  ring

private theorem energy_nonneg (s : Finset Nat) (f : Nat -> Real) :
    0 <= nymanWindowEnergy s f := by
  apply Finset.sum_nonneg
  intro m _
  positivity

private theorem window_sample (K : Nat) (hK : 1 <= K) (s : Finset Nat)
    (f : Nat -> Real) (c : Real) (hc : 0 <= c)
    (hsub : nymanProfileWindow K ⊆ s)
    (hbudget : 144 * nymanWindowEnergy s f <= (K : Real) * c ^ 2) :
    ∃ m ∈ nymanProfileWindow K, |f m| <= (K : Real) * c := by
  have hKr : (0 : Real) < K := by exact_mod_cast (show 0 < K by omega)
  have hcard : (nymanProfileWindow K).card = K := by
    simp [nymanProfileWindow, show 8 * K - 7 * K = K by omega]
  have hden (m : Nat) (hm : m ∈ nymanProfileWindow K) :
      0 < (m : Real) * (m + 1) ∧ (m : Real) * (m + 1) <= 144 * (K : Real)^2 := by
    have h := Finset.mem_Ioc.mp hm
    have hp : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
    have hu : (m : Real) <= 8 * K := by exact_mod_cast h.2
    have hk1 : (1 : Real) <= K := by exact_mod_cast hK
    constructor
    · positivity
    · nlinarith
  have he : (∑ m ∈ nymanProfileWindow K, f m ^ 2) <=
      144 * (K : Real)^2 * nymanWindowEnergy s f := by
    calc
      _ <= ∑ m ∈ nymanProfileWindow K,
          144 * (K : Real)^2 * (f m ^ 2 / ((m : Real) * (m + 1))) := by
        apply Finset.sum_le_sum
        intro m hm
        have hd := hden m hm
        calc
          _ = ((m : Real) * (m + 1)) *
              (f m ^ 2 / ((m : Real) * (m + 1))) := by
            field_simp [ne_of_gt hd.1]
          _ <= _ := mul_le_mul_of_nonneg_right hd.2 (by positivity)
      _ = 144 * (K : Real)^2 * nymanWindowEnergy (nymanProfileWindow K) f := by
        rw [nymanWindowEnergy, Finset.mul_sum]
      _ <= _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro m _ _
        positivity
  by_contra hn
  push_neg at hn
  have hpoint (m : Nat) (hm : m ∈ nymanProfileWindow K) :
      ((K : Real) * c)^2 < f m ^ 2 := by
    have ha := hn m hm
    nlinarith [sq_abs (f m), abs_nonneg (f m), mul_nonneg hKr.le hc]
  have hstrict : (∑ _m ∈ nymanProfileWindow K, ((K : Real) * c)^2) <
      ∑ m ∈ nymanProfileWindow K, f m ^ 2 := by
    apply Finset.sum_lt_sum
    · intro m hm
      exact (hpoint m hm).le
    · exact ⟨7 * K + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩,
        hpoint _ (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)⟩
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hstrict
  have hb := mul_le_mul_of_nonneg_left hbudget (sq_nonneg (K : Real))
  nlinarith

private theorem recover_coefficient (K m : Nat) (hK : 1 <= K)
    (hm : m ∈ nymanProfileWindow K) (t z r c a : Real)
    (hz : z = t * nymanTwoBandProfile K m + r)
    (hzc : |z| <= (K : Real) * c) (hra : |r| <= 8 * (K : Real) * a) :
    |t| <= c + 8 * a := by
  have hp := profile_self K m hm
  have hmlo : (K : Real) <= (m : Real) - 6 * K := by
    have h := (Finset.mem_Ioc.mp hm).1
    have : 7 * (K : Real) < m := by exact_mod_cast h
    linarith
  have hk : (0 : Real) < K := by exact_mod_cast (show 0 < K by omega)
  have htri : |t| * ((m : Real) - 6 * K) <= |z| + |r| := by
    have hh : t * nymanTwoBandProfile K m = z - r := by linarith
    calc
      _ = |t * nymanTwoBandProfile K m| := by
        rw [abs_mul, hp, abs_of_nonneg (by linarith)]
      _ = |z - r| := congrArg abs hh
      _ <= _ := abs_sub _ _
  nlinarith [mul_le_mul_of_nonneg_left hmlo (abs_nonneg t)]

/-- Uniform coercivity for the three complete original floor profiles.
At N=12K the denominator is 11,479,104, improving CP1's 49,647,168. -/
theorem nyman_three_profile_coercivity (K : Nat) (hK : 1 <= K)
    (t0 t1 t2 : Real) :
    (K : Real) / 956592 * (t0^2 + t1^2 + t2^2) <=
      nymanWindowEnergy (nymanThreeProfileWindows K) (nymanThreeProfile K t0 t1 t2) := by
  let E := nymanWindowEnergy (nymanThreeProfileWindows K) (nymanThreeProfile K t0 t1 t2)
  let c := Real.sqrt (144 * E / K)
  have hE : 0 <= E := energy_nonneg _ _
  have hk : (0 : Real) < K := by exact_mod_cast (show 0 < K by omega)
  have hc : 0 <= c := Real.sqrt_nonneg _
  have hcsq : (K : Real) * c^2 = 144 * E := by
    dsimp [c]
    rw [Real.sq_sqrt (by positivity)]
    field_simp [ne_of_gt hk]
  have hsample (q : Nat) (hq : K <= q)
      (hs : nymanProfileWindow q ⊆ nymanThreeProfileWindows K) :
      ∃ m ∈ nymanProfileWindow q,
        |nymanThreeProfile K t0 t1 t2 m| <= (q : Real) * c := by
    apply window_sample q (by omega) _ _ c hc hs
    have hqr : (K : Real) <= q := by exact_mod_cast hq
    dsimp [E] at hcsq
    nlinarith [mul_le_mul_of_nonneg_right hqr (sq_nonneg c)]
  have h0 : |t0| <= c := by
    obtain ⟨m, hm, hz⟩ := hsample K le_rfl (by
      intro m hm; exact Finset.mem_union_left _ (Finset.mem_union_left _ hm))
    have hu := (Finset.mem_Ioc.mp hm).2
    have h4 := profile_zero (4 * K) m (by omega)
    have h16 := profile_zero (16 * K) m (by omega)
    have hr := recover_coefficient K m hK hm t0
      (nymanThreeProfile K t0 t1 t2 m) 0 c 0
      (by simp [nymanThreeProfile, h4, h16]) hz (by simp)
    simpa using hr
  have h1 : |t1| <= 9 * c := by
    obtain ⟨m, hm, hz⟩ := hsample (4 * K) (by omega) (by
      intro m hm; exact Finset.mem_union_left _ (Finset.mem_union_right _ hm))
    have hu : (m : Real) <= 8 * (4 * K : Nat) := by
      exact_mod_cast (Finset.mem_Ioc.mp hm).2
    have h16 := profile_zero (16 * K) m (by have := (Finset.mem_Ioc.mp hm).2; omega)
    have hr : |t0 * nymanTwoBandProfile K m| <= 8 * (4 * K : Nat) * |t0| := by
      rw [abs_mul]
      have hp := (profile_abs_le K m hK).trans hu
      nlinarith [mul_le_mul_of_nonneg_left hp (abs_nonneg t0)]
    have ht := recover_coefficient (4 * K) m (by omega) hm t1
      (nymanThreeProfile K t0 t1 t2 m) (t0 * nymanTwoBandProfile K m) c |t0|
      (by simp [nymanThreeProfile, h16]; ring) hz hr
    linarith
  have h2 : |t2| <= 81 * c := by
    obtain ⟨m, hm, hz⟩ := hsample (16 * K) (by omega) (by
      intro m hm; exact Finset.mem_union_right _ hm)
    have hu : (m : Real) <= 8 * (16 * K : Nat) := by
      exact_mod_cast (Finset.mem_Ioc.mp hm).2
    have hr : |t0 * nymanTwoBandProfile K m + t1 * nymanTwoBandProfile (4 * K) m| <=
        8 * (16 * K : Nat) * (|t0| + |t1|) := by
      have hp0 := (profile_abs_le K m hK).trans hu
      have hp1 := (profile_abs_le (4 * K) m (by omega)).trans hu
      have ha := abs_add (t0 * nymanTwoBandProfile K m) (t1 * nymanTwoBandProfile (4 * K) m)
      rw [abs_mul, abs_mul] at ha
      nlinarith [mul_le_mul_of_nonneg_left hp0 (abs_nonneg t0),
        mul_le_mul_of_nonneg_left hp1 (abs_nonneg t1)]
    have ht := recover_coefficient (16 * K) m (by omega) hm t2
      (nymanThreeProfile K t0 t1 t2 m)
      (t0 * nymanTwoBandProfile K m + t1 * nymanTwoBandProfile (4 * K) m)
      c (|t0| + |t1|) (by unfold nymanThreeProfile; ring) hz hr
    linarith
  have hs0 : t0^2 <= c^2 := by nlinarith [sq_abs t0, abs_nonneg t0]
  have hs1 : t1^2 <= 81 * c^2 := by nlinarith [sq_abs t1, abs_nonneg t1]
  have hs2 : t2^2 <= 6561 * c^2 := by nlinarith [sq_abs t2, abs_nonneg t2]
  have hs := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hs0 hs1) hs2) hk.le
  change (K : Real) / 956592 * (t0^2 + t1^2 + t2^2) <= E
  nlinarith

/-- The restoration is retained explicitly. No profile-only domination of
the genuine residual is asserted. -/
theorem nyman_three_profile_restored_lower (K : Nat) (hK : 1 <= K)
    (t0 t1 t2 : Real) (r : Nat -> Real) :
    (K : Real) / 1913184 * (t0^2 + t1^2 + t2^2) -
        nymanWindowEnergy (nymanThreeProfileWindows K) r <=
      nymanWindowEnergy (nymanThreeProfileWindows K)
        (fun m => nymanThreeProfile K t0 t1 t2 m + r m) := by
  have hp := nyman_three_profile_coercivity K hK t0 t1 t2
  have hs : nymanWindowEnergy (nymanThreeProfileWindows K)
      (nymanThreeProfile K t0 t1 t2) / 2 -
      nymanWindowEnergy (nymanThreeProfileWindows K) r <=
      nymanWindowEnergy (nymanThreeProfileWindows K)
        (fun m => nymanThreeProfile K t0 t1 t2 m + r m) := by
    unfold nymanWindowEnergy
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro m _
    have hd : 0 <= (m : Real) * (m + 1) := by positivity
    have hb : nymanThreeProfile K t0 t1 t2 m ^ 2 / 2 - r m ^ 2 <=
        (nymanThreeProfile K t0 t1 t2 m + r m)^2 := by
      nlinarith [sq_nonneg (nymanThreeProfile K t0 t1 t2 m + 2 * r m)]
    have hh := div_le_div_of_nonneg_right hb hd
    convert hh using 1 <;> ring
  linarith

end RHLean.Analysis
