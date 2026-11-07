import RHLean.Analysis.DeterministicTGreenKuboComparison

/-!
The quantitative large-gcd tail from 20261107-analytic-1/GL2, independently
accepted by 20261107-referee-1. The original forward pair n+d is not clipped.
The proof uses a positive lattice majorant, not a favorable Mobius sign.
In fact X >= 1 suffices: the paper assumption h <= X is unnecessary here.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace RHLean.Analysis

def codivLargeGcdPairs (X h G : Nat) : Finset (Prod Nat Nat) :=
  ((Ico 1 h).product (Ico X (4 * X))).filter
    (fun p => G <= Nat.gcd p.2 p.1)

def codivLargeGcdCovariance (X h G : Nat) : Real :=
  (codivLargeGcdPairs X h G).sum (fun p =>
    2 * ((h : Real) - p.1) * realMoebiusStep p.2 * realMoebiusStep (p.2 + p.1))

def codivLargeGcdSupport (X h G : Nat) : Real :=
  (codivLargeGcdPairs X h G).sum (fun p =>
    2 * ((h : Real) - p.1) * realMoebiusStep p.2 ^ 2 *
      realMoebiusStep (p.2 + p.1) ^ 2)

private def gcdCoordinates (p : Prod Nat Nat) : Sigma (fun _ : Nat => Prod Nat Nat) :=
  Sigma.mk (Nat.gcd p.2 p.1) (p.1 / Nat.gcd p.2 p.1, p.2 / Nat.gcd p.2 p.1)

private def gcdExpand (v : Sigma (fun _ : Nat => Prod Nat Nat)) : Prod Nat Nat :=
  (v.1 * v.2.1, v.1 * v.2.2)

private theorem gcdExpand_coordinates (p : Prod Nat Nat) :
    gcdExpand (gcdCoordinates p) = p := by
  apply Prod.ext
  · exact Nat.mul_div_cancel' (Nat.gcd_dvd_right p.2 p.1)
  · exact Nat.mul_div_cancel' (Nat.gcd_dvd_left p.2 p.1)

private theorem gcdCoordinates_injective : Function.Injective gcdCoordinates := by
  intro a b hab
  calc
    a = gcdExpand (gcdCoordinates a) := (gcdExpand_coordinates a).symm
    _ = gcdExpand (gcdCoordinates b) := congrArg gcdExpand hab
    _ = b := gcdExpand_coordinates b

private theorem triangular_sum (h g q : Nat) :
    (Icc 1 q).sum (fun k => (h : Real) - (g : Real) * k) =
      (q : Real) * h - (g : Real) * q * (q + 1) / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

private theorem triangular_sum_nonneg (h g : Nat) :
    0 <= (Icc 1 (h / g)).sum (fun k => (h : Real) - (g : Real) * k) := by
  apply Finset.sum_nonneg
  intro k hk
  have hk' := (Finset.mem_Icc.mp hk).2
  have hmul : g * k <= h :=
    (Nat.mul_le_mul_left g hk').trans (Nat.mul_div_le h g)
  have : (g : Real) * k <= h := by exact_mod_cast hmul
  linarith

private theorem triangular_sum_le (h g : Nat) (hg : 0 < g) :
    (Icc 1 (h / g)).sum (fun k => (h : Real) - (g : Real) * k) <=
      (h : Real) ^ 2 / (2 * g) := by
  rw [triangular_sum]
  have hgR : (0 : Real) < g := by exact_mod_cast hg
  apply (le_div_iff₀ (by positivity : (0 : Real) < 2 * g)).mpr
  have hq : (0 : Real) <= (h / g : Nat) := by positivity
  nlinarith [sq_nonneg ((h : Real) - (g : Real) * (h / g : Nat)),
    mul_nonneg (sq_nonneg (g : Real)) hq]

private theorem reciprocal_square_tail (G h : Nat) (hG : 2 <= G) (hGh : G <= h) :
    (Ico G h).sum (fun g => (1 : Real) / (g : Real) ^ 2) <=
      1 / ((G : Real) - 1) - 1 / ((h : Real) - 1) := by
  induction h, hGh using Nat.le_induction with
  | base => simp
  | succ h hGh ih =>
    rw [Finset.sum_Ico_succ_top hGh]
    have hh : (1 : Real) < h := by exact_mod_cast (show 1 < h by omega)
    have hstep : (1 : Real) / (h : Real) ^ 2 <=
        1 / ((h : Real) - 1) - 1 / (h : Real) := by
      have h0 : (0 : Real) < h := by linarith
      have hm1 : (0 : Real) < (h : Real) - 1 := by linarith
      have he : 1 / ((h : Real) - 1) - 1 / (h : Real) =
          1 / ((h : Real) * ((h : Real) - 1)) := by
        field_simp [ne_of_gt h0, ne_of_gt hm1]
        ring
      rw [he]
      exact one_div_le_one_div_of_le (mul_pos h0 hm1) (by nlinarith)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    linarith

private theorem gcd_lattice_bound (X h G : Nat) (hX : 1 <= X)
    (hG : 2 <= G) (hGh : G <= h) :
    (codivLargeGcdPairs X h G).sum (fun p => 2 * ((h : Real) - p.1)) <=
      4 * X * (h : Real) ^ 2 / ((G : Real) - 1) := by
  let t := (Ico G h).sigma (fun g =>
    (Icc 1 (h / g)).product (Icc 1 (4 * X / g)))
  let w := fun v : Sigma (fun _ : Nat => Prod Nat Nat) =>
    2 * ((h : Real) - (v.1 : Real) * v.2.1)
  have hmap : (codivLargeGcdPairs X h G).image gcdCoordinates <= t := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hp, hgp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hd, hn⟩ := Finset.mem_product.mp hp
    obtain ⟨hd1, hdh⟩ := Finset.mem_Ico.mp hd
    obtain ⟨hnX, hn4X⟩ := Finset.mem_Ico.mp hn
    have hg0 : 0 < Nat.gcd p.2 p.1 := by omega
    have hgd : Nat.gcd p.2 p.1 <= p.1 :=
      Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right p.2 p.1)
    have hgn : Nat.gcd p.2 p.1 <= p.2 :=
      Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left p.2 p.1)
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Ico.mpr ⟨hgp, hgd.trans_lt hdh⟩
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · exact (Nat.le_div_iff_mul_le hg0).mpr (by simpa using hgd)
        · exact Nat.div_le_div_right (Nat.le_of_lt hdh)
      · apply Finset.mem_Icc.mpr
        constructor
        · exact (Nat.le_div_iff_mul_le hg0).mpr (by simpa using hgn)
        · exact Nat.div_le_div_right (Nat.le_of_lt hn4X)
  have hpos : forall v, v ∈ t -> 0 <= w v := by
    intro v hv
    obtain ⟨_, hk⟩ := Finset.mem_sigma.mp hv
    have hk' := (Finset.mem_Icc.mp (Finset.mem_product.mp hk).1).2
    have hm : v.1 * v.2.1 <= h :=
      (Nat.mul_le_mul_left v.1 hk').trans (Nat.mul_div_le h v.1)
    have hmR : (v.1 : Real) * v.2.1 <= h := by exact_mod_cast hm
    dsimp [w]
    linarith
  have hinj : (codivLargeGcdPairs X h G).sum (fun p => 2 * ((h : Real) - p.1)) <=
      t.sum w := by
    apply Finset.sum_le_sum_of_injOn gcdCoordinates gcdCoordinates_injective.injOn hmap
    · intro p _
      have he := congrArg Prod.fst (gcdExpand_coordinates p)
      change Nat.gcd p.2 p.1 * (p.1 / Nat.gcd p.2 p.1) = p.1 at he
      dsimp [w, gcdCoordinates]
      have heR : (Nat.gcd p.2 p.1 : Real) * (p.1 / Nat.gcd p.2 p.1 : Nat) = p.1 := by
        exact_mod_cast he
      rw [heR]
    · intro v hv _
      exact hpos v hv
  have heq : t.sum w = (Ico G h).sum (fun g =>
      (4 * X / g : Nat) * 2 *
        (Icc 1 (h / g)).sum (fun k => (h : Real) - (g : Real) * k)) := by
    dsimp [t, w]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro g _
    rw [Finset.sum_product]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hrow : forall g, g ∈ Ico G h ->
      (4 * X / g : Nat) * 2 *
        (Icc 1 (h / g)).sum (fun k => (h : Real) - (g : Real) * k) <=
      4 * X * (h : Real) ^ 2 * (1 / (g : Real) ^ 2) := by
    intro g hg
    have hg0 : 0 < g := by have := (Finset.mem_Ico.mp hg).1; omega
    have hgR : (0 : Real) < g := by exact_mod_cast hg0
    have hc : ((4 * X / g : Nat) : Real) <= 4 * X / (g : Real) := by
      apply (le_div_iff₀ hgR).mpr
      exact_mod_cast Nat.div_mul_le_self (4 * X) g
    have hs := triangular_sum_le h g hg0
    have hs0 := triangular_sum_nonneg h g
    calc
      _ <= (4 * X / (g : Real)) * 2 *
          ((h : Real) ^ 2 / (2 * g)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hc (by norm_num)) hs hs0 (by positivity)
      _ = _ := by field_simp [ne_of_gt hgR]
  calc
    _ <= t.sum w := hinj
    _ = _ := heq
    _ <= (Ico G h).sum (fun g => 4 * X * (h : Real) ^ 2 * (1 / (g : Real) ^ 2)) :=
      Finset.sum_le_sum hrow
    _ = 4 * X * (h : Real) ^ 2 *
        (Ico G h).sum (fun g => (1 : Real) / (g : Real) ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ <= 4 * X * (h : Real) ^ 2 * (1 / ((G : Real) - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have ht := reciprocal_square_tail G h hG hGh
      have hh : (1 : Real) < h := by exact_mod_cast (show 1 < h by omega)
      have : (0 : Real) <= 1 / ((h : Real) - 1) := by positivity
      linarith
    _ = _ := by ring

theorem codivLargeGcdCovariance_eq_original (X h G : Nat) :
    codivLargeGcdCovariance X h G =
      2 * (Ico 1 h).sum (fun d => ((h : Real) - d) *
        ((Ico X (4 * X)).filter (fun n => G <= Nat.gcd n d)).sum
          (fun n => realMoebiusStep n * realMoebiusStep (n + d))) := by
  unfold codivLargeGcdCovariance codivLargeGcdPairs
  simp only [Finset.sum_filter, Finset.mul_sum]
  refine (Finset.sum_finset_product _ (Ico 1 h) (fun _ => Ico X (4 * X))
    (fun _ => Finset.mem_product)).trans ?_
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem codivLargeGcdCovariance_abs_le_support (X h G : Nat) :
    |codivLargeGcdCovariance X h G| <= codivLargeGcdSupport X h G := by
  unfold codivLargeGcdCovariance codivLargeGcdSupport
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hd := (Finset.mem_Ico.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1).2
  have hdR : (p.1 : Real) <= h := by exact_mod_cast Nat.le_of_lt hd
  have hw : 0 <= 2 * ((h : Real) - p.1) := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hw]
  rcases ArithmeticFunction.moebius_eq_or p.2 with ha | ha | ha <;>
    rcases ArithmeticFunction.moebius_eq_or (p.2 + p.1) with hb | hb | hb <;>
    simp [realMoebiusStep, ha, hb]

theorem codivLargeGcdSupport_le_sharp (X h G : Nat) (hX : 1 <= X)
    (hG : 2 <= G) (hGh : G <= h) :
    codivLargeGcdSupport X h G <= 4 * X * (h : Real) ^ 2 / ((G : Real) - 1) := by
  apply le_trans _ (gcd_lattice_bound X h G hX hG hGh)
  apply Finset.sum_le_sum
  intro p hp
  have hd := (Finset.mem_Ico.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1).2
  have hdR : (p.1 : Real) <= h := by exact_mod_cast Nat.le_of_lt hd
  have hw : 0 <= 2 * ((h : Real) - p.1) := by positivity
  have ha := realMoebiusStep_sq_le_one p.2
  have hb := realMoebiusStep_sq_le_one (p.2 + p.1)
  calc
    _ <= 2 * ((h : Real) - p.1) * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left ha hw) hb (sq_nonneg _) (by positivity)
    _ = _ := by ring

theorem codivLargeGcdSupport_le (X h G : Nat) (hX : 1 <= X)
    (hG : 2 <= G) (hGh : G <= h) :
    codivLargeGcdSupport X h G <= 8 * X * (h : Real) ^ 2 / G := by
  apply (codivLargeGcdSupport_le_sharp X h G hX hG hGh).trans
  have hGR : (2 : Real) <= G := by exact_mod_cast hG
  apply (div_le_div_iff₀ (by linarith : (0 : Real) < (G : Real) - 1)
    (by linarith : (0 : Real) < G)).mpr
  nlinarith [mul_nonneg (by positivity : (0 : Real) <= X * (h : Real) ^ 2)
    (by linarith : (0 : Real) <= (G : Real) - 2)]

theorem codivLargeGcdCovariance_abs_le (X h G : Nat) (hX : 1 <= X)
    (hG : 2 <= G) (hGh : G <= h) :
    |codivLargeGcdCovariance X h G| <= 8 * X * (h : Real) ^ 2 / G :=
  (codivLargeGcdCovariance_abs_le_support X h G).trans
    (codivLargeGcdSupport_le X h G hX hG hGh)

#check codivLargeGcdCovariance_eq_original
#check codivLargeGcdCovariance_abs_le_support
#check codivLargeGcdSupport_le_sharp
#check codivLargeGcdSupport_le
#check codivLargeGcdCovariance_abs_le
#print axioms codivLargeGcdCovariance_eq_original
#print axioms codivLargeGcdCovariance_abs_le_support
#print axioms codivLargeGcdSupport_le_sharp
#print axioms codivLargeGcdSupport_le
#print axioms codivLargeGcdCovariance_abs_le

end RHLean.Analysis
