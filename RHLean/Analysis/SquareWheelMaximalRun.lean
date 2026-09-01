import Mathlib
import RHLean.Analysis.PrimeWheelHarmonicCriterion
import RHLean.Analysis.PrimorialWheelMertensTransfer
import RHLean.Analysis.SquareWheelZeroModeElimination

/-!
# Maximal signed square runs inside primorial wheels

The complete square-block increments are the natural time steps of the Mertens
wave.  This file isolates the uniform RH-scale bound on every consecutive signed
run lying inside one synchronized primorial block and proves that it is exactly
the existing pinned primorial-wheel residual criterion.

No new analytic estimate is introduced here.  The reverse implication is
purely geometric: an arbitrary pinned residual is one first partial-square edge,
one consecutive run of complete squares, and one final partial-square edge.
Each edge is already at square-root scale by `|mu| <= 1` and the exact square-gap
geometry.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Uniform RH-scale energy bound for every nonempty consecutive run of complete
square-block increments whose two square endpoints lie in one primorial block.
The scale is the actual terminal square endpoint, never the wheel endpoint. -/
def SquareRunEnergyBoundedStatement : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    exists C : Real, 0 <= C /\
      forall k a b : Nat,
        1 <= a ->
        a <= b ->
        primorialBlockLower k <= squarePrefixEndpoint (a - 1) ->
        squarePrefixEndpoint b <= primorialBlockUpper k ->
        ‖sum j in Finset.Ico a (b + 1), canonicalTotalIncrement j‖ ^ 2 <=
          C * Real.rpow (((squarePrefixEndpoint b + 1 : Nat) : Real))
            (1 + epsilon)

private theorem maximalRun_norm_sq_add_le_two (x y : Complex) :
    ‖x + y‖ ^ 2 <= 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 <= ‖x‖ := norm_nonneg x
  have hy : 0 <= ‖y‖ := norm_nonneg y
  have hxy : 0 <= ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem squarePrefixEndpoint_strictMono_of_lt
    {a b : Nat} (hab : a < b) :
    squarePrefixEndpoint a < squarePrefixEndpoint b := by
  have hsquare : (a + 1) ^ 2 < (b + 1) ^ 2 :=
    Nat.pow_lt_pow_left (by omega) (by norm_num : 2 != 0)
  have ha := squarePrefixEndpoint_add_one a
  have hb := squarePrefixEndpoint_add_one b
  omega

private theorem squarePrefixEndpoint_mono_of_le
    {a b : Nat} (hab : a <= b) :
    squarePrefixEndpoint a <= squarePrefixEndpoint b := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (squarePrefixEndpoint_strictMono_of_lt hlt).le

/-- Every natural prefix is bracketed by two consecutive complete-square
endpoints. -/
private theorem maximalRun_square_sample_bracket (x : Nat) :
    exists n : Nat,
      squarePrefixEndpoint n <= x /\ x < squarePrefixEndpoint (n + 1) := by
  refine ⟨Nat.sqrt (x + 1) - 1, ?_, ?_⟩
  · have h1 : Nat.sqrt (x + 1) ^ 2 <= x + 1 := Nat.sqrt_le' (x + 1)
    have hr1 : 1 <= Nat.sqrt (x + 1) := Nat.sqrt_pos.mpr (by omega)
    have h2 := squarePrefixEndpoint_add_one (Nat.sqrt (x + 1) - 1)
    have h3 : Nat.sqrt (x + 1) - 1 + 1 = Nat.sqrt (x + 1) := by omega
    rw [h3] at h2
    omega
  · have h1 : x + 1 < (Nat.sqrt (x + 1) + 1) ^ 2 := Nat.lt_succ_sqrt' (x + 1)
    have hr1 : 1 <= Nat.sqrt (x + 1) := Nat.sqrt_pos.mpr (by omega)
    have h2 := squarePrefixEndpoint_add_one (Nat.sqrt (x + 1) - 1 + 1)
    have h3 : Nat.sqrt (x + 1) - 1 + 1 + 1 = Nat.sqrt (x + 1) + 1 := by omega
    rw [h3] at h2
    omega

private theorem linear_scale_le_rpow
    {epsilon : Real} (hepsilon : 0 < epsilon) (x : Nat) :
    (((x + 1 : Nat) : Real)) <=
      Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) := by
  have hbase : (1 : Real) <= (((x + 1 : Nat) : Real)) := by positivity
  have h := Real.rpow_le_rpow_of_exponent_le hbase (by linarith : (1 : Real) <= 1 + epsilon)
  simpa using h

private theorem rpow_endpoint_mono
    {epsilon : Real} (hepsilon : 0 < epsilon) {a b : Nat} (hab : a <= b) :
    Real.rpow (((a + 1 : Nat) : Real)) (1 + epsilon) <=
      Real.rpow (((b + 1 : Nat) : Real)) (1 + epsilon) := by
  have hbase : (((a + 1 : Nat) : Real)) <= (((b + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.add_le_add_right hab 1
  exact Real.rpow_le_rpow (by positivity) hbase (by linarith)

/-- A pinned residual bound controls every complete signed square run, with no
loss of scale and only an absolute constant loss. -/
theorem squareRunEnergyBounded_of_primorialResidualBounded
    (hres : PrimeWheelResidualBoundedStatement primorialWheelFamily) :
    SquareRunEnergyBoundedStatement := by
  intro epsilon hepsilon
  rcases hres epsilon hepsilon with ⟨C, hC, hbound⟩
  refine ⟨4 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro k a b ha hab hleftLower hrightUpper
  have hindex : a - 1 < b := by omega
  have hendpoint : squarePrefixEndpoint (a - 1) < squarePrefixEndpoint b :=
    squarePrefixEndpoint_strictMono_of_lt hindex
  have hleftUpper : squarePrefixEndpoint (a - 1) <= primorialBlockUpper k :=
    hendpoint.le.trans hrightUpper
  have hrightLower : primorialBlockLower k < squarePrefixEndpoint b :=
    lt_of_le_of_lt hleftLower hendpoint
  have hright := hbound k (squarePrefixEndpoint b) hrightLower hrightUpper
  have hleft :
      ‖(((primorialWheelSystem k).residual (squarePrefixEndpoint (a - 1)) : Int) : Complex)‖ ^ 2 <=
        C * Real.rpow (((squarePrefixEndpoint b + 1 : Nat) : Real)) (1 + epsilon) := by
    by_cases hstrict : primorialBlockLower k < squarePrefixEndpoint (a - 1)
    · have hraw := hbound k (squarePrefixEndpoint (a - 1)) hstrict hleftUpper
      have hmono := rpow_endpoint_mono hepsilon hendpoint.le
      exact hraw.trans (mul_le_mul_of_nonneg_left hmono hC)
    · have heq : primorialBlockLower k = squarePrefixEndpoint (a - 1) := by omega
      rw [← heq]
      have hblock : primorialBlockLower k <= primorialBlockUpper k :=
        hleftLower.trans hleftUpper
      rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
        k le_rfl hblock]
      simp
  have hright' :
      ‖(((primorialWheelSystem k).residual (squarePrefixEndpoint b) : Int) : Complex)‖ ^ 2 <=
        C * Real.rpow (((squarePrefixEndpoint b + 1 : Nat) : Real)) (1 + epsilon) := hright
  rw [RHLean.Proof.sum_canonicalTotalIncrement_Ico_eq_primorialResidual_sub
    k a b ha (by omega) hleftLower hleftUpper hrightLower.le hrightUpper]
  have htwo := maximalRun_norm_sq_add_le_two
    ((((primorialWheelSystem k).residual (squarePrefixEndpoint b) : Int) : Complex))
    (-((((primorialWheelSystem k).residual (squarePrefixEndpoint (a - 1)) : Int) : Complex)))
  simp only [add_neg_eq_sub, norm_neg] at htwo
  calc
    ‖(((primorialWheelSystem k).residual (squarePrefixEndpoint b) : Int) : Complex) -
        (((primorialWheelSystem k).residual (squarePrefixEndpoint (a - 1)) : Int) : Complex)‖ ^ 2 <=
      2 * ‖(((primorialWheelSystem k).residual (squarePrefixEndpoint b) : Int) : Complex)‖ ^ 2 +
        2 * ‖(((primorialWheelSystem k).residual (squarePrefixEndpoint (a - 1)) : Int) : Complex)‖ ^ 2 := htwo
    _ <= 2 * (C * Real.rpow (((squarePrefixEndpoint b + 1 : Nat) : Real)) (1 + epsilon)) +
        2 * (C * Real.rpow (((squarePrefixEndpoint b + 1 : Nat) : Real)) (1 + epsilon)) := by
          gcongr
    _ = (4 * C) * Real.rpow (((squarePrefixEndpoint b + 1 : Nat) : Real)) (1 + epsilon) := by ring

/-- If a wheel starts and ends before the next complete square, its whole pinned
residual is one square-root-scale edge. -/
private theorem shortWheelResidual_sq_lt_nine
    {k m x : Nat}
    (hmLower : squarePrefixEndpoint m <= primorialBlockLower k)
    (hlower : primorialBlockLower k < x)
    (hright : x < squarePrefixEndpoint (m + 1))
    (hupper : x <= primorialBlockUpper k) :
    ‖(((primorialWheelSystem k).residual x : Int) : Complex)‖ ^ 2 <
      9 * (((x + 1 : Nat) : Real)) := by
  have hxLower : primorialBlockLower k <= x := hlower.le
  rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
    k hxLower hupper]
  have hnorm :
      ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ <=
        (((x - primorialBlockLower k : Nat) : Real)) :=
    norm_mertensSummatory_sub_le (primorialBlockLower k) x hlower.le
  have hgapNat : x - primorialBlockLower k < 2 * m + 3 := by
    have hgap := sub_squarePrefixEndpoint_lt_gap m x
      (hmLower.trans hlower.le) hright
    omega
  have hgapReal : (((x - primorialBlockLower k : Nat) : Real)) <
      (((2 * m + 3 : Nat) : Real)) := by exact_mod_cast hgapNat
  have hsqGapNat := squareGap_sq_le_nine_mul_succ m x (hmLower.trans hlower.le)
  have hsqGapReal : (((2 * m + 3 : Nat) : Real)) ^ 2 <=
      9 * (((x + 1 : Nat) : Real)) := by exact_mod_cast hsqGapNat
  have h0 : 0 <= ‖mertensSummatory x - mertensSummatory (primorialBlockLower k)‖ := norm_nonneg _
  have h1 : 0 <= (((x - primorialBlockLower k : Nat) : Real)) := by positivity
  have h2 : 0 <= (((2 * m + 3 : Nat) : Real)) := by positivity
  nlinarith

/-- The first partial square from the wheel anchor to the first complete square
inside the wheel has square-root energy. -/
private theorem firstWheelEdge_sq_le_nine
    {k m x : Nat}
    (hmLower : squarePrefixEndpoint m <= primorialBlockLower k)
    (hLowerNext : primorialBlockLower k < squarePrefixEndpoint (m + 1))
    (hnextx : squarePrefixEndpoint (m + 1) <= x)
    (hupper : x <= primorialBlockUpper k) :
    ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
        mertensSummatory (primorialBlockLower k)‖ ^ 2 <=
      9 * (((x + 1 : Nat) : Real)) := by
  have hnorm :
      ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
          mertensSummatory (primorialBlockLower k)‖ <=
        (((squarePrefixEndpoint (m + 1) - primorialBlockLower k : Nat) : Real)) :=
    norm_mertensSummatory_sub_le (primorialBlockLower k)
      (squarePrefixEndpoint (m + 1)) hLowerNext.le
  have hgapNat : squarePrefixEndpoint (m + 1) - primorialBlockLower k <= 2 * m + 3 := by
    rw [squarePrefixEndpoint_succ_eq_add_gap m]
    omega
  have hgapReal :
      (((squarePrefixEndpoint (m + 1) - primorialBlockLower k : Nat) : Real)) <=
        (((2 * m + 3 : Nat) : Real)) := by exact_mod_cast hgapNat
  have hmx : squarePrefixEndpoint m <= x := hmLower.trans hLowerNext.le.trans hnextx
  have hsqGapNat := squareGap_sq_le_nine_mul_succ m x hmx
  have hsqGapReal : (((2 * m + 3 : Nat) : Real)) ^ 2 <=
      9 * (((x + 1 : Nat) : Real)) := by exact_mod_cast hsqGapNat
  have h0 : 0 <= ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
      mertensSummatory (primorialBlockLower k)‖ := norm_nonneg _
  have h1 : 0 <= (((squarePrefixEndpoint (m + 1) - primorialBlockLower k : Nat) : Real)) := by positivity
  have h2 : 0 <= (((2 * m + 3 : Nat) : Real)) := by positivity
  nlinarith

/-- A maximal signed square-run bound controls every pinned primorial residual.
The proof uses only the first/last square-gap edges and the exact run telescope. -/
theorem primorialResidualBounded_of_squareRunEnergyBounded
    (hrun : SquareRunEnergyBoundedStatement) :
    PrimeWheelResidualBoundedStatement primorialWheelFamily := by
  intro epsilon hepsilon
  rcases hrun epsilon hepsilon with ⟨C, hC, hrunBound⟩
  refine ⟨4 * C + 54, by linarith, ?_⟩
  intro k x hlower hupper
  change primorialBlockLower k < x at hlower
  change x <= primorialBlockUpper k at hupper
  change ‖(((primorialWheelSystem k).residual x : Int) : Complex)‖ ^ 2 <= _
  obtain ⟨m, hmLower, hLowerNext⟩ :=
    maximalRun_square_sample_bracket (primorialBlockLower k)
  by_cases hshort : x < squarePrefixEndpoint (m + 1)
  · have hshortSq := shortWheelResidual_sq_lt_nine hmLower hlower hshort hupper
    have hlin := linear_scale_le_rpow hepsilon x
    have hpow0 : 0 <= Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) :=
      Real.rpow_nonneg (by positivity) _
    calc
      ‖(((primorialWheelSystem k).residual x : Int) : Complex)‖ ^ 2 <=
          9 * (((x + 1 : Nat) : Real)) := hshortSq.le
      _ <= 9 * Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) :=
        mul_le_mul_of_nonneg_left hlin (by norm_num)
      _ <= (4 * C + 54) * Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) := by
        apply mul_le_mul_of_nonneg_right _ hpow0
        linarith
  · have hnextx : squarePrefixEndpoint (m + 1) <= x := by omega
    obtain ⟨n, hnLower, hnNext⟩ := maximalRun_square_sample_bracket x
    have hmn : m + 1 <= n := by
      by_contra hnot
      have hnm : n <= m := by omega
      have hnextMono := squarePrefixEndpoint_mono_of_le (Nat.add_le_add_right hnm 1)
      omega
    have hsampleLower : primorialBlockLower k <= squarePrefixEndpoint n := by
      exact hLowerNext.le.trans
        (squarePrefixEndpoint_mono_of_le hmn)
    have hrightEdge :=
      norm_sq_primorialWheelResidual_sub_squareEndpoint_lt_nine_mul_succ
        k n x hsampleLower hnLower hnNext hupper
    have hleftEdge := firstWheelEdge_sq_le_nine hmLower hLowerNext hnextx hupper
    by_cases hEq : n = m + 1
    · subst n
      have hresid := RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
        k hlower.le hupper
      rw [hresid]
      have hsplit :
          mertensSummatory x - mertensSummatory (primorialBlockLower k) =
            (mertensSummatory (squarePrefixEndpoint (m + 1)) -
                mertensSummatory (primorialBlockLower k)) +
              (mertensSummatory x - mertensSummatory (squarePrefixEndpoint (m + 1))) := by ring
      rw [hsplit]
      have hrightM :
          ‖mertensSummatory x - mertensSummatory (squarePrefixEndpoint (m + 1))‖ ^ 2 <
            9 * (((x + 1 : Nat) : Real)) := by
        simpa [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
          k hlower.le hupper,
          RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
            k hsampleLower (hnLower.trans hupper)] using hrightEdge
      have htwo := maximalRun_norm_sq_add_le_two
        (mertensSummatory (squarePrefixEndpoint (m + 1)) -
          mertensSummatory (primorialBlockLower k))
        (mertensSummatory x - mertensSummatory (squarePrefixEndpoint (m + 1)))
      have hlin := linear_scale_le_rpow hepsilon x
      have hpow0 : 0 <= Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) :=
        Real.rpow_nonneg (by positivity) _
      calc
        ‖(mertensSummatory (squarePrefixEndpoint (m + 1)) -
            mertensSummatory (primorialBlockLower k)) +
            (mertensSummatory x - mertensSummatory (squarePrefixEndpoint (m + 1)))‖ ^ 2 <=
          2 * ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
            mertensSummatory (primorialBlockLower k)‖ ^ 2 +
          2 * ‖mertensSummatory x - mertensSummatory (squarePrefixEndpoint (m + 1))‖ ^ 2 := htwo
        _ <= 36 * (((x + 1 : Nat) : Real)) := by nlinarith
        _ <= 36 * Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) :=
          mul_le_mul_of_nonneg_left hlin (by norm_num)
        _ <= (4 * C + 54) * Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) := by
          apply mul_le_mul_of_nonneg_right _ hpow0
          linarith
    · have hstrict : m + 1 < n := by omega
      have ha : 1 <= m + 2 := by omega
      have hab : m + 2 <= n := by omega
      have hrunRaw := hrunBound k (m + 2) n ha hab
        (by simpa using hLowerNext.le)
        (hnLower.trans hupper)
      have hrunEq := RHLean.Proof.sum_canonicalTotalIncrement_Ico_eq_squarePrefix_sub
        (m + 2) n ha (by omega)
      have hmiddle :
          ‖mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (squarePrefixEndpoint (m + 1))‖ ^ 2 <=
            C * Real.rpow (((squarePrefixEndpoint n + 1 : Nat) : Real))
              (1 + epsilon) := by
        rw [hrunEq] at hrunRaw
        simpa [squarePrefixMertens] using hrunRaw
      have hmiddleMono := rpow_endpoint_mono hepsilon hnLower
      have hmiddleX :
          ‖mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (squarePrefixEndpoint (m + 1))‖ ^ 2 <=
            C * Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) :=
        hmiddle.trans (mul_le_mul_of_nonneg_left hmiddleMono hC)
      have hrightM :
          ‖mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)‖ ^ 2 <
            9 * (((x + 1 : Nat) : Real)) := by
        have hXlower : primorialBlockLower k <= x := hlower.le
        have hsampleUpper : squarePrefixEndpoint n <= primorialBlockUpper k := hnLower.trans hupper
        rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
            k hXlower hupper,
          RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
            k hsampleLower hsampleUpper] at hrightEdge
        simpa only [sub_sub_sub_cancel_right] using hrightEdge
      rw [RHLean.Proof.primorialWheel_residual_cast_eq_mertens_sub_le
        k hlower.le hupper]
      have hsplit :
          mertensSummatory x - mertensSummatory (primorialBlockLower k) =
            (mertensSummatory (squarePrefixEndpoint (m + 1)) -
                mertensSummatory (primorialBlockLower k)) +
            ((mertensSummatory (squarePrefixEndpoint n) -
                mertensSummatory (squarePrefixEndpoint (m + 1))) +
              (mertensSummatory x - mertensSummatory (squarePrefixEndpoint n))) := by ring
      rw [hsplit]
      have hinner := maximalRun_norm_sq_add_le_two
        (mertensSummatory (squarePrefixEndpoint n) -
          mertensSummatory (squarePrefixEndpoint (m + 1)))
        (mertensSummatory x - mertensSummatory (squarePrefixEndpoint n))
      have houter := maximalRun_norm_sq_add_le_two
        (mertensSummatory (squarePrefixEndpoint (m + 1)) -
          mertensSummatory (primorialBlockLower k))
        ((mertensSummatory (squarePrefixEndpoint n) -
            mertensSummatory (squarePrefixEndpoint (m + 1))) +
          (mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)))
      have hlin := linear_scale_le_rpow hepsilon x
      have hpow0 : 0 <= Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) :=
        Real.rpow_nonneg (by positivity) _
      calc
        ‖(mertensSummatory (squarePrefixEndpoint (m + 1)) -
            mertensSummatory (primorialBlockLower k)) +
          ((mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (squarePrefixEndpoint (m + 1))) +
            (mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)))‖ ^ 2 <=
          2 * ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
            mertensSummatory (primorialBlockLower k)‖ ^ 2 +
          2 * ‖(mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (squarePrefixEndpoint (m + 1))) +
            (mertensSummatory x - mertensSummatory (squarePrefixEndpoint n))‖ ^ 2 := houter
        _ <= 2 * ‖mertensSummatory (squarePrefixEndpoint (m + 1)) -
            mertensSummatory (primorialBlockLower k)‖ ^ 2 +
          4 * ‖mertensSummatory (squarePrefixEndpoint n) -
              mertensSummatory (squarePrefixEndpoint (m + 1))‖ ^ 2 +
          4 * ‖mertensSummatory x - mertensSummatory (squarePrefixEndpoint n)‖ ^ 2 := by
            nlinarith
        _ <= 4 * (C * Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon)) +
            54 * (((x + 1 : Nat) : Real)) := by nlinarith
        _ <= 4 * (C * Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon)) +
            54 * Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) := by
              gcongr
        _ = (4 * C + 54) * Real.rpow (((x + 1 : Nat) : Real)) (1 + epsilon) := by ring

/-- The maximal signed square-run criterion is exactly the existing pinned
primorial-wheel residual criterion. -/
theorem squareRunEnergyBounded_iff_primorialResidualBounded :
    SquareRunEnergyBoundedStatement <->
      PrimeWheelResidualBoundedStatement primorialWheelFamily := by
  exact ⟨primorialResidualBounded_of_squareRunEnergyBounded,
    squareRunEnergyBounded_of_primorialResidualBounded⟩

/-- Consequently the maximal signed square-run criterion is exactly the global
Mertens energy criterion already used by the repository. -/
theorem squareRunEnergyBounded_iff_mertensEnergy :
    SquareRunEnergyBoundedStatement <-> MertensEnergyBoundedStatement := by
  exact squareRunEnergyBounded_iff_primorialResidualBounded.trans
    primorialWheel_residualBounded_iff_mertensEnergy

end RHLean.Analysis
