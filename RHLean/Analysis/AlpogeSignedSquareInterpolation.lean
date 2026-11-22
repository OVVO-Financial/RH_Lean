import Mathlib
import RHLean.Analysis.AlpogeSquareClockSignedHistorySampling
import RHLean.Analysis.AlpogeGzErdosReciprocalHistory

/-!
# Exact signed square-lattice interpolation for Alpoge Gz

The genuine, full prime-power Gz source is interpolated between consecutive
square endpoints. The interpolation defect is an *exact signed difference*:
  deterministic logarithmic chord excess MINUS arithmetic prime-power
  chord excess. Neither source is separately discarded in that identity.

Mertens' first theorem already proved in RHLean gives a two-sided bounded
one-step slope for the full Gz; this yields an unconditional O(R) bound on
the interpolation defect on [R^2,(R+1)^2]. Consequently any O(R) bound
at the square endpoints propagates to O(sqrt N) at *every* integer N.

The square-endpoint O(R) hypothesis is intentionally NOT claimed here:
that estimate is the outstanding RH-strength input. These results are
a source-preserving reduction, not a proof of the Riemann hypothesis.
-/

noncomputable section

namespace RHLean.Analysis

/-- A convenient two-sided step constant, with an explicit safety margin. -/
def alpogeGzInterpolationSlope : ℝ := nativeAlpogeSafeSlope + 3

theorem alpogeGzInterpolationSlope_nonneg :
    0 ≤ alpogeGzInterpolationSlope := by
  unfold alpogeGzInterpolationSlope
  linarith [nativeAlpogeSafeSlope_nonneg]

/-- Elementary upper bound for the logarithmic increment, complementary
to nativeOne_le_succ_mul_log_succ_sub_log. -/
private theorem alpogeLogIncrement_upper
    (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 2 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hsp : 0 < (n : ℝ) + 1 := by linarith
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < ((n : ℝ) + 1) / (n : ℝ) by positivity)
  rw [Real.log_div (ne_of_gt hsp) (ne_of_gt hnpos)] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hsp.le
  have hident :
      ((n : ℝ) + 1) * (((n : ℝ) + 1) / (n : ℝ) - 1) =
        ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp [ne_of_gt hnpos]
    ring
  rw [hident] at hscaled
  have hratio : ((n : ℝ) + 1) / (n : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hnpos).2
    linarith
  linarith

/-- The complete Gz source also has a uniform LOWER step bound.
This is where the two-sided interpolant improves the previous one-sided
square-clock sampling. The proof uses no zero-free-region assumption. -/
theorem nativeAlpogeGz_succ_ge_of_finiteMertens
    (n : ℕ) (hn : 1 ≤ n) :
    nativeAlpogeGz n - alpogeGzInterpolationSlope ≤
      nativeAlpogeGz (n + 1) := by
  have hstep := nativeAlpogeGz_succ_sub n
  have hrecip := (nativeLambdaRecip_sub_log_bounds n hn).1
  have hlog := alpogeLogIncrement_upper n hn
  have hgamma := neg_abs_le Real.eulerMascheroniConstant
  have hlog4 : 0 ≤ Real.log (4 : ℝ) :=
    Real.log_nonneg (by norm_num)
  simp only [Nat.cast_add, Nat.cast_one] at hstep
  unfold alpogeGzInterpolationSlope nativeAlpogeSafeSlope
  linarith

/-- Unconditional bounded *absolute* one-step Gz variation. -/
theorem nativeAlpogeGz_succ_abs_le
    (n : ℕ) (hn : 1 ≤ n) :
    |nativeAlpogeGz (n + 1) - nativeAlpogeGz n| ≤
      alpogeGzInterpolationSlope := by
  have hup := nativeAlpogeGz_succ_le n hn
  have hlow := nativeAlpogeGz_succ_ge_of_finiteMertens n hn
  rw [abs_le]
  constructor
  · unfold alpogeGzInterpolationSlope at *
    linarith
  · unfold alpogeGzInterpolationSlope at *
    linarith

/-- Telescoping the two one-step inequalities without splitting or
absolutizing the underlying prime-power source. -/
theorem nativeAlpogeGz_interval_abs_le
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    |nativeAlpogeGz b - nativeAlpogeGz a| ≤
      alpogeGzInterpolationSlope * (((b - a : ℕ) : ℝ)) := by
  have hupStep : ∀ n : ℕ, 1 ≤ n →
      nativeAlpogeGz (n + 1) ≤
        nativeAlpogeGz n + alpogeGzInterpolationSlope := by
    intro n hn
    have h := nativeAlpogeGz_succ_le n hn
    unfold alpogeGzInterpolationSlope
    linarith
  have hdownStep : ∀ n : ℕ, 1 ≤ n →
      -nativeAlpogeGz (n + 1) ≤
        -nativeAlpogeGz n + alpogeGzInterpolationSlope := by
    intro n hn
    have h := nativeAlpogeGz_succ_ge_of_finiteMertens n hn
    linarith
  have hup := nativeOneSidedLipschitz_Icc
    nativeAlpogeGz alpogeGzInterpolationSlope hupStep a b ha hab
  have hdown := nativeOneSidedLipschitz_Icc
    (fun n => -nativeAlpogeGz n)
    alpogeGzInterpolationSlope hdownStep a b ha hab
  have hdown' : -nativeAlpogeGz b ≤
      -nativeAlpogeGz a +
        alpogeGzInterpolationSlope * (((b - a : ℕ) : ℝ)) := hdown
  rw [abs_le]
  constructor <;> linarith

/-- Barycentric coordinate of N between lattice endpoints a < b. -/
def alpogeSquareSecantWeight (a N b : ℕ) : ℝ :=
  ((N : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))

/-- Affine chord of ANY real-valued arithmetic history. -/
def alpogeSquareChord (f : ℕ → ℝ) (a N b : ℕ) : ℝ :=
  let t := alpogeSquareSecantWeight a N b
  (1 - t) * f a + t * f b

theorem alpogeSquareSecantWeight_mem_unit
    (a N b : ℕ) (ha : a ≤ N) (hb : N ≤ b) (hab : a < b) :
    0 ≤ alpogeSquareSecantWeight a N b ∧
      alpogeSquareSecantWeight a N b ≤ 1 := by
  have har : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast ha
  have hbr : (N : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hstrict : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hden : 0 < (b : ℝ) - (a : ℝ) := by linarith
  unfold alpogeSquareSecantWeight
  constructor
  · exact div_nonneg (by linarith) hden.le
  · apply (div_le_iff₀ hden).2
    linarith

/-- Linear interpolation preserves the endpoint coordinate itself. -/
theorem alpogeSquareChord_cast
    (a N b : ℕ) (hab : a < b) :
    alpogeSquareChord (fun n => (n : ℝ)) a N b = (N : ℝ) := by
  have habr : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hden : (b : ℝ) - (a : ℝ) ≠ 0 := ne_of_gt (by linarith)
  dsimp [alpogeSquareChord, alpogeSquareSecantWeight]
  field_simp [hden]
  ring

/-- The REAL prime-power source of Gz, before any sign splitting. -/
def alpogeSquarePrimePowerSource (N : ℕ) : ℝ :=
  (N : ℝ) * nativeLambdaRecip N - nativePsi N

/-- The deterministic x log x source. -/
def alpogeSquareLogMain (N : ℕ) : ℝ :=
  (N : ℝ) * Real.log (N : ℝ)

/-- The full, SIGNED prime-power chord defect: no absolute values. -/
def alpogeSquareArithmeticChordDefect (a N b : ℕ) : ℝ :=
  alpogeSquareChord alpogeSquarePrimePowerSource a N b -
    alpogeSquarePrimePowerSource N

/-- The deterministic logarithmic chord defect. -/
def alpogeSquareLogChordDefect (a N b : ℕ) : ℝ :=
  alpogeSquareChord alpogeSquareLogMain a N b -
    alpogeSquareLogMain N

/-- The exact signed remainder is log curvature MINUS prime-power curvature. -/
def alpogeSquareSignedCorrection (a N b : ℕ) : ℝ :=
  alpogeSquareLogChordDefect a N b -
    alpogeSquareArithmeticChordDefect a N b

/-- The complete arithmetic interpolation identity. All prime powers are
retained in the signed correction, before any estimates are used. -/
theorem nativeAlpogeGz_sub_squareChord_eq_signedCorrection
    (a N b : ℕ) (hab : a < b) :
    nativeAlpogeGz N -
        alpogeSquareChord nativeAlpogeGz a N b =
      alpogeSquareSignedCorrection a N b := by
  have hlinear := alpogeSquareChord_cast a N b hab
  unfold alpogeSquareSignedCorrection
    alpogeSquareLogChordDefect alpogeSquareArithmeticChordDefect
    alpogeSquarePrimePowerSource alpogeSquareLogMain
    alpogeSquareChord alpogeSquareSecantWeight at *
  unfold nativeAlpogeGz
  linear_combination -(1 + Real.eulerMascheroniConstant) * hlinear

/-- Purely algebraic signed error expressed as two endpoint differences. -/
theorem alpogeSquareChord_error_rewrite
    (f : ℕ → ℝ) (a N b : ℕ) :
    f N - alpogeSquareChord f a N b =
      (1 - alpogeSquareSecantWeight a N b) * (f N - f a) +
        alpogeSquareSecantWeight a N b * (f N - f b) := by
  dsimp [alpogeSquareChord]
  ring

/-- The chord residual is bounded by the full interval length whenever
the original function has uniform two-sided endpoint variation. -/
theorem alpogeSquareChord_error_abs_le
    (f : ℕ → ℝ) (a N b : ℕ) (L : ℝ)
    (ha : a ≤ N) (hb : N ≤ b) (hab : a < b) (hL : 0 ≤ L)
    (hleft : |f N - f a| ≤ L * ((N : ℝ) - (a : ℝ)))
    (hright : |f N - f b| ≤ L * ((b : ℝ) - (N : ℝ))) :
    |f N - alpogeSquareChord f a N b| ≤
      L * ((b : ℝ) - (a : ℝ)) := by
  let t := alpogeSquareSecantWeight a N b
  have ht := alpogeSquareSecantWeight_mem_unit a N b ha hb hab
  have ht0 : 0 ≤ t := ht.1
  have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
  have haR : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast ha
  have hbR : (N : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hleft' : |f N - f a| ≤ L * ((b : ℝ) - (a : ℝ)) := by
    have hcomp := mul_le_mul_of_nonneg_left
      (show (N : ℝ) - (a : ℝ) ≤ (b : ℝ) - (a : ℝ) by linarith) hL
    linarith
  have hright' : |f N - f b| ≤ L * ((b : ℝ) - (a : ℝ)) := by
    have hcomp := mul_le_mul_of_nonneg_left
      (show (b : ℝ) - (N : ℝ) ≤ (b : ℝ) - (a : ℝ) by linarith) hL
    linarith
  rw [alpogeSquareChord_error_rewrite]
  calc
    |(1 - t) * (f N - f a) + t * (f N - f b)| ≤
        |(1 - t) * (f N - f a)| + |t * (f N - f b)| :=
          abs_add_le _ _
    _ = (1 - t) * |f N - f a| + t * |f N - f b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht1, abs_of_nonneg ht0]
    _ ≤ (1 - t) * (L * ((b : ℝ) - (a : ℝ))) +
          t * (L * ((b : ℝ) - (a : ℝ))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hleft' ht1)
        (mul_le_mul_of_nonneg_left hright' ht0)
    _ = L * ((b : ℝ) - (a : ℝ)) := by ring

/-- Apply the unconditional first-Mertens two-sided local variation to
the complete original Alpoge signed source. -/
theorem nativeAlpogeGz_squareChord_error_abs_le
    (a N b : ℕ) (ha : 1 ≤ a) (hleft : a ≤ N)
    (hright : N ≤ b) (hab : a < b) :
    |nativeAlpogeGz N -
      alpogeSquareChord nativeAlpogeGz a N b| ≤
        alpogeGzInterpolationSlope * ((b : ℝ) - (a : ℝ)) := by
  have hp := nativeAlpogeGz_interval_abs_le a N ha hleft
  have hq := nativeAlpogeGz_interval_abs_le N b (ha.trans hleft) hright
  have hgapP : (((N - a : ℕ) : ℝ)) = (N : ℝ) - (a : ℝ) := by
    exact Nat.cast_sub hleft
  have hgapQ : (((b - N : ℕ) : ℝ)) = (b : ℝ) - (N : ℝ) := by
    exact Nat.cast_sub hright
  rw [hgapP] at hp
  rw [hgapQ] at hq
  rw [abs_sub_comm] at hq
  exact alpogeSquareChord_error_abs_le nativeAlpogeGz a N b
    alpogeGzInterpolationSlope hleft hright hab
    alpogeGzInterpolationSlope_nonneg hp hq

/-- Unconditional O(R) interpolation error on the square lattice itself,
with the exact signed prime-power correction attached. -/
theorem nativeAlpogeGz_square_lattice_signed_remainder
    (N : ℕ) (hN : 4 ≤ N) :
    let R := Nat.sqrt N
    |alpogeSquareSignedCorrection (R ^ 2) N ((R + 1) ^ 2)| ≤
      alpogeGzInterpolationSlope * ((2 * R + 1 : ℕ) : ℝ) := by
  dsimp
  let R := Nat.sqrt N
  have hlo : R ^ 2 ≤ N := Nat.sqrt_le' N
  have hhi : N < (R + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hR : 2 ≤ R := by
    by_contra h
    have hR1 : R ≤ 1 := by omega
    nlinarith
  have hsq : R ^ 2 < (R + 1) ^ 2 := by
    calc
      R ^ 2 < R ^ 2 + (2 * R + 1) := by omega
      _ = (R + 1) ^ 2 := by ring
  have hone : 1 ≤ R ^ 2 := by nlinarith
  have hsource := nativeAlpogeGz_squareChord_error_abs_le
    (R ^ 2) N ((R + 1) ^ 2) hone hlo hhi.le hsq
  rw [nativeAlpogeGz_sub_squareChord_eq_signedCorrection
    (R ^ 2) N ((R + 1) ^ 2) hsq] at hsource
  have hwidth :
      (((R + 1) ^ 2 : ℕ) : ℝ) - ((R ^ 2 : ℕ) : ℝ) =
        ((2 * R + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hwidth] at hsource
  exact hsource

/-- The signed square-lattice formula itself, with no discarded source. -/
theorem nativeAlpogeGz_square_lattice_exact
    (N : ℕ) (_hN : 4 ≤ N) :
    let R := Nat.sqrt N
    nativeAlpogeGz N =
      alpogeSquareChord nativeAlpogeGz (R ^ 2) N ((R + 1) ^ 2) +
      alpogeSquareSignedCorrection (R ^ 2) N ((R + 1) ^ 2) := by
  dsimp
  let R := Nat.sqrt N
  have hsq : R ^ 2 < (R + 1) ^ 2 := by
    calc
      R ^ 2 < R ^ 2 + (2 * R + 1) := by omega
      _ = (R + 1) ^ 2 := by ring
  have h := nativeAlpogeGz_sub_squareChord_eq_signedCorrection
    (R ^ 2) N ((R + 1) ^ 2) hsq
  linarith

/-- A critical O(R) bound at all genuine square endpoints automatically
gives a critical O(sqrt N) bound at EVERY integer endpoint. The ONLY
quantitative input still assumed is exactly the square-lattice bound. -/
theorem nativeAlpogeGz_all_of_square_lattice_critical
    (C : ℝ) (hC : 0 ≤ C)
    (hSquare : ∀ R : ℕ, 2 ≤ R →
      |nativeAlpogeGz (R ^ 2)| ≤ C * (R : ℝ))
    (N : ℕ) (hN : 4 ≤ N) :
    |nativeAlpogeGz N| ≤
      (2 * C + 3 * alpogeGzInterpolationSlope) *
        Real.sqrt (N : ℝ) := by
  let R := Nat.sqrt N
  have hlo : R ^ 2 ≤ N := Nat.sqrt_le' N
  have hhi : N < (R + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hR : 2 ≤ R := by
    by_contra h
    have hR1 : R ≤ 1 := by omega
    nlinarith
  have hsq : R ^ 2 < (R + 1) ^ 2 := by
    calc
      R ^ 2 < R ^ 2 + (2 * R + 1) := by omega
      _ = (R + 1) ^ 2 := by ring
  have ht := alpogeSquareSecantWeight_mem_unit
    (R ^ 2) N ((R + 1) ^ 2) hlo hhi.le hsq
  let t := alpogeSquareSecantWeight (R ^ 2) N ((R + 1) ^ 2)
  have ht0 : 0 ≤ t := ht.1
  have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hb0 := hSquare R hR
  have hb1 := hSquare (R + 1) (by omega)
  have hchord :
      |alpogeSquareChord nativeAlpogeGz (R ^ 2) N ((R + 1) ^ 2)| ≤
        C * ((R : ℝ) + 1) := by
    dsimp [alpogeSquareChord]
    calc
      |(1 - t) * nativeAlpogeGz (R ^ 2) +
        t * nativeAlpogeGz ((R + 1) ^ 2)| ≤
          |(1 - t) * nativeAlpogeGz (R ^ 2)| +
            |t * nativeAlpogeGz ((R + 1) ^ 2)| := abs_add_le _ _
      _ = (1 - t) * |nativeAlpogeGz (R ^ 2)| +
          t * |nativeAlpogeGz ((R + 1) ^ 2)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht1, abs_of_nonneg ht0]
      _ ≤ (1 - t) * (C * (R : ℝ)) +
          t * (C * ((R + 1 : ℕ) : ℝ)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hb0 ht1)
          (mul_le_mul_of_nonneg_left hb1 ht0)
      _ ≤ C * ((R : ℝ) + 1) := by
        push_cast
        have hh : (R : ℝ) + t ≤ (R : ℝ) + 1 := by linarith [ht.2]
        calc
          (1 - t) * (C * (R : ℝ)) + t * (C * ((R : ℝ) + 1)) =
              C * ((R : ℝ) + t) := by ring
          _ ≤ C * ((R : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hh hC
  have hrem := nativeAlpogeGz_square_lattice_signed_remainder N hN
  dsimp at hrem
  have hsource := nativeAlpogeGz_square_lattice_exact N hN
  dsimp at hsource
  have hs : 0 ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_nonneg _
  have hsSq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hR2 : ((R : ℝ) ^ 2) ≤ (N : ℝ) := by
    exact_mod_cast hlo
  have hRs : (R : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
    nlinarith
  have hs2 : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hN4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hgeo1 : ((R : ℝ) + 1) ≤ 2 * Real.sqrt (N : ℝ) := by
    linarith
  have hgeo2 :
      ((2 * R + 1 : ℕ) : ℝ) ≤ 3 * Real.sqrt (N : ℝ) := by
    push_cast
    linarith
  have hL := alpogeGzInterpolationSlope_nonneg
  have hmargin1 := mul_le_mul_of_nonneg_left hgeo1 hC
  have hmargin2 := mul_le_mul_of_nonneg_left hgeo2 hL
  calc
    |nativeAlpogeGz N| ≤
        |alpogeSquareChord nativeAlpogeGz (R ^ 2) N ((R + 1) ^ 2)| +
          |alpogeSquareSignedCorrection (R ^ 2) N ((R + 1) ^ 2)| := by
      rw [hsource]
      exact abs_add_le _ _
    _ ≤ C * ((R : ℝ) + 1) +
          alpogeGzInterpolationSlope * ((2 * R + 1 : ℕ) : ℝ) :=
      add_le_add hchord hrem
    _ ≤ 2 * C * Real.sqrt (N : ℝ) +
          3 * alpogeGzInterpolationSlope * Real.sqrt (N : ℝ) := by
      linarith [hmargin1, hmargin2]
    _ = (2 * C + 3 * alpogeGzInterpolationSlope) *
        Real.sqrt (N : ℝ) := by ring

/-- The central native NNS signed-history consumer. -/
theorem nativeAlpogeCenteredHistory_all_of_square_lattice_critical
    (C : ℝ) (hC : 0 ≤ C)
    (hSquare : ∀ R : ℕ, 2 ≤ R →
      |nativeAlpogeGz (R ^ 2)| ≤ C * (R : ℝ))
    (N : ℕ) (hN : 4 ≤ N) :
    |nativeAlpogeCenteredHistory N| ≤
      (2 * C + 3 * alpogeGzInterpolationSlope) /
        Real.sqrt (N : ℝ) := by
  have hG := nativeAlpogeGz_all_of_square_lattice_critical C hC hSquare N hN
  have hhist := nativeAlpogeGz_eq_centeredHistory N (by omega)
  rw [hhist] at hG
  have hNpos : 0 < (N : ℝ) := by positivity
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hrootSq := Real.sq_sqrt (le_of_lt hNpos)
  rw [abs_mul, abs_of_nonneg hNpos.le] at hG
  have hDiv :
      |nativeAlpogeCenteredHistory N| ≤
        ((2 * C + 3 * alpogeGzInterpolationSlope) *
          Real.sqrt (N : ℝ)) / (N : ℝ) := by
    apply (le_div_iff₀ hNpos).2
    nlinarith [hG]
  calc
    |nativeAlpogeCenteredHistory N| ≤
        ((2 * C + 3 * alpogeGzInterpolationSlope) *
          Real.sqrt (N : ℝ)) / (N : ℝ) := hDiv
    _ = (2 * C + 3 * alpogeGzInterpolationSlope) /
          Real.sqrt (N : ℝ) := by
      calc
        ((2 * C + 3 * alpogeGzInterpolationSlope) * Real.sqrt (N : ℝ)) /
            (N : ℝ) =
            ((2 * C + 3 * alpogeGzInterpolationSlope) * Real.sqrt (N : ℝ)) /
              (Real.sqrt (N : ℝ)) ^ 2 := by rw [hrootSq]
        _ = (2 * C + 3 * alpogeGzInterpolationSlope) /
              Real.sqrt (N : ℝ) := by
          field_simp [ne_of_gt hroot]

end RHLean.Analysis
