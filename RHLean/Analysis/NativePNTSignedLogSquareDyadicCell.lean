import Mathlib
import RHLean.Analysis.NativePNTErdosContraction
import RHLean.Analysis.NativePNTSignedLogSquarePrimeCells

/-!
# Positive-kernel dyadic compression of signed log-square prime cells

The raw log-square cells from `NativePNTSignedLogSquarePrimeCells` still carry
Möbius signs one divisor at a time.  On an odd product fibre `d`, every divisor
is coprime to the fresh prime `2`.  Summing the cross-endpoint cells over all
`m ∣ d` therefore recombines their log-square coefficients exactly into the
nonnegative second Selberg kernel `Lambda_2(d)`.

This produces the concrete positive-kernel cell

`Lambda_2(d) * (E(N/d) - E(N/(2*d)))`.

When both endpoints are beta-bad with the same sign, its absolute pairing
surplus is at least

`2 * beta * floor(N/(2*d)) * Lambda_2(d)`.

No Selberg remainder, cutoff adapter, or scalarized good-mass hypothesis is
introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Sum of all prime-2 cross-endpoint log-square cells over the divisor fibre
of one odd product `d`. -/
def nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber
    (N d : ℕ) : ℝ :=
  ∑ m ∈ d.divisors,
    (nativePNTMobiusLogSquareSignedAtom N m (d / m) +
      nativePNTMobiusLogSquareSignedAtom N (m * 2) (d / m))

/-- **Positive-kernel compression.**  On an odd product fibre, the complete
prime-2 divisor-cell sum is exactly `Lambda_2(d)` times the difference of the
two reciprocal Chebyshev endpoints. -/
theorem nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber_eq
    (N d : ℕ) (hd : Odd d) :
    nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber N d =
      nativeLambdaTwo d *
        (nativePNTError (N / d) - nativePNTError (N / (2 * d))) := by
  have hd0 : d ≠ 0 := by
    rcases hd with ⟨a, ha⟩
    omega
  have htwoD : Nat.Coprime 2 d := hd.coprime_two_left
  unfold nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber
  calc
    (∑ m ∈ d.divisors,
        (nativePNTMobiusLogSquareSignedAtom N m (d / m) +
          nativePNTMobiusLogSquareSignedAtom N (m * 2) (d / m))) =
      ∑ m ∈ d.divisors,
        ((μ : ArithmeticFunction ℝ) m *
          (Real.log ((d / m : ℕ) : ℝ)) ^ 2) *
          (nativePNTError (N / d) -
            nativePNTError (N / (2 * d))) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmData := Nat.mem_divisors.mp hm
      have hmd : m ∣ d := hmData.1
      have hcop2m : Nat.Coprime 2 m := htwoD.of_dvd_right hmd
      have hcopm2 : Nat.Coprime m 2 := hcop2m.symm
      have hcell := nativePNTMobiusLogSquareSignedAtom_cross_endpoint
        N m 2 (d / m) Nat.prime_two hcopm2
      have hmul : m * (d / m) = d := Nat.mul_div_cancel' hmd
      have hmul2 : (m * 2) * (d / m) = 2 * d := by
        calc
          (m * 2) * (d / m) = 2 * (m * (d / m)) := by ring
          _ = 2 * d := by rw [hmul]
      rw [hmul, hmul2] at hcell
      simpa [mul_assoc] using hcell
    _ = nativeMobiusLogSquareDivisorFiber d *
        (nativePNTError (N / d) - nativePNTError (N / (2 * d))) := by
      unfold nativeMobiusLogSquareDivisorFiber
      rw [Finset.sum_mul]
    _ = nativeLambdaTwo d *
        (nativePNTError (N / d) - nativePNTError (N / (2 * d))) := by
      rw [nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo]

/-- The compressed dyadic log-square cell with its positive `Lambda_2`
coefficient exposed. -/
def nativePNTLambdaTwoDyadicSignedCell (N d : ℕ) : ℝ :=
  nativeLambdaTwo d *
    (nativePNTError (N / d) - nativePNTError (N / (2 * d)))

/-- Odd divisor-cell compression is literally the positive-kernel dyadic cell. -/
theorem nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber_eq_dyadicCell
    (N d : ℕ) (hd : Odd d) :
    nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber N d =
      nativePNTLambdaTwoDyadicSignedCell N d := by
  simpa [nativePNTLambdaTwoDyadicSignedCell] using
    nativePNTMobiusLogSquarePrimeTwoDivisorCellFiber_eq N d hd

/-- Absolute mass released by pairing the two positive-kernel endpoints before
taking an absolute value. -/
def nativePNTLambdaTwoDyadicAbsSurplus (N d : ℕ) : ℝ :=
  nativeLambdaTwo d *
    (|nativePNTError (N / d)| +
      |nativePNTError (N / (2 * d))| -
      |nativePNTError (N / d) - nativePNTError (N / (2 * d))|)

/-- The dyadic positive-kernel surplus is nonnegative. -/
theorem nativePNTLambdaTwoDyadicAbsSurplus_nonneg
    (N d : ℕ) (hd : 1 ≤ d) :
    0 ≤ nativePNTLambdaTwoDyadicAbsSurplus N d := by
  have hkernel : 0 ≤ nativeLambdaTwo d := nativeLambdaTwo_nonneg d hd
  have htri :
      |nativePNTError (N / d) - nativePNTError (N / (2 * d))| ≤
        |nativePNTError (N / d)| + |nativePNTError (N / (2 * d))| :=
    abs_sub _ _
  unfold nativePNTLambdaTwoDyadicAbsSurplus
  exact mul_nonneg hkernel (sub_nonneg.mpr htri)

private theorem abs_pair_surplus_ge_two_common_lower
    (x y L : ℝ)
    (hx : L ≤ |x|) (hy : L ≤ |y|)
    (hsign : (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0)) :
    2 * L ≤ |x| + |y| - |x - y| := by
  rcases hsign with hpos | hneg
  · rcases hpos with ⟨hx0, hy0⟩
    have hxL : L ≤ x := by simpa [abs_of_nonneg hx0] using hx
    have hyL : L ≤ y := by simpa [abs_of_nonneg hy0] using hy
    rw [abs_of_nonneg hx0, abs_of_nonneg hy0]
    by_cases hxy : x ≤ y
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith
    · have hyx : y ≤ x := le_of_not_ge hxy
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      linarith
  · rcases hneg with ⟨hx0, hy0⟩
    have hxL : L ≤ -x := by simpa [abs_of_nonpos hx0] using hx
    have hyL : L ≤ -y := by simpa [abs_of_nonpos hy0] using hy
    rw [abs_of_nonpos hx0, abs_of_nonpos hy0]
    by_cases hxy : x ≤ y
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith
    · have hyx : y ≤ x := le_of_not_ge hxy
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      linarith

/-- **Explicit local signed charge.**  If both reciprocal endpoints of one
positive-kernel dyadic cell are beta-bad and have the same sign, then pairing
them releases at least

`2 * beta * floor(N/(2*d)) * Lambda_2(d)`.

The smaller endpoint is used as the common badness scale, so no real-valued
floor replacement or asymptotic estimate enters the statement. -/
theorem nativePNTLambdaTwoDyadicAbsSurplus_ge_of_bad_sameSign
    (N d : ℕ) (beta : ℝ)
    (hd : 1 ≤ d) (hbeta : 0 ≤ beta)
    (hsource :
      beta * ((N / d : ℕ) : ℝ) ≤ |nativePNTError (N / d)|)
    (hchild :
      beta * ((N / (2 * d) : ℕ) : ℝ) ≤
        |nativePNTError (N / (2 * d))|)
    (hsign :
      (0 ≤ nativePNTError (N / d) ∧
        0 ≤ nativePNTError (N / (2 * d))) ∨
      (nativePNTError (N / d) ≤ 0 ∧
        nativePNTError (N / (2 * d)) ≤ 0)) :
    2 * beta * ((N / (2 * d) : ℕ) : ℝ) * nativeLambdaTwo d ≤
      nativePNTLambdaTwoDyadicAbsSurplus N d := by
  have hdpos : 0 < d := by omega
  have hqmul : (N / (2 * d)) * d ≤ N := by
    calc
      (N / (2 * d)) * d ≤ (N / (2 * d)) * (2 * d) := by
        exact Nat.mul_le_mul_left (N / (2 * d)) (by omega)
      _ ≤ N := Nat.div_mul_le_self N (2 * d)
  have hqle : N / (2 * d) ≤ N / d := by
    exact (Nat.le_div_iff_mul_le hdpos).2 hqmul
  have hqleR :
      ((N / (2 * d) : ℕ) : ℝ) ≤ ((N / d : ℕ) : ℝ) := by
    exact_mod_cast hqle
  have hcommonSource :
      beta * ((N / (2 * d) : ℕ) : ℝ) ≤
        |nativePNTError (N / d)| := by
    exact (mul_le_mul_of_nonneg_left hqleR hbeta).trans hsource
  have hpair := abs_pair_surplus_ge_two_common_lower
    (nativePNTError (N / d))
    (nativePNTError (N / (2 * d)))
    (beta * ((N / (2 * d) : ℕ) : ℝ))
    hcommonSource hchild hsign
  have hkernel : 0 ≤ nativeLambdaTwo d := nativeLambdaTwo_nonneg d hd
  have hmul := mul_le_mul_of_nonneg_left hpair hkernel
  unfold nativePNTLambdaTwoDyadicAbsSurplus
  nlinarith

/-! ## Opposite-sign bad endpoints force a good point -/

/-- If the two endpoints of an interval have opposite signs, and the elementary
one-step no-crossing inequalities hold throughout the interval, then the
normalized Chebyshev error must enter the `beta`-tube somewhere between them.
This is the local alternative to the same-sign cell surplus above. -/
theorem nativePNTError_exists_beta_good_between_of_oppositeSign
    (A B : ℕ) (beta : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hbeta : 0 < beta)
    (hdownA : 1 < beta * (2 * (A : ℝ) + 1))
    (hupA :
      Real.log ((B + 1 : ℕ) : ℝ) - 1 <
        beta * (2 * (A : ℝ) + 1))
    (hopposite :
      (nativePNTError A ≤ 0 ∧ 0 ≤ nativePNTError B) ∨
      (nativePNTError B ≤ 0 ∧ 0 ≤ nativePNTError A)) :
    ∃ n ∈ Finset.Icc A B,
      |nativePNTError n| < beta * (n : ℝ) := by
  by_contra hno
  have haway : ∀ n ∈ Finset.Icc A B,
      beta * (n : ℝ) ≤ |nativePNTError n| := by
    intro n hn
    by_contra hnot
    have hlt : |nativePNTError n| < beta * (n : ℝ) := lt_of_not_ge hnot
    exact hno ⟨n, hn, hlt⟩
  have hdown : ∀ n, A ≤ n → n < B →
      1 < beta * (2 * (n : ℝ) + 1) := by
    intro n hAn _hnB
    have hAnR : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAn
    have hbeta0 : 0 ≤ beta := hbeta.le
    nlinarith [hdownA]
  have hup : ∀ n, A ≤ n → n < B →
      Real.log ((n + 1 : ℕ) : ℝ) - 1 <
        beta * (2 * (n : ℝ) + 1) := by
    intro n hAn hnB
    have hlog :
        Real.log ((n + 1 : ℕ) : ℝ) ≤
          Real.log ((B + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast (show n + 1 ≤ B + 1 by omega)
    have hAnR : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAn
    have hbeta0 : 0 ≤ beta := hbeta.le
    nlinarith [hupA]
  have hsign := nativePNTError_sign_constant_of_away
    A B beta hA hAB hbeta hdown hup haway
  have hAmem : A ∈ Finset.Icc A B := Finset.mem_Icc.mpr ⟨le_rfl, hAB⟩
  have hBmem : B ∈ Finset.Icc A B := Finset.mem_Icc.mpr ⟨hAB, le_rfl⟩
  have hAaway := haway A hAmem
  have hBaway := haway B hBmem
  have hB1 : 1 ≤ B := hA.trans hAB
  have hbetaA : 0 < beta * (A : ℝ) := by
    exact mul_pos hbeta (by exact_mod_cast (show 0 < A by omega))
  have hbetaB : 0 < beta * (B : ℝ) := by
    exact mul_pos hbeta (by exact_mod_cast (show 0 < B by omega))
  rcases hsign with hallpos | hallneg
  · rcases hopposite with hop | hop
    · have hzero : nativePNTError A = 0 :=
        le_antisymm hop.1 (hallpos A hAmem)
      simp [hzero] at hAaway
      linarith
    · have hzero : nativePNTError B = 0 :=
        le_antisymm hop.1 (hallpos B hBmem)
      simp [hzero] at hBaway
      linarith
  · rcases hopposite with hop | hop
    · have hzero : nativePNTError B = 0 :=
        le_antisymm (hallneg B hBmem) hop.2
      simp [hzero] at hBaway
      linarith
    · have hzero : nativePNTError A = 0 :=
        le_antisymm (hallneg A hAmem) hop.2
      simp [hzero] at hAaway
      linarith

end RHLean.Analysis
