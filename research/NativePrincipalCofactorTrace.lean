import RHLean.Analysis.AlpogeNativeZetaBalance
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Analysis.NativePNTMobiusSecondMoment
import RHLean.Analysis.NativePNTLogSums

/-! Principal responses at the genuine quotient arguments of one integer.
The full sum can be evaluated before estimating it. Subtraction at an
Euler dilation removes the common linear term. -/

noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHLean.Analysis.PrincipalCofactor

/-- One arithmetic response for each original cofactor. -/
def trace (N : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 N, alpogeNativeGzArithmetic ((N : ℝ)/d)

private theorem prime_sum (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, alpogeNativePrincipalPrimeSum ((N : ℝ)/d) =
      ∑ k ∈ Finset.Icc 1 N, Real.log k * ((N : ℝ)/k-1) := by
  let f (d k : ℕ) : ℝ := Λ k * ((N : ℝ)/(d*k : ℕ)-1)
  have swap := congrArg Complex.re (sum_Icc_divisorsAntidiagonal_eq_sum_div
    (fun d k => ((f d k : ℝ) : ℂ)) N)
  simp only [Complex.re_sum, Complex.ofReal_re] at swap
  have row (d : ℕ) : alpogeNativePrincipalPrimeSum ((N : ℝ)/d) = ∑ k ∈ Finset.Icc 1 (N/d), f d k := by
    unfold alpogeNativePrincipalPrimeSum
    rw [Nat.floor_div_eq_div (K := ℝ)]
    apply Finset.sum_congr rfl
    intro k _
    simp only [f, alpogeNativePrimePowerWeight, Nat.cast_mul, div_div]
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N/d), f d k := Finset.sum_congr rfl fun d _ => row d
    _ = _ := swap.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      calc
        _ = ∑ z ∈ k.divisorsAntidiagonal, (Λ z.2 : ℝ) * ((N:ℝ)/k-1) :=
          Finset.sum_congr rfl fun z hz => by simp only [f, (Nat.mem_divisorsAntidiagonal.mp hz).1]
        _ = _ := by
          rw [← Finset.sum_mul, Nat.sum_divisorsAntidiagonal' (f := fun _ j => (Λ j : ℝ)),
            ArithmeticFunction.vonMangoldt_sum]

/-- The divisor sum of the original prime powers evaluates the complete
cofactor trace through ordinary integer sums. -/
theorem trace_eq (N : ℕ) (hN : 1 ≤ N) :
    trace N = 2*(N:ℝ)*nativeLogRecipMass N - Real.log (N.factorial : ℝ) +
      (N:ℝ)*(1+Real.eulerMascheroniConstant-Real.log N)*(harmonic N : ℝ) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hh : (harmonic N : ℝ) = ∑ d ∈ Finset.Icc 1 N, (1:ℝ)/d := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  let c := (N:ℝ)*(1+Real.eulerMascheroniConstant-Real.log N)
  have main (d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
      alpogeNativeGzArithmetic ((N:ℝ)/d) = alpogeNativePrincipalPrimeSum ((N:ℝ)/d) +
        ((N:ℝ)*(Real.log d/d) + c*(1/d)) := by
    have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Icc.mp hd).1.ne'
    rw [alpogeNativeGzArithmetic_eq_principal,Real.log_div hn hd0]
    dsimp only [c]
    ring
  have raw : ∑ k ∈ Finset.Icc 1 N, Real.log k*((N:ℝ)/k-1) =
      (N:ℝ)*nativeLogRecipMass N-Real.log (N.factorial:ℝ) := by
    rw [nativeLogFactorial_eq_sum_log, nativeLogRecipMass, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  unfold trace
  rw [Finset.sum_congr rfl main, Finset.sum_add_distrib, Finset.sum_add_distrib,
    prime_sum, raw, ← Finset.mul_sum, ← Finset.mul_sum, ← hh]
  change _ + ((N:ℝ)*nativeLogRecipMass N+c*(harmonic N:ℝ)) = _
  dsimp only [c]
  ring

private theorem log_drift {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) :
    |nativeLogRecipDefect B-nativeLogRecipDefect A| ≤ Real.log A/A := by
  have low : Real.log (B:ℝ)/B-Real.log (A:ℝ)/A ≤ nativeLogRecipDefect B-nativeLogRecipDefect A := by
    induction B, hAB using Nat.le_induction with
    | base => simp
    | succ b hb ih => linarith only [ih, nativeLogRecipDefect_succ_sub_ge b (hA.trans hb)]
  rw [abs_of_nonpos (sub_nonpos.mpr (nativeLogRecipDefect_antitone_three hA hAB))]
  linarith only [low, div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))) (Nat.cast_nonneg B)]

private theorem trace_center (N : ℕ) (hN : 1 ≤ N) :
    |trace N-(N:ℝ)*(1+Real.eulerMascheroniConstant+Real.eulerMascheroniConstant^2+2*nativeLogRecipDefect N)| ≤
      3+2*Real.log N := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hl : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ' := Real.one_half_lt_eulerMascheroniConstant
  have he := nativeHarmonicLogError_bounds N hN
  have hne : 0 ≤ (N:ℝ)*nativeHarmonicLogError N := mul_nonneg hn.le he.1
  have hne' : (N:ℝ)*nativeHarmonicLogError N ≤ 1 := by
    simpa [hn.ne'] using mul_le_mul_of_nonneg_left he.2 hn.le
  have weight : |1+Real.eulerMascheroniConstant-Real.log N| ≤ 2+Real.log N := abs_le.mpr ⟨by linarith, by linarith⟩
  have prod := mul_le_mul (show |(N:ℝ)*nativeHarmonicLogError N| ≤ 1 by rwa [abs_of_nonneg hne])
    weight (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have fac := nativeLogFactorial_sub_main_abs_le N hN
  have id : trace N-(N:ℝ)*(1+Real.eulerMascheroniConstant+Real.eulerMascheroniConstant^2+2*nativeLogRecipDefect N) =
      ((N:ℝ)*nativeHarmonicLogError N)*(1+Real.eulerMascheroniConstant-Real.log N) -
      (Real.log (N.factorial:ℝ)-((N:ℝ)*Real.log N-N+1))-1 := by
    rw [trace_eq N hN]
    unfold nativeHarmonicLogError nativeLogRecipDefect
    ring
  rw [← abs_mul, one_mul] at prod
  rw [id, abs_le]
  obtain ⟨p₁,p₂⟩ := abs_le.mp prod
  obtain ⟨f₁,f₂⟩ := abs_le.mp fac
  constructor <;> linarith

/-- Full signed cancellation at an integer dilation. The cost is
logarithmic at each fixed admitted prime. All quotient arguments are real. -/
theorem trace_dilation (m N : ℕ) (hm : 1 ≤ m) (hN : 3 ≤ N) :
    |trace (m*N)-(m:ℝ)*trace N| ≤ 3+2*Real.log (m*N:ℕ)+(m:ℝ)*(3+4*Real.log N) := by
  have hab : N ≤ m*N := Nat.le_mul_of_pos_left _ hm
  have hlow := trace_center N (by omega)
  have hhigh := trace_center (m*N) (by omega)
  have hd := log_drift hN hab
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0 < N by omega)
  let c (k : ℕ) := 1+Real.eulerMascheroniConstant+Real.eulerMascheroniConstant^2+2*nativeLogRecipDefect k
  change |trace N-(N:ℝ)*c N| ≤ _ at hlow
  change |trace (m*N)-((m*N:ℕ):ℝ)*c (m*N)| ≤ _ at hhigh
  have price : (2*(m:ℝ)*N)*(Real.log N/N) = 2*m*Real.log N := by field_simp [hNpos.ne']
  have drift := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2*(m:ℝ)*N)
  rw [price] at drift
  have id : trace (m*N)-(m:ℝ)*trace N =
      (trace (m*N)-((m*N:ℕ):ℝ)*c (m*N)) - (m:ℝ)*(trace N-(N:ℝ)*c N) +
        (2*(m:ℝ)*N)*(nativeLogRecipDefect (m*N)-nativeLogRecipDefect N) := by
    simp only [c,Nat.cast_mul]
    ring
  rw [id]
  calc
    _ ≤ (|trace (m*N)-((m*N:ℕ):ℝ)*c (m*N)| + |(m:ℝ)*(trace N-(N:ℝ)*c N)|) +
        |(2*(m:ℝ)*N)*(nativeLogRecipDefect (m*N)-nativeLogRecipDefect N)| :=
      (abs_add_le ..).trans (add_le_add_right (abs_sub _ _) _)
    _ ≤ _ := by
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg m),abs_of_nonneg (by positivity : 0 ≤ 2*(m:ℝ)*N)]
      linarith only [hhigh,mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg m),drift]

end RHLean.Analysis.PrincipalCofactor
