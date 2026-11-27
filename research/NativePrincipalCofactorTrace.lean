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
  have pos : 0 ≤ Real.log (B:ℝ)/B :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))) (Nat.cast_nonneg B)
  linarith only [low,pos]

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
      (abs_add_le ..).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m),
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      linarith only [hhigh,mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg m),drift]

/-- Difference on the adjacent odd and even cofactor at the same endpoint. -/
def pairTerm (N k : ℕ) : ℝ :=
  alpogeNativeGzArithmetic (2*(N:ℝ)/(2*(k:ℝ)+1)) -
    alpogeNativeGzArithmetic (2*(N:ℝ)/(2*(k:ℝ)+2))

private theorem dyadic_pairs (N : ℕ) :
    trace (2*N)-2*trace N = ∑ k ∈ Finset.range N, pairTerm N k := by
  have twice (f : ℕ → ℝ) (b : ℕ) :
      ∑ d ∈ Finset.Icc 1 (2*b), f d = ∑ k ∈ Finset.range b, (f (2*k+1)+f (2*k+2)) := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [show 2*(b+1)=2*b+1+1 by omega, Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
      ring
  have shift (f : ℕ → ℝ) (b : ℕ) : ∑ d ∈ Finset.Icc 1 b, f d = ∑ k ∈ Finset.range b, f (k+1) := by
    induction b with
    | zero => simp
    | succ b ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  unfold trace
  rw [twice, shift, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [pairTerm]
  push_cast
  have evenRatio : 2*(N:ℝ)/(2*(k:ℝ)+2) = (N:ℝ)/(k+1) := by
    rw [show 2*(k:ℝ)+2 = 2*(k+1) by ring, mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
  rw [evenRatio]
  ring

/-- The complete tail of adjacent cofactor pairs costs at most the length of
their disjoint quotient intervals times the native movement constant. -/
theorem paired_tail (N R : ℕ) (hR : R ≤ N)
    (room : 2*(N:ℝ) ≤ (2*(R:ℝ)+1)*(2*(R:ℝ)+2)) :
    |∑ k ∈ Finset.Ico R N, pairTerm N k| ≤ alpogeNativeMoveConstant * (2*(N:ℝ)/(2*R+1)) := by
  let u (k : ℕ) := 2*(N:ℝ)/(2*(k:ℝ)+1)
  let v (k : ℕ) := 2*(N:ℝ)/(2*(k:ℝ)+2)
  have point (k : ℕ) (hk : k ∈ Finset.Ico R N) :
      |pairTerm N k| ≤ alpogeNativeMoveConstant * (u k-u (k+1)) := by
    obtain ⟨hrk,hkn⟩ := Finset.mem_Ico.mp hk
    have hr : (R:ℝ) ≤ k := by exact_mod_cast hrk
    have hkn' : (k:ℝ)+1 ≤ N := by exact_mod_cast hkn
    have dk : (0:ℝ) < 2*k+1 := by positivity
    have ek : (0:ℝ) < 2*k+2 := by positivity
    have vu : v k ≤ u k := div_le_div_of_nonneg_left (by positivity) dk (by linarith only)
    have next : u (k+1) ≤ v k := by
      dsimp only [u,v]
      push_cast
      exact div_le_div_of_nonneg_left (by positivity) ek (by linarith only)
    have len : u k-v k = 2*(N:ℝ)/((2*k+1)*(2*k+2)) := by
      dsimp only [u,v]
      field_simp [dk.ne', ek.ne']
      ring
    have prod := mul_le_mul (show 2*(R:ℝ)+1 ≤ 2*k+1 by linarith)
      (show 2*(R:ℝ)+2 ≤ 2*k+2 by linarith) (by positivity) dk.le
    have unit : u k-v k ≤ 1 := by
      rw [len]
      exact (div_le_one (mul_pos dk ek)).2 (room.trans prod)
    have one : 1 ≤ v k := (one_le_div ek).2 (by linarith)
    exact (alpogeNativeGzArithmetic_sub_abs_le_of_le (u k) (v k) one vu (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith only [next]) alpogeNativeMoveConstant_nonneg)
  have tel (b : ℕ) (hb : R ≤ b) : ∑ k ∈ Finset.Ico R b, (u k-u (k+1)) = u R-u b := by
    induction b, hb using Nat.le_induction with
    | base => simp
    | succ b hb ih => rw [Finset.sum_Ico_succ_top hb, ih]; ring
  calc
    _ ≤ ∑ k ∈ Finset.Ico R N, |pairTerm N k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico R N, alpogeNativeMoveConstant*(u k-u (k+1)) := Finset.sum_le_sum point
    _ = alpogeNativeMoveConstant*(u R-u N) := by rw [← Finset.mul_sum, tel N hR]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_self _ (by dsimp [u]; positivity)) alpogeNativeMoveConstant_nonneg

/-- The signed children other than the parent cofactor. -/
def signedChildren (N R : ℕ) : ℝ :=
  alpogeNativeGzArithmetic N - ∑ k ∈ Finset.Ico 1 R, pairTerm N k

private theorem parent (N R : ℕ) (hN : 3 ≤ N) (h₁ : 1 ≤ R) (hR : R ≤ N)
    (room : 2*(N:ℝ) ≤ (2*(R:ℝ)+1)*(2*(R:ℝ)+2)) :
    |alpogeNativeGzArithmetic (2*(N:ℝ))-signedChildren N R| ≤
      (3+2*Real.log (2*N:ℕ)+2*(3+4*Real.log N)) + alpogeNativeMoveConstant*(2*(N:ℝ)/(2*R+1)) := by
  have full := dyadic_pairs N
  have split : (∑ k ∈ Finset.range N, pairTerm N k) =
      pairTerm N 0 + (∑ k ∈ Finset.Ico 1 R, pairTerm N k) + ∑ k ∈ Finset.Ico R N, pairTerm N k := by
    rw [← Finset.sum_range_add_sum_Ico _ hR, ← Finset.sum_range_add_sum_Ico _ h₁]
    simp
  have zero : pairTerm N 0 = alpogeNativeGzArithmetic (2*(N:ℝ))-alpogeNativeGzArithmetic N := by
    simp [pairTerm]
  rw [split, zero] at full
  have id : alpogeNativeGzArithmetic (2*(N:ℝ))-signedChildren N R =
      (trace (2*N)-2*trace N)-(∑ k ∈ Finset.Ico R N, pairTerm N k) := by
    dsimp only [signedChildren]
    linarith only [full]
  rw [id]
  exact (abs_sub _ _).trans (add_le_add (by exact_mod_cast trace_dilation 2 N (by decide) hN) (paired_tail N R hR room))

/-- On every real anchor the independently evaluated trace and all pairs
past the square-root cutoff have an explicit total price, with no assumption
on principal responses at the retained quotient arguments. -/
theorem real_principal_children (x : ℝ) (hx : 16 ≤ x) :
    let N := ⌊x/2⌋₊
    let R := ⌈Real.sqrt x⌉₊
    |alpogeNativeGzArithmetic x-signedChildren N R| ≤
      9+10*Real.log x+alpogeNativeMoveConstant*(2+Real.sqrt x) := by
  intro N R
  have hx0 : 0 < x := by linarith
  have hnlo : (N:ℝ) ≤ x/2 := Nat.floor_le (by linarith)
  have hnhi : x/2 < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hn3 : (3:ℝ) ≤ N := by linarith
  have hN : 3 ≤ N := by exact_mod_cast hn3
  have hr0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hr4 : 4 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).2 (by linarith)
  have hrN : Real.sqrt x ≤ N := by
    nlinarith only [Real.sq_sqrt hx0.le, mul_nonneg hr0 (sub_nonneg.mpr hr4), hnhi, hx]
  have hR : R ≤ N := Nat.ceil_le.mpr hrN
  have hr : Real.sqrt x ≤ (R:ℝ) := Nat.le_ceil _
  have h₁ : 1 ≤ R := by exact_mod_cast (show (1:ℝ) ≤ R by linarith)
  have room : 2*(N:ℝ) ≤ (2*(R:ℝ)+1)*(2*(R:ℝ)+2) := by
    nlinarith only [hnlo, Real.sq_sqrt hx0.le, pow_le_pow_left₀ hr0 hr 2,
      Nat.cast_nonneg (α := ℝ) R, sq_nonneg (R:ℝ)]
  have width : 2*(N:ℝ)/(2*R+1) ≤ Real.sqrt x := (div_le_iff₀ (by positivity)).2 (by
    nlinarith only [hnlo,Real.sq_sqrt hx0.le, mul_le_mul_of_nonneg_left hr hr0,hr0])
  have ell : Real.log (2*N:ℕ) ≤ Real.log x := Real.log_le_log (by positivity)
    (by push_cast; linarith)
  have en : Real.log (N:ℝ) ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
  let t := (x+2*(N:ℝ))/2
  have l := alpogeNativeGzArithmetic_sub_abs_le_of_le t (2*N) (by linarith)
    (by dsimp [t]; linarith) (by dsimp [t]; linarith)
  have u := alpogeNativeGzArithmetic_sub_abs_le_of_le x t (by dsimp [t]; linarith)
    (by dsimp [t]; linarith) (by dsimp [t]; linarith)
  have mv := (abs_sub_le (alpogeNativeGzArithmetic x) (alpogeNativeGzArithmetic t) (alpogeNativeGzArithmetic (2*N))).trans (add_le_add u l)
  have p := parent N R hN h₁ hR room
  refine (abs_sub_le _ (alpogeNativeGzArithmetic (2*(N:ℝ))) _).trans ?_
  dsimp only [t] at mv
  linarith only [p,mv,ell,en, mul_le_mul_of_nonneg_left width alpogeNativeMoveConstant_nonneg,
    mul_le_mul_of_nonneg_left (show x-2*(N:ℝ) ≤ 2 by linarith) alpogeNativeMoveConstant_nonneg]

/-- A quotient interval measured from its original reciprocal prefix and
every von Mangoldt crossing between its two endpoints. -/
def intervalReading (y z : ℝ) : ℝ :=
  (y-z)*(nativeLambdaRecip ⌊z⌋₊+1+Real.eulerMascheroniConstant) +
    (∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊y⌋₊, (Λ n : ℝ)*(y/n-1)) - (y*Real.log y-z*Real.log z)

theorem intervalReading_eq (y z : ℝ) (hzy : z ≤ y) :
    intervalReading y z = alpogeNativeGzArithmetic y-alpogeNativeGzArithmetic z := by
  have sub : Finset.Icc 1 ⌊z⌋₊ ⊆ Finset.Icc 1 ⌊y⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hzy)
  have cells : Finset.Icc 1 ⌊y⌋₊ \ Finset.Icc 1 ⌊z⌋₊ = Finset.Ioc ⌊z⌋₊ ⌊y⌋₊ := by
    ext n; simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have add := Finset.sum_sdiff sub (f := fun n : ℕ => (Λ n : ℝ)*(y/n-1))
  rw [cells] at add
  have prefix : (y-z)*nativeLambdaRecip ⌊z⌋₊ =
      (∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (Λ n:ℝ)*(y/n-1)) - ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, (Λ n:ℝ)*(z/n-1) := by
    rw [nativeLambdaRecip, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [alpogeNativeGzArithmetic_eq_principal y, alpogeNativeGzArithmetic_eq_principal z]
  unfold intervalReading alpogeNativePrincipalPrimeSum alpogeNativePrimePowerWeight
  linarith only [add,prefix]

/-- Starting from the original integer, descend through its actual dyadic
quotients. Each interval contributes its measured arithmetic reading once
at that scale, with the sign forced by the odd/even trace. -/
def sumHistory (reading : ℕ → ℝ → ℝ → ℝ) (n : ℕ) : ℝ :=
  if h : n < 16 then 0 else
    sumHistory reading (n/2) -
      ∑ k ∈ Finset.Ico 1 ⌈Real.sqrt n⌉₊,
        reading n (2*((n/2:ℕ):ℝ)/(2*(k:ℝ)+1)) (2*((n/2:ℕ):ℝ)/(2*(k:ℝ)+2))
termination_by n
decreasing_by omega

/-- Complete signed dyadic history of the original prime-power intervals. -/
abbrev quotientHistory := sumHistory (fun _ => intervalReading)

private theorem base_price (n : ℕ) (hn : 1 ≤ n) :
    |alpogeNativeGzArithmetic n| ≤ (2*Real.log 4+6)*n := by
  have id : alpogeNativeGzArithmetic n = (n:ℝ)*(nativeLambdaRecip n-Real.log n)-nativePsi n+
      (1+Real.eulerMascheroniConstant)*n := by simp only [alpogeNativeGzArithmetic,Nat.floor_natCast]; ring
  rw [id, abs_le]
  have p := abs_le.mp (nativeLambdaRecip_sub_log_abs_le n hn)
  have hz := nativePsi_nonneg n
  have hu := nativePsi_le_const_mul n
  have t := mul_le_mul_of_nonneg_right (show 1+Real.eulerMascheroniConstant ≤ 2 by
    linarith only [Real.eulerMascheroniConstant_lt_two_thirds]) (Nat.cast_nonneg (α := ℝ) n)
  have b := mul_nonneg (show 0 ≤ 1+Real.eulerMascheroniConstant by
    linarith only [Real.one_half_lt_eulerMascheroniConstant]) (Nat.cast_nonneg (α := ℝ) n)
  have logpos := mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)) (Nat.cast_nonneg (α := ℝ) n)
  constructor <;> linarith only [hz,hu,t,b,logpos,Nat.cast_nonneg (α := ℝ) n,
    mul_le_mul_of_nonneg_left p.1 (Nat.cast_nonneg n), mul_le_mul_of_nonneg_left p.2 (Nat.cast_nonneg n)]

private theorem log_le_two_sqrt (x : ℝ) (hx : 0 < x) : Real.log x ≤ 2*Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith

/-- The dyadic prices sum geometrically. The signed remainder is an explicit
finite sum of reciprocal prefixes and crossing atoms and contains no terminal
principal value at a smaller scale. -/
theorem integer_history_price (n : ℕ) (hn : 1 ≤ n) :
    |alpogeNativeGzArithmetic n-quotientHistory n| ≤
      4*(29+3*alpogeNativeMoveConstant)*Real.sqrt n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hr : 1 ≤ Real.sqrt (n:ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg n)).2 (by exact_mod_cast hn)
    have hlog : 0 ≤ Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
    have hK : 0 ≤ 29+3*alpogeNativeMoveConstant := by linarith only [alpogeNativeMoveConstant_nonneg]
    by_cases small : n < 16
    · rw [sumHistory, dif_pos small, sub_zero]
      have hn16 : (n:ℝ) ≤ 16 := by exact_mod_cast small.le
      have hr4 : Real.sqrt (n:ℝ) ≤ 4 := (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
      have ns : (n:ℝ) ≤ 4 * Real.sqrt n := by
        nlinarith only [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),
          mul_le_mul_of_nonneg_right hr4 (Real.sqrt_nonneg (n:ℝ))]
      have coeff : 2*Real.log 4+6 ≤ 29+3*alpogeNativeMoveConstant := by
        dsimp only [alpogeNativeMoveConstant]; linarith
      exact (base_price n hn).trans ((mul_le_mul coeff ns (Nat.cast_nonneg n) hK).trans_eq (by ring))
    · have hn16 : 16 ≤ n := by omega
      have hq1 : 1 ≤ n/2 := by omega
      have castHalf : ⌊(n:ℝ)/2⌋₊ = n/2 := by simpa only [Nat.cast_ofNat] using Nat.floor_div_eq_div (K := ℝ) n 2
      have single := real_principal_children (n:ℝ) (by exact_mod_cast hn16)
      dsimp only at single
      rw [castHalf] at single
      let q := n/2
      let S := ∑ k ∈ Finset.Ico 1 ⌈Real.sqrt n⌉₊, pairTerm q k
      change |alpogeNativeGzArithmetic n-(alpogeNativeGzArithmetic q-S)| ≤ _ at single
      have hist : quotientHistory n = quotientHistory q-S := by
        rw [sumHistory, dif_neg small]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact intervalReading_eq _ _ (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only))
      have hq : ((q:ℕ):ℝ)*2 ≤ n := by exact_mod_cast (show q*2 ≤ n by dsimp [q]; omega)
      have root : Real.sqrt (q:ℝ) ≤ (3/4)*Real.sqrt n := (Real.sqrt_le_iff).2
        ⟨by positivity, by nlinarith only [hq,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),Nat.cast_nonneg (α := ℝ) n]⟩
      have previous := ih q (by dsimp [q]; omega) hq1
      have bill : 9+10*Real.log (n:ℝ)+alpogeNativeMoveConstant*(2+Real.sqrt n) ≤
          (29+3*alpogeNativeMoveConstant)*Real.sqrt n := by
        linarith only [hr, log_le_two_sqrt n (by exact_mod_cast hn),
          mul_le_mul_of_nonneg_left hr alpogeNativeMoveConstant_nonneg]
      rw [hist, show alpogeNativeGzArithmetic n-(quotientHistory q-S) =
        (alpogeNativeGzArithmetic n-(alpogeNativeGzArithmetic q-S))+
        (alpogeNativeGzArithmetic q-quotientHistory q) by ring]
      apply (abs_add_le ..).trans
      linarith only [single.trans bill,previous,mul_le_mul_of_nonneg_left root hK]

/-- Uniform passage from the dyadic prime-power readings to the real anchor
of the measured centered thick frame. -/
theorem real_history_price (x : ℝ) (hx : 1 ≤ x) :
    |alpogeNativeGzArithmetic x-quotientHistory ⌊x⌋₊| ≤
      alpogeNativeMoveConstant + 4*(29+3*alpogeNativeMoveConstant)*Real.sqrt x := by
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.le_floor (by simpa using hx))
  have hlo := Nat.floor_le (zero_le_one.trans hx)
  have hhi := Nat.lt_floor_add_one x
  have mv := alpogeNativeGzArithmetic_sub_abs_le_of_le x ⌊x⌋₊ (by exact_mod_cast hn) hlo hhi.le
  have m : alpogeNativeMoveConstant*(x-(⌊x⌋₊:ℝ)) ≤ alpogeNativeMoveConstant := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (show x-(⌊x⌋₊:ℝ) ≤ 1 by linarith) alpogeNativeMoveConstant_nonneg
  refine (abs_sub_le _ (alpogeNativeGzArithmetic ⌊x⌋₊) _).trans (add_le_add (mv.trans m) ?_)
  exact (integer_history_price _ hn).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlo)
    (by have := alpogeNativeMoveConstant_nonneg; positivity))

end RHLean.Analysis.PrincipalCofactor
