import «research.NativePrincipalCofactorTrace»
import RHLean.Analysis.AlpogeNativeProperPowerCentering
import RHLean.Analysis.NativePNTTransfer

/-! On each dyadic ancestor, retain the first primes above its square root in
the interval readings. All other original atoms keep their finite reciprocal
intercept. Disjoint cofactor intervals share a single clipping charge. -/

noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt Classical
open Filter

namespace RHLean.Analysis.PrincipalCofactor

private def kept (M i : ℕ) : Prop := i.Prime ∧ M.sqrt < i

private def removed (M i : ℕ) : ℝ := if kept M i then 0 else Λ i

private theorem removed_nonneg (M i : ℕ) : 0 ≤ removed M i := by
  unfold removed
  split <;> first | exact le_rfl | exact ArithmeticFunction.vonMangoldt_nonneg

private theorem removed_mass :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, 1 ≤ M →
      ∑ i ∈ Finset.Icc 1 M, removed M i ≤ K*Real.sqrt M := by
  obtain ⟨C,hC,proper⟩ := nativeProperPower_clippedMass_le
  refine ⟨C+Real.log 4,add_nonneg hC (Real.log_nonneg (by norm_num)),?_⟩
  intro M hM
  have small : (M.sqrt:ℝ) ≤ Real.sqrt M := (Real.le_sqrt (by positivity) (Nat.cast_nonneg M)).2
    (by rw [sq]; exact_mod_cast Nat.sqrt_le M)
  have prime (i : ℕ) (hi : i ∈ Finset.Icc 1 M) : removed M i =
      nativeProperPowerAtom i * min ((M:ℝ)/i) 1 +
        (if i ∈ nativePrimeSet M.sqrt then Real.log i else 0) := by
    obtain ⟨hi₁,hiM⟩ := Finset.mem_Icc.mp hi
    have u : (1:ℝ) ≤ (M:ℝ)/i := (one_le_div (by exact_mod_cast hi₁)).2 (by exact_mod_cast hiM)
    by_cases hp : i.Prime
    · by_cases h : M.sqrt < i
      · have hm : i ∉ nativePrimeSet M.sqrt := fun hm => (not_le.mpr h) (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
        simp [removed,kept,hp,h,nativeProperPowerAtom,hm]
      · have hm : i ∈ nativePrimeSet M.sqrt := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi₁,le_of_not_gt h⟩,hp⟩
        simp [removed,kept,hp,h,nativeProperPowerAtom,hm,ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [removed,kept,hp,nativeProperPowerAtom,nativePrimeSet,min_eq_right u]
  have sub : nativePrimeSet M.sqrt ⊆ Finset.Icc 1 M := fun p hp =>
    Finset.Icc_subset_Icc le_rfl (Nat.sqrt_le_self M) (Finset.mem_filter.mp hp).1
  have eq : (Finset.Icc 1 M).filter (fun i => i ∈ nativePrimeSet M.sqrt) = nativePrimeSet M.sqrt := by
    ext i; simp only [Finset.mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
  rw [Finset.sum_congr rfl prime,Finset.sum_add_distrib,← Finset.sum_filter,eq]
  have θ := (nativeTheta_le_log4_mul M.sqrt).trans (mul_le_mul_of_nonneg_left small (Real.log_nonneg (by norm_num)))
  change nativeTheta M.sqrt ≤ _ at θ
  change _+nativeTheta M.sqrt ≤ _
  linarith only [proper M M hM,θ]

/-- The physical high-prime sum, with the reciprocal slopes of all removed
atoms measured once at the same integer source cutoff. -/
def firstPrimeValue (M : ℕ) (t : ℝ) : ℝ :=
  (∑ p ∈ (Finset.Icc 1 M).filter (kept M), Real.log p * max (t/p-1) 0) +
    t*(∑ i ∈ Finset.Icc 1 M, removed M i/i)-t*Real.log t+(1+Real.eulerMascheroniConstant)*t

def retainedFirstPrimes (M : ℕ) : Finset ℕ := (Finset.Icc 1 M).filter (kept M)

theorem mem_retainedFirstPrimes {M p : ℕ} :
    p ∈ retainedFirstPrimes M ↔ (1 ≤ p ∧ p ≤ M) ∧ p.Prime ∧ M.sqrt < p := by
  simp only [retainedFirstPrimes, Finset.mem_filter, Finset.mem_Icc, kept]

def clippedReciprocal (M : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 M, removed M i/i

/-- In the cofactor coordinate the clipped reciprocal slopes and the affine
part of the original MAIN form a single constant, independent of the cofactor. -/
theorem scaled_firstPrimeValue (M : ℕ) {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    d*firstPrimeValue M (a/d) =
      (∑ p ∈ retainedFirstPrimes M, Real.log p * max (a/p-d) 0) + a*Real.log d +
      a*(clippedReciprocal M+1+Real.eulerMascheroniConstant-Real.log a) := by
  have atom (p : ℕ) : d*(Real.log p * max (a/d/p-1) 0) = Real.log p * max (a/p-d) 0 := by
    have da : d*(a/d) = a := by field_simp
    rw [mul_left_comm, mul_max_of_nonneg _ _ hd.le, mul_zero, mul_sub, ← mul_div_assoc, da, mul_one]
  let P := retainedFirstPrimes M
  let s := clippedReciprocal M
  have sum := Finset.sum_congr (s₁ := P) rfl (fun p _ => atom p)
  rw [← Finset.mul_sum] at sum
  change d*((∑ p ∈ P, Real.log p*max (a/d/p-1) 0)+(a/d)*s-
    (a/d)*Real.log (a/d)+(1+Real.eulerMascheroniConstant)*(a/d)) =
    (∑ p ∈ P, Real.log p*max (a/p-d) 0)+a*Real.log d+
    a*(s+1+Real.eulerMascheroniConstant-Real.log a)
  rw [Real.log_div ha.ne' hd.ne']
  have da : d*(a/d) = a := by field_simp
  linear_combination sum + (s-(Real.log a-Real.log d)+(1+Real.eulerMascheroniConstant))*da

private def clip (M : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 M, removed M i*min (t/i) 1

private theorem clip_mono (M : ℕ) : Monotone (clip M) := by
  intro y z h
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (min_le_min_right _ (div_le_div_of_nonneg_right h (Nat.cast_nonneg i))) (removed_nonneg M i)

private theorem clip_bounds (M : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ clip M t ∧ clip M t ≤ ∑ i ∈ Finset.Icc 1 M, removed M i := by
  exact ⟨Finset.sum_nonneg fun i _ => mul_nonneg (removed_nonneg M i)
    (le_min (div_nonneg ht (Nat.cast_nonneg i)) zero_le_one),
    Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (removed_nonneg M i) (min_le_right _ _)⟩

private theorem physical (M : ℕ) (t : ℝ) (ht : 0 ≤ t) (hM : t ≤ M) :
    firstPrimeValue M t = alpogeNativeGzArithmetic t+clip M t := by
  have hsub : Finset.Icc 1 ⌊t⌋₊ ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc le_rfl (Nat.floor_le_of_le hM)
  have raw : alpogeNativePrincipalPrimeSum t = ∑ i ∈ Finset.Icc 1 M, (Λ i:ℝ)*max (t/i-1) 0 := by
    unfold alpogeNativePrincipalPrimeSum
    calc
      _ = ∑ i ∈ Finset.Icc 1 ⌊t⌋₊, (Λ i:ℝ)*max (t/i-1) 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp hi
        have hi0 : 0 < (i:ℝ) := by exact_mod_cast h₁
        rw [max_eq_left (sub_nonneg.mpr ((one_le_div hi0).2 ((Nat.le_floor_iff ht).1 h₂)))]
        rfl
      _ = _ := Finset.sum_subset hsub fun i hi hmiss => by
        have h₁ := (Finset.mem_Icc.mp hi).1
        have hlt : ⌊t⌋₊ < i := by contrapose! hmiss; exact Finset.mem_Icc.mpr ⟨h₁,hmiss⟩
        have hi0 : 0 < (i:ℝ) := by exact_mod_cast h₁
        rw [max_eq_right (sub_nonpos.mpr ((div_le_one hi0).2 (Nat.lt_of_floor_lt hlt).le)),mul_zero]
  have split : (∑ i ∈ (Finset.Icc 1 M).filter (kept M), Real.log i*max (t/i-1) 0) +
      t*(∑ i ∈ Finset.Icc 1 M, removed M i/i) =
      (∑ i ∈ Finset.Icc 1 M, (Λ i:ℝ)*max (t/i-1) 0)+clip M t := by
    rw [Finset.sum_filter, Finset.mul_sum, clip, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : kept M i
    · simp [removed,hi, ArithmeticFunction.vonMangoldt_apply_prime hi.1]
    · simp only [hi, ite_false, removed, zero_add]
      rcases le_total (t/i) 1 with h|h
      · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h]; ring
      · rw [max_eq_left (sub_nonneg.mpr h), min_eq_right h]; ring
  rw [firstPrimeValue, split, ← raw, alpogeNativeGzArithmetic_eq_principal]
  ring

/-- Across the actual disjoint quotient intervals, removing all small first
primes and all higher powers has one finite total charge at this scale. -/
private theorem one_scale (M : ℕ) (R : ℕ) (hR : 1 ≤ R) :
    let t := fun k : ℕ => 2*((M/2:ℕ):ℝ)/(2*(k:ℝ)+1)
    let u := fun k : ℕ => 2*((M/2:ℕ):ℝ)/(2*(k:ℝ)+2)
    let gap := (∑ k ∈ Finset.Ico 1 R, (firstPrimeValue M (t k)-firstPrimeValue M (u k))) -
      ∑ k ∈ Finset.Ico 1 R, intervalReading (t k) (u k)
    0 ≤ gap ∧ gap ≤ ∑ i ∈ Finset.Icc 1 M, removed M i := by
  intro t u gap
  have ht (k : ℕ) : 0 ≤ t k := by dsimp [t]; positivity
  have hu (k : ℕ) : 0 ≤ u k := by dsimp [u]; positivity
  have order (k : ℕ) : u k ≤ t k :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only)
  have next (k : ℕ) : t (k+1) ≤ u k := by
    dsimp only [t,u]; push_cast
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only)
  have top (k : ℕ) : t k ≤ M := by
    have cap : 2*((M/2:ℕ):ℝ) ≤ M := by exact_mod_cast (show 2*(M/2) ≤ M by omega)
    exact (div_le_self (by positivity) (by linarith only [Nat.cast_nonneg (α := ℝ) k] : (1:ℝ) ≤ 2*k+1)).trans cap
  have id : gap = ∑ k ∈ Finset.Ico 1 R, (clip M (t k)-clip M (u k)) := by
    dsimp only [gap]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [physical M _ (ht k) (top k),physical M _ (hu k) ((order k).trans (top k)), intervalReading_eq _ _ (order k)]
    ring
  rw [id]
  refine ⟨Finset.sum_nonneg (fun k _ => sub_nonneg.mpr (clip_mono M (order k))),?_⟩
  have cum (b : ℕ) (hb : 1 ≤ b) : ∑ k ∈ Finset.Ico 1 b, (clip M (t k)-clip M (u k)) ≤ clip M (t 1)-clip M (t b) := by
    induction b, hb using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [Finset.sum_Ico_succ_top hb]
      linarith only [ih, clip_mono M (next b)]
  exact (cum R hR).trans ((sub_le_self _ (clip_bounds M (ht R)).1).trans (clip_bounds M (ht 1)).2)

def firstPrimeHistory : ℕ → ℝ :=
  sumHistory (fun M y z => firstPrimeValue M y-firstPrimeValue M z)

/-- The higher-power and small-prime correction across the entire tree has
one sign and a square-root upper bound independent of the anchor. -/
theorem history_clipping_price :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → 0 ≤ quotientHistory n-firstPrimeHistory n ∧
      quotientHistory n-firstPrimeHistory n ≤ K*Real.sqrt n := by
  obtain ⟨C,hC,cap⟩ := removed_mass
  refine ⟨4*C,by positivity,?_⟩
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold firstPrimeHistory quotientHistory
    by_cases h : n < 16
    · rw [sumHistory_small _ n h, sumHistory_small _ n h, sub_self]
      exact ⟨le_rfl,by positivity⟩
    · let q := n/2
      have hq : 1 ≤ q := by dsimp [q]; omega
      have prev := ih q (by dsimp [q]; omega) hq
      have hr : 1 ≤ Real.sqrt (n:ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg n)).2 (by exact_mod_cast hn)
      have hR : 1 ≤ ⌈Real.sqrt n⌉₊ := by exact_mod_cast hr.trans (Nat.le_ceil _)
      have step := one_scale n _ hR
      dsimp only at step
      have half : ((q:ℕ):ℝ)*2 ≤ n := by exact_mod_cast (show q*2 ≤ n by dsimp [q]; omega)
      have root : Real.sqrt (q:ℝ) ≤ (3/4)*Real.sqrt n := Real.sqrt_le_iff.mpr
        ⟨by positivity, by nlinarith only [half,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),Nat.cast_nonneg (α := ℝ) n]⟩
      rw [sumHistory_step _ n h, sumHistory_step _ n h]
      change 0 ≤ quotientHistory q-_-(firstPrimeHistory q-_) ∧
        quotientHistory q-_-(firstPrimeHistory q-_) ≤ _
      constructor <;> linarith only [prev.1,prev.2,step.1,step.2,cap n hn,mul_le_mul_of_nonneg_left root hC]

theorem real_firstPrime_history_price :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x →
      |alpogeNativeGzArithmetic x-firstPrimeHistory ⌊x⌋₊| ≤ K*Real.sqrt x := by
  obtain ⟨B,hB,clipPrice⟩ := history_clipping_price
  refine ⟨1+alpogeNativeMoveConstant+4*(29+3*alpogeNativeMoveConstant)+B,
    by linarith only [hB, alpogeNativeMoveConstant_nonneg],?_⟩
  intro x hx
  have one : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have p := clipPrice _ one
  have hs : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) (zero_le_one.trans hx)).2 (by linarith)
  apply (abs_sub_le _ (quotientHistory ⌊x⌋₊) _).trans
  rw [abs_of_nonneg p.1]
  linarith only [real_history_price x hx, p.2, mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (Nat.floor_le (zero_le_one.trans hx))) hB,
    mul_le_mul_of_nonneg_left hs alpogeNativeMoveConstant_nonneg,Real.sqrt_nonneg x]

/-- Log mass of the actual high first primes falling in odd quotient cells. -/
def highOddMass (q : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 (2*q)).filter (kept (2*q)), Real.log p * (((2*q/p)%2:ℕ):ℝ)

private theorem odd_factorial (q : ℕ) :
    ∑ i ∈ Finset.Icc 1 (2*q), (Λ i:ℝ)*(((2*q/i)%2:ℕ):ℝ) =
      Real.log ((2*q).factorial:ℝ) - 2*Real.log (q.factorial:ℝ) := by
  rw [← nativeVonMangoldtSummatory,← nativeVonMangoldtSummatory]
  have sub : Finset.Icc 1 q ⊆ Finset.Icc 1 (2*q) := Finset.Icc_subset_Icc le_rfl (by omega)
  have extSum := Finset.sum_subset (f := fun i : ℕ => (Λ i:ℝ)*((q/i:ℕ):ℝ)) sub (by
    intro i h hi
    have h₁ := (Finset.mem_Icc.mp h).1
    have hq : q < i := by contrapose! hi; exact Finset.mem_Icc.mpr ⟨h₁,hi⟩
    simp [Nat.div_eq_of_lt hq])
  rw [extSum,Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have id : (2*q/i)/2 = q/i := by
    rw [Nat.div_div_eq_div_mul,Nat.mul_comm i 2,←Nat.div_div_eq_div_mul]
    simp
  have b : (2*q/i)%2+2*(q/i) = 2*q/i := by omega
  have realId : ((((2*q/i)%2:ℕ):ℝ))+2*((q/i:ℕ):ℝ) = ((2*q/i:ℕ):ℝ) := by exact_mod_cast b
  linear_combination (Λ i:ℝ)*realId

/-- The independent central binomial coefficient prices the entire odd-cell
mass. The small first-prime and proper-power contributions have one sign. -/
theorem binomial_high_odd_mass :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q →
      0 ≤ Real.log (((2*q).choose q:ℕ):ℝ)-highOddMass q ∧
      Real.log (((2*q).choose q:ℕ):ℝ)-highOddMass q ≤ K*Real.sqrt (2*q:ℕ) ∧
      |highOddMass q-2*(q:ℝ)*Real.log 2| ≤ K*Real.sqrt (2*q:ℕ)+1+Real.log (2*q:ℕ)+2*Real.log q := by
  obtain ⟨K,hK,cap⟩ := removed_mass
  refine ⟨K,hK,?_⟩
  intro q hq
  have hq₂ : q ≤ 2*q := by omega
  have choose := Nat.choose_mul_factorial_mul_factorial hq₂
  rw [show 2*q-q=q by omega] at choose
  have chooseR := congrArg (fun k : ℕ => Real.log (k:ℝ)) choose
  have hpos : (0:ℝ) < ((2*q).choose q:ℕ) := by exact_mod_cast Nat.choose_pos hq₂
  have fac0 : (q.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  simp only [Nat.cast_mul,Real.log_mul (mul_ne_zero hpos.ne' fac0) fac0,Real.log_mul hpos.ne' fac0] at chooseR
  let bit (i : ℕ) := (((2*q/i)%2:ℕ):ℝ)
  have id : Real.log (((2*q).choose q:ℕ):ℝ)-highOddMass q =
      ∑ i ∈ Finset.Icc 1 (2*q), removed (2*q) i*bit i := by
    have parts : highOddMass q + (∑ i ∈ Finset.Icc 1 (2*q), removed (2*q) i*bit i) =
        ∑ i ∈ Finset.Icc 1 (2*q), (Λ i:ℝ)*bit i := by
      rw [highOddMass, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : kept (2*q) i
      · simp [removed,h,bit,ArithmeticFunction.vonMangoldt_apply_prime h.1]
      · simp [removed,h,bit]
    dsimp only [bit] at parts
    rw [odd_factorial] at parts
    linarith only [parts,chooseR]
  have lower : 0 ≤ Real.log (((2*q).choose q:ℕ):ℝ)-highOddMass q := id ▸
    Finset.sum_nonneg fun i _ => mul_nonneg (removed_nonneg _ i) (Nat.cast_nonneg _)
  have upper : Real.log (((2*q).choose q:ℕ):ℝ)-highOddMass q ≤ K*Real.sqrt (2*q:ℕ) := by
    rw [id]
    refine (Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (removed_nonneg (2*q) i) ?_).trans (cap _ (by omega))
    dsimp only [bit]
    exact_mod_cast (show (2*q/i)%2 ≤ 1 by omega)
  have a := abs_le.mp (nativeLogFactorial_sub_main_abs_le (2*q) (by omega))
  have b := abs_le.mp (nativeLogFactorial_sub_main_abs_le q hq)
  have logid : Real.log ((2*q:ℕ):ℝ) = Real.log 2 + Real.log q := by
    push_cast; rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hq)]
  rw [logid] at a
  push_cast at a
  refine ⟨lower,upper,abs_le.mpr ⟨?_,?_⟩⟩ <;>
    linarith only [lower,upper,a.1,a.2,b.1,b.2,chooseR,logid, mul_nonneg hK (Real.sqrt_nonneg ((2*q:ℕ):ℝ))]

/-- In the same coarse quotient cell, arbitrarily large odd primes can lie
one integer from its boundary. Their binomial hit is full and their
triangular crossing multiplier is exactly one over three times the prime. -/
theorem high_hit_boundary (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    let q := (3*p+1)/2
    (2*q).sqrt < p ∧ (2*q/p)%2 = 1 ∧
      2*(q:ℝ)/(3*p)-1 = 1/(3*(p:ℝ)) := by
  intro q
  have odd := hp.odd_of_ne_two (by omega)
  obtain ⟨a,ha⟩ := odd
  have twice : 2*q = 3*p+1 := by dsimp only [q]; omega
  have div : (2*q)/p = 3 := by
    rw [twice]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hs := Nat.sqrt_le (2*q)
  have pr : (2*q).sqrt < p := by
    by_contra! h
    have sq := Nat.mul_le_mul h h
    nlinarith only [hs,twice,sq,Nat.mul_le_mul_right p h5,h5]
  have realId : 2*(q:ℝ)=3*p+1 := by exact_mod_cast twice
  refine ⟨pr,by rw [div],?_⟩
  rw [realId, add_div, div_self (mul_ne_zero (by norm_num : (3:ℝ) ≠ 0)
    (show (p:ℝ) ≠ 0 by exact_mod_cast hp.ne_zero))]
  ring

/-- The affine part includes the original MAIN and every high-prime slope
already active at the left endpoint. -/
def affineReading (M : ℕ) (y z : ℝ) : ℝ :=
  (y-z)*((∑ i ∈ Finset.Icc 1 M, removed M i/i) +
    (∑ p ∈ (Finset.Icc 1 M).filter (kept M), if z < (p:ℝ) then 0 else Real.log p/p) +
    1+Real.eulerMascheroniConstant) - (y*Real.log y-z*Real.log z)

/-- The true triangular gains at new high first primes in this interval. -/
def crossing (M : ℕ) (y z : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M).filter (kept M),
    if z < (p:ℝ) then Real.log p * max (y/p-1) 0 else 0

private theorem crossing_nonneg (M : ℕ) (y z : ℝ) : 0 ≤ crossing M y z := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le)
  split <;> first | exact mul_nonneg hlog (le_max_right _ _) | exact le_rfl

private theorem reading_split (M : ℕ) {y z : ℝ} (hzy : z ≤ y) :
    firstPrimeValue M y-firstPrimeValue M z = affineReading M y z+crossing M y z := by
  let P := (Finset.Icc 1 M).filter (kept M)
  have source : (∑ p ∈ P, Real.log p*max (y/p-1) 0)-(∑ p ∈ P, Real.log p*max (z/p-1) 0) =
      (y-z)*(∑ p ∈ P, if z < (p:ℝ) then 0 else Real.log p/p)+crossing M y z := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, crossing, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have pp : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast pp.pos
    by_cases h : z < (p:ℝ)
    · simp [h, max_eq_right (sub_nonpos.mpr ((div_le_one hp0).2 h.le))]
    · have z₁ := (one_le_div hp0).2 (le_of_not_gt h)
      have y₁ := (one_le_div hp0).2 ((le_of_not_gt h).trans hzy)
      simp only [h,ite_false,max_eq_left (sub_nonneg.mpr z₁),max_eq_left (sub_nonneg.mpr y₁),add_zero]
      ring
  dsimp only [P] at source
  unfold firstPrimeValue affineReading
  linarith only [source]

/-- A fixed interior band gives a positive linear lower payment on the first
retained triangular crossing, uniformly in every sufficiently large integer
ancestor. The theta input is the native PNT. -/
theorem interior_crossing_gain :
    ∀ᶠ M : ℕ in Filter.atTop, (M:ℝ)/972 ≤ crossing M (2*((M/2:ℕ):ℝ)/3) (2*((M/2:ℕ):ℝ)/4) := by
  have lo := (tendsto_order.1 nativeTheta_div_atTop_one).1 (99/100) (by norm_num)
  have hi := (tendsto_order.1 nativeTheta_div_atTop_one).2 (101/100) (by norm_num)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 (lo.and hi)
  filter_upwards [Filter.eventually_ge_atTop (80*(N+80))] with M hM
  let h := M/80
  have hh : N+80 ≤ h := by dsimp [h]; omega
  have rangeM : M ≤ 81*h := by dsimp [h] at *; omega
  have hq : 80*h ≤ 2*(M/2) := by dsimp [h]; omega
  have hh0 : 0 < h := by omega
  have hθ₁ := (lt_div_iff₀ (by exact_mod_cast (show 0 < 22*h by omega) : (0:ℝ)<((22*h:ℕ):ℝ))).1
    ((hN (22*h) (by omega)).1)
  have hθ₂ := (div_lt_iff₀ (by exact_mod_cast (show 0 < 21*h by omega) : (0:ℝ)<((21*h:ℕ):ℝ))).1
    ((hN (21*h) (by omega)).2)
  push_cast at hθ₁ hθ₂
  let B := nativePrimeSet (22*h) \ nativePrimeSet (21*h)
  let P := (Finset.Icc 1 M).filter (kept M)
  have nested : nativePrimeSet (21*h) ⊆ nativePrimeSet (22*h) := by
    intro p hp; obtain ⟨ha,hp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.Icc_subset_Icc le_rfl (by omega) ha,hp⟩
  have mass := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) nested
  change (∑ p ∈ B, Real.log p)+nativeTheta (21*h) = nativeTheta (22*h) at mass
  have spec {p : ℕ} (hp : p ∈ B) : p.Prime ∧ 21*h < p ∧ p ≤ 22*h := by
    obtain ⟨large,small⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hc,prime⟩ := Finset.mem_filter.mp large
    exact ⟨prime,lt_of_not_ge fun hle => small (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨prime.one_le,hle⟩,prime⟩),
      (Finset.mem_Icc.mp hc).2⟩
  have root : M.sqrt ≤ 21*h := by
    by_contra! fail
    have sq := Nat.mul_le_mul fail.le fail.le
    have hsq : h ≤ h*h := Nat.le_mul_of_pos_left _ hh0
    nlinarith only [sq,Nat.sqrt_le M,rangeM,hsq,hh0]
  have sub : B ⊆ P := by
    intro p hp
    obtain ⟨pr,l,r⟩ := spec hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨pr.one_le,by omega⟩,pr,root.trans_lt l⟩
  let a := 2*((M/2:ℕ):ℝ)
  let f (p : ℕ) := if a/4 < (p:ℝ) then Real.log p*max ((a/3)/p-1) 0 else 0
  have alo : 80*(h:ℝ) ≤ a := by dsimp only [a]; exact_mod_cast hq
  have ahi : a ≤ 81*(h:ℝ) := by dsimp only [a]; exact_mod_cast (show 2*(M/2) ≤ 81*h by omega)
  have w (p : ℕ) (hp : p ∈ B) : Real.log p/6 ≤ f p := by
    obtain ⟨pr,l,r⟩ := spec hp
    have l' : 21*(h:ℝ) < p := by exact_mod_cast l
    have r' : (p:ℝ) ≤ 22*h := by exact_mod_cast r
    have pos : 0 < (p:ℝ) := by exact_mod_cast pr.pos
    have hit : a/4 < (p:ℝ) := by linarith
    have weight : (1:ℝ)/6 ≤ a/3/p-1 := by
      rw [le_sub_iff_add_le,le_div_iff₀ pos]
      linarith only [r',alo]
    dsimp only [f]
    rw [ite_eq_left hit]
    exact (show Real.log p/6 = Real.log p*(1/6) by ring).le.trans
      (mul_le_mul_of_nonneg_left (weight.trans (le_max_left _ _)) (Real.log_nonneg (by exact_mod_cast pr.one_le)))
  change _ ≤ ∑ p ∈ P, f p
  have sum : (∑ p ∈ B, Real.log p)/6 ≤ ∑ p ∈ P, f p := by
    rw [Finset.sum_div]
    refine (Finset.sum_le_sum w).trans (Finset.sum_le_sum_of_subset_of_nonneg sub ?_)
    intro p hp _
    have l : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le)
    dsimp only [f]
    split <;> first | exact mul_nonneg l (le_max_right _ _) | exact le_rfl
  have size : (M:ℝ) ≤ 81*h := by exact_mod_cast rangeM
  linarith only [sum,mass,hθ₁,hθ₂,size]

/-- The whole history with just the already-active slopes and original MAIN. -/
def affineHistory := sumHistory affineReading

private theorem history_gap_step (M : ℕ) (h : ¬ M < 16) :
    affineHistory M-firstPrimeHistory M = (affineHistory (M/2)-firstPrimeHistory (M/2)) +
      ∑ k ∈ Finset.Ico 1 ⌈Real.sqrt M⌉₊,
        crossing M (2*((M/2:ℕ):ℝ)/(2*(k:ℝ)+1)) (2*((M/2:ℕ):ℝ)/(2*(k:ℝ)+2)) := by
  let t (k : ℕ) := 2*((M/2:ℕ):ℝ)/(2*(k:ℝ)+1)
  let u (k : ℕ) := 2*((M/2:ℕ):ℝ)/(2*(k:ℝ)+2)
  let S := Finset.Ico 1 ⌈Real.sqrt M⌉₊
  have split : (∑ k ∈ S, (firstPrimeValue M (t k)-firstPrimeValue M (u k))) =
      (∑ k ∈ S, affineReading M (t k) (u k))+∑ k ∈ S, crossing M (t k) (u k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => reading_split M (div_le_div_of_nonneg_left (by positivity)
      (by positivity) (by linarith only) : u k ≤ t k)
  unfold affineHistory firstPrimeHistory
  rw [sumHistory_step _ M h,sumHistory_step _ M h]
  dsimp only [S,t,u] at split
  linarith only [split]

/-- Sum of the actual triangular crossing payments over all retained cells
and ancestors, with the positive sign of the gain. -/
def weightedCrossings (N : ℕ) : ℝ := -sumHistory crossing N

theorem affine_sub_weightedCrossings (N : ℕ) :
    affineHistory N-weightedCrossings N = firstPrimeHistory N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases short : N < 16
    · unfold affineHistory weightedCrossings firstPrimeHistory
      rw [sumHistory_small _ _ short,sumHistory_small _ _ short,sumHistory_small _ _ short]
      ring
    · have prev := ih (N/2) (by omega)
      unfold weightedCrossings at prev ⊢
      rw [sumHistory_step _ _ short]
      linarith only [prev,history_gap_step N short]

/-- The interior bands used by successive admissions are disjoint even with
the original integer cutoffs. -/
theorem interior_bands_separate {M m p : ℕ} (hm : m ≤ M/2) (hp : p ≤ 22*(m/80)) :
    p ≤ 21*(M/80) := by omega

/-- Every large dyadic ancestor contributes its own interior prime band.
Their gains accumulate with the original history signs. The finite initial
range and all integer halving losses fit one constant for all anchors. -/
theorem firstPrime_history_signed_gain :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, firstPrimeHistory M ≤ affineHistory M-(M:ℝ)/500+B := by
  have pos (M : ℕ) : 0 ≤ affineHistory M-firstPrimeHistory M := by
    induction M using Nat.strong_induction_on with
    | h M ih =>
      by_cases small : M < 16
      · unfold affineHistory firstPrimeHistory
        rw [sumHistory_small _ M small,sumHistory_small _ M small,sub_self]
      · rw [history_gap_step M small]
        exact add_nonneg (ih (M/2) (by omega)) (Finset.sum_nonneg fun _ _ => crossing_nonneg ..)
  have stage : ∀ᶠ M : ℕ in atTop, (M:ℝ)/972+(affineHistory (M/2)-firstPrimeHistory (M/2)) ≤
      affineHistory M-firstPrimeHistory M := by
    filter_upwards [interior_crossing_gain,Filter.eventually_ge_atTop 16] with M gain hM
    have hs : 4 ≤ Real.sqrt (M:ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg M)).2 (by exact_mod_cast hM)
    have four : 4 ≤ ⌈Real.sqrt M⌉₊ := by exact_mod_cast hs.trans (Nat.le_ceil _)
    have one : 1 ∈ Finset.Ico 1 ⌈Real.sqrt M⌉₊ := Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩
    have lower := Finset.single_le_sum (f := fun k : ℕ =>
      crossing M (2*((M/2:ℕ):ℝ)/(2*(k:ℝ)+1)) (2*((M/2:ℕ):ℝ)/(2*(k:ℝ)+2))) (fun k _ => crossing_nonneg ..) one
    norm_num at lower
    linarith only [history_gap_step M (by omega),gain,lower]
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.1 stage
  let A := max L 80
  refine ⟨(A:ℝ)/500,by positivity,?_⟩
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    by_cases short : M < A
    · have lt : (M:ℝ) ≤ A := by exact_mod_cast short.le
      linarith only [pos M,lt]
    · have hA := le_of_not_gt short
      have large : 80 ≤ M := (le_max_right L 80).trans hA
      have floorBill : (M:ℝ) ≤ 2*((M/2:ℕ):ℝ)+1 := by exact_mod_cast (show M ≤ 2*(M/2)+1 by omega)
      have size : (80:ℝ) ≤ M := by exact_mod_cast large
      linarith only [hL M ((le_max_left L 80).trans hA),ih (M/2) (by omega),floorBill,size]

private theorem principal_move {z y : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y) :
    |alpogeNativeGzArithmetic y-alpogeNativeGzArithmetic z| ≤ alpogeNativeMoveConstant*(y-z) := by
  have walk (j : ℕ) : ∀ z y : ℝ, 1 ≤ z → z ≤ y → y ≤ z+j →
      |alpogeNativeGzArithmetic y-alpogeNativeGzArithmetic z| ≤ alpogeNativeMoveConstant*(y-z) := by
    induction j with
    | zero =>
      intro z y _ lo hi
      have e : y=z := le_antisymm (by simpa using hi) lo
      simp [e]
    | succ j ih =>
      intro z y one lo hi
      by_cases h : y ≤ z+1
      · exact alpogeNativeGzArithmetic_sub_abs_le_of_le y z one lo h
      · push_cast at hi
        have left := alpogeNativeGzArithmetic_sub_abs_le_of_le (z+1) z one (by linarith) le_rfl
        have right := ih (z+1) y (by linarith) (by linarith) (by linarith)
        exact (abs_sub_le _ (alpogeNativeGzArithmetic (z+1)) _).trans (by linarith only [left,right])
  exact walk ⌈y-z⌉₊ z y hz hzy (by linarith only [Nat.le_ceil (y-z)])

/-- Variation along consecutive odd quotients. The signed principal response
costs at most its total physical length. All clipped prime powers together
have monotone variation bounded once at the original scale. -/
theorem odd_quotient_variation :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (M K R : ℕ) (a : ℝ), 1 ≤ M → 0 ≤ a → a ≤ M → K ≤ R →
      1 ≤ a/(2*(R:ℝ)+1) →
      let v (k : ℕ) := firstPrimeValue M (a/(2*(k:ℝ)+1))
      ∑ k ∈ Finset.Ico K R, |v k-v (k+1)| ≤ alpogeNativeMoveConstant*(a/(2*(K:ℝ)+1))+B*Real.sqrt M := by
  obtain ⟨B,hB,cap⟩ := removed_mass
  refine ⟨B,hB,?_⟩
  intro M K R a hM ha top kr one v
  let t (k : ℕ) := a/(2*(k:ℝ)+1)
  have ord : Antitone t := by
    intro i j h
    have hh : (i:ℝ) ≤ j := by exact_mod_cast h
    exact div_le_div_of_nonneg_left ha (by positivity) (by linarith)
  have below (k : ℕ) : t k ≤ M :=
    (div_le_self ha (by linarith only [Nat.cast_nonneg (α := ℝ) k] : (1:ℝ) ≤ 2*k+1)).trans top
  let s (k : ℕ) := alpogeNativeMoveConstant*t k+clip M (t k)
  have bound (k : ℕ) (hk : k < R) : |v k-v (k+1)| ≤ s k-s (k+1) := by
    have o := ord (Nat.le_succ k)
    have l : 1 ≤ t (k+1) := one.trans (ord hk)
    change |firstPrimeValue M (t k)-firstPrimeValue M (t (k+1))| ≤ _
    rw [physical M _ (by dsimp [t]; positivity) (below k),
      physical M _ (by dsimp [t]; positivity) (below (k+1)),
      show alpogeNativeGzArithmetic (t k)+clip M (t k)-
        (alpogeNativeGzArithmetic (t (k+1))+clip M (t (k+1))) =
        (alpogeNativeGzArithmetic (t k)-alpogeNativeGzArithmetic (t (k+1)))+
        (clip M (t k)-clip M (t (k+1))) by ring]
    have add := abs_add_le (alpogeNativeGzArithmetic (t k)-alpogeNativeGzArithmetic (t (k+1)))
      (clip M (t k)-clip M (t (k+1)))
    rw [abs_of_nonneg (sub_nonneg.mpr (clip_mono M o))] at add
    dsimp only [s]
    linarith only [add,principal_move l o]
  have tel (r : ℕ) (hr : K ≤ r) : ∑ k ∈ Finset.Ico K r, (s k-s (k+1)) = s K-s r := by
    induction r, hr using Nat.le_induction with
    | base => simp
    | succ r hr ih => rw [Finset.sum_Ico_succ_top hr, ih]; ring
  refine (Finset.sum_le_sum fun k hk => bound k (Finset.mem_Ico.mp hk).2).trans ?_
  rw [tel R kr]
  have nonneg (k : ℕ) : 0 ≤ t k := div_nonneg ha (by positivity)
  have b := ((clip_bounds M (nonneg K)).2).trans (cap M hM)
  dsimp only [s]
  linarith only [b,(clip_bounds M (nonneg R)).1,
    mul_nonneg alpogeNativeMoveConstant_nonneg (nonneg R)]

end RHLean.Analysis.PrincipalCofactor
