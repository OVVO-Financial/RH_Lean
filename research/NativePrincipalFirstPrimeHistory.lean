import «research.NativePrincipalCofactorTrace»
import RHLean.Analysis.AlpogeNativeProperPowerCentering

/-! On each dyadic ancestor, retain the first primes above its square root in
the interval readings. All other original atoms keep their finite reciprocal
intercept. Disjoint cofactor intervals share a single clipping charge. -/

noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt Classical

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
    · simp only [hi, if_false, removed, zero_add]
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
    exact_mod_cast (show (2*q/i)%2 ≤ 1 by omega)
  have a := abs_le.mp (nativeLogFactorial_sub_main_abs_le (2*q) (by omega))
  have b := abs_le.mp (nativeLogFactorial_sub_main_abs_le q hq)
  have logid : Real.log ((2*q:ℕ):ℝ) = Real.log 2 + Real.log q := by
    push_cast; rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by exact_mod_cast hq.ne')]
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
  refine ⟨pr,by rw [div]; decide,?_⟩
  rw [realId]
  field_simp [show (p:ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  <;> ring

end RHLean.Analysis.PrincipalCofactor
