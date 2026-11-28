import «research.NativeSignSchurHandoff»
import Mathlib.NumberTheory.Padics.PadicNorm

/-! Sparse physical anchors remove all accidental cofactor primes.
Their local determinant changes are exactly the admitted Euler factors.
The global signed price is computed rather than discarded. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.AlpogeThin.SlotProjector.SparseHeight

open TrueZeroSchur

/-- The indicator of one original layer, not an additional top. -/
def anchor {r : ℕ} (j : Fin (r+1)) (i : Fin (r+1)) : ℝ :=
  if i=j then 1 else 0

theorem anchor_normal {r : ℕ} (D : Fin (r+1) → ℕ) (j : Fin (r+1)) :
    (∑ i, (wheelNormal D i:ℝ)*anchor j i) = wheelNormal D j := by
  classical
  simp [anchor, mul_ite]

theorem sparse_amplitude_det {r : ℕ} (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i)
    (j : Fin (r+1)) :
    (amplitude (fun i => (D i:ℝ)) (anchor j)).det = wheelNormal D j := by
  rw [amplitude_det D hD, anchor_normal]

theorem sparse_gram_det {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i) (j : Fin (r+1)) :
    (WheelNNS.coDiv (anchoredColumns S D (anchor j))).det =
      (∏ i, ((S i).card:ℝ))*(wheelNormal D j:ℝ)^2 := by
  rw [augmented_det S D hD, anchor_normal]

theorem sparse_pivot {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (j : Fin (r+1)) :
    WheelNNS.coDiv (anchoredColumns S D (anchor j)) 0 0 = (S j).card := by
  classical
  rw [WheelNNS.coDiv_eq, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, anchoredColumns_zero]
  rw [Fintype.sum_sigma]
  simp [anchor, ite_mul]

theorem sparse_schur_det {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (hD : ∀ i, 0 < D i) (j : Fin (r+1))
    (hS : (S j).Nonempty) :
    (schur (WheelNNS.coDiv (anchoredColumns S D (anchor j)))).det =
      (∏ i, ((S i).card:ℝ))*(wheelNormal D j:ℝ)^2/(S j).card := by
  have hp : WheelNNS.coDiv (anchoredColumns S D (anchor j)) 0 0 ≠ 0 := by
    rw [sparse_pivot]
    exact_mod_cast hS.card_pos.ne'
  rw [native_schur_det S D hD (anchor j) hp, anchor_normal, sparse_pivot]

/-- The local omitted normal is literally the product of the remaining
prime powers; this is a rational certificate of the actual determinant. -/
def factor (p u v : ℕ) : ℚ := (p:ℚ)^u/(p:ℚ)^v

def ratio {I : Type*} [Fintype I] (p b a : I → ℕ) : ℚ :=
  ∏ i, factor (p i) (b i) (a i)

def omitted {I : Type*} [Fintype I] [DecidableEq I] (p b a : I → ℕ) (j : I) : ℚ :=
  ∏ i ∈ Finset.univ.erase j, factor (p i) (b i) (a i)

theorem omitted_mul {I : Type*} [Fintype I] [DecidableEq I]
    (p b a : I → ℕ) (j : I) :
    omitted p b a j * factor (p j) (b j) (a j) = ratio p b a :=
  Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ j)

theorem omitted_eq_normal {r : ℕ} (p b a : Fin (r+1) → ℕ) :
    ∀ j, omitted p b a j =
      (wheelNormal (fun i => (p i)^(b i)) j:ℚ)/
        (wheelNormal (fun i => (p i)^(a i)) j:ℚ) := by
  intro j
  simp only [omitted,factor,wheelNormal,Nat.cast_prod,Nat.cast_pow,Finset.prod_div_distrib]

private theorem factor_pos (p u v : ℕ) (hp : 0 < p) : 0 < factor p u v := by
  unfold factor
  positivity

/-- Restore the omitted coordinate exactly: no estimate of prime
distribution is used in this finite log identity. -/
theorem log_omitted_add {I : Type*} [Fintype I] [DecidableEq I]
    (p b a : I → ℕ) (hp : ∀ i, 0 < p i) (j : I) :
    Real.log (omitted p b a j:ℝ) +
      ((b j:ℝ)-a j)*Real.log (p j) = Real.log (ratio p b a:ℝ) := by
  have hO : 0 < omitted p b a j := Finset.prod_pos fun i _ => factor_pos _ _ _ (hp i)
  have hF := factor_pos (p j) (b j) (a j) (hp j)
  have eqn := congrArg (fun q : ℚ => Real.log (q:ℝ)) (omitted_mul p b a j)
  simp only [Rat.cast_mul] at eqn
  rw [Real.log_mul (by exact_mod_cast hO.ne') (by exact_mod_cast hF.ne')] at eqn
  have term : Real.log (factor (p j) (b j) (a j):ℝ) =
      ((b j:ℝ)-a j)*Real.log (p j) := by
    simp only [factor,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast]
    have h : (p j:ℝ) ≠ 0 := by exact_mod_cast (hp j).ne'
    rw [Real.log_div (pow_ne_zero _ h) (pow_ne_zero _ h),Real.log_pow,Real.log_pow]
    ring
  rw [term] at eqn
  exact eqn

theorem log_ratio {I : Type*} [Fintype I]
    (p b a : I → ℕ) (hp : ∀ i, 0 < p i) :
    Real.log (ratio p b a:ℝ) = ∑ i, ((b i:ℝ)-a i)*Real.log (p i) := by
  classical
  unfold ratio
  rw [Rat.cast_prod, Real.log_prod (fun i _ => by exact_mod_cast (factor_pos _ _ _ (hp i)).ne')]
  apply Finset.sum_congr rfl
  intro i _
  simp only [factor,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast]
  have h : (p i:ℝ) ≠ 0 := by exact_mod_cast (hp i).ne'
  rw [Real.log_div (pow_ne_zero _ h) (pow_ne_zero _ h),Real.log_pow,Real.log_pow]
  ring

private theorem norm_prod {I : Type*} (l : ℕ) [Fact l.Prime]
    (s : Finset I) (f : I → ℚ) :
    padicNorm l (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm l (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, padicNorm.mul, ih]

private theorem norm_pow (l : ℕ) [Fact l.Prime] (q : ℚ) (k : ℕ) :
    padicNorm l (q^k) = (padicNorm l q)^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,padicNorm.mul,ih,pow_succ]

theorem factor_norm_other (l p b a : ℕ) [Fact l.Prime] (hp : p.Prime) (hne : l ≠ p) :
    padicNorm l (factor p b a) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [factor,padicNorm.div,norm_pow,norm_pow,padicNorm.padicNorm_of_prime_of_ne hne]
  simp

theorem factor_norm_self (p b a : ℕ) [Fact p.Prime] :
    padicNorm p (factor p b a) = ((p:ℚ)⁻¹)^b/((p:ℚ)⁻¹)^a := by
  rw [factor,padicNorm.div,norm_pow,norm_pow,padicNorm.padicNorm_p_of_prime]

/-- At the admitted place the sparse pivot is exactly the one that
removes that place's Euler factor; all remaining factors are units. -/
theorem omitted_norm_self {I : Type*} [Fintype I] [DecidableEq I]
    (p b a : I → ℕ) (hp : ∀ i, (p i).Prime) (hi : Function.Injective p) (j : I)
    [Fact (p j).Prime] :
    padicNorm (p j) (omitted p b a j) = 1 := by
  rw [omitted,norm_prod]
  apply Finset.prod_eq_one
  intro i hm
  exact factor_norm_other _ _ _ _ (hp i) (fun h => (Finset.mem_erase.mp hm).1 (hi h).symm)

/-- There are no accidental finite primes in the sparse determinant. -/
theorem omitted_norm_outside {I : Type*} [Fintype I] [DecidableEq I]
    (p b a : I → ℕ) (hp : ∀ i, (p i).Prime) (l : ℕ) [Fact l.Prime]
    (hl : ∀ i, l ≠ p i) (j : I) :
    padicNorm l (omitted p b a j) = 1 := by
  rw [omitted,norm_prod]
  exact Finset.prod_eq_one fun i _ => factor_norm_other _ _ _ _ (hp i) (hl i)

theorem ratio_norm_self {I : Type*} [Fintype I] [DecidableEq I]
    (p b a : I → ℕ) (hp : ∀ i, (p i).Prime) (hi : Function.Injective p) (j : I)
    [Fact (p j).Prime] :
    padicNorm (p j) (ratio p b a) =
      (((p j):ℚ)⁻¹)^(b j)/(((p j):ℚ)⁻¹)^(a j) := by
  rw [← omitted_mul p b a j,padicNorm.mul,omitted_norm_self p b a hp hi j,
    one_mul,factor_norm_self]

theorem ratio_norm_outside {I : Type*} [Fintype I]
    (p b a : I → ℕ) (hp : ∀ i, (p i).Prime) (l : ℕ) [Fact l.Prime]
    (hl : ∀ i, l ≠ p i) :
    padicNorm l (ratio p b a) = 1 := by
  rw [ratio,norm_prod]
  exact Finset.prod_eq_one fun i _ => factor_norm_other _ _ _ _ (hp i) (hl i)

/-- The precise all-place log price of one fixed global ratio. -/
theorem log_norm_ratio {I : Type*} [Fintype I] [DecidableEq I]
    (p b a : I → ℕ) (hp : ∀ i, (p i).Prime) (hi : Function.Injective p) (j : I) :
    Real.log (padicNorm (p j) (ratio p b a):ℝ) =
      -((b j:ℝ)-a j)*Real.log (p j) := by
  letI : Fact (p j).Prime := ⟨hp j⟩
  rw [ratio_norm_self p b a hp hi j,Rat.cast_div,Rat.cast_pow,Rat.cast_pow,
    Rat.cast_inv,Rat.cast_natCast]
  have h : (p j:ℝ) ≠ 0 := by exact_mod_cast (hp j).ne_zero
  rw [Real.log_div (pow_ne_zero _ (inv_ne_zero h)) (pow_ne_zero _ (inv_ne_zero h)),
    Real.log_pow,Real.log_pow,Real.log_inv]
  ring

/-- For the fixed ratio the product formula is exact on the original
admitted primes. Its local-unit replacements have removed precisely
the signed price, not a harmless auxiliary normalization. -/
theorem ratio_log_product {I : Type*} [Fintype I] [DecidableEq I]
    (p b a : I → ℕ) (hp : ∀ i, (p i).Prime) (hi : Function.Injective p) :
    Real.log (ratio p b a:ℝ) +
      ∑ i, Real.log (padicNorm (p i) (ratio p b a):ℝ) = 0 := by
  rw [log_ratio p b a (fun i => (hp i).pos)]
  simp_rw [log_norm_ratio p b a hp hi, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Global recovery of the signed arithmetic amount: all pivots
together include each admitted factor exactly d-1 times. -/
theorem all_pivot_log {I : Type*} [Fintype I] [DecidableEq I]
    (p b a : I → ℕ) (hp : ∀ i, 0 < p i) :
    (∑ j, Real.log (omitted p b a j:ℝ)) =
      ((Fintype.card I:ℝ)-1)*Real.log (ratio p b a:ℝ) := by
  classical
  have eqn : (∑ j, (Real.log (omitted p b a j:ℝ) +
      ((b j:ℝ)-a j)*Real.log (p j))) =
      ∑ _j : I, Real.log (ratio p b a:ℝ) :=
    Finset.sum_congr rfl fun j _ => log_omitted_add p b a hp j
  rw [Finset.sum_add_distrib,← log_ratio p b a hp] at eqn
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at eqn
  linarith only [eqn]

/-- The primitive sparse dual on one physical layer. Only the original
depth and measured layer cardinality occur in the denominator. -/
def test {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (j : Fin (r+1)) (k : Fin r) (i : Fin (r+1)) : ℚ :=
  ((if i=k.succ then 1 else 0)-(if j=k.succ then 1 else 0))/
    (((S i).card:ℚ)*(D i:ℚ))

@[simp] theorem test_pivot {r : ℕ} (S : Fin (r+1) → Finset ℕ)
    (D : Fin (r+1) → ℕ) (j : Fin (r+1)) (k : Fin r) : test S D j k j = 0 := by
  simp [test]

/-- Both the original signed star and its projection off the sparse
anchor pair with the same actual test. The removed layer is zero
in that test, not discarded from the arithmetic source. -/
theorem test_pair {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i)
    (j : Fin (r+1)) (k l : Fin r) :
    (∑ i, ((S i).card:ℝ)*(amplitude (fun i => (D i:ℝ)) (anchor j) i l.succ)*
      (test S D j k i:ℝ)) = if k=l then 1 else 0 := by
  classical
  let B : Fin (r+1) → ℝ := fun i => (if i=k.succ then 1 else 0)-(if j=k.succ then 1 else 0)
  have term (i : Fin (r+1)) :
      ((S i).card:ℝ)*(amplitude (fun i => (D i:ℝ)) (anchor j) i l.succ)*
        (test S D j k i:ℝ) =
      ((if i=l.succ then 1 else 0)-(if i=0 then 1 else 0))*B i := by
    have hn : ((S i).card:ℝ) ≠ 0 := by exact_mod_cast (hS i).card_pos.ne'
    have hd : (D i:ℝ) ≠ 0 := by exact_mod_cast (hD i).ne'
    simp only [test,amplitude,Fin.cases_succ,Rat.cast_div,Rat.cast_mul,
      Rat.cast_sub,Rat.cast_ite,Rat.cast_one,Rat.cast_zero,Rat.cast_natCast,B]
    field_simp [hn,hd]
    ring
  rw [Finset.sum_congr rfl (fun i _ => term i)]
  have hsum : (∑ i, ((if i=l.succ then 1 else 0)-(if i=0 then 1 else 0))*B i) =
      B l.succ-B 0 := by
    simp only [sub_mul,Finset.sum_sub_distrib,ite_mul,one_mul,zero_mul]
    simp
  rw [hsum]
  by_cases h : k=l
  · subst l
    simp [B, (Fin.succ_ne_zero k).symm]
  · have hn : l.succ ≠ k.succ := fun he => h ((Fin.succ_injective r he).symm)
    simp [B, h, hn, (Fin.succ_ne_zero k).symm]

/-- Actual measured real energy, with no inverse Gram determinant.
A sharper rowwise sum is given in the companion paper derivation. -/
theorem test_energy {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (hS : ∀ i, (S i).Nonempty) (hD : ∀ i, 0 < D i)
    (j : Fin (r+1)) (k : Fin r) (m : ℝ) (hm : 0 < m)
    (hmin : ∀ i, m ≤ ((S i).card:ℝ)) :
    slotEnergy S (fun i => (test S D j k i:ℝ)) ≤ (r+1:ℕ)/m := by
  classical
  unfold slotEnergy
  calc
    _ ≤ ∑ _i : Fin (r+1), (1/m:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      let n : ℝ := (S i).card
      let d : ℝ := D i
      have hn : 0 < n := hm.trans_le (hmin i)
      have hd : 1 ≤ d := by exact_mod_cast hD i
      have hdn : 0 < d := by linarith
      let b : ℝ := (if i=k.succ then 1 else 0)-(if j=k.succ then 1 else 0)
      have hb : b^2 ≤ 1 := by
        dsimp only [b]
        split_ifs <;> norm_num
      have hf : (test S D j k i:ℝ) = b/(n*d) := by
        simp only [test,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,
          Rat.cast_ite,Rat.cast_one,Rat.cast_zero,Rat.cast_natCast,b,n,d]
      change n*(test S D j k i:ℝ)^2 ≤ _
      rw [hf]
      have hnd : 0 < n*d^2 := mul_pos hn (sq_pos_of_pos hdn)
      calc
        _ = b^2/(n*d^2) := by field_simp [hn.ne',hdn.ne']; ring
        _ ≤ 1/(n*d^2) := div_le_div_of_nonneg_right hb hnd.le
        _ ≤ 1/m := by
          have hh : 1 ≤ d^2 := by nlinarith only [hd, sq_nonneg (d-1)]
          have hmul := mul_le_mul_of_nonneg_left hh hn.le
          exact one_div_le_one_div_of_le hm ((hmin i).trans (by simpa using hmul))
    _ = _ := by simp [div_eq_mul_inv]

/-- The same coefficient formula is integral at every place where the
retained depth and measured cardinality are units. No condition on the
pivot's depth is imposed. -/
theorem test_place {r : ℕ} (S : Fin (r+1) → Finset ℕ) (D : Fin (r+1) → ℕ)
    (j : Fin (r+1)) (k : Fin r) (l : ℕ) [Fact l.Prime]
    (hu : ∀ i, i ≠ j → ¬ l ∣ (S i).card ∧ ¬ l ∣ D i) :
    ∀ i, padicNorm l (test S D j k i) ≤ 1 := by
  intro i
  by_cases hi : i=j
  · subst i
    simp
  · have hN := (padicNorm.nat_eq_one_iff ((S i).card)).2 (hu i hi).1
    have hD := (padicNorm.nat_eq_one_iff (D i)).2 (hu i hi).2
    rw [test,padicNorm.div,padicNorm.mul,hN,hD,mul_one,div_one]
    split_ifs <;> norm_num [padicNorm.neg,padicNorm.one,padicNorm.zero]

/-- The rational product formula, proved here from the finite prime
factorization of a natural number. No external height theorem is
used. The cutoff can be chosen beyond both numerator and denominator. -/
theorem nat_log_product (n M : ℕ) (hn : 0 < n) (hM : n < M) :
    Real.log (n:ℝ) +
      ∑ l ∈ (Finset.range M).filter Nat.Prime, Real.log (padicNorm l (n:ℚ):ℝ) = 0 := by
  classical
  let S := (Finset.range M).filter Nat.Prime
  have hp (l : ℕ) (hl : l ∈ S) : l.Prime := (Finset.mem_filter.mp hl).2
  have hprod := congrArg (fun k : ℕ => Real.log (k:ℝ))
    (Nat.prod_pow_prime_padicValNat n hn.ne' M hM)
  change Real.log ((↑(∏ l ∈ S, l^padicValNat l n):ℝ)) = Real.log (n:ℝ) at hprod
  rw [Nat.cast_prod, Real.log_prod (fun l hl => pow_ne_zero _ (by exact_mod_cast (hp l hl).ne_zero))] at hprod
  simp only [Nat.cast_pow,Real.log_pow] at hprod
  have term (l : ℕ) (hl : l ∈ S) : Real.log (padicNorm l (n:ℚ):ℝ) =
      -(padicValNat l n:ℝ)*Real.log (l:ℝ) := by
    have hnq : (n:ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [padicNorm.eq_zpow_of_nonzero hnq, Rat.cast_zpow, Rat.cast_natCast,
      Real.log_zpow,padicValRat.of_nat,Int.cast_neg,Int.cast_natCast]
  change Real.log (n:ℝ) + (∑ l ∈ S, Real.log (padicNorm l (n:ℚ):ℝ)) = 0
  rw [Finset.sum_congr rfl term]
  simp_rw [neg_mul,Finset.sum_neg_distrib]
  linarith only [hprod]

theorem quotient_log_product (A B M : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hMA : A < M) (hMB : B < M) :
    Real.log ((A:ℝ)/B) +
      ∑ l ∈ (Finset.range M).filter Nat.Prime, Real.log (padicNorm l ((A:ℚ)/B):ℝ) = 0 := by
  classical
  let S := (Finset.range M).filter Nat.Prime
  have h1 := nat_log_product A M hA hMA
  have h2 := nat_log_product B M hB hMB
  have hAr : (A:ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBr : (B:ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hAq : (A:ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBq : (B:ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have term (l : ℕ) (hl : l ∈ S) :
      Real.log (padicNorm l ((A:ℚ)/B):ℝ) =
        Real.log (padicNorm l (A:ℚ):ℝ)-Real.log (padicNorm l (B:ℚ):ℝ) := by
    letI : Fact l.Prime := ⟨(Finset.mem_filter.mp hl).2⟩
    rw [padicNorm.div,Rat.cast_div,Real.log_div
      (by exact_mod_cast padicNorm.nonzero hAq)
      (by exact_mod_cast padicNorm.nonzero hBq)]
  change Real.log ((A:ℝ)/B) + (∑ l ∈ S, Real.log (padicNorm l ((A:ℚ)/B):ℝ)) = 0
  rw [Real.log_div hAr hBr,Finset.sum_congr rfl term,Finset.sum_sub_distrib]
  linarith only [h1,h2]

/-- Recentring by a rational witness cannot improve the total signed
height of a fixed ratio. This equality retains both the archimedean
and all finite places, with a single common witness A/B. -/
theorem common_witness_log (A B C D M : ℕ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hAC : A*C < M) (hBD : B*D < M) :
    Real.log ((A:ℝ)/B) +
      ∑ l ∈ (Finset.range M).filter Nat.Prime,
        Real.log (padicNorm l (((A:ℚ)/B)*((C:ℚ)/D)):ℝ) =
      -Real.log ((C:ℝ)/D) := by
  have h := quotient_log_product (A*C) (B*D) M (Nat.mul_pos hA hC)
    (Nat.mul_pos hB hD) hAC hBD
  have hA' : (A:ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hB' : (B:ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hC' : (C:ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hD' : (D:ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast at h
  rw [show (A:ℝ)*C/((B:ℝ)*D) = ((A:ℝ)/B)*((C:ℝ)/D) by ring,
    Real.log_mul (div_ne_zero hA' hB') (div_ne_zero hC' hD'),
    show (A:ℚ)*C/((B:ℚ)*D) = ((A:ℚ)/B)*((C:ℚ)/D) by ring] at h
  linarith only [h]

end RHLean.Analysis.AlpogeThin.SlotProjector.SparseHeight
