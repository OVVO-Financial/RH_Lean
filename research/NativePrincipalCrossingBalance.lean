import «research.NativePrincipalFirstPrimeHistory»

/-! The weighted crossing and its affine counterpart on the same physical
quotient cells. Multiplication by the cofactor makes every reciprocal
intercept constant. The second difference sees just a triangular prime
weight and the second difference of the logarithm in the original MAIN. -/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis.PrincipalCofactor

private def cap (d u : ℝ) : ℝ := min 1 (max (u-d) 0)

/-- The prime's triangular weight across the two adjacent cofactor segments. -/
def crossingTent (d u : ℝ) : ℝ := cap d u-cap (d+1) u

private theorem cap_antitone (u : ℝ) : Antitone (fun d => cap d u) :=
  fun _ _ h => min_le_min_left _ (max_le_max_right _ (sub_le_sub_left h u))

private theorem cap_nonneg (d u : ℝ) : 0 ≤ cap d u := le_min (by norm_num) (le_max_right _ _)

private theorem cap_ramp (d u : ℝ) : cap d u = max (u-d) 0-max (u-(d+1)) 0 := by
  simp only [cap,min_def,max_def]
  split_ifs <;> linarith

theorem crossingTent_eq (d u : ℝ) : crossingTent d u = max (1-|u-(d+1)|) 0 := by
  unfold crossingTent cap
  rcases le_total u d with h|h
  · have a : u-d ≤ 0 := by linarith
    have b : u-(d+1) ≤ 0 := by linarith
    rw [abs_of_nonpos b,max_eq_right a,max_eq_right b,max_eq_right (by linarith)]
    norm_num
  · rcases le_total u (d+1) with h'|h'
    · have b : u-(d+1) ≤ 0 := by linarith
      rw [abs_of_nonpos b,max_eq_left (by linarith : 0 ≤ u-d),max_eq_right b,
        min_eq_right (by linarith : u-d ≤ 1),min_eq_right (by norm_num : (0:ℝ) ≤ 1),
        max_eq_left (by linarith)]
      ring
    · have b : 0 ≤ u-(d+1) := by linarith
      rw [abs_of_nonneg b,max_eq_left (by linarith : 0 ≤ u-d),max_eq_left b,
        min_eq_left (by linarith : 1 ≤ u-d)]
      rcases le_total (u-(d+1)) 1 with t|t
      · rw [min_eq_right t,max_eq_left (by linarith)]
      · rw [min_eq_left t,max_eq_right (by linarith),sub_self]

private theorem tent_ramps (d u : ℝ) : crossingTent d u =
    max (u-d) 0-2*max (u-(d+1)) 0+max (u-(d+2)) 0 := by
  rw [crossingTent,cap_ramp,cap_ramp,show d+1+1 = d+2 by ring]
  ring

private def primeSet (M : ℕ) := (Finset.Icc 1 M).filter (fun p => p.Prime ∧ M.sqrt < p)

def tentMass (M : ℕ) (a d : ℝ) : ℝ :=
  ∑ p ∈ primeSet M, Real.log p * crossingTent d (a/p)

private def logStep (d : ℝ) : ℝ := Real.log (1+1/d)

def logCurvature (d : ℝ) : ℝ := logStep d-logStep (d+1)

private theorem logStep_eq {d : ℝ} (hd : 0 < d) : logStep d = Real.log (d+1)-Real.log d := by
  rw [logStep,show 1+1/d=(d+1)/d by field_simp,Real.log_div (by positivity) hd.ne']

/-- Exact mass comparison on one cofactor pair, with the adjacent odd
endpoint retained. The terms linear in the height have cancelled exactly. -/
theorem cofactor_second_difference (M : ℕ) {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    d*firstPrimeValue M (a/d)-2*((d+1)*firstPrimeValue M (a/(d+1)))+
      (d+2)*firstPrimeValue M (a/(d+2)) = tentMass M a d-a*logCurvature d := by
  have mass : tentMass M a d =
      (∑ p ∈ primeSet M, Real.log p*max (a/p-d) 0) -
      2*(∑ p ∈ primeSet M, Real.log p*max (a/p-(d+1)) 0) +
      ∑ p ∈ primeSet M, Real.log p*max (a/p-(d+2)) 0 := by
    rw [tentMass, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [tent_ramps]; ring
  rw [scaled_firstPrimeValue _ ha hd, scaled_firstPrimeValue _ ha (by positivity),
    scaled_firstPrimeValue _ ha (by positivity),mass,logCurvature,logStep_eq hd,
    logStep_eq (by positivity),show d+1+1=d+2 by ring]
  dsimp only [primeSet]
  ring

private def odd (k : ℕ) : ℝ := 2*(k:ℝ)+1
private def endpoint (M : ℕ) : ℝ := 2*((M/2:ℕ):ℝ)
private def price (k : ℕ) : ℝ := 1/(2*(odd k+1))

/-- Both adjacent odd endpoints of the actual high-prime reading. -/
def chord (M k : ℕ) : ℝ :=
  ((odd k+2)/(2*(odd k+1)))*(firstPrimeValue M (endpoint M/odd k)-
    firstPrimeValue M (endpoint M/(odd k+2)))

/-- Arithmetic mass less the original logarithmic MAIN on this pair. -/
def crossingBalance (M k : ℕ) : ℝ :=
  price k*(tentMass M (endpoint M) (odd k)-endpoint M*logCurvature (odd k))

theorem weighted_cell_eq (M k : ℕ) (hM : 2 ≤ M) :
    firstPrimeValue M (endpoint M/odd k)-firstPrimeValue M (endpoint M/(odd k+1)) =
      chord M k+crossingBalance M k := by
  have ha : 0 < endpoint M := by
    have h : 0 < M/2 := by omega
    dsimp [endpoint]; positivity
  have hd : 0 < odd k := by dsimp [odd]; positivity
  have den : 2*(odd k+1) ≠ 0 := by positivity
  unfold chord crossingBalance price
  rw [← cofactor_second_difference M ha hd]
  field_simp
  <;> ring

private theorem paired_drop (F : ℕ → ℝ) (hF : Antitone F) (K R : ℕ) (h : K ≤ R) :
    ∑ k ∈ Finset.Ico K R, (F (2*k)-F (2*k+1)) ≤ F (2*K)-F (2*R) := by
  induction R, h using Nat.le_induction with
  | base => simp
  | succ R h ih =>
    rw [Finset.sum_Ico_succ_top h]
    linarith only [ih,hF (show 2*R+1 ≤ 2*(R+1) by omega)]

private theorem total_tent (K R : ℕ) (h : K ≤ R) (u : ℝ) :
    ∑ k ∈ Finset.Ico K R, crossingTent (odd k) u ≤ cap (odd K) u := by
  let f (j : ℕ) := cap ((j:ℝ)+1) u
  have drop := paired_drop f (fun _ _ hj => cap_antitone u (by dsimp [f]; exact_mod_cast Nat.succ_le_succ hj)) K R h
  have eq (k : ℕ) : crossingTent (odd k) u = f (2*k)-f (2*k+1) := by simp [crossingTent,odd,f]
  simp_rw [eq]
  exact drop.trans ((sub_le_self _ (cap_nonneg _ _)).trans_eq (by simp [f,odd]))

private theorem total_mass (M K R : ℕ) (h : K ≤ R) (a : ℝ) (ha : 0 ≤ a) :
    ∑ k ∈ Finset.Ico K R, tentMass M a (odd k) ≤ Real.log 4*(a/odd K) := by
  let Q := ⌊a/odd K⌋₊
  let P := primeSet M
  have hd : 0 < odd K := by dsimp [odd]; positivity
  have l (p : ℕ) (hp : p ∈ P) : 0 ≤ Real.log (p:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le)
  have subset : P.filter (fun p => p ≤ Q) ⊆ nativePrimeSet Q := by
    intro p hp
    obtain ⟨mem,le⟩ := Finset.mem_filter.mp hp
    have pr := (Finset.mem_filter.mp mem).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨pr.one_le,le⟩,pr⟩
  have bound (p : ℕ) (hp : p ∈ P) : Real.log p*(∑ k ∈ Finset.Ico K R, crossingTent (odd k) (a/p)) ≤
      if p ≤ Q then Real.log p else 0 := by
    have b := total_tent K R h (a/p)
    by_cases cut : p ≤ Q
    · rw [ite_eq_left cut]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (b.trans (min_le_left _ _)) (l p hp)
    · rw [ite_eq_right cut]
      have out : a/odd K < (p:ℝ) := Nat.lt_of_floor_lt (lt_of_not_ge cut)
      have pp : 0 < (p:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos
      have u : a/p ≤ odd K := (div_le_iff₀ pp).2 (by linarith only [((div_lt_iff₀ hd).1 out)])
      have cz : cap (odd K) (a/p) = 0 := by simp [cap,max_eq_right (sub_nonpos.mpr u)]
      exact mul_nonpos_of_nonneg_of_nonpos (l p hp) (b.trans_eq cz)
  calc
    _ = ∑ p ∈ P, Real.log p*(∑ k ∈ Finset.Ico K R, crossingTent (odd k) (a/p)) := by
      unfold tentMass
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum ..).symm
    _ ≤ ∑ p ∈ P, if p ≤ Q then Real.log p else 0 := Finset.sum_le_sum bound
    _ ≤ nativeTheta Q := by
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg subset (fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
    _ ≤ _ := (nativeTheta_le_log4_mul Q).trans (mul_le_mul_of_nonneg_left
      (Nat.floor_le (div_nonneg ha hd.le)) (Real.log_nonneg (by norm_num)))

private theorem logStep_mono {d e : ℝ} (hd : 0 < d) (h : d ≤ e) : logStep e ≤ logStep d :=
  Real.log_le_log (by have := hd.trans_le h; positivity) (add_le_add_left (one_div_le_one_div_of_le hd h) _)

private theorem total_log (K R : ℕ) (h : K ≤ R) :
    ∑ k ∈ Finset.Ico K R, logCurvature (odd k) ≤ 1/odd K := by
  let f (j : ℕ) := logStep ((j:ℝ)+1)
  have drop := paired_drop f (fun _ _ hj => logStep_mono (by positivity)
    (by exact_mod_cast Nat.succ_le_succ hj)) K R h
  have eq (k : ℕ) : logCurvature (odd k) = f (2*k)-f (2*k+1) := by simp [logCurvature,odd,f]
  simp_rw [eq]
  have last : 0 ≤ f (2*R) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  refine drop.trans ((sub_le_self _ last).trans ?_)
  have hd : 0 < odd K := by dsimp [odd]; positivity
  have est := Real.log_le_sub_one_of_pos (show 0 < 1+1/odd K by positivity)
  simpa [f,odd,logStep] using est

/-- All paired curvatures from K onwards together. Each physical prime has
total triangular weight at most one and must lie below a/(2K+1). -/
theorem fine_crossing_price (M K R : ℕ) (h : K ≤ R) :
    ∑ k ∈ Finset.Ico K R, |crossingBalance M k| ≤
      (Real.log 4+1)*(endpoint M/odd K)*(1/odd K) := by
  let a := endpoint M
  have ha : 0 ≤ a := by dsimp [a,endpoint]; positivity
  have hd (k : ℕ) : 0 < odd k := by dsimp [odd]; positivity
  have mass (k : ℕ) : 0 ≤ tentMass M a (odd k) :=
    Finset.sum_nonneg fun p hp => mul_nonneg (Real.log_nonneg
      (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le)) (sub_nonneg.mpr (cap_antitone _ (by linarith)))
  have logc (k : ℕ) : 0 ≤ logCurvature (odd k) := sub_nonneg.mpr (logStep_mono (hd k) (by linarith))
  have point (k : ℕ) (hk : k ∈ Finset.Ico K R) :
      |crossingBalance M k| ≤ (1/odd K)*(tentMass M a (odd k)+a*logCurvature (odd k)) := by
    have le : (K:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
    have price0 : 0 ≤ price k := by dsimp [price,odd]; positivity
    have priceK : price k ≤ 1/odd K := one_div_le_one_div_of_le (hd K) (by dsimp [odd]; linarith only [le,Nat.cast_nonneg (α := ℝ) k])
    rw [crossingBalance,abs_mul,abs_of_nonneg price0]
    exact mul_le_mul priceK ((abs_sub _ _).trans_eq (by rw [abs_of_nonneg (mass k),abs_of_nonneg (mul_nonneg ha (logc k))]))
      (abs_nonneg _) (one_div_pos.mpr (hd K)).le
  refine (Finset.sum_le_sum point).trans ?_
  rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum]
  have combined := add_le_add (total_mass M K R h a ha) (mul_le_mul_of_nonneg_left (total_log K R h) ha)
  exact (mul_le_mul_of_nonneg_left combined (one_div_pos.mpr (hd K)).le).trans_eq (by dsimp only [a]; ring)

end RHLean.Analysis.PrincipalCofactor
