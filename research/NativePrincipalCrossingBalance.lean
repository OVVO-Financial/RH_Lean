import «research.NativePrincipalFirstPrimeHistory»
import RHLean.Geometry.AlpogeAllPlace.Formalism.CorankShare.CorankShareProofs.LayerCakeFormula

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

def tentMass (M : ℕ) (a d : ℝ) : ℝ :=
  ∑ p ∈ retainedFirstPrimes M, Real.log p * crossingTent d (a/p)

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
      (∑ p ∈ retainedFirstPrimes M, Real.log p*max (a/p-d) 0) -
      2*(∑ p ∈ retainedFirstPrimes M, Real.log p*max (a/p-(d+1)) 0) +
      ∑ p ∈ retainedFirstPrimes M, Real.log p*max (a/p-(d+2)) 0 := by
    rw [tentMass, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [tent_ramps]; ring
  rw [scaled_firstPrimeValue _ ha hd, scaled_firstPrimeValue _ ha (by positivity),
    scaled_firstPrimeValue _ ha (by positivity),mass,logCurvature,logStep_eq hd,
    logStep_eq (by positivity),show d+1+1=d+2 by ring]
  ring

def oddCofactor (k : ℕ) : ℝ := 2*(k:ℝ)+1
def evenEndpoint (M : ℕ) : ℝ := 2*((M/2:ℕ):ℝ)
def cellWeight (k : ℕ) : ℝ := 1/(2*(oddCofactor k+1))

/-- Both adjacent odd endpoints of the actual high-prime reading. -/
def chord (M k : ℕ) : ℝ :=
  ((oddCofactor k+2)/(2*(oddCofactor k+1)))*(firstPrimeValue M (evenEndpoint M/oddCofactor k)-
    firstPrimeValue M (evenEndpoint M/(oddCofactor k+2)))

/-- Arithmetic mass less the original logarithmic MAIN on this pair. -/
def crossingBalance (M k : ℕ) : ℝ :=
  cellWeight k*(tentMass M (evenEndpoint M) (oddCofactor k)-evenEndpoint M*logCurvature (oddCofactor k))

theorem weighted_cell_eq (M k : ℕ) (hM : 2 ≤ M) :
    firstPrimeValue M (evenEndpoint M/oddCofactor k)-firstPrimeValue M (evenEndpoint M/(oddCofactor k+1)) =
      chord M k+crossingBalance M k := by
  have ha : 0 < evenEndpoint M := by
    have h : 0 < M/2 := by omega
    dsimp [evenEndpoint]; positivity
  have hd : 0 < oddCofactor k := by dsimp [oddCofactor]; positivity
  have den : 2*(oddCofactor k+1) ≠ 0 := by positivity
  unfold chord crossingBalance cellWeight
  rw [← cofactor_second_difference M ha hd]
  field_simp
  ring

private theorem paired_drop (F : ℕ → ℝ) (hF : Antitone F) (K R : ℕ) (h : K ≤ R) :
    ∑ k ∈ Finset.Ico K R, (F (2*k)-F (2*k+1)) ≤ F (2*K)-F (2*R) := by
  induction R, h using Nat.le_induction with
  | base => simp
  | succ R h ih =>
    rw [Finset.sum_Ico_succ_top h]
    linarith only [ih,hF (show 2*R+1 ≤ 2*(R+1) by omega)]

private theorem total_tent (K R : ℕ) (h : K ≤ R) (u : ℝ) :
    ∑ k ∈ Finset.Ico K R, crossingTent (oddCofactor k) u ≤ cap (oddCofactor K) u := by
  let f (j : ℕ) := cap ((j:ℝ)+1) u
  have drop := paired_drop f (fun _ _ hj => cap_antitone u (by exact_mod_cast Nat.succ_le_succ hj)) K R h
  have eq (k : ℕ) : crossingTent (oddCofactor k) u = f (2*k)-f (2*k+1) := by simp [crossingTent,oddCofactor,f]
  simp_rw [eq]
  exact drop.trans ((sub_le_self _ (cap_nonneg _ _)).trans_eq (by simp [f,oddCofactor]))

private theorem total_mass (M K R : ℕ) (h : K ≤ R) (a : ℝ) (ha : 0 ≤ a) :
    ∑ k ∈ Finset.Ico K R, tentMass M a (oddCofactor k) ≤ Real.log 4*(a/oddCofactor K) := by
  let Q := ⌊a/oddCofactor K⌋₊
  let P := retainedFirstPrimes M
  have hd : 0 < oddCofactor K := by dsimp [oddCofactor]; positivity
  have l (p : ℕ) (hp : p ∈ P) : 0 ≤ Real.log (p:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le)
  have subset : P.filter (fun p => p ≤ Q) ⊆ nativePrimeSet Q := by
    intro p hp
    obtain ⟨mem,le⟩ := Finset.mem_filter.mp hp
    have pr := (Finset.mem_filter.mp mem).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨pr.one_le,le⟩,pr⟩
  have bound (p : ℕ) (hp : p ∈ P) : Real.log p*(∑ k ∈ Finset.Ico K R, crossingTent (oddCofactor k) (a/p)) ≤
      if p ≤ Q then Real.log p else 0 := by
    have b := total_tent K R h (a/p)
    by_cases cut : p ≤ Q
    · rw [ite_eq_left cut]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (b.trans (min_le_left _ _)) (l p hp)
    · rw [ite_eq_right cut]
      have out : a/oddCofactor K < (p:ℝ) := Nat.lt_of_floor_lt (lt_of_not_ge cut)
      have pp : 0 < (p:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos
      have u : a/p ≤ oddCofactor K := (div_le_iff₀ pp).2 (by linarith only [((div_lt_iff₀ hd).1 out)])
      have cz : cap (oddCofactor K) (a/p) = 0 := by simp [cap,max_eq_right (sub_nonpos.mpr u)]
      exact mul_nonpos_of_nonneg_of_nonpos (l p hp) (b.trans_eq cz)
  calc
    _ = ∑ p ∈ P, Real.log p*(∑ k ∈ Finset.Ico K R, crossingTent (oddCofactor k) (a/p)) := by
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
  Real.log_le_log (by have := hd.trans_le h; positivity) (add_le_add le_rfl (one_div_le_one_div_of_le hd h))

private theorem total_log (K R : ℕ) (h : K ≤ R) :
    ∑ k ∈ Finset.Ico K R, logCurvature (oddCofactor k) ≤ 1/oddCofactor K := by
  let f (j : ℕ) := logStep ((j:ℝ)+1)
  have drop := paired_drop f (fun _ _ hj => logStep_mono (by positivity)
    (by exact_mod_cast Nat.succ_le_succ hj)) K R h
  have eq (k : ℕ) : logCurvature (oddCofactor k) = f (2*k)-f (2*k+1) := by simp [logCurvature,oddCofactor,f]
  simp_rw [eq]
  have last : 0 ≤ f (2*R) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  refine drop.trans ((sub_le_self _ last).trans ?_)
  have hd : 0 < oddCofactor K := by dsimp [oddCofactor]; positivity
  have est := Real.log_le_sub_one_of_pos (show 0 < 1+1/oddCofactor K by positivity)
  simpa [f,oddCofactor,logStep] using est

/-- All paired curvatures from K onwards together. Each physical prime has
total triangular weight at most one and must lie below a/(2K+1). -/
theorem fine_crossing_price (M K R : ℕ) (h : K ≤ R) :
    ∑ k ∈ Finset.Ico K R, |crossingBalance M k| ≤
      (Real.log 4+1)*(evenEndpoint M/oddCofactor K)*(1/oddCofactor K) := by
  let a := evenEndpoint M
  have ha : 0 ≤ a := by dsimp [a,evenEndpoint]; positivity
  have hd (k : ℕ) : 0 < oddCofactor k := by dsimp [oddCofactor]; positivity
  have mass (k : ℕ) : 0 ≤ tentMass M a (oddCofactor k) :=
    Finset.sum_nonneg fun p hp => mul_nonneg (Real.log_nonneg
      (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le)) (sub_nonneg.mpr (cap_antitone _ (by linarith)))
  have logc (k : ℕ) : 0 ≤ logCurvature (oddCofactor k) := sub_nonneg.mpr (logStep_mono (hd k) (by linarith))
  have point (k : ℕ) (hk : k ∈ Finset.Ico K R) :
      |crossingBalance M k| ≤ (1/oddCofactor K)*(tentMass M a (oddCofactor k)+a*logCurvature (oddCofactor k)) := by
    have le : (K:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
    have price0 : 0 ≤ cellWeight k := by dsimp [cellWeight,oddCofactor]; positivity
    have priceK : cellWeight k ≤ 1/oddCofactor K := one_div_le_one_div_of_le (hd K) (by dsimp [oddCofactor]; linarith only [le,Nat.cast_nonneg (α := ℝ) k])
    rw [crossingBalance,abs_mul,abs_of_nonneg price0]
    exact mul_le_mul priceK ((abs_sub _ _).trans_eq (by rw [abs_of_nonneg (mass k),abs_of_nonneg (mul_nonneg ha (logc k))]))
      (abs_nonneg _) (one_div_pos.mpr (hd K)).le
  refine (Finset.sum_le_sum point).trans ?_
  rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum]
  have combined := add_le_add (total_mass M K R h a ha) (mul_le_mul_of_nonneg_left (total_log K R h) ha)
  exact (mul_le_mul_of_nonneg_left combined (one_div_pos.mpr (hd K)).le).trans_eq (by dsimp only [a]; ring)

def oddPrimeReading (M k : ℕ) : ℝ := firstPrimeValue M (evenEndpoint M/oddCofactor k)
def primePairReading (M k : ℕ) : ℝ :=
  oddPrimeReading M k-firstPrimeValue M (evenEndpoint M/(oddCofactor k+1))

private theorem odd_next (k : ℕ) : oddCofactor (k+1) = oddCofactor k+2 := by unfold oddCofactor; push_cast; ring

/-- The complete crossing identity on an arbitrary contiguous set of retained
cells. Both sums on the right are measured on its original high primes. -/
theorem all_cells_eq (M K R : ℕ) (hM : 2 ≤ M) :
    (∑ k ∈ Finset.Ico K R, (firstPrimeValue M (evenEndpoint M/oddCofactor k)-
      firstPrimeValue M (evenEndpoint M/(oddCofactor k+1)))) =
      (∑ k ∈ Finset.Ico K R, chord M k)+∑ k ∈ Finset.Ico K R, crossingBalance M k := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => weighted_cell_eq M k hM

private theorem residual_pair (M k : ℕ) (hm : 2 ≤ M) :
    primePairReading M k = (oddPrimeReading M k-oddPrimeReading M (k+1))/2 +
      (cellWeight k*(oddPrimeReading M k-oddPrimeReading M (k+1))+crossingBalance M k) := by
  change firstPrimeValue M _-firstPrimeValue M _ = _
  rw [weighted_cell_eq M k hm]
  unfold chord oddPrimeReading
  rw [odd_next]
  have hd : 0 < oddCofactor k := by dsimp [oddCofactor]; positivity
  have factor : (oddCofactor k+2)/(2*(oddCofactor k+1))=1/2+cellWeight k := by
    dsimp only [cellWeight]
    field_simp
    ring
  rw [factor]
  ring

/-- The entire fine part of both the affine and crossing readings reduces
to one endpoint difference. The square-root clipping cost is shared by all
pairs. No estimate of individual prime gaps or a principal window is used. -/
theorem fine_pairs_to_endpoints :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M K R : ℕ, 2 ≤ M → K ≤ R → 1 ≤ evenEndpoint M/oddCofactor R →
      |(∑ k ∈ Finset.Ico K R, primePairReading M k)-
        (oddPrimeReading M K-oddPrimeReading M R)/2| ≤
      (Real.log 4+1+alpogeNativeMoveConstant)*(evenEndpoint M/oddCofactor K)*(1/oddCofactor K)+B*Real.sqrt M := by
  obtain ⟨B,hB,variation⟩ := odd_quotient_variation
  refine ⟨B,hB,?_⟩
  intro M K R hm kr one
  have hd (j : ℕ) : 0 < oddCofactor j := by dsimp [oddCofactor]; positivity
  have oneD : 1/oddCofactor K ≤ 1 := (div_le_one (hd K)).2 (by dsimp [oddCofactor]; linarith only [Nat.cast_nonneg (α := ℝ) K])
  let diff (k : ℕ) := oddPrimeReading M k-oddPrimeReading M (k+1)
  let S := Finset.Ico K R
  have tel (r : ℕ) (hr : K ≤ r) : ∑ k ∈ Finset.Ico K r, diff k = oddPrimeReading M K-oddPrimeReading M r := by
    induction r, hr using Nat.le_induction with
    | base => simp
    | succ r hr ih => rw [Finset.sum_Ico_succ_top hr, ih]; dsimp only [diff]; ring
  have split : (∑ k ∈ S, primePairReading M k)-(oddPrimeReading M K-oddPrimeReading M R)/2 =
      (∑ k ∈ S, cellWeight k*diff k)+∑ k ∈ S, crossingBalance M k := by
    simp_rw [residual_pair M _ hm]
    change (∑ k ∈ S, (diff k/2+(cellWeight k*diff k+crossingBalance M k)))-_ = _
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.sum_div,tel R kr]
    ring
  have scale : evenEndpoint M ≤ M := by dsimp only [evenEndpoint]; exact_mod_cast (show 2*(M/2) ≤ M by omega)
  have v := variation M K R (evenEndpoint M) (by omega) (by dsimp [evenEndpoint]; positivity) scale kr one
  change ∑ k ∈ S, |diff k| ≤ alpogeNativeMoveConstant*(evenEndpoint M/oddCofactor K)+B*Real.sqrt M at v
  have e : |∑ k ∈ S, cellWeight k*diff k| ≤ (1/oddCofactor K)*(alpogeNativeMoveConstant*(evenEndpoint M/oddCofactor K)+B*Real.sqrt M) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun k => (1/oddCofactor K)*|diff k|) fun k hk => ?_).trans ?_
    · have le : (K:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
      have cost : cellWeight k ≤ 1/oddCofactor K := one_div_le_one_div_of_le (hd K)
        (by dsimp [oddCofactor]; linarith only [le,Nat.cast_nonneg (α := ℝ) k])
      rw [abs_mul,abs_of_nonneg (by dsimp [cellWeight,oddCofactor]; positivity : 0 ≤ cellWeight k)]
      exact mul_le_mul_of_nonneg_right cost (abs_nonneg _)
    · rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left v (one_div_pos.mpr (hd K)).le
  rw [split]
  have paid : |∑ k ∈ S, crossingBalance M k| ≤ _ :=
    (Finset.abs_sum_le_sum_abs _ _).trans (fine_crossing_price M K R kr)
  have b := mul_le_mul_of_nonneg_right oneD (mul_nonneg hB (Real.sqrt_nonneg (M:ℝ)))
  exact (abs_add_le ..).trans (by linarith only [e,paid,b])

/-- Cut off the cofactor pairs at the fourth root, with the two endpoints
of all finer pairs retained as a single signed reading. -/
def quarterStep (M : ℕ) : ℝ :=
  let K := ⌈Real.sqrt (Real.sqrt M)⌉₊
  let R := ⌈Real.sqrt M⌉₊
  (∑ k ∈ Finset.Ico 1 K, (chord M k+crossingBalance M k))+
    (oddPrimeReading M K-oddPrimeReading M R)/2

private theorem quarter_parameters (M : ℕ) (hm : 16 ≤ M) :
    let K := ⌈Real.sqrt (Real.sqrt M)⌉₊
    let R := ⌈Real.sqrt M⌉₊
    1 ≤ K ∧ K ≤ R ∧ 1 ≤ evenEndpoint M/oddCofactor R ∧ (evenEndpoint M/oddCofactor K)*(1/oddCofactor K) ≤ Real.sqrt M := by
  intro K R
  have m16 : (16:ℝ) ≤ M := by exact_mod_cast hm
  have sr := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) M)
  have pos := Real.sqrt_nonneg (M:ℝ)
  have four : 4 ≤ Real.sqrt (M:ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg M)).2 (by exact_mod_cast hm)
  have small : 4*Real.sqrt (M:ℝ) ≤ M := by nlinarith only [sr,mul_le_mul_of_nonneg_right four pos]
  have qpos := Real.sqrt_nonneg (Real.sqrt (M:ℝ))
  have qsq := Real.sq_sqrt pos
  have qone : 1 ≤ Real.sqrt (Real.sqrt (M:ℝ)) := (Real.le_sqrt (by norm_num) pos).2 (by linarith)
  have kr : K ≤ R := Nat.ceil_le.mpr ((Real.sqrt_le_sqrt (by linarith : Real.sqrt (M:ℝ) ≤ M)).trans (Nat.le_ceil _))
  have aM : evenEndpoint M ≤ M := by dsimp only [evenEndpoint]; exact_mod_cast (show 2*(M/2) ≤ M by omega)
  have Ma : (M:ℝ) ≤ evenEndpoint M+1 := by dsimp only [evenEndpoint]; exact_mod_cast (show M ≤ 2*(M/2)+1 by omega)
  have Rcap : (R:ℝ) ≤ Real.sqrt M+1 := (Nat.ceil_lt_add_one pos).le
  have kd : Real.sqrt (Real.sqrt (M:ℝ)) ≤ oddCofactor K := by
    have qK : Real.sqrt (Real.sqrt (M:ℝ)) ≤ (K:ℝ) := Nat.le_ceil _
    dsimp only [oddCofactor]
    linarith only [qK,Nat.cast_nonneg (α := ℝ) K]
  have dp : 0 < oddCofactor K := by dsimp [oddCofactor]; positivity
  have sq : Real.sqrt (M:ℝ) ≤ oddCofactor K * oddCofactor K := by
    nlinarith only [qsq,pow_le_pow_left₀ qpos kd 2]
  refine ⟨by exact_mod_cast qone.trans (Nat.le_ceil _),kr,
    (one_le_div (by dsimp [oddCofactor]; positivity)).2 (by dsimp only [oddCofactor]; linarith only [small,Ma,Rcap,m16]),?_⟩
  rw [show evenEndpoint M/oddCofactor K*(1/oddCofactor K) = evenEndpoint M/(oddCofactor K*oddCofactor K) by ring]
  apply (div_le_iff₀ (mul_pos dp dp)).2
  nlinarith only [aM,sr,mul_le_mul_of_nonneg_left sq pos]

theorem quarter_step_price :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 16 ≤ M →
      |(∑ k ∈ Finset.Ico 1 ⌈Real.sqrt M⌉₊, primePairReading M k)-quarterStep M| ≤ C*Real.sqrt M := by
  obtain ⟨B,hB,tail⟩ := fine_pairs_to_endpoints
  let c := Real.log 4+1+alpogeNativeMoveConstant
  have hc : 0 ≤ c := by dsimp [c]; linarith only [alpogeNativeMoveConstant_nonneg,Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
  refine ⟨c+B,add_nonneg hc hB,?_⟩
  intro M hm
  let K := ⌈Real.sqrt (Real.sqrt M)⌉₊
  let R := ⌈Real.sqrt M⌉₊
  obtain ⟨one,kr,room,root⟩ := quarter_parameters M hm
  have bound := tail M K R (by omega) kr room
  have coarse : ∑ k ∈ Finset.Ico 1 K, primePairReading M k =
      ∑ k ∈ Finset.Ico 1 K, (chord M k+crossingBalance M k) :=
    Finset.sum_congr rfl fun k _ => weighted_cell_eq M k (by omega)
  have split := Finset.sum_Ico_consecutive (f := primePairReading M) one kr
  change |(∑ k ∈ Finset.Ico 1 R, primePairReading M k)-((∑ k ∈ Finset.Ico 1 K, _)+_)| ≤ _
  rw [← split,coarse,show ∀ b t u : ℝ, (b+t)-(b+u)=t-u by intros; ring]
  change _ ≤ c*(evenEndpoint M/oddCofactor K)*(1/oddCofactor K)+B*Real.sqrt M at bound
  linarith only [bound,mul_le_mul_of_nonneg_left root hc]

/-- Complete signed dyadic sum with one endpoint pair replacing the fine
cells at each ancestor. All broad cells retain their logarithmic MAIN. -/
def quarterHistory (N : ℕ) : ℝ :=
  if _h : N < 16 then 0 else quarterHistory (N/2)-quarterStep N
termination_by N
decreasing_by omega

theorem quarter_history_price :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, |firstPrimeHistory N-quarterHistory N| ≤ K*Real.sqrt N := by
  obtain ⟨C,hC,estimate⟩ := quarter_step_price
  refine ⟨4*C,by positivity,?_⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases small : N < 16
    · have base : quarterHistory N = 0 := by rw [quarterHistory]; simp [small]
      rw [base,firstPrimeHistory,sumHistory_small _ _ small]
      simpa only [sub_zero,abs_zero] using mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC) (Real.sqrt_nonneg (N:ℝ))
    · let q := N/2
      let S := ∑ k ∈ Finset.Ico 1 ⌈Real.sqrt N⌉₊, primePairReading N k
      have step : firstPrimeHistory N = firstPrimeHistory q-S := by
        rw [firstPrimeHistory,sumHistory_step _ _ small]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        unfold primePairReading oddPrimeReading evenEndpoint oddCofactor
        rw [show 2*(k:ℝ)+1+1=2*k+2 by ring]
      have half : (q:ℝ)*2 ≤ N := by exact_mod_cast (show q*2 ≤ N by dsimp [q]; omega)
      have root : Real.sqrt (q:ℝ) ≤ (3/4)*Real.sqrt N := (Real.sqrt_le_iff).2
        ⟨by positivity,by nlinarith only [half,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N),Nat.cast_nonneg (α := ℝ) N]⟩
      have price := estimate N (by omega)
      have prev := ih q (by dsimp [q]; omega)
      have big : quarterHistory N = quarterHistory q-quarterStep N := by rw [quarterHistory]; simp [small,q]
      rw [step,big,show firstPrimeHistory q-S-(quarterHistory q-quarterStep N) =
        (firstPrimeHistory q-quarterHistory q)-(S-quarterStep N) by ring]
      exact (abs_sub _ _).trans (by linarith only [prev,price,mul_le_mul_of_nonneg_left root hC])

/-- No local thresholds depend on the chosen real anchor. -/
theorem real_quarter_history_price :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |alpogeNativeGzArithmetic x-quarterHistory ⌊x⌋₊| ≤ C*Real.sqrt x := by
  obtain ⟨A,hA,a⟩ := real_firstPrime_history_price
  obtain ⟨B,hB,b⟩ := quarter_history_price
  refine ⟨A+B,by positivity,?_⟩
  intro x hx
  exact (abs_sub_le _ (firstPrimeHistory ⌊x⌋₊) _).trans (by
    linarith only [a x hx,b ⌊x⌋₊,mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Nat.floor_le (zero_le_one.trans hx))) hB])

section
open MeasureTheory
open RHLean.Geometry.AlpogeAllPlace.Formalism.CorankShareLayerCake.FR.Pgsn2pfran

private def activeMass (M : ℕ) (a v : ℝ) : ℝ :=
  ∑ p ∈ retainedFirstPrimes M, Real.log p * (if v < a/p then (1:ℝ) else 0)

/-- The centered Chebyshev count in the cofactor variable. -/
def cofactorDiscrepancy (M : ℕ) (a v : ℝ) : ℝ := activeMass M a v-a/v

theorem cofactorDiscrepancy_eq (M : ℕ) (a : ℝ) {v : ℝ} (hv : 0 < v) :
    cofactorDiscrepancy M a v =
      (∑ p ∈ (retainedFirstPrimes M).filter (fun p : ℕ => (p:ℝ) < a/v), Real.log p)-a/v := by
  rw [cofactorDiscrepancy,activeMass,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have pp : 0 < (p:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos
  have iff : v < a/p ↔ (p:ℝ) < a/v := by rw [lt_div_iff₀ pp,lt_div_iff₀ hv,mul_comm]
  by_cases cut : (p:ℝ) < a/v <;> simp [iff,cut]

private theorem integral_cap (d u : ℝ) :
    (∫ s in (0:ℝ)..1, if s < u-d then (1:ℝ) else 0) = cap d u := by
  by_cases lo : 0 ≤ u-d
  · by_cases hi : u-d ≤ 1
    · rw [ind_int _ _ lo hi,cap,max_eq_left lo,min_eq_right hi]
    · have eq : (∫ s in (0:ℝ)..1, if s < u-d then (1:ℝ) else 0) = ∫ _s in (0:ℝ)..1, (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le zero_le_one] at hs
        simp [hs.2.trans_lt (lt_of_not_ge hi)]
      rw [eq,cap,max_eq_left lo,min_eq_left (le_of_not_ge hi)]
      norm_num
  · have eq : (∫ s in (0:ℝ)..1, if s < u-d then (1:ℝ) else 0) = ∫ _s in (0:ℝ)..1, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le zero_le_one] at hs
      simp [not_lt.mpr ((le_of_not_ge lo).trans hs.1)]
    rw [eq,cap,max_eq_right (le_of_not_ge lo)]
    norm_num

private theorem active_anti (M : ℕ) (a d : ℝ) : Antitone (fun s => activeMass M a (d+s)) := by
  intro s t h
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left (ind_anti (a/(p:ℝ)) (add_le_add le_rfl h))
    (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le))

private theorem integrated_active (M : ℕ) (a d : ℝ) :
    (∫ s in (0:ℝ)..1, activeMass M a (d+s)) = ∑ p ∈ retainedFirstPrimes M, Real.log p*cap d (a/p) := by
  have obs (s : ℝ) : activeMass M a (d+s) =
      ∑ p ∈ retainedFirstPrimes M, Real.log p*(if s < a/p-d then (1:ℝ) else 0) := by
    unfold activeMass
    apply Finset.sum_congr rfl
    intro p _
    simp only [show d+s < a/p ↔ s < a/p-d by constructor <;> intro h <;> linarith]
  simp_rw [obs]
  rw [intervalIntegral.integral_finsetSum (fun (p : ℕ) _ => ((ind_anti (a/(p:ℝ)-d)).intervalIntegrable).const_mul (Real.log p))]
  exact Finset.sum_congr rfl fun p _ => by rw [intervalIntegral.integral_const_mul,integral_cap]

private theorem density_integrable (a : ℝ) {d : ℝ} (hd : 0 < d) :
    IntervalIntegrable (fun s : ℝ => a/(d+s)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_const.div (continuousOn_const.add continuousOn_id) ?_
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  exact (lt_of_lt_of_le hd (le_add_of_nonneg_right hs.1)).ne'

private theorem integrated_density (a : ℝ) {d : ℝ} (hd : 0 < d) :
    (∫ s in (0:ℝ)..1, a/(d+s)) = a*logStep d := by
  have shift := intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) (a := 0) (b := 1) d
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul,shift,integral_inv_of_pos (by linarith) (by linarith)]
  simp only [add_zero]
  rw [logStep,show 1+1/d=(d+1)/d by field_simp]

private theorem discrepancy_integrable (M : ℕ) (a : ℝ) {d : ℝ} (hd : 0 < d) :
    IntervalIntegrable (fun s => cofactorDiscrepancy M a (d+s)) volume 0 1 :=
  (active_anti M a d).intervalIntegrable.sub (density_integrable a hd)

/-- Exact discrepancy balance on two equal cofactor intervals. A common
constant discrepancy has zero contribution. Unit spatial density gives
exactly the original log curvature with its original scale. -/
theorem tent_minus_main_eq_integral (M : ℕ) (a : ℝ) {d : ℝ} (hd : 0 < d) :
    tentMass M a d-a*logCurvature d =
      ∫ s in (0:ℝ)..1, (cofactorDiscrepancy M a (d+s)-cofactorDiscrepancy M a (d+1+s)) := by
  have one : 0 < d+1 := by linarith
  rw [intervalIntegral.integral_sub (discrepancy_integrable M a hd) (discrepancy_integrable M a one)]
  simp only [cofactorDiscrepancy]
  rw [intervalIntegral.integral_sub (active_anti M a d).intervalIntegrable (density_integrable a hd),
    intervalIntegral.integral_sub (active_anti M a (d+1)).intervalIntegrable (density_integrable a one),
    integrated_active,integrated_active,integrated_density a hd,integrated_density a one]
  have split : tentMass M a d = (∑ p ∈ retainedFirstPrimes M, Real.log p*cap d (a/p))-
      ∑ p ∈ retainedFirstPrimes M, Real.log p*cap (d+1) (a/p) := by
    rw [tentMass,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by rw [crossingTent,mul_sub]
  rw [split,logCurvature]
  ring

/-- High-prime log mass in the actual moving interval, less its length.
The lower endpoint is included and the upper endpoint is excluded. -/
def movingExcess (M : ℕ) (a v : ℝ) : ℝ :=
  (∑ p ∈ (retainedFirstPrimes M).filter (fun p : ℕ => a/(v+1) ≤ (p:ℝ) ∧ (p:ℝ) < a/v), Real.log p)-
    (a/v-a/(v+1))

theorem moving_eq (M : ℕ) {a v : ℝ} (ha : 0 ≤ a) (hv : 0 < v) :
    cofactorDiscrepancy M a v-cofactorDiscrepancy M a (v+1) = movingExcess M a v := by
  have lo : a/(v+1) ≤ a/v := div_le_div_of_nonneg_left ha hv (by linarith)
  let P := retainedFirstPrimes M
  let U := a/v
  let L := a/(v+1)
  have count : (∑ p ∈ P.filter (fun p : ℕ => (p:ℝ) < U), Real.log p)-
      (∑ p ∈ P.filter (fun p : ℕ => (p:ℝ) < L), Real.log p) =
      ∑ p ∈ P.filter (fun p : ℕ => L ≤ (p:ℝ) ∧ (p:ℝ) < U), Real.log p := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases low : (p:ℝ) < L
    · have up : (p:ℝ) < U := low.trans_le lo
      simp [low,up,not_le.mpr low]
    · have hit : L ≤ (p:ℝ) := le_of_not_gt low
      simp [low,hit]
  rw [cofactorDiscrepancy_eq _ _ hv,cofactorDiscrepancy_eq _ _ (by linarith),movingExcess]
  dsimp only [P,U,L] at count
  linarith only [count]

/-- Complete weighted identity with every retained affine counterpart.
The integral averages actual interval discrepancies over the same shift s. -/
theorem all_cells_centered (M K R : ℕ) (hm : 2 ≤ M) :
    (∑ k ∈ Finset.Ico K R, primePairReading M k) = (∑ k ∈ Finset.Ico K R, chord M k)+
      ∫ s in (0:ℝ)..1, ∑ k ∈ Finset.Ico K R, cellWeight k*movingExcess M (evenEndpoint M) (oddCofactor k+s) := by
  let a := evenEndpoint M
  let S := Finset.Ico K R
  let E (k : ℕ) (s : ℝ) := cofactorDiscrepancy M a (oddCofactor k+s)-
    cofactorDiscrepancy M a (oddCofactor k+1+s)
  have hd (k : ℕ) : 0 < oddCofactor k := by dsimp [oddCofactor]; positivity
  have hint (k : ℕ) : IntervalIntegrable (fun s => cellWeight k*E k s) volume 0 1 :=
    ((discrepancy_integrable M a (hd k)).sub (discrepancy_integrable M a (d := oddCofactor k+1)
      (by linarith only [hd k]))).const_mul _
  have joint : (∫ s in (0:ℝ)..1, ∑ k ∈ S, cellWeight k*movingExcess M a (oddCofactor k+s)) =
      ∫ s in (0:ℝ)..1, ∑ k ∈ S, cellWeight k*E k s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [E]
    rw [show oddCofactor k+1+s=(oddCofactor k+s)+1 by ring,
      moving_eq M (by dsimp [a,evenEndpoint]; positivity) (by linarith only [hd k,hs.1])]
  unfold primePairReading oddPrimeReading
  rw [all_cells_eq M K R hm,joint,intervalIntegral.integral_finsetSum (fun k _ => hint k)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_const_mul,crossingBalance,tent_minus_main_eq_integral _ _ (hd k)]


/-- A single shift prices the whole retained sum from the side needed in the
dyadic history. The unit rounding is uniform in both endpoints and in M. -/
theorem exists_common_shift_lower (M K R : ℕ) (hm : 2 ≤ M) :
    ∃ s ∈ Set.Icc (0:ℝ) 1,
      (∑ k ∈ Finset.Ico K R, (chord M k + cellWeight k*movingExcess M (evenEndpoint M) (oddCofactor k+s)))
        ≤ (∑ k ∈ Finset.Ico K R, primePairReading M k)+1 := by
  let a := evenEndpoint M
  let S := Finset.Ico K R
  let E (k : ℕ) (s : ℝ) := cofactorDiscrepancy M a (oddCofactor k+s)-
    cofactorDiscrepancy M a (oddCofactor k+1+s)
  let f := fun s => ∑ k ∈ S, cellWeight k * E k s
  let avg := ∫ s in (0:ℝ)..1, f s
  have hd (k : ℕ) : 0 < oddCofactor k := by dsimp [oddCofactor]; positivity
  have intE (k : ℕ) : IntervalIntegrable (fun s => cellWeight k*E k s) volume 0 1 :=
    ((discrepancy_integrable M a (hd k)).sub (discrepancy_integrable M a (d := oddCofactor k+1)
      (by linarith only [hd k]))).const_mul _
  have sumInt (T : Finset ℕ) : IntervalIntegrable (fun s => ∑ k ∈ T, cellWeight k*E k s) volume 0 1 := by
    induction T using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (intervalIntegrable_const (a := (0:ℝ)) (b := 1) (μ := volume) (c := (0:ℝ)))
    | insert k t hk ih => simpa only [Finset.sum_insert hk] using (intE k).add ih
  have integrable : IntervalIntegrable f volume 0 1 := sumInt S
  have point (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
      f s = ∑ k ∈ S, cellWeight k*movingExcess M a (oddCofactor k+s) := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [E]
    rw [show oddCofactor k+1+s=oddCofactor k+s+1 by ring,
      moving_eq M (by dsimp [a,evenEndpoint]; positivity) (by linarith only [hd k,hs.1])]
  have avg_id : avg = ∫ s in (0:ℝ)..1, ∑ k ∈ S, cellWeight k*movingExcess M a (oddCofactor k+s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    exact point s hs
  have choose : ∃ s ∈ Set.Icc (0:ℝ) 1, f s ≤ avg+1 := by
    by_contra! h
    have impossible : (∫ _s in (0:ℝ)..1, avg+1) ≤ avg :=
      intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const integrable (fun s hs => (h s hs).le)
    simp only [intervalIntegral.integral_const,sub_zero,one_smul] at impossible
    linarith
  obtain ⟨s,hs,ok⟩ := choose
  refine ⟨s,hs,?_⟩
  rw [point s hs,avg_id] at ok
  rw [Finset.sum_add_distrib,all_cells_centered M K R hm]
  linarith only [ok]

private theorem theta_envelope {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, |nativeTheta n-n| ≤ δ*n+B := by
  have lo := (tendsto_order.1 nativeTheta_div_atTop_one).1 (1-δ) (by linarith)
  have hi := (tendsto_order.1 nativeTheta_div_atTop_one).2 (1+δ) (by linarith)
  obtain ⟨L,good⟩ := Filter.eventually_atTop.1 (lo.and hi)
  let C := Real.log 4+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C*(L+1),by positivity,?_⟩
  intro n
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  by_cases large : L+1 ≤ n
  · have pos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    obtain ⟨l,u⟩ := good n (by omega)
    have base : 0 ≤ C*((L:ℝ)+1) := by positivity
    rw [abs_le]
    constructor <;> linarith only [(lt_div_iff₀ pos).1 l,(div_lt_iff₀ pos).1 u,base]
  · have small : (n:ℝ) ≤ (L:ℝ)+1 := by exact_mod_cast (show n ≤ L+1 by omega)
    have b := mul_le_mul_of_nonneg_left small hC
    dsimp only [C] at b ⊢
    rw [abs_le]
    constructor <;> linarith only [b,nativeTheta_nonneg n,nativeTheta_le_log4_mul n,
      mul_nonneg hδ.le hn,mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)) hn,hn]

/-- Both endpoint conventions are explicit. At t=a/v, j is the largest
integer strictly below t. -/
private theorem active_at (M : ℕ) {a v : ℝ} (hv : 0 < v) (ht : 0 < a/v) (hm : a/v ≤ M) :
    let j := ⌈a/v⌉₊-1
    activeMass M a v = nativeTheta j-nativeTheta (min M.sqrt j) := by
  intro j
  have hceil : 0 < ⌈a/v⌉₊ := Nat.lt_ceil.mpr (by simpa only [Nat.cast_zero] using ht)
  have limit := Nat.ceil_le.mpr hm
  have jm : j ≤ M := by dsimp [j]; omega
  have cutoff (p : ℕ) : (p:ℝ) < a/v ↔ p ≤ j := by rw [← Nat.lt_ceil]; dsimp [j]; omega
  have sets : (retainedFirstPrimes M).filter (fun p : ℕ => (p:ℝ) < a/v) =
      nativePrimeSet j \ nativePrimeSet (min M.sqrt j) := by
    ext p
    constructor
    · intro hp
      obtain ⟨ret,t⟩ := Finset.mem_filter.mp hp
      obtain ⟨⟨one,_⟩,pr,root⟩ := mem_retainedFirstPrimes.mp ret
      have pj := (cutoff p).1 t
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨one,pj⟩,pr⟩,?_⟩
      intro low
      exact (not_le.mpr root) ((Finset.mem_Icc.mp (Finset.mem_filter.mp low).1).2.trans (min_le_left ..))
    · intro hp
      obtain ⟨hit,out⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨r,pr⟩ := Finset.mem_filter.mp hit
      obtain ⟨one,pj⟩ := Finset.mem_Icc.mp r
      have root : M.sqrt < p := lt_of_not_ge fun down =>
        out (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨one,le_min down pj⟩,pr⟩)
      exact Finset.mem_filter.mpr ⟨mem_retainedFirstPrimes.mpr ⟨⟨one,pj.trans jm⟩,pr,root⟩,(cutoff p).2 pj⟩
  have sub : nativePrimeSet (min M.sqrt j) ⊆ nativePrimeSet j := by
    intro p hp
    obtain ⟨r,pr⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.Icc_subset_Icc le_rfl (min_le_right ..) r,pr⟩
  have mass := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) sub
  have eq := cofactorDiscrepancy_eq M a hv
  rw [sets,cofactorDiscrepancy] at eq
  change _+nativeTheta (min M.sqrt j)=nativeTheta j at mass
  linarith only [eq,mass]

theorem discrepancy_envelope {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (M : ℕ) (v : ℝ), 2 ≤ M → 1 ≤ v →
      |cofactorDiscrepancy M (evenEndpoint M) v| ≤ δ*M+B+Real.log 4*Real.sqrt M := by
  obtain ⟨C,hC,theta⟩ := theta_envelope hδ
  refine ⟨C+1,by positivity,?_⟩
  intro M v hM hv
  let a := evenEndpoint M
  let t := a/v
  let j := ⌈t⌉₊-1
  have a0 : 0 < a := by
    have h : 0 < M/2 := by omega
    dsimp [a,evenEndpoint]; positivity
  have scale : a ≤ M := by dsimp [a,evenEndpoint]; exact_mod_cast (show 2*(M/2) ≤ M by omega)
  have v0 : 0 < v := by linarith
  have t0 : 0 < t := div_pos a0 v0
  have tm : t ≤ M := (div_le_self a0.le hv).trans scale
  have hc : 0 < ⌈t⌉₊ := Nat.lt_ceil.mpr (by simpa only [Nat.cast_zero] using t0)
  have ceil : (j:ℝ)+1=⌈t⌉₊ := by exact_mod_cast (show j+1=⌈t⌉₊ by dsimp [j]; omega)
  have jl : (j:ℝ) ≤ t := by linarith only [ceil,Nat.ceil_lt_add_one t0.le]
  have ju : t ≤ (j:ℝ)+1 := by linarith only [ceil,Nat.le_ceil t]
  have hs : (M.sqrt:ℝ) ≤ Real.sqrt M := (Real.le_sqrt (by positivity) (Nat.cast_nonneg M)).2 (by
    rw [sq]; exact_mod_cast Nat.sqrt_le M)
  have lower : ((min M.sqrt j:ℕ):ℝ) ≤ Real.sqrt M :=
    (show ((min M.sqrt j:ℕ):ℝ) ≤ M.sqrt by exact_mod_cast min_le_left M.sqrt j).trans hs
  have cut := active_at M v0 t0 tm
  change activeMass M a v=nativeTheta j-nativeTheta (min M.sqrt j) at cut
  change |activeMass M a v-t| ≤ _
  rw [cut,abs_le]
  have paid := (nativeTheta_le_log4_mul (min M.sqrt j)).trans (mul_le_mul_of_nonneg_left lower
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)))
  have d := mul_le_mul_of_nonneg_left (jl.trans tm) hδ.le
  have b := abs_le.mp (theta j)
  constructor <;> linarith only [b.1,b.2,paid,nativeTheta_nonneg (min M.sqrt j),ju,jl,d]

private theorem cell_envelope {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M k : ℕ, 2 ≤ M →
      |crossingBalance M k| ≤ 2*(δ*M+B+Real.log 4*Real.sqrt M) := by
  obtain ⟨B,hB,obs⟩ := discrepancy_envelope hδ
  refine ⟨B,hB,?_⟩
  intro M k hm
  let a := evenEndpoint M
  let d := oddCofactor k
  let C := δ*M+B+Real.log 4*Real.sqrt M
  have hd : 1 ≤ d := by dsimp [d,oddCofactor]; linarith only [Nat.cast_nonneg (α := ℝ) k]
  have pos : 0 < d := by linarith
  have cost : 0 ≤ cellWeight k := by dsimp [cellWeight,oddCofactor]; positivity
  have cost1 : cellWeight k ≤ 1 := (div_le_one (by dsimp [oddCofactor]; positivity)).2 (by change 1 ≤ 2*(d+1); linarith)
  have obs2 (s : ℝ) (hs : 0 ≤ s) : |cofactorDiscrepancy M a (d+s)-cofactorDiscrepancy M a (d+1+s)| ≤ 2*C := by
    exact (abs_sub _ _).trans (by linarith only [obs M (d+s) hm (by linarith),obs M (d+1+s) hm (by linarith)])
  have integral := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun s => cofactorDiscrepancy M a (d+s)-cofactorDiscrepancy M a (d+1+s)) (C := 2*C) (fun s hs => by
      rw [Set.uIoc_of_le zero_le_one] at hs
      simpa only [Real.norm_eq_abs] using obs2 s hs.1.le)
  simp only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] at integral
  rw [crossingBalance,tent_minus_main_eq_integral M a pos,abs_mul,abs_of_nonneg cost]
  exact (mul_le_mul_of_nonneg_right cost1 (abs_nonneg _)).trans ((one_mul _).le.trans integral)

/-- Unconditional matching of the entire absolute sum of prime curvature
discrepancies to every fixed relative precision. B may depend on that
precision. The same B works for every integer scale and all terminal cells. -/
theorem complete_curvature_relative (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M R : ℕ, 2 ≤ M →
      ∑ k ∈ Finset.Ico 1 R, |crossingBalance M k| ≤ δ*M+B*Real.sqrt M := by
  let c := Real.log 4+1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨T,hT⟩ := exists_nat_gt (2*c/δ+1)
  have posT : 1 ≤ T := by
    have pos : 0 ≤ 2*c/δ := by positivity
    exact_mod_cast (show (1:ℝ) ≤ T by linarith)
  have cover : 2*c ≤ δ*T := by
    have h : 2*c/δ ≤ T := by linarith
    linarith only [(div_le_iff₀ hδ).1 h]
  let η := δ/(4*((T:ℝ)+1))
  have posη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A,hA,early⟩ := cell_envelope posη
  let B := 2*(T:ℝ)*(A+Real.log 4)
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro M R hm
  let U := max R T
  have tU : T ≤ U := le_max_right ..
  have rU : R ≤ U := le_max_left ..
  have root : 1 ≤ Real.sqrt (M:ℝ) := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg M)).2 (by exact_mod_cast (show 1 ≤ M by omega))
  have cap : ∑ k ∈ Finset.Ico 1 T, |crossingBalance M k| ≤ (T:ℝ)*(2*(η*M+A+Real.log 4*Real.sqrt M)) := by
    refine (Finset.sum_le_sum (fun k _ => early M k hm)).trans ?_
    rw [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show (Finset.Ico 1 T).card ≤ T by simp))
      (by positivity)
  have dc : 0 < oddCofactor T := by dsimp [oddCofactor]; positivity
  have ds : (T:ℝ) ≤ oddCofactor T*oddCofactor T := by
    dsimp [oddCofactor]; nlinarith only [Nat.cast_nonneg (α := ℝ) T,sq_nonneg (T:ℝ)]
  have denom : c/(oddCofactor T*oddCofactor T) ≤ δ/2 := (div_le_iff₀ (mul_pos dc dc)).2
    (by linarith only [cover,mul_le_mul_of_nonneg_left ds hδ.le])
  have endM : evenEndpoint M ≤ M := by dsimp [evenEndpoint]; exact_mod_cast (show 2*(M/2) ≤ M by omega)
  have fine := fine_crossing_price M T U tU
  have late : ∑ k ∈ Finset.Ico T U, |crossingBalance M k| ≤ (δ/2)*M := by
    change _ ≤ c*(evenEndpoint M/oddCofactor T)*(1/oddCofactor T) at fine
    rw [show c*(evenEndpoint M/oddCofactor T)*(1/oddCofactor T)=c/(oddCofactor T*oddCofactor T)*evenEndpoint M by ring] at fine
    exact fine.trans (mul_le_mul denom endM (by dsimp [evenEndpoint]; positivity) (by positivity))
  have rate : 2*(T:ℝ)*η ≤ δ/2 := by
    have id : 4*((T:ℝ)+1)*η=δ := by dsimp [η]; field_simp
    linarith only [id,posη]
  have start : (∑ k ∈ Finset.Ico 1 R, |crossingBalance M k|) ≤ ∑ k ∈ Finset.Ico 1 U, |crossingBalance M k| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl rU) (fun k _ _ => abs_nonneg _)
  rw [← Finset.sum_Ico_consecutive (f := fun k => |crossingBalance M k|) posT tU] at start
  dsimp only [B]
  linarith only [start,cap,late,mul_le_mul_of_nonneg_right rate (Nat.cast_nonneg (α := ℝ) M),
    mul_le_mul_of_nonneg_left (show A ≤ A*Real.sqrt M by nlinarith only [mul_le_mul_of_nonneg_left root hA])
      (show 0 ≤ 2*(T:ℝ) by positivity)]

/-- The endpoint contribution of all paired cells and all ancestors. -/
def chordHistory (N : ℕ) : ℝ :=
  if _h : N < 16 then 0 else chordHistory (N/2)-∑ k ∈ Finset.Ico 1 ⌈Real.sqrt N⌉₊, chord N k
termination_by N
decreasing_by omega

/-- A common independently obtained relative tolerance accounts for all
centered prime intervals in the complete signed history. -/
theorem whole_chord_price (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, |(affineHistory N-weightedCrossings N)-chordHistory N| ≤
      δ*N+B*Real.sqrt N := by
  simp_rw [affine_sub_weightedCrossings]
  obtain ⟨C,hC,all⟩ := complete_curvature_relative (δ/2) (by positivity)
  refine ⟨4*C,by positivity,?_⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases short : N < 16
    · have base : chordHistory N=0 := by rw [chordHistory]; simp [short]
      rw [base,firstPrimeHistory,sumHistory_small _ _ short,sub_zero,abs_zero]
      positivity
    · let q := N/2
      let R := ⌈Real.sqrt N⌉₊
      let S := Finset.Ico 1 R
      have raw : firstPrimeHistory N =
          firstPrimeHistory q-((∑ k ∈ S, chord N k)+∑ k ∈ S, crossingBalance N k) := by
        rw [firstPrimeHistory,sumHistory_step _ _ short]
        congr 1
        have proof := all_cells_eq N 1 R (by omega)
        simpa only [evenEndpoint,oddCofactor,show ∀ k : ℕ, 2*(k:ℝ)+1+1=2*k+2 by intro k; ring] using proof
      have cstep : chordHistory N=chordHistory q-∑ k ∈ S, chord N k := by
        rw [chordHistory]; simp [short,q,S,R]
      have id : firstPrimeHistory N-chordHistory N =
          (firstPrimeHistory q-chordHistory q)-∑ k ∈ S, crossingBalance N k := by rw [raw,cstep]; ring
      have cap : |∑ k ∈ S, crossingBalance N k| ≤ (δ/2)*N+C*Real.sqrt N :=
        (Finset.abs_sum_le_sum_abs _ _).trans (all N R (by omega))
      have half : (q:ℝ)*2 ≤ N := by exact_mod_cast (show q*2 ≤ N by dsimp [q]; omega)
      have root : Real.sqrt (q:ℝ) ≤ (3/4)*Real.sqrt N := (Real.sqrt_le_iff).2
        ⟨by positivity,by nlinarith only [half,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N),Nat.cast_nonneg (α := ℝ) N]⟩
      have previous := ih q (by dsimp [q]; omega)
      have scaledHalf := mul_le_mul_of_nonneg_left half hδ.le
      have scaledRoot := mul_le_mul_of_nonneg_left root hC
      rw [id]
      exact (abs_sub _ _).trans (by linarith only [previous,cap,scaledHalf,scaledRoot])

end
end RHLean.Analysis.PrincipalCofactor
