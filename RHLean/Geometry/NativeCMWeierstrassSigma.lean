import RHLean.Geometry.NativeCMWeierstrassQuasiPeriod

/-!
# The actual entire sigma function with its simple lattice zeros

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean`.

The infinite product is proved locally normally convergent. Its divisor,
first derivative and exact translation multipliers are derived from the
original lattice sum and quasi-periods.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real

namespace RHLean.Geometry.NativeCM.Weierstrass

open RHLean.Geometry.NativeCM.PeriodMean

variable (L : PeriodPair)

def primaryFactor (w : ℂ) : ℂ := (1 - w) * cexp (w + w ^ 2 / 2)

@[simp] theorem primaryFactor_zero : primaryFactor 0 = 1 := by simp [primaryFactor]

theorem primaryFactor_eq_zero_iff {w : ℂ} : primaryFactor w = 0 ↔ w = 1 := by
  rw [primaryFactor, mul_eq_zero, or_iff_left (exp_ne_zero _), sub_eq_zero, eq_comm]

@[fun_prop] theorem differentiable_primaryFactor : Differentiable ℂ primaryFactor := by
  unfold primaryFactor; fun_prop

theorem norm_primaryFactor_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖primaryFactor w - 1‖ ≤ 2 * ‖w‖ ^ 3 := by
  have h1 : 1 - w ≠ 0 := by
    intro h
    rw [← sub_eq_zero.1 h] at hw
    norm_num at hw
  have h2 := norm_log_sub_logTaylor_le 2 (z := -w) (by rw [norm_neg]; linarith)
  have h3 : logTaylor (2 + 1) (-w) = -(w + w ^ 2 / 2) := by
    simp [logTaylor, Finset.sum_range_succ]; ring
  rw [h3, norm_neg, ← sub_eq_add_neg, sub_neg_eq_add] at h2
  have h4 : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h0 := norm_nonneg w
  have h5 : ‖log (1 - w) + (w + w ^ 2 / 2)‖ ≤ ‖w‖ ^ 3 := by
    refine h2.trans ?_
    have : 0 ≤ ‖w‖ ^ 3 := by positivity
    push_cast
    nlinarith
  have h6 : ‖w‖ ^ 3 ≤ 1 := pow_le_one₀ h0 (by linarith)
  rw [primaryFactor, ← exp_log h1, ← Complex.exp_add]
  exact (norm_exp_sub_one_le (h5.trans h6)).trans (by linarith)

def sigmaFactor (l z : ℂ) : ℂ := if l = 0 then 1 else primaryFactor (z / l)

theorem sigmaFactor_eq (l z : ℂ) : sigmaFactor l z = primaryFactor (z / l) := by
  unfold sigmaFactor
  split_ifs with h
  · simp [h]
  · rfl

theorem differentiable_sigmaFactor (l : ℂ) : Differentiable ℂ (sigmaFactor l) := by
  have : sigmaFactor l = fun z => primaryFactor (z / l) := funext (sigmaFactor_eq l)
  rw [this]; fun_prop

theorem sigmaFactor_eq_zero_iff {l z : ℂ} : sigmaFactor l z = 0 ↔ l ≠ 0 ∧ z = l := by
  unfold sigmaFactor
  split_ifs with h
  · simp [h]
  · simp [h, primaryFactor_eq_zero_iff, div_eq_one_iff_eq h]

theorem norm_sigmaFactor_sub_one_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) {l : ℂ}
    (h : 2 * r ≤ ‖l‖) : ‖sigmaFactor l z - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hl : 0 < ‖l‖ := by linarith
  rw [sigmaFactor_eq]
  refine (norm_primaryFactor_sub_one_le ?_).trans ?_
  · rw [norm_div, div_le_iff₀ hl]; linarith
  · calc 2 * ‖z / l‖ ^ 3 = 2 * ‖z‖ ^ 3 / ‖l‖ ^ 3 := by rw [norm_div]; ring
      _ ≤ 2 * r ^ 3 / ‖l‖ ^ 3 := by gcongr
      _ = _ := by norm_cast

theorem logDeriv_sigmaFactor {l z : ℂ} (h : sigmaFactor l z ≠ 0) :
    logDeriv (sigmaFactor l) z = if l = 0 then 0 else zetaTerm l z := by
  split_ifs with hl
  · have : sigmaFactor l = fun _ => 1 := by ext; simp [sigmaFactor, hl]
    simp [this]
  have hz : z - l ≠ 0 := fun h' => h (sigmaFactor_eq_zero_iff.2 ⟨hl, sub_eq_zero.1 h'⟩)
  have e : sigmaFactor l = fun z => (1 - z / l) * cexp (z / l + (z / l) ^ 2 / 2) :=
    funext (sigmaFactor_eq l)
  have h1 := (hasDerivAt_id' z).div_const l
  have h2 := ((h1.const_sub 1).fun_mul (h1.fun_add ((h1.fun_pow 2).div_const 2)).cexp).deriv
  have hz' : l - z ≠ 0 := fun h' => hz (by linear_combination -h')
  rw [logDeriv_apply, e, h2, zetaTerm_eq, show z - l = -(l - z) by ring]
  beta_reduce
  have := exp_ne_zero (z / l + (z / l) ^ 2 / 2)
  generalize cexp (z / l + (z / l) ^ 2 / 2) = E at *
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  ring

def sigmaProd (z : ℂ) : ℂ := ∏' l : L.lattice, sigmaFactor l z

def weierstrassSigma (z : ℂ) : ℂ := z * sigmaProd L z

theorem hasProdLocallyUniformlyOn_sigmaProd :
    HasProdLocallyUniformlyOn (fun (l : L.lattice) z => sigmaFactor l z) (sigmaProd L)
      Set.univ := by
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun K _ hK => ?_
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_le
  have := Summable.hasProdUniformlyOn_one_add (f := fun (l : L.lattice) z => sigmaFactor l z - 1)
    (u := fun l => 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ)) hK
    ((ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _)
    ((eventually_cofinite_le_norm L (2 * r)).mono fun l hl z hz =>
      norm_sigmaFactor_sub_one_le hr (hKr z hz) hl)
    (fun l => ((differentiable_sigmaFactor l).continuous.sub continuous_const).continuousOn)
  simpa only [add_sub_cancel] using! this

theorem hasProd_sigmaProd (z : ℂ) :
    HasProd (fun l : L.lattice => sigmaFactor l z) (sigmaProd L z) :=
  (hasProdLocallyUniformlyOn_sigmaProd L).hasProd (Set.mem_univ z)

theorem summable_norm_sigmaFactor_sub_one (z : ℂ) :
    Summable fun l : L.lattice => ‖sigmaFactor l z - 1‖ := by
  refine Summable.of_norm_bounded_eventually
    (g := fun l : L.lattice => 2 * (‖z‖ + 1) ^ 3 * ‖l‖ ^ (-3 : ℝ))
    ((ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) ?_
  filter_upwards [eventually_cofinite_le_norm L (2 * (‖z‖ + 1))] with l hl
  rw [norm_norm]
  exact norm_sigmaFactor_sub_one_le (by positivity) (by linarith) hl

@[fun_prop] theorem differentiable_sigmaProd : Differentiable ℂ (sigmaProd L) :=
  differentiableOn_univ.1 <| TendstoLocallyUniformlyOn.differentiableOn
    (hasProdLocallyUniformlyOn_sigmaProd L)
    (.of_forall fun _ => DifferentiableOn.fun_finset_prod fun l _ =>
      (differentiable_sigmaFactor l).differentiableOn) isOpen_univ

@[simp] theorem sigmaProd_zero : sigmaProd L 0 = 1 := by simp [sigmaProd, sigmaFactor_eq]

@[simp] theorem sigmaProd_neg (z : ℂ) : sigmaProd L (-z) = sigmaProd L z := by
  simp only [sigmaProd, sigmaFactor_eq]
  rw [← (Equiv.neg L.lattice).tprod_eq]
  simp

theorem sigmaProd_ne_zero {z : ℂ} (hz : z ∈ ((L.lattice : Set ℂ) \ {0})ᶜ) : sigmaProd L z ≠ 0 := by
  have := tprod_one_add_ne_zero_of_summable (f := fun l : L.lattice => sigmaFactor l z - 1)
    (fun l => by
      rw [add_sub_cancel, Ne, sigmaFactor_eq_zero_iff]
      rintro ⟨h0, rfl⟩
      exact hz ⟨l.2, h0⟩) (summable_norm_sigmaFactor_sub_one L z)
  simpa only [add_sub_cancel] using! this

theorem logDeriv_sigmaProd {z : ℂ} (hz : z ∈ ((L.lattice : Set ℂ) \ {0})ᶜ) :
    logDeriv (sigmaProd L) z = weierstrassZetaExcept L 0 z := by
  have hne : ∀ l : L.lattice, sigmaFactor l z ≠ 0 := fun l => by
    rw [Ne, sigmaFactor_eq_zero_iff]
    rintro ⟨h0, rfl⟩
    exact hz ⟨l.2, h0⟩
  have := logDeriv_tprod_eq_tsum (f := fun (l : L.lattice) z => sigmaFactor l z) isOpen_univ
    (Set.mem_univ z) hne (fun l => (differentiable_sigmaFactor l).differentiableOn)
    ((hasSum_weierstrassZetaExcept L 0 z).summable.congr fun l =>
      (logDeriv_sigmaFactor (hne l)).symm)
    (hasProdLocallyUniformlyOn_sigmaProd L).multipliableLocallyUniformlyOn
    (sigmaProd_ne_zero L hz)
  exact this.trans (tsum_congr fun l => logDeriv_sigmaFactor (hne l))

@[fun_prop] theorem differentiable_weierstrassSigma : Differentiable ℂ (weierstrassSigma L) := by
  unfold weierstrassSigma; fun_prop

@[fun_prop] theorem analyticAt_weierstrassSigma (z : ℂ) : AnalyticAt ℂ (weierstrassSigma L) z :=
  (differentiable_weierstrassSigma L).analyticAt z

@[fun_prop] theorem continuous_weierstrassSigma : Continuous (weierstrassSigma L) :=
  (differentiable_weierstrassSigma L).continuous

@[simp] theorem weierstrassSigma_zero : weierstrassSigma L 0 = 0 := by simp [weierstrassSigma]

@[simp] theorem weierstrassSigma_neg (z : ℂ) :
    weierstrassSigma L (-z) = -weierstrassSigma L z := by simp [weierstrassSigma]

theorem hasDerivAt_weierstrassSigma_zero : HasDerivAt (weierstrassSigma L) 1 0 :=
  ((hasDerivAt_id' (0 : ℂ)).fun_mul (differentiable_sigmaProd L 0).hasDerivAt).congr_deriv (by simp)

theorem weierstrassSigma_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : weierstrassSigma L z ≠ 0 :=
  mul_ne_zero (fun h => hz (h ▸ zero_mem _)) (sigmaProd_ne_zero L fun h => hz h.1)

theorem hasDerivAt_weierstrassSigma {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (weierstrassSigma L) (weierstrassZeta L z * weierstrassSigma L z) z := by
  refine ((hasDerivAt_id' z).fun_mul (differentiable_sigmaProd L z).hasDerivAt).congr_deriv ?_
  have h0 : z ≠ 0 := fun h => hz (h ▸ zero_mem _)
  have h1 := sigmaProd_ne_zero L (z := z) fun h => hz h.1
  rw [weierstrassZeta_eq_inv_add, ← logDeriv_sigmaProd L fun h => hz h.1, logDeriv_apply,
    weierstrassSigma]
  field_simp

theorem logDeriv_weierstrassSigma {z : ℂ} (hz : z ∉ L.lattice) :
    logDeriv (weierstrassSigma L) z = weierstrassZeta L z := by
  rw [logDeriv_apply, (hasDerivAt_weierstrassSigma L hz).deriv,
    mul_div_cancel_right₀ _ (weierstrassSigma_ne_zero L hz)]

theorem IsHomothetic.sigmaProd_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') (z : ℂ) :
    sigmaProd L' (c * z) = sigmaProd L z := by
  simp only [sigmaProd, sigmaFactor_eq]
  rw [← h.equiv.tprod_eq]
  simp only [IsHomothetic.coe_equiv, mul_div_mul_left _ _ h.ne_zero]

theorem IsHomothetic.weierstrassSigma_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (z : ℂ) : weierstrassSigma L' (c * z) = c * weierstrassSigma L z := by
  rw [weierstrassSigma, h.sigmaProd_mul, weierstrassSigma, mul_assoc]

theorem weierstrassSigma_congr {L L' : PeriodPair} (h : L'.lattice = L.lattice) :
    weierstrassSigma L' = weierstrassSigma L := by
  ext z; simpa using (isHomothetic_one_iff.2 h).weierstrassSigma_mul z

open Classical in

def sigmaSign (w : ℂ) : ℂ := if w / 2 ∈ L.lattice then 1 else -1

theorem sigmaSign_of_mem {w : ℂ} (h : w / 2 ∈ L.lattice) : sigmaSign L w = 1 := if_pos h

theorem sigmaSign_of_notMem {w : ℂ} (h : w / 2 ∉ L.lattice) : sigmaSign L w = -1 := if_neg h

@[simp] theorem sigmaSign_sq (w : ℂ) : sigmaSign L w ^ 2 = 1 := by
  unfold sigmaSign; split_ifs <;> simp

@[simp] theorem norm_sigmaSign (w : ℂ) : ‖sigmaSign L w‖ = 1 := by
  unfold sigmaSign; split_ifs <;> simp

theorem sigmaSign_ne_zero (w : ℂ) : sigmaSign L w ≠ 0 := by
  unfold sigmaSign; split_ifs <;> simp

def sigmaSignCircle (w : ℂ) : Circle := ⟨sigmaSign L w, by simp [Submonoid.unitSphere]⟩

@[simp] theorem coe_sigmaSignCircle (w : ℂ) : (sigmaSignCircle L w : ℂ) = sigmaSign L w := rfl

@[simp] theorem sigmaSign_zero : sigmaSign L 0 = 1 := sigmaSign_of_mem L (by simp)

@[simp] theorem sigmaSign_neg (w : ℂ) : sigmaSign L (-w) = sigmaSign L w := by
  classical
  unfold sigmaSign
  exact if_congr (by rw [neg_div, neg_mem_iff]) rfl rfl

theorem IsHomothetic.sigmaSign_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') (w : ℂ) :
    sigmaSign L' (c * w) = sigmaSign L w := by
  classical
  unfold sigmaSign
  exact if_congr (by rw [mul_div_assoc, h (w / 2)]) rfl rfl

theorem sigmaSign_int (m n : ℤ) : sigmaSign L (m * L.ω₁ + n * L.ω₂) = (-1) ^ (m + n + m * n) := by
  have h : (m * L.ω₁ + n * L.ω₂) / 2 ∈ L.lattice ↔ Even m ∧ Even n := by
    constructor
    · intro h
      obtain ⟨a, b, e⟩ := mem_lattice.1 h
      have := LinearIndependent.pair_iff.1 L.indep (m - 2 * a) (n - 2 * b) (by
        simp only [real_smul]; push_cast; linear_combination (-2) * e)
      simp only [sub_eq_zero] at this
      norm_cast at this
      exact ⟨⟨a, by omega⟩, ⟨b, by omega⟩⟩
    · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
      exact mem_lattice.2 ⟨a, b, by push_cast; ring⟩
  by_cases h' : Even m ∧ Even n
  · rw [sigmaSign_of_mem L (h.2 h'), Even.neg_one_zpow ((h'.1.add h'.2).add (h'.1.mul_right _))]
  · rw [sigmaSign_of_notMem L (h.not.2 h'), Odd.neg_one_zpow]
    rw [← Int.not_even_iff_odd]
    simp only [Int.even_add, Int.even_mul]
    tauto

theorem exists_weierstrassSigma_add {w : ℂ} (hw : w ∈ L.lattice) : ∃ C : ℂ, C ≠ 0 ∧ ∀ z,
    weierstrassSigma L (z + w) = C * cexp (quasiPeriod L w * (z + w / 2)) * weierstrassSigma L z := by
  set x := L.ω₁ / 2
  have hx : x ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  let g : ℂ → ℂ := fun z =>
    weierstrassSigma L (z + w) / (cexp (quasiPeriod L w * (z + w / 2)) * weierstrassSigma L z)
  have hg : ∀ z ∉ L.lattice, HasDerivAt g 0 z := by
    intro z hz
    have h1 := (hasDerivAt_weierstrassSigma L (add_notMem_lattice hz hw)).comp_add_const
    have h2 := (((hasDerivAt_id' z).add_const (w / 2)).const_mul (quasiPeriod L w)).cexp
    refine (h1.fun_div (h2.fun_mul (hasDerivAt_weierstrassSigma L hz))
      (mul_ne_zero (exp_ne_zero _) (weierstrassSigma_ne_zero L hz))).congr_deriv ?_
    rw [weierstrassZeta_add L hw hz, div_eq_zero_iff]
    left
    ring
  refine ⟨g x, div_ne_zero (weierstrassSigma_ne_zero L (add_notMem_lattice hx hw))
    (mul_ne_zero (exp_ne_zero _) (weierstrassSigma_ne_zero L hx)), fun z => ?_⟩
  refine congrFun (Continuous.ext_on (dense_compl_lattice L)
    (f := fun z => weierstrassSigma L (z + w))
    (g := fun z => g x * cexp (quasiPeriod L w * (z + w / 2)) * weierstrassSigma L z)
    (by fun_prop) (by fun_prop) fun z hz => ?_) z
  have := eqOn_compl_lattice_of_hasDerivAt L hg (fun z _ => hasDerivAt_const z (g x)) hx rfl hz
  beta_reduce
  rw [← this, mul_assoc, div_mul_cancel₀ _
    (mul_ne_zero (exp_ne_zero _) (weierstrassSigma_ne_zero L hz))]

theorem weierstrassSigma_eq_zero_iff {z : ℂ} : weierstrassSigma L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h => by_contra fun hz => weierstrassSigma_ne_zero L hz h, fun hz => ?_⟩
  obtain ⟨C, -, h⟩ := exists_weierstrassSigma_add L hz
  simpa using h 0

theorem deriv_weierstrassSigma_add_of_law {w C η x : ℂ}
    (h : ∀ z, weierstrassSigma L (z + w) = C * cexp (η * (z + w / 2)) * weierstrassSigma L z)
    (hx : weierstrassSigma L x = 0) : deriv (weierstrassSigma L) (x + w) =
      C * cexp (η * (x + w / 2)) * deriv (weierstrassSigma L) x := by
  have h1 := (differentiable_weierstrassSigma L (x + w)).hasDerivAt.comp_add_const
  have h2 := (((((hasDerivAt_id' x).add_const (w / 2)).const_mul η).cexp).const_mul C).fun_mul
    (differentiable_weierstrassSigma L x).hasDerivAt
  rw [funext h] at h1
  simpa [hx] using h1.unique h2

theorem deriv_weierstrassSigma_ne_zero {w : ℂ} (hw : w ∈ L.lattice) :
    deriv (weierstrassSigma L) w ≠ 0 := by
  obtain ⟨C, hC, h⟩ := exists_weierstrassSigma_add L hw
  have := deriv_weierstrassSigma_add_of_law L h (weierstrassSigma_zero L)
  rw [zero_add, (hasDerivAt_weierstrassSigma_zero L).deriv, mul_one] at this
  rw [this]
  exact mul_ne_zero hC (exp_ne_zero _)

theorem deriv_weierstrassSigma_neg (z : ℂ) :
    deriv (weierstrassSigma L) (-z) = deriv (weierstrassSigma L) z := by
  have h := deriv_comp_neg (weierstrassSigma L) z
  simp only [weierstrassSigma_neg, deriv.fun_neg', neg_inj] at h
  exact h.symm

theorem weierstrassSigma_add {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    weierstrassSigma L (z + w) =
      sigmaSign L w * cexp (quasiPeriod L w * (z + w / 2)) * weierstrassSigma L z := by
  obtain ⟨C, -, h⟩ := exists_weierstrassSigma_add L hw
  have e : -(w / 2) + w = w / 2 := by ring
  suffices C = sigmaSign L w by rw [h, this]
  by_cases h2 : w / 2 ∈ L.lattice
  · have := deriv_weierstrassSigma_add_of_law L h
      ((weierstrassSigma_eq_zero_iff L).2 (neg_mem h2))
    rw [e, deriv_weierstrassSigma_neg, neg_add_cancel, mul_zero, Complex.exp_zero, mul_one] at this
    rw [sigmaSign_of_mem L h2]
    exact mul_right_cancel₀ (deriv_weierstrassSigma_ne_zero L h2) (by linear_combination -this)
  · have := h (-(w / 2))
    rw [e, weierstrassSigma_neg, neg_add_cancel, mul_zero, Complex.exp_zero, mul_one] at this
    rw [sigmaSign_of_notMem L h2]
    exact mul_right_cancel₀ (weierstrassSigma_ne_zero L h2) (by linear_combination this)

theorem deriv_weierstrassSigma_of_mem {w : ℂ} (hw : w ∈ L.lattice) :
    deriv (weierstrassSigma L) w = sigmaSign L w * cexp (quasiPeriod L w * (w / 2)) := by
  simpa [(hasDerivAt_weierstrassSigma_zero L).deriv] using
    deriv_weierstrassSigma_add_of_law L (weierstrassSigma_add L hw) (weierstrassSigma_zero L)

theorem analyticOrderAt_weierstrassSigma_of_mem {w : ℂ} (hw : w ∈ L.lattice) :
    analyticOrderAt (weierstrassSigma L) w = 1 :=
  (analyticAt_weierstrassSigma L w).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    ((weierstrassSigma_eq_zero_iff L).2 hw) (deriv_weierstrassSigma_ne_zero L hw)

theorem analyticOrderAt_weierstrassSigma_of_notMem {z : ℂ} (hz : z ∉ L.lattice) :
    analyticOrderAt (weierstrassSigma L) z = 0 :=
  (analyticAt_weierstrassSigma L z).analyticOrderAt_eq_zero.2 (weierstrassSigma_ne_zero L hz)

end RHLean.Geometry.NativeCM.Weierstrass
