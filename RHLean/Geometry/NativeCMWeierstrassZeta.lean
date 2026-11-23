import RHLean.Geometry.NativeCMWeierstrassPeriodScaling
import RHLean.Geometry.NativeCMPeriodNormInvariant

/-!
# The actual Weierstrass zeta function and its quasi-periods

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean`.

The lattice sums are built from the original PeriodPair. Normal convergence,
derivatives, lattice translation and the pole expansion are proved directly.
No theta-uniformization law or metric is assumed.
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

theorem isPreconnected_compl_lattice_sdiff (s : Set ℂ) :
    IsPreconnected ((L.lattice : Set ℂ) \ s)ᶜ :=
  (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    (.mono Set.sdiff_subset (countable_of_Lindelof_of_discrete (X := L.lattice)))).2

theorem isPreconnected_compl_lattice : IsPreconnected (L.lattice : Set ℂ)ᶜ := by
  simpa using isPreconnected_compl_lattice_sdiff L ∅

theorem dense_compl_lattice : Dense (L.lattice : Set ℂ)ᶜ :=
  Set.Countable.dense_compl ℝ (countable_of_Lindelof_of_discrete (X := L.lattice))

theorem eventually_notMem_lattice (x : ℂ) : ∀ᶠ z in 𝓝[≠] x, z ∉ L.lattice := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds x)] with w hw hw'
  simp_all

theorem add_notMem_lattice {L : PeriodPair} {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∈ L.lattice) :
    z + w ∉ L.lattice := fun h => hz (by simpa using sub_mem h hw)

theorem eventually_cofinite_le_norm (R : ℝ) : ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intro l hl
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hl
  simpa using hl.le

def zetaTerm (l z : ℂ) : ℂ := if l = 0 then 1 / z else 1 / (z - l) + 1 / l + z / l ^ 2

theorem zetaTerm_eq (l z : ℂ) : zetaTerm l z = 1 / (z - l) + 1 / l + z / l ^ 2 := by
  unfold zetaTerm
  split_ifs with h
  · simp [h]
  · rfl

theorem norm_zetaTerm_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ < r) {l : ℂ} (h : 2 * r ≤ ‖l‖) :
    ‖zetaTerm l z‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl : 0 < ‖l‖ := by linarith
  have hl0 : l ≠ 0 := norm_pos_iff.1 hl
  have hzl : ‖l‖ / 2 ≤ ‖z - l‖ := by
    rw [norm_sub_rev]; exact .trans (by linarith) (norm_sub_norm_le l z)
  have hzl0 : z - l ≠ 0 := norm_pos_iff.1 (by linarith)
  have : zetaTerm l z = z ^ 2 / ((z - l) * l ^ 2) := by
    rw [zetaTerm_eq]; field_simp; ring
  rw [this]
  calc ‖z ^ 2 / ((z - l) * l ^ 2)‖ = ‖z‖ ^ 2 / (‖z - l‖ * ‖l‖ ^ 2) := by simp
    _ ≤ r ^ 2 / (‖l‖ / 2 * ‖l‖ ^ 2) := by gcongr
    _ = 2 * r ^ 2 / ‖l‖ ^ 3 := by field
    _ = _ := by norm_cast

def weierstrassZetaExcept (l₀ z : ℂ) : ℂ :=
  ∑' l : L.lattice, if (l : ℂ) = l₀ then 0 else zetaTerm l z

def weierstrassZeta (z : ℂ) : ℂ := ∑' l : L.lattice, zetaTerm l z

theorem hasSumLocallyUniformly_weierstrassZetaExcept (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) => if (l : ℂ) = l₀ then 0 else zetaTerm l z)
      (weierstrassZetaExcept L l₀) := by
  refine L.hasSumLocallyUniformly_aux (u := fun r l => 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ)) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · rw [norm_zero]; positivity
  · exact norm_zetaTerm_le hr hs h

theorem hasSum_weierstrassZetaExcept (l₀ z : ℂ) :
    HasSum (fun l : L.lattice => if (l : ℂ) = l₀ then 0 else zetaTerm l z)
      (weierstrassZetaExcept L l₀ z) :=
  (hasSumLocallyUniformly_weierstrassZetaExcept L l₀).hasSum

theorem weierstrassZetaExcept_of_notMem {l₀ : ℂ} (h : l₀ ∉ L.lattice) :
    weierstrassZetaExcept L l₀ = weierstrassZeta L := by
  ext z
  refine tsum_congr fun l => if_neg ?_
  rintro rfl
  exact h l.2

theorem hasSumLocallyUniformly_weierstrassZeta :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) => zetaTerm l z) (weierstrassZeta L) := by
  convert hasSumLocallyUniformly_weierstrassZetaExcept L (L.ω₁ / 2) using 3 with l
  · rw [if_neg]; exact fun e => L.ω₁_div_two_notMem_lattice (e ▸ l.2)
  · rw [weierstrassZetaExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]

theorem hasSum_weierstrassZeta (z : ℂ) :
    HasSum (fun l : L.lattice => zetaTerm l z) (weierstrassZeta L z) :=
  (hasSumLocallyUniformly_weierstrassZeta L).hasSum

theorem weierstrassZetaExcept_add {l₀ : ℂ} (h : l₀ ∈ L.lattice) (z : ℂ) :
    weierstrassZetaExcept L l₀ z + zetaTerm l₀ z = weierstrassZeta L z := by
  have h1 : HasSum (fun l : L.lattice => if l = ⟨l₀, h⟩ then zetaTerm l₀ z else 0)
      (zetaTerm l₀ z) := hasSum_ite_eq _ _
  refine ((hasSum_weierstrassZetaExcept L l₀ z).add h1).unique ?_
  convert hasSum_weierstrassZeta L z using 2 with l
  by_cases hl : (l : ℂ) = l₀
  · simp [hl, Subtype.ext_iff]
  · simp [hl, Subtype.ext_iff]

theorem weierstrassZeta_eq (z : ℂ) : weierstrassZeta L z = 1 / z +
    ∑' l : L.lattice, if (l : ℂ) = 0 then 0 else (1 / (z - l) + 1 / l + z / l ^ 2) := by
  rw [← weierstrassZetaExcept_add L (zero_mem _), add_comm, weierstrassZetaExcept]
  simp only [zetaTerm_eq]
  simp

theorem hasDerivAt_zetaTerm {l z : ℂ} (h : z ≠ l) :
    HasDerivAt (zetaTerm l) (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  have h0 : z - l ≠ 0 := sub_ne_zero.2 h
  have e : zetaTerm l = fun z => (z - l)⁻¹ + 1 / l + z / l ^ 2 := by
    ext; simp [zetaTerm_eq]
  rw [e]
  exact (((((hasDerivAt_id' z).sub_const l).fun_inv h0).add_const (1 / l)).fun_add
    ((hasDerivAt_id' z).div_const (l ^ 2))).congr_deriv (by ring)

theorem hasDerivAt_weierstrassZetaExcept (l₀ : ℂ) {z : ℂ} (hz : z ∈ ((L.lattice : Set ℂ) \ {l₀})ᶜ) :
    HasDerivAt (weierstrassZetaExcept L l₀) (-℘[L - l₀] z) z := by
  refine hasDerivAt_of_tendstoLocallyUniformlyOn (𝕜 := ℂ) L.isOpen_compl_lattice_sdiff
    (l := atTop)
    (f := fun (s : Finset L.lattice) z => ∑ l ∈ s, if (l : ℂ) = l₀ then 0 else zetaTerm l z)
    (f' := fun (s : Finset L.lattice) z =>
      -∑ l ∈ s, if (l : ℂ) = l₀ then 0 else (1 / (z - l) ^ 2 - 1 / l ^ 2))
    (g' := fun z => -℘[L - l₀] z)
    (L.hasSumLocallyUniformly_weierstrassPExcept l₀).tendstoLocallyUniformlyOn.neg
    (.of_forall fun s x hx => ?_)
    (fun x _ => hasSum_weierstrassZetaExcept L l₀ x) hz
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun l _ => ?_
  split_ifs with h
  · simpa using hasDerivAt_const x (0 : ℂ)
  · refine hasDerivAt_zetaTerm ?_
    rintro rfl
    exact hx ⟨l.2, h⟩

theorem analyticOnNhd_weierstrassZetaExcept (l₀ : ℂ) :
    AnalyticOnNhd ℂ (weierstrassZetaExcept L l₀) ((L.lattice : Set ℂ) \ {l₀})ᶜ :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (hasDerivAt_weierstrassZetaExcept L l₀ hz).differentiableAt.differentiableWithinAt)
    L.isOpen_compl_lattice_sdiff

theorem analyticAt_weierstrassZetaExcept (l₀ : ℂ) :
    AnalyticAt ℂ (weierstrassZetaExcept L l₀) l₀ :=
  analyticOnNhd_weierstrassZetaExcept L l₀ l₀ (by simp)

theorem hasDerivAt_weierstrassZeta {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (weierstrassZeta L) (-℘[L] z) z := by
  rw [← weierstrassZetaExcept_of_notMem L L.ω₁_div_two_notMem_lattice,
    ← L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice]
  exact hasDerivAt_weierstrassZetaExcept L _ fun h => hz h.1

theorem deriv_weierstrassZeta {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (weierstrassZeta L) z = -℘[L] z := (hasDerivAt_weierstrassZeta L hz).deriv

theorem analyticOnNhd_weierstrassZeta :
    AnalyticOnNhd ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (hasDerivAt_weierstrassZeta L hz).differentiableAt.differentiableWithinAt)
    L.isClosed_lattice.isOpen_compl

@[simp] theorem weierstrassZeta_neg (z : ℂ) : weierstrassZeta L (-z) = -weierstrassZeta L z := by
  simp only [weierstrassZeta, zetaTerm_eq]
  rw [← (Equiv.neg L.lattice).tsum_eq, ← tsum_neg]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg]
  rw [show -z - -(l : ℂ) = -(z - l) by ring, div_neg, div_neg]
  ring

theorem weierstrassZeta_eq_inv_add (z : ℂ) :
    weierstrassZeta L z = 1 / z + weierstrassZetaExcept L 0 z := by
  rw [← weierstrassZetaExcept_add L (zero_mem _), add_comm, zetaTerm, if_pos rfl]

@[simp] theorem weierstrassZetaExcept_zero (l₀ : ℂ) : weierstrassZetaExcept L l₀ 0 = 0 := by
  simp [weierstrassZetaExcept, zetaTerm_eq]

theorem meromorphic_weierstrassZeta : Meromorphic (weierstrassZeta L) := by
  intro x
  by_cases hx : x ∈ L.lattice
  · have e : weierstrassZeta L =
        fun z => weierstrassZetaExcept L x z + (1 / (z - x) + 1 / x + z / x ^ 2) := by
      ext z; rw [← weierstrassZetaExcept_add L hx, zetaTerm_eq]
    have := (analyticAt_weierstrassZetaExcept L x).meromorphicAt
    rw [e]
    fun_prop
  · exact (analyticOnNhd_weierstrassZeta L x hx).meromorphicAt

theorem tendsto_sub_mul_weierstrassZeta {x : ℂ} (hx : x ∈ L.lattice) :
    Tendsto (fun z => (z - x) * weierstrassZeta L z) (𝓝[≠] x) (𝓝 1) := by
  have hc : ContinuousAt (fun z => (z - x) * (weierstrassZetaExcept L x z + (1 / x + z / x ^ 2)) + 1)
      x := by
    have := (analyticAt_weierstrassZetaExcept L x).continuousAt
    fun_prop
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {x}ᶜ))
  simp only [sub_self, zero_mul, zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have : z - x ≠ 0 := sub_ne_zero.2 hz
  rw [← weierstrassZetaExcept_add L hx, zetaTerm_eq]
  have : (z - x) * (1 / (z - x)) = 1 := by field_simp
  linear_combination -this

def quasiPeriod : ℂ →ₗ[ℝ] ℂ :=
  L.basis.constr ℝ ![2 * weierstrassZeta L (L.ω₁ / 2), 2 * weierstrassZeta L (L.ω₂ / 2)]

theorem quasiPeriod_ω₁ : quasiPeriod L L.ω₁ = 2 * weierstrassZeta L (L.ω₁ / 2) := by
  rw [← L.basis_zero, quasiPeriod, Module.Basis.constr_basis]; simp

theorem quasiPeriod_ω₂ : quasiPeriod L L.ω₂ = 2 * weierstrassZeta L (L.ω₂ / 2) := by
  rw [← L.basis_one, quasiPeriod, Module.Basis.constr_basis]; simp

theorem eqOn_compl_lattice_of_hasDerivAt {f g f' : ℂ → ℂ}
    (hf : ∀ z ∉ L.lattice, HasDerivAt f (f' z) z) (hg : ∀ z ∉ L.lattice, HasDerivAt g (f' z) z)
    {x : ℂ} (hx : x ∉ L.lattice) (h : f x = g x) {z : ℂ} (hz : z ∉ L.lattice) : f z = g z :=
  IsOpen.eqOn_of_deriv_eq (𝕜 := ℂ) L.isClosed_lattice.isOpen_compl (isPreconnected_compl_lattice L)
    (fun z hz => (hf z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hg z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hf z hz).deriv.trans (hg z hz).deriv.symm) hx h hz

theorem weierstrassZeta_add_of_half_notMem {w : ℂ} (hw : w ∈ L.lattice) (hw2 : w / 2 ∉ L.lattice)
    {z : ℂ} (hz : z ∉ L.lattice) :
    weierstrassZeta L (z + w) = weierstrassZeta L z + 2 * weierstrassZeta L (w / 2) := by
  refine eqOn_compl_lattice_of_hasDerivAt L (f := fun z => weierstrassZeta L (z + w))
    (g := fun z => weierstrassZeta L z + 2 * weierstrassZeta L (w / 2)) (f' := fun z => -℘[L] z)
    (fun z hz => ?_) (fun z hz => (hasDerivAt_weierstrassZeta L hz).add_const _)
    (x := -(w / 2)) (by simpa using hw2) ?_ hz
  · have := (hasDerivAt_weierstrassZeta L (add_notMem_lattice hz hw)).comp_add_const
    rwa [L.weierstrassP_add_coe z ⟨w, hw⟩] at this
  · simp only [weierstrassZeta_neg]
    rw [show -(w / 2) + w = w / 2 by ring]
    ring

theorem weierstrassZeta_add {w : ℂ} (hw : w ∈ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    weierstrassZeta L (z + w) = weierstrassZeta L z + quasiPeriod L w := by
  induction hw using Submodule.span_induction generalizing z with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [quasiPeriod_ω₁]
      exact weierstrassZeta_add_of_half_notMem L L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice hz
    · rw [quasiPeriod_ω₂]
      exact weierstrassZeta_add_of_half_notMem L L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice hz
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [← add_assoc, ihy (add_notMem_lattice hz hx), ihx hz, map_add, add_assoc]
  | smul n x hx ih =>
    have hx' : x ∈ L.lattice := hx
    rw [map_zsmul]
    induction n using Int.induction_on generalizing z with
    | zero => simp
    | succ n ihn =>
      rw [add_smul, one_smul, ← add_assoc,
        ih (add_notMem_lattice hz (Submodule.smul_mem _ _ hx')), ihn hz, add_smul, one_smul,
        add_assoc]
    | pred n ihn =>
      have h1 := ih (add_notMem_lattice hz (Submodule.smul_mem _ (-(n : ℤ) - 1) hx'))
      rw [show z + (-(n : ℤ) - 1) • x + x = z + (-(n : ℤ)) • x by module, ihn hz] at h1
      rw [sub_smul (-(n : ℤ)) 1 (quasiPeriod L x), one_smul]
      linear_combination -h1

theorem quasiPeriod_eq_two_mul {w : ℂ} (hw : w ∈ L.lattice) (hw2 : w / 2 ∉ L.lattice) :
    quasiPeriod L w = 2 * weierstrassZeta L (w / 2) := by
  have h1 := weierstrassZeta_add L hw hw2
  rw [weierstrassZeta_add_of_half_notMem L hw hw2 hw2] at h1
  linear_combination -h1

theorem quasiPeriod_eq_weierstrassZetaExcept {w : ℂ} (hw : w ∈ L.lattice) (h0 : w ≠ 0) :
    quasiPeriod L w = weierstrassZetaExcept L w w + 2 / w := by
  have hc : ContinuousAt (fun z => weierstrassZetaExcept L w (z + w) + (1 / w + (z + w) / w ^ 2)
      - weierstrassZetaExcept L 0 z) 0 := by
    have h1 := (analyticAt_weierstrassZetaExcept L 0).continuousAt
    have h2 : ContinuousAt (fun z => weierstrassZetaExcept L w (z + w)) 0 :=
      ContinuousAt.comp_of_eq (analyticAt_weierstrassZetaExcept L w).continuousAt (by fun_prop)
        (zero_add w)
    fun_prop
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have h' : Tendsto (fun _ : ℂ => quasiPeriod L w) (𝓝[≠] 0) _ := h.congr' (by
    filter_upwards [eventually_notMem_lattice L 0] with z hz
    have h1 := weierstrassZeta_add L hw hz
    rw [← weierstrassZetaExcept_add L hw, zetaTerm_eq, weierstrassZeta_eq_inv_add,
      add_sub_cancel_right] at h1
    linear_combination h1)
  rw [tendsto_nhds_unique tendsto_const_nhds h']
  simp only [zero_add, weierstrassZetaExcept_zero, sub_zero]
  field_simp
  ring

end RHLean.Geometry.NativeCM.Weierstrass
