import «research.NativeRankOneEulerRepayment»

/-! The joint local comparison at the pinned Sernau fit-family cut.
A normalized inertia-character test is measured before choosing a direction.
On the native conductor its trivial character attains the largest p-adic
test norm at every profile, including both kinds of ramification. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open RHLean.Geometry.NativeTheta.Fock

namespace RHLean.Analysis.AlpogeThin.WheelFit

open RankOne
private abbrev G (e : ℕ) := AlpogeNativeE0 × AlpogeNativeDyadicH e

def channel {C : Type*} [AddCommGroup C] [Fintype C] (a : C → ℕ) (χ : AddChar C ℂ) : ℂ :=
  (∑ v, χ v * (a v:ℂ))/(Fintype.card C:ℂ)

private theorem channel_const {C : Type*} [AddCommGroup C] [Fintype C] (a : ℕ) (χ : AddChar C ℂ) :
    channel (fun _ => a) χ = if χ = 0 then (a:ℂ) else 0 := by
  classical
  rw [channel, ← Finset.sum_mul, AddChar.sum_eq_ite]
  split_ifs <;> simp [Fintype.card_ne_zero]

private theorem place_rat (p : ℕ) [Fact p.Prime] (ι : ℂ →+* PadicAlgCl p) (r : ℚ) :
    ‖ι (r:ℂ)‖ = (padicNorm p r:ℝ) := by
  rw [map_ratCast, ← Padic.eq_padicNorm, ← PadicAlgCl.norm_extends]
  norm_cast

private theorem root_unit {C : Type*} [AddCommGroup C] [Fintype C] {L : Type*} [NormedField L]
    (ι : ℂ →+* L) (χ : AddChar C ℂ) (v : C) : ‖ι (χ v)‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨Fintype.card C, Fintype.card_pos, ?_⟩
  rw [← map_pow, ← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one, map_one]

private theorem two_norm {C : Type*} [AddCommGroup C] [Fintype C] (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (ι : ℂ →+* PadicAlgCl p) (v : C) (k : ℕ) :
    (∀ χ : AddChar C ℂ, ‖ι ((1+χ v*(p:ℂ)^k)/2)‖ ≤ 1) ∧
      ‖ι ((1+(p:ℂ)^k)/2)‖ = 1 := by
  have hr2 := place_rat p ι 2
  have htwo : ‖ι 2‖ = 1 := by
    have hrat : padicNorm p (2:ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne (p := p) (q := 2) hp
    change ‖ι 2‖ = ((padicNorm p (2:ℚ):ℚ):ℝ) at hr2
    rwa [hrat, Rat.cast_one] at hr2
  have hp0 : ‖ι (p:ℂ)‖ < 1 := by
    have h := place_rat p ι (p:ℚ)
    simpa only [Rat.cast_natCast, ← Padic.eq_padicNorm, Rat.cast_natCast] using
      h.trans_lt (by exact_mod_cast padicNorm.padicNorm_p_lt_one_of_prime (p := p))
  constructor
  · intro χ
    rw [map_div₀, map_add, map_one, map_mul, map_pow, norm_div, htwo, div_one]
    refine (IsUltrametricDist.norm_add_le_max ..).trans (max_le (norm_one.le) ?_)
    rw [norm_mul, root_unit, one_mul, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hp0.le
  · cases k with
    | zero => norm_num
    | succ k =>
      rw [map_div₀, map_add, map_one, map_pow, norm_div, htwo, div_one]
      have hlt : ‖ι (p:ℂ) ^ (k+1)‖ < ‖(1 : PadicAlgCl p)‖ := by
        rw [norm_one, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hp0 (Nat.succ_ne_zero k)
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, norm_one]

private theorem phi_depth (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] (w : G e → ℝ)
    (u : G e) (hu : alpogeNativeInPhi u) (hF : alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p)) :
    chartDepth w (alpogeNativeHostData e q d).frob N p u = 0 := by
  unfold chartDepth
  refine Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun i _ => ?_
  apply ite_eq_left
  change i • ((alpogeNativeHostData e q d).frob p).1.1 + u.1.1 = 0
  rw [show ((alpogeNativeHostData e q d).frob p).1.1 = 0 from hF, show u.1.1 = 0 from hu,
    nsmul_zero, add_zero]

private theorem phi_read (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] (w : G e → ℝ)
    (u : G e) (hu : alpogeNativeInPhi u) (hF : alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p)) :
    chartRead w (alpogeNativeHostData e q d).frob N p u = 1 := by
  rw [chartRead_eq, phi_depth e q d N p w u hu hF, pow_zero]

/-- The single trivial inertia character achieves the largest local test
norm for every width profile and every power of that character. -/
theorem dyadic_all_channels (e q d p N : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (w : G e → ℝ) :
    let D := alpogeNativeHostData e q d
    let f := fun v : D.inertia p => chartRead w D.frob N p v
    (∀ χ, ‖ι (channel f χ)‖ ≤ ‖ι (f 0:ℂ)‖) ∧ ∀ j : ℕ,
      ‖ι (channel f (j • (0 : AddChar (D.inertia p) ℂ)))‖ = ‖ι (f 0:ℂ)‖ := by
  classical
  let D := alpogeNativeHostData e q d
  let f := fun v : D.inertia p => chartRead w D.frob N p v
  have constant (hc : ∀ v, f v = f 0) :
      (∀ χ, ‖ι (channel f χ)‖ ≤ ‖ι (f 0:ℂ)‖) ∧ ∀ j : ℕ,
        ‖ι (channel f (j • (0 : AddChar (D.inertia p) ℂ)))‖ = ‖ι (f 0:ℂ)‖ := by
    have heq (χ) : channel f χ = (if χ = 0 then (f 0:ℂ) else 0) :=
      (congrArg (fun a => channel a χ) (funext hc)).trans (channel_const _ _)
    constructor
    · intro χ
      rw [heq]
      split_ifs <;> simp
    · intro j
      simp [heq]
  by_cases hbad : p ∣ alpogeNativeHostN e q d
  · by_cases hd : p = d
    · subst p
      let v : D.inertia d := ⟨nativeDyadicDInvolution e,
        (nativeDyadicHostData_mem_inertia_d e q d hH _).2 (Or.inr rfl)⟩
      have hv : v ≠ 0 := fun he => nativeDyadicDInvolution_ne_zero e (congrArg Subtype.val he)
      have hu : (Finset.univ : Finset (D.inertia d)) = {0,v} := by
        ext i
        have hi := (nativeDyadicHostData_mem_inertia_d e q d hH i).1 i.property
        rcases hi with h | h
        · simp [show i = 0 from Subtype.ext h]
        · simp [show i = v from Subtype.ext h]
      have hf : f 0 = 1 := phi_read e q d N d w 0 rfl (nativeDyadicHostData_frob_d_inPhi e q d hH)
      have hc : Fintype.card (D.inertia d) = 2 := by
        change Finset.univ.card = 2
        rw [hu]
        simp [Ne.symm hv]
      let k := chartDepth w D.frob N d v
      have form (χ : AddChar (D.inertia d) ℂ) : channel f χ = (1+χ v*(d:ℂ)^k)/2 := by
        rw [channel, hu, hc, Finset.sum_insert (by simpa using Ne.symm hv), Finset.sum_singleton, hf]
        simp [f, chartRead_eq, k]
      have hd2 : d ≠ 2 := by have := hH.2.2.2.1; omega
      obtain ⟨all, best⟩ := two_norm d hd2 ι v k
      constructor
      · intro χ
        change ‖ι (channel f χ)‖ ≤ ‖ι (f 0:ℂ)‖
        simpa only [form, hf, Nat.cast_one, map_one, norm_one] using all χ
      · intro j
        change ‖ι (channel f (j • 0))‖ = ‖ι (f 0:ℂ)‖
        simpa [form, hf] using best
    · have hA : p ∣ 2^(e+2)*q := ((Fact.out : p.Prime).dvd_mul.mp hbad).resolve_right
        (fun h => hd ((Nat.prime_dvd_prime_iff_eq Fact.out hH.2.1).1 h))
      obtain ⟨hI,hF⟩ := nativeDyadicHostData_typeI e q d p hH Fact.out hA
      have one (v : D.inertia p) : f v = 1 := phi_read e q d N p w v (hI _ v.property) hF
      exact constant fun v => (one v).trans (one 0).symm
  · have ht : D.inertia p ≤ ⊥ := (nativeDyadicHostData_inertia_unramified e q d p Fact.out hbad).le
    exact constant fun v => congrArg f (Subtype.ext (AddSubgroup.mem_bot.mp (ht v.property)))

/-- The integral reading at the common zero representative, prior to
selection of the prime, place, direction or power. -/
def wheel (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime] (P : Finset ℕ) (w : G e → ℝ) : ℕ :=
  ∏ l ∈ P, chartRead w (alpogeNativeHostData e q d).frob N l 0

/-- Zero realizes the depth allowance simultaneously at every actual
prime. Conductor primes have zero depth at this representative, and
unramified inertia has only this representative. -/
theorem zero_depth_le (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (w : G e → ℝ)
    (hw : ∀ σ ∈ alpogeNativePhiSet (AlpogeNativeDyadicH e), 0 ≤ w σ) :
    let D := alpogeNativeHostData e q d
    (chartDepth w D.frob N p 0:ℝ) ≤ forced D.inertia D.frob w N p := by
  let D := alpogeNativeHostData e q d
  obtain ⟨v,hv,hcost⟩ := exists_chart D.inertia D.frob w N p hw
  by_cases hb : p ∣ alpogeNativeHostN e q d
  · have hf : alpogeNativeInPhi (D.frob p) := by
      by_cases h : p = d
      · subst p; exact nativeDyadicHostData_frob_d_inPhi e q d hH
      · exact (nativeDyadicHostData_typeI e q d p hH Fact.out
          (((Fact.out : p.Prime).dvd_mul.mp hb).resolve_right
            (fun k => h ((Nat.prime_dvd_prime_iff_eq Fact.out hH.2.1).1 k)))).2
    change (chartDepth w D.frob N p 0:ℝ) ≤ _
    rw [phi_depth e q d N p w 0 rfl hf, Nat.cast_zero]
    exact (Nat.cast_nonneg _).trans hcost
  · have hz : v = 0 := by
      change v ∈ (alpogeNativeHostData e q d).inertia p at hv
      rwa [nativeDyadicHostData_inertia_unramified e q d p Fact.out hb, AddSubgroup.mem_bot] at hv
    simpa only [hz] using hcost

/-- The same physical wheel integer has the exact prime depths used
by the common class character, before the all-nominal ASK sum. -/
theorem wheel_depths (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime] (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime) (w : G e → ℝ) (p : ℕ) (h : p ∈ P) :
    (wheel e q d N P w).factorization p = chartDepth w (alpogeNativeHostData e q d).frob N p 0 := by
  let D := alpogeNativeHostData e q d
  unfold wheel
  simp_rw [chartRead_eq]
  rw [Nat.factorization_prod_apply (fun l hl => (pow_pos (hp l hl).pos _).ne')]
  rw [Finset.sum_eq_single_of_mem p h]
  · exact Nat.factorization_pow_self (hp p h)
  · intro l hl hne
    simp [Nat.factorization_pow, Nat.Prime.factorization (hp l hl), Finsupp.single_eq_of_ne hne.symm]

/-- Vary only the admitted factor at the place p. Outside the cutoff its
class test is the transform of a constant. -/
def readAt (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime] (P : Finset ℕ) (w : G e → ℝ)
    (p : ℕ) (χ : AddChar ((alpogeNativeHostData e q d).inertia p) ℂ) : ℂ :=
  (wheel e q d N (P.erase p) w:ℂ) * channel (fun u : (alpogeNativeHostData e q d).inertia p =>
    if p ∈ P then chartRead w (alpogeNativeHostData e q d).frob N p u else 1) χ

theorem common_read (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ) (w : G e → ℝ) :
    (∀ χ, ‖ι (readAt e q d N P w p χ)‖ ≤ ‖ι (wheel e q d N P w:ℂ)‖) ∧
      ‖ι (readAt e q d N P w p 0)‖ = ‖ι (wheel e q d N P w:ℂ)‖ := by
  classical
  by_cases hp : p ∈ P
  · have fac : wheel e q d N P w = wheel e q d N (P.erase p) w *
        chartRead w (alpogeNativeHostData e q d).frob N p 0 := (Finset.prod_erase_mul P _ hp).symm
    obtain ⟨all,best⟩ := dyadic_all_channels e q d p N hH ι w
    simp only [readAt, ite_eq_left hp, fac, Nat.cast_mul, map_mul, norm_mul]
    exact ⟨fun χ => mul_le_mul_of_nonneg_left (all χ) (norm_nonneg _), congrArg (_ * ·) (by simpa using best 0)⟩
  · simp only [readAt, Finset.erase_eq_of_notMem hp, ite_eq_right hp, channel_const, Nat.cast_one]
    constructor
    · intro χ
      split_ifs <;> simp
    · simp

/-- The literal tested rank-one pairing. h is a separate class multiplier. -/
def tested {S : Type*} (α : S →₀ ℕ) (r : ℚ) (h : ℕ) (z z' : ℂ) : ℂ :=
  (h:ℂ) * fockInner (measuredTest α (Real.sqrt (r:ℝ)) z)
    (derivativeProjection α (measuredTest α (Real.sqrt (r:ℝ)) z'))

def payment {S : Type*} (α : S →₀ ℕ) (r : ℚ) (h A : ℕ) : ℚ :=
  ((h:ℚ)*r/(multiFactorial α:ℚ))*(A:ℚ)^2

/-- The rational entry of the *same* projector is a measured height
witness for its inverse: its finite product with that inverse is one,
and its archimedean log has the factorial and full nominal ASK with
opposite signs. The section twist/untwisted ratio requires a separate
identification with this measured quantity. -/
theorem nominal_signed_witness (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (w : G e → ℝ)
    (hw : ∀ σ ∈ alpogeNativePhiSet (AlpogeNativeDyadicH e), 0 ≤ w σ)
    (hpos : ∀ σ ∈ alpogeNativePhiSet (AlpogeNativeDyadicH e), ∀ ρ, alpogeNativeInPhi ρ → 0 < w (σ+ρ))
    (hN : ∀ σ ∈ alpogeNativePhiSet (AlpogeNativeDyadicH e), ∀ ρ, alpogeNativeInPhi ρ → w σ/w (σ+ρ) ≤ N)
    {S : Type*} (α : S →₀ ℕ) (r : ℚ) (hr : 0 < r) :
    let D := alpogeNativeHostData e q d
    let P := (Finset.range (N+1)).filter Nat.Prime
    let Q := payment α r 1 (wheel e q d N P w)
    0 < Q ∧
      (∀ j : ℂ ≃+* ℂ, Real.log ‖j (Q:ℂ)‖ ≤ -Real.log (multiFactorial α) + Real.log (r:ℝ) +
        ∑ σ ∈ alpogeNativePhiSet (AlpogeNativeDyadicH e),
          (alpogeNativeFullKernelASK D.inertia D.frob N (w σ) 0 (fun ρ => w (σ+ρ))).re) ∧
      ∀ p : ℕ, ∀ [Fact p.Prime], ∀ ι : ℂ →+* PadicAlgCl p, ι (Q:ℂ)*ι ((Q:ℂ)⁻¹) = 1 := by
  classical
  let D := alpogeNativeHostData e q d
  let P := (Finset.range (N+1)).filter Nat.Prime
  let k := fun p => chartDepth w D.frob N p 0
  let A := wheel e q d N P w
  have hp (p) (h : p ∈ P) : p.Prime := (Finset.mem_filter.mp h).2
  have wh : A = ∏ p ∈ P, p^k p := by simp [A, wheel, chartRead_eq, k, D]
  have hA : 0 < A := wh ▸ Finset.prod_pos (fun p h => pow_pos (hp p h).pos _)
  have hAr : 0 < (A:ℝ) := by exact_mod_cast hA
  have logA : Real.log (A:ℝ) = ∑ p ∈ P, (k p:ℝ)*Real.log p := by
    rw [wh, Nat.cast_prod, Real.log_prod (fun p h => Nat.cast_ne_zero.mpr (pow_pos (hp p h).pos _).ne')]
    simp only [Nat.cast_pow, Real.log_pow]
  let Q := payment α r 1 A
  have hf := multiFactorial_pos α
  have hQ : 0 < Q := by
    change 0 < ((1:ℚ)*r/(multiFactorial α:ℚ))*(A:ℚ)^2
    positivity
  refine ⟨hQ, ?_, ?_⟩
  · intro j
    have hj : ‖j (Q:ℂ)‖ = (Q:ℝ) := by
      rw [map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by exact_mod_cast hQ)]
    rw [hj, ← forced_sum_eq_nominal_ask D.inertia D.frob w N hpos hN]
    have val : (Q:ℝ) = ((r:ℝ)/(multiFactorial α:ℝ))*(A:ℝ)^2 := by simp [Q, payment]
    rw [val, Real.log_mul (div_pos (by exact_mod_cast hr) (by exact_mod_cast hf)).ne' (pow_pos hAr _).ne',
      Real.log_div (by exact_mod_cast hr.ne') (by exact_mod_cast hf.ne'), Real.log_pow, logA, Finset.mul_sum]
    have bound : ∑ p ∈ P, 2*((k p:ℝ)*Real.log p) ≤ ∑ p ∈ P, 2*forced D.inertia D.frob w N p*Real.log p := by
      refine Finset.sum_le_sum fun p h => ?_
      have : Fact p.Prime := ⟨hp p h⟩
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (zero_depth_le e q d N p hH w hw) zero_le_two)
        (Real.log_natCast_nonneg _)
    norm_num only [Nat.cast_ofNat]
    rw [sub_eq_add_neg, add_comm (Real.log (r:ℝ)) (-Real.log (multiFactorial α))]
    exact add_le_add le_rfl bound
  · intro p _ ι
    have hc : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]

/-- At odd primes outside the selected wheel, a dyadic metric leaves
the entire factorial pole in the unscaled row. The class multiplier
can remove at most its own valuation on a line. -/
theorem outside_wheel_price (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (w : G e → ℝ) (p : ℕ) [Fact p.Prime]
    (hout : p ∉ P) (hodd : p ≠ 2) {S : Type*} (α : S →₀ ℕ) (k : ℤ) (h : ℕ) :
    padicNorm p (payment α ((2:ℚ)^k) h (wheel e q d N P w)) =
      padicNorm p (h:ℚ)*(p:ℚ)^(multiFactorial α).factorization p := by
  let A := wheel e q d N P w
  have pos : 0 < A := by
    unfold A wheel
    simp_rw [chartRead_eq]
    exact Finset.prod_pos (fun l hl => pow_pos (hP l hl).pos _)
  have cop : p.Coprime A := by
    apply Nat.Coprime.prod_right
    intro l hl
    rw [chartRead_eq]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Fact.out (hP l hl)).2 (by rintro rfl; exact hout hl))
  have unit : padicNorm p (A:ℚ) = 1 := by
    rw [padicNorm.eq_zpow_of_nonzero (Nat.cast_ne_zero.mpr pos.ne'), padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd ((Fact.out : p.Prime).coprime_iff_not_dvd.mp cop)]
    simp
  have hu : padicNorm p ((A:ℚ)^2) = 1 := (map_pow (IsAbsoluteValue.abvHom (padicNorm p)) (A:ℚ) 2).trans
    (by change (padicNorm p (A:ℚ))^2 = 1; rw [unit, one_pow])
  have hf : padicNorm p (multiFactorial α:ℚ) = ((p:ℚ)^(multiFactorial α).factorization p)⁻¹ := by
    rw [padicNorm.eq_zpow_of_nonzero (Nat.cast_ne_zero.mpr (multiFactorial_pos α).ne'), padicValRat.of_nat,
      Nat.factorization_def _ (Fact.out : p.Prime), zpow_neg, zpow_natCast]
  rw [payment, padicNorm.mul, padicNorm.div, padicNorm.mul, dyadic_metric_padic, ite_eq_right hodd, mul_one,
    hu, mul_one, hf, div_inv_eq_mul]

private theorem tested_eq {S : Type*} (α : S →₀ ℕ) (r : ℚ) (hr : 0 ≤ r) (h : ℕ) (z z' : ℂ) :
    tested α r h z z' = ((((h:ℚ)*r/(multiFactorial α:ℚ)):ℚ):ℂ)*z*starRingEnd ℂ z' := by
  have sq : ((Real.sqrt (r:ℝ):ℂ))^2 = (r:ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hr)]
    norm_cast
  rw [tested, projected_test_pair, sq]
  push_cast
  ring

/-- Every paired test is controlled by a rational number read from the
same wheel and metric. Trivial characters attain the bound at every
place, simultaneously for all directions. The second test is measured
through the conjugate embedding, as in the compact rank-one proof. -/
theorem exact_projector_price (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ) (w : G e → ℝ)
    {S : Type*} (α : S →₀ ℕ) (r : ℚ) (hr : 0 < r) (h : ℕ) :
    let z := readAt e q d N P w p
    let Q := payment α r h (wheel e q d N P w)
    (∀ χ ψ, ‖ι (tested α r h (z χ) (z ψ))‖ ≤ (padicNorm p Q:ℝ)) ∧
      ‖ι (tested α r h (z 0) (z 0))‖ = (padicNorm p Q:ℝ) := by
  let z := readAt e q d N P w p
  let A := wheel e q d N P w
  let c := (h:ℚ)*r/(multiFactorial α:ℚ)
  let κ := ι.comp (starRingEnd ℂ)
  have hc : ‖κ (A:ℂ)‖ = ‖ι (A:ℂ)‖ := by simp [κ]
  obtain ⟨first, f0⟩ := common_read e q d N p hH ι P w
  obtain ⟨second, s0⟩ := common_read e q d N p hH κ P w
  have entry χ ψ : ‖ι (tested α r h (z χ) (z ψ))‖ =
      ‖ι (c:ℂ)‖ * ‖ι (z χ)‖ * ‖κ (z ψ)‖ := by
    rw [tested_eq α r hr.le, map_mul, map_mul, norm_mul, norm_mul]
    rfl
  have price : (padicNorm p (payment α r h A):ℝ) = ‖ι (c:ℂ)‖ * ‖ι (A:ℂ)‖ * ‖ι (A:ℂ)‖ := by
    rw [← place_rat p ι]
    change ‖ι (((c*(A:ℚ)^2:ℚ):ℂ))‖ = _
    push_cast
    rw [map_mul, map_pow, norm_mul, norm_pow]
    ring
  change (∀ χ ψ, ‖ι (tested α r h (z χ) (z ψ))‖ ≤ _) ∧ ‖ι (tested α r h (z 0) (z 0))‖ = _
  rw [price]
  constructor
  · intro χ ψ
    rw [entry]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (first χ) (norm_nonneg _))
      ((second ψ).trans_eq hc) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · rw [entry]
    change _ * ‖ι (readAt e q d N P w p 0)‖ * ‖κ (readAt e q d N P w p 0)‖ = _
    rw [f0, s0, hc]

/-- Mixed tests in integral coordinates on a single family of distinct
measured Fock monomials. The full row space has class multiplier one. -/
def rowMatrix {S : Type*} {n : ℕ} (α : Fin n → S →₀ ℕ) (r : Fin n → ℚ)
    (z z' : Fin n → ℂ) (U V : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℂ :=
  U.map (Int.castRingHom ℂ) *
    Matrix.of (fun i j => fockInner (measuredTest (α i) (Real.sqrt (r i:ℝ)) (z i))
      (derivativeProjection (α j) (measuredTest (α j) (Real.sqrt (r j:ℝ)) (z' j)))) *
    (V.map (Int.castRingHom ℂ)).transpose

theorem row_det {S : Type*} {n : ℕ} (α : Fin n → S →₀ ℕ) (hi : Function.Injective α)
    (r : Fin n → ℚ) (z z' : Fin n → ℂ) (U V : Matrix (Fin n) (Fin n) ℤ) :
    (rowMatrix α r z z' U V).det =
      (U.det:ℂ)*(∏ i, tested (α i) (r i) 1 (z i) (z' i))*(V.det:ℂ) := by
  classical
  have diag : Matrix.of (fun i j => fockInner (measuredTest (α i) (Real.sqrt (r i:ℝ)) (z i))
      (derivativeProjection (α j) (measuredTest (α j) (Real.sqrt (r j:ℝ)) (z' j)))) =
      Matrix.diagonal (fun i => tested (α i) (r i) 1 (z i) (z' i)) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [tested]
    · simp [derivativeProjection, measuredTest, fockInner_monomial_right,
        hi.ne h, Matrix.diagonal, h]
  have castDet (L : Matrix (Fin n) (Fin n) ℤ) : (L.map (Int.castRingHom ℂ)).det = (L.det:ℂ) :=
    ((Int.castRingHom ℂ).map_det L).symm
  rw [rowMatrix, diag, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    castDet, castDet]

/-- The full row determinant and every rank-one test share the same
attaining character. Integral changes of the two test tables are included,
and the determinant receives every direction's squared wheel reading. -/
theorem exact_row_price (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ)
    {S : Type*} {n : ℕ} (w : Fin n → G e → ℝ) (α : Fin n → S →₀ ℕ) (hi : Function.Injective α)
    (r : Fin n → ℚ) (hr : ∀ i, 0 < r i) :
    let z := fun (χ : Fin n → AddChar ((alpogeNativeHostData e q d).inertia p) ℂ) i =>
      readAt e q d N P (w i) p (χ i)
    let Q := fun i => payment (α i) (r i) 1 (wheel e q d N P (w i))
    (∀ χ ψ U V, ‖ι ((rowMatrix α r (z χ) (z ψ) U V).det)‖ ≤ ∏ i, (padicNorm p (Q i):ℝ)) ∧
      ‖ι ((rowMatrix α r (z 0) (z 0) 1 1).det)‖ = ∏ i, (padicNorm p (Q i):ℝ) := by
  classical
  let b i := exact_projector_price e q d N p hH ι P (w i) (α i) (r i) (hr i) 1
  dsimp only
  constructor
  · intro χ ψ U V
    rw [row_det α hi, map_mul, map_mul, map_intCast, map_intCast, norm_mul, norm_mul,
      map_prod, norm_prod]
    have hu := IsUltrametricDist.norm_intCast_le_one (PadicAlgCl p) U.det
    have hv := IsUltrametricDist.norm_intCast_le_one (PadicAlgCl p) V.det
    exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)) hv).trans
      ((mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => norm_nonneg _) hu).trans
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => (b i).1 (χ i) (ψ i)))
  · rw [row_det α hi, Matrix.det_one, Int.cast_one, one_mul, mul_one, map_prod, norm_prod]
    exact Finset.prod_congr rfl fun i _ => (b i).2

/-- This is the simultaneous fit comparison on the measured monomial
space. The class multiplier occurs only on the rank-one side. The full
determinant has the original dimension times the auxiliary rank in its
exponent. All character tests are quantified before the bound. -/
theorem joint_budget_iff (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ)
    {S : Type*} {n : ℕ} (w : Fin n → G e → ℝ) (α : Fin n → S →₀ ℕ) (hi : Function.Injective α)
    (r : Fin n → ℚ) (hr : ∀ i, 0 < r i) (h : Fin n → ℕ) (auxRank : ℕ) (β : ℝ) :
    let A := fun i => wheel e q d N P (w i)
    let z := fun i => readAt e q d N P (w i) p
    let rz := fun (χ : Fin n → AddChar ((alpogeNativeHostData e q d).inertia p) ℂ) i => z i (χ i)
    ((∀ i χ ψ, ‖ι (tested (α i) (r i) (h i) (z i χ) (z i ψ))‖ ≤ Real.exp β) ∧
      ∀ χ ψ U V, ‖ι ((rowMatrix α r (rz χ) (rz ψ) U V).det)‖ ≤ Real.exp ((n:ℝ)*(auxRank*β))) ↔
    ((∀ i, (padicNorm p (payment (α i) (r i) (h i) (A i)):ℝ) ≤ Real.exp β) ∧
      (∏ i, (padicNorm p (payment (α i) (r i) 1 (A i)):ℝ)) ≤ Real.exp ((n:ℝ)*(auxRank*β))) := by
  let one i := exact_projector_price e q d N p hH ι P (w i) (α i) (r i) (hr i) (h i)
  let row := exact_row_price e q d N p hH ι P w α hi r hr
  constructor
  · rintro ⟨hl,hd⟩
    exact ⟨fun i => (one i).2.symm.le.trans (hl i 0 0), row.2.symm.le.trans (hd 0 0 1 1)⟩
  · rintro ⟨hl,hd⟩
    exact ⟨fun i χ ψ => ((one i).1 χ ψ).trans (hl i), fun χ ψ U V => (row.1 χ ψ U V).trans hd⟩

/-- Coordinates of a row of character tests relative to each direction's
common trivial-character test. Coefficients can vary with row, direction
and character. -/
def characterCoordinates {X : Type*} {n : ℕ} (x₀ : X)
    (z : Fin n → X → ℂ) (u : Fin n → Fin n → X →₀ ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a i => ∑ χ ∈ (u a i).support, u a i χ * (z i χ / z i x₀)

/-- Every combination with integral coefficients at this embedding lies
in the local span of the common test, and the normalized coordinate
recovers the original, unnormalized row entry exactly. -/
theorem character_coordinates (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ)
    {n : ℕ} (w : Fin n → G e → ℝ)
    (u : Fin n → Fin n → AddChar ((alpogeNativeHostData e q d).inertia p) ℂ →₀ ℂ)
    (hu : ∀ a i χ, ‖ι (u a i χ)‖ ≤ 1) :
    let z := fun i => readAt e q d N P (w i) p
    ∀ a i, ‖ι (characterCoordinates 0 z u a i)‖ ≤ 1 ∧
      characterCoordinates 0 z u a i * z i 0 = ∑ χ ∈ (u a i).support, u a i χ * z i χ := by
  classical
  let z := fun i => readAt e q d N P (w i) p
  dsimp only
  intro a i
  obtain ⟨all, attained⟩ := common_read e q d N p hH ι P (w i)
  have best (χ) : ‖ι (z i χ)‖ ≤ ‖ι (z i 0)‖ := (all χ).trans_eq attained.symm
  have ratio (χ) : ‖ι (z i χ / z i 0)‖ ≤ 1 := by
    by_cases hz : z i 0 = 0
    · simp [hz]
    · rw [map_div₀, norm_div]
      exact (div_le_one (norm_pos_iff.mpr (fun he => hz (ι.injective (he.trans ι.map_zero.symm))))).2 (best χ)
  change ‖ι (∑ χ ∈ (u a i).support, u a i χ * (z i χ / z i 0))‖ ≤ 1 ∧ _
  constructor
  · rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun χ _ => ?_
    rw [map_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hu a i χ)).trans (ratio χ)
  · change (∑ χ ∈ (u a i).support, u a i χ * (z i χ / z i 0)) * z i 0 =
      ∑ χ ∈ (u a i).support, u a i χ * z i χ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [mul_assoc]
    by_cases hz : z i 0 = 0
    · have hn : ι (z i χ) = 0 := norm_le_zero_iff.mp (by simpa only [hz, map_zero, norm_zero] using best χ)
      have hχ : z i χ = 0 := ι.injective (hn.trans ι.map_zero.symm)
      simp [hz, hχ]
    · rw [div_mul_cancel₀ _ hz]

private theorem integral_det (p : ℕ) [Fact p.Prime] (ι : ℂ →+* PadicAlgCl p) {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hu : ∀ a i, ‖ι (U a i)‖ ≤ 1) : ‖ι U.det‖ ≤ 1 := by
  rw [Matrix.det_apply', map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [map_mul, map_intCast, map_prod, norm_mul, norm_prod]
  exact (mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (IsUltrametricDist.norm_intCast_le_one _ _)).trans
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hu _ i)

/-- The Gram of two independent row tables in the measured basis.
The second coordinates are conjugated in the Fock pairing. -/
def latticeGram {S : Type*} {n : ℕ} (α : Fin n → S →₀ ℕ) (r : Fin n → ℚ) (z : Fin n → ℂ)
    (U V : Matrix (Fin n) (Fin n) ℂ) :=
  U * rowMatrix α r z z 1 1 * (V.map (starRingEnd ℂ)).transpose

/-- Sharp joint comparison for all place-integral combinations of the
wheel tests. The two tables may vary independently at every entry.
The identity tables and common trivial characters attain both prices. -/
theorem lattice_budget_iff (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (ι : ℂ →+* PadicAlgCl p) (P : Finset ℕ)
    {S : Type*} {n : ℕ} (w : Fin n → G e → ℝ) (α : Fin n → S →₀ ℕ) (hi : Function.Injective α)
    (r : Fin n → ℚ) (hr : ∀ i, 0 < r i) (h : Fin n → ℕ) (auxRank : ℕ) (β : ℝ) :
    let A := fun i => wheel e q d N P (w i)
    let z := fun i => readAt e q d N P (w i) p
    ((∀ i χ ψ, ‖ι (tested (α i) (r i) (h i) (z i χ) (z i ψ))‖ ≤ Real.exp β) ∧
      ∀ U V : Matrix (Fin n) (Fin n) ℂ, (∀ a i, ‖ι (U a i)‖ ≤ 1) →
        (∀ a i, ‖(ι.comp (starRingEnd ℂ)) (V a i)‖ ≤ 1) →
        ‖ι (latticeGram α r (fun i => z i 0) U V).det‖ ≤ Real.exp ((n:ℝ)*(auxRank*β))) ↔
    ((∀ i, (padicNorm p (payment (α i) (r i) (h i) (A i)):ℝ) ≤ Real.exp β) ∧
      (∏ i, (padicNorm p (payment (α i) (r i) 1 (A i)):ℝ)) ≤ Real.exp ((n:ℝ)*(auxRank*β))) := by
  classical
  let z := fun i => readAt e q d N P (w i) p 0
  let core := rowMatrix α r z z 1 1
  let κ := ι.comp (starRingEnd ℂ)
  have price := (exact_row_price e q d N p hH ι P w α hi r hr).2
  have one i := exact_projector_price e q d N p hH ι P (w i) (α i) (r i) (hr i) (h i)
  have scalar (U V : Matrix (Fin n) (Fin n) ℂ) :
      ‖ι (latticeGram α r z U V).det‖ = ‖ι U.det‖ * ‖ι core.det‖ * ‖κ V.det‖ := by
    have hj : (V.map (starRingEnd ℂ)).det = starRingEnd ℂ V.det := ((starRingEnd ℂ).map_det V).symm
    rw [latticeGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hj, map_mul, map_mul,
      norm_mul, norm_mul]
    rfl
  have idBound (j : ℂ →+* PadicAlgCl p) (a i : Fin n) : ‖j ((1 : Matrix (Fin n) (Fin n) ℂ) a i)‖ ≤ 1 := by
    by_cases ha : a = i <;> simp [Matrix.one_apply, ha]
  constructor
  · rintro ⟨hl, hd⟩
    have hbase := hd 1 1 (idBound ι) (idBound κ)
    change ‖ι (latticeGram α r z 1 1).det‖ ≤ _ at hbase
    rw [scalar, Matrix.det_one, map_one, map_one, norm_one, one_mul, mul_one] at hbase
    exact ⟨fun i => (one i).2.symm.le.trans (hl i 0 0), price.symm.le.trans hbase⟩
  · rintro ⟨hl, hd⟩
    refine ⟨fun i χ ψ => ((one i).1 χ ψ).trans (hl i), ?_⟩
    intro U V hu hv
    change ‖ι (latticeGram α r z U V).det‖ ≤ _
    rw [scalar]
    exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (integral_det p κ V hv)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (integral_det p ι U hu)).trans (price.le.trans hd))

/-- Least common clearing of the rational diagonal readings. Its
factorization is a single per-prime allowance, shared by all rows. -/
def rowLCM {n : ℕ} (Q : Fin n → ℚ) : ℕ := Finset.univ.lcm fun i => (Q i).den

theorem finite_row_budget (M : ℕ) (T : Finset ℕ) :
    (∑ p ∈ T, (M.factorization p:ℝ)*Real.log p) ≤ Real.log M := by
  classical
  rw [Real.log_nat_eq_sum_factorization]
  let S := M.factorization.support ∪ T
  rw [Finsupp.sum_of_support_subset _ (show M.factorization.support ⊆ S from Finset.subset_union_left)
    (fun (p t : ℕ) => (t:ℝ)*Real.log p) (by simp)]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))

theorem rowLCM_local {n : ℕ} (Q : Fin n → ℚ) (i : Fin n) (p : ℕ) [Fact p.Prime] :
    (padicNorm p (Q i):ℝ) ≤ Real.exp (((rowLCM Q).factorization p:ℝ)*Real.log p) := by
  let M := rowLCM Q
  have hm : M ≠ 0 := Finset.lcm_ne_zero_iff.mpr fun i _ => (Q i).den_ne_zero
  obtain ⟨k,hk⟩ : (Q i).den ∣ M := Finset.dvd_lcm (Finset.mem_univ i)
  have hmul : (M:ℚ)*(Q i) = (((Q i).num*(k:ℤ):ℤ):ℚ) := by
    rw [hk, Nat.cast_mul, mul_right_comm, mul_comm ((Q i).den:ℚ), Rat.mul_den_eq_num]
    push_cast
    rfl
  have hb : padicNorm p (M:ℚ)*padicNorm p (Q i) ≤ 1 := by
    rw [← padicNorm.mul, hmul]
    exact padicNorm.of_int _
  have hp0 : 0 < (p:ℚ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have pnorm : padicNorm p (M:ℚ) = ((p:ℚ)^M.factorization p)⁻¹ := by
    rw [padicNorm.eq_zpow_of_nonzero (Nat.cast_ne_zero.mpr hm), Nat.factorization_def M Fact.out,
      padicValRat.of_nat, zpow_neg, zpow_natCast]
  rw [pnorm, inv_mul_eq_div] at hb
  have hq := (div_le_one (pow_pos hp0 _)).1 hb
  rw [Real.exp_nat_mul, Real.exp_log (show 0 < (p:ℝ) by exact_mod_cast hp0)]
  exact_mod_cast hq

private theorem pole_iff (p : ℕ) [Fact p.Prime] (Q : ℚ) (b : ℝ) (hb : 0 ≤ b) :
    (padicNorm p Q:ℝ) ≤ Real.exp b ↔ (Q.den.factorization p:ℝ)*Real.log p ≤ b := by
  by_cases hd : Q.den.factorization p = 0
  · have hin : (padicNorm p Q:ℝ) ≤ 1 := by
      simpa [rowLCM, hd] using rowLCM_local (n := 1) (fun _ => Q) 0 p
    rw [hd, Nat.cast_zero, zero_mul]
    exact iff_of_true (hin.trans (Real.one_le_exp hb)) hb
  · have hp := (Fact.out : p.Prime)
    have hv : padicValNat p Q.den ≠ 0 := by rwa [← Nat.factorization_def Q.den hp]
    have hQ : Q ≠ 0 := by rintro rfl; simp at hd
    have hn := (Q.num_or_den_zero_padicVal hp).resolve_right hv
    have hnrm : padicNorm p Q = (p:ℚ)^Q.den.factorization p := by
      rw [padicNorm.eq_zpow_of_nonzero hQ, padicValRat_def, hn, Nat.cast_zero, zero_sub,
        neg_neg, zpow_natCast, Nat.factorization_def _ hp]
    rw [hnrm, Rat.cast_pow, Rat.cast_natCast]
    calc
      _ ↔ Real.exp ((Q.den.factorization p:ℝ)*Real.log p) ≤ Real.exp b := by
        rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hp.pos)]
      _ ↔ _ := Real.exp_le_exp

private theorem row_pole_iff {m : ℕ} (S : Fin (m+1) → ℚ) (p : ℕ) [Fact p.Prime] (b : ℝ) (hb : 0 ≤ b) :
    (∀ i, (padicNorm p (S i):ℝ) ≤ Real.exp b) ↔ ((rowLCM S).factorization p:ℝ)*Real.log p ≤ b := by
  rw [rowLCM, Finset.factorization_lcm (fun i _ => (S i).den_ne_zero)]
  let f := fun i => (S i).den.factorization p
  constructor
  · intro h
    obtain ⟨i, _, attained⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
    rw [attained]
    exact (pole_iff p (S i) b hb).1 (h i)
  · intro h i
    apply (pole_iff p (S i) b hb).2
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.le_sup (f := f) (Finset.mem_univ i))
      (Real.log_natCast_nonneg _)).trans h

/-- A single integer for the exact joint budget. E is row dimension
times auxiliary rank. Powers of the class-scaled line entries and the
unscaled determinant are reduced as rational numbers before taking LCM. -/
def jointDen {n : ℕ} (L Q : Fin n → ℚ) (E : ℕ) : ℕ :=
  rowLCM (Fin.cases (∏ i, Q i) fun i => L i ^ E)

theorem sharp_joint_place {n : ℕ} (L Q : Fin n → ℚ) (E p : ℕ) (hE : 0 < E) [Fact p.Prime]
    (b : ℝ) (hb : 0 ≤ b) :
    ((∀ i, (padicNorm p (L i):ℝ) ≤ Real.exp b) ∧
      (∏ i, (padicNorm p (Q i):ℝ)) ≤ Real.exp ((E:ℝ)*b)) ↔
    ((jointDen L Q E).factorization p:ℝ)*Real.log p ≤ (E:ℝ)*b := by
  let S : Fin (n+1) → ℚ := Fin.cases (∏ i, Q i) fun i => L i ^ E
  have lp i : (padicNorm p (L i ^ E):ℝ) ≤ Real.exp ((E:ℝ)*b) ↔ (padicNorm p (L i):ℝ) ≤ Real.exp b := by
    have hp : padicNorm p (L i ^ E) = (padicNorm p (L i))^E :=
      map_pow (IsAbsoluteValue.abvHom (padicNorm p)) _ _
    rw [hp, Rat.cast_pow, Real.exp_nat_mul, pow_le_pow_iff_left₀
      (by exact_mod_cast padicNorm.nonneg (p := p) (L i)) (Real.exp_pos _).le hE.ne']
  have vp : (padicNorm p (∏ i, Q i):ℝ) = ∏ i, (padicNorm p (Q i):ℝ) := by
    have h : padicNorm p (∏ i, Q i) = ∏ i, padicNorm p (Q i) :=
      map_prod (IsAbsoluteValue.abvHom (padicNorm p)) _ _
    rw [h, Rat.cast_prod]
  change _ ↔ ((rowLCM S).factorization p:ℝ)*Real.log p ≤ _
  rw [← row_pole_iff S p _ (mul_nonneg (Nat.cast_nonneg _) hb)]
  constructor
  · rintro ⟨hl, hv⟩ k
    refine Fin.cases ?_ (fun i => ?_) k
    · exact vp.le.trans hv
    · exact (lp i).2 (hl i)
  · intro h
    exact ⟨fun i => (lp i).1 (h i.succ), vp.symm.le.trans (h 0)⟩

/-- There exists one nonnegative allowance for all primes with the
original finite-sum quantifier exactly when this measured integer fits
the proposed total. Its minimizing local allocation is v_p(M) log p / E. -/
theorem sharp_joint_total {n : ℕ} (L Q : Fin n → ℚ) (E : ℕ) (hE : 0 < E) (B : ℝ) :
    (∃ γ : ℕ → ℝ, (∀ p, 0 ≤ γ p) ∧
      (∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → ∑ p ∈ T, γ p ≤ B) ∧
      ∀ p : ℕ, ∀ [Fact p.Prime], (∀ i, (padicNorm p (L i):ℝ) ≤ Real.exp (γ p)) ∧
        (∏ i, (padicNorm p (Q i):ℝ)) ≤ Real.exp ((E:ℝ)*γ p)) ↔
      Real.log (jointDen L Q E) ≤ (E:ℝ)*B := by
  let M := jointDen L Q E
  let f := fun p => (M.factorization p:ℝ)*Real.log p
  have he : 0 < (E:ℝ) := by exact_mod_cast hE
  constructor
  · rintro ⟨γ, hg, ht, hl⟩
    let T := M.factorization.support
    have hp (p) (h : p ∈ T) : p.Prime := Nat.prime_of_mem_primeFactors h
    calc
      _ = ∑ p ∈ T, f p := Real.log_nat_eq_sum_factorization M
      _ ≤ ∑ p ∈ T, (E:ℝ)*γ p := by
        refine Finset.sum_le_sum fun p h => ?_
        have : Fact p.Prime := ⟨hp p h⟩
        exact (sharp_joint_place L Q E p hE _ (hg p)).1 (hl p)
      _ = (E:ℝ)*∑ p ∈ T, γ p := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (ht T hp) he.le
  · intro h
    have hf p : 0 ≤ f p := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    refine ⟨fun p => f p / E, fun p => div_nonneg (hf p) he.le, ?_, ?_⟩
    · intro T _
      rw [← Finset.sum_div]
      exact (div_le_iff₀ he).2 ((finite_row_budget M T).trans (h.trans_eq (mul_comm _ _)))
    · intro p _
      apply (sharp_joint_place L Q E p hE _ (div_nonneg (hf p) he.le)).2
      change f p ≤ (E:ℝ)*(f p/E)
      rw [mul_div_cancel₀ _ he.ne']

/-- Construct the sharp common budget on the actual wheel family.
Its sum on any finite set is bounded by log(M)/E, and at each place
a nonnegative proposed allowance works for all tests exactly when it
covers this prime's share. E is row dimension times auxiliary rank. -/
theorem native_fit_budget (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (P : Finset ℕ)
    {S : Type*} {n : ℕ} (w : Fin n → G e → ℝ) (α : Fin n → S →₀ ℕ) (hi : Function.Injective α)
    (r : Fin n → ℚ) (hr : ∀ i, 0 < r i) (h : Fin n → ℕ) (auxRank : ℕ) (hE : 0 < n*auxRank) :
    let E := n*auxRank
    let A := fun i => wheel e q d N P (w i)
    let M := jointDen (fun i => payment (α i) (r i) (h i) (A i))
      (fun i => payment (α i) (r i) 1 (A i)) E
    let γ := fun p => (M.factorization p:ℝ)*Real.log p / E
    (∀ T : Finset ℕ, ∑ p ∈ T, γ p ≤ Real.log M / E) ∧
      ∀ p : ℕ, ∀ [Fact p.Prime], ∀ (ι : ℂ →+* PadicAlgCl p) (b : ℝ), 0 ≤ b →
        let z := fun i => readAt e q d N P (w i) p
        (((∀ i χ ψ, ‖ι (tested (α i) (r i) (h i) (z i χ) (z i ψ))‖ ≤ Real.exp b) ∧
          ∀ U V : Matrix (Fin n) (Fin n) ℂ, (∀ a i, ‖ι (U a i)‖ ≤ 1) →
            (∀ a i, ‖(ι.comp (starRingEnd ℂ)) (V a i)‖ ≤ 1) →
            ‖ι (latticeGram α r (fun i => z i 0) U V).det‖ ≤ Real.exp ((n:ℝ)*(auxRank*b))) ↔
          γ p ≤ b) := by
  let E := n*auxRank
  let A := fun i => wheel e q d N P (w i)
  let L := fun i => payment (α i) (r i) (h i) (A i)
  let Q := fun i => payment (α i) (r i) 1 (A i)
  let M := jointDen L Q E
  have he : 0 < (E:ℝ) := by exact_mod_cast hE
  constructor
  · intro T
    change (∑ p ∈ T, (M.factorization p:ℝ)*Real.log p/E) ≤ _
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (finite_row_budget M T) he.le
  · intro p _ ι b hb
    refine (lattice_budget_iff e q d N p hH ι P w α hi r hr h auxRank b).trans ?_
    have eprod : (n:ℝ)*((auxRank:ℝ)*b) = (E:ℝ)*b := by simp [E, mul_assoc]
    rw [eprod]
    refine (sharp_joint_place L Q E p hE b hb).trans ?_
    rw [div_le_iff₀ he, mul_comm b]

/-- Construct a single summable allowance for the two native tested
spaces at every prime and embedding. Its independently measured total
is log(M). Comparison of this total or the sharper joint criterion with
the compact per-direction budget is the remaining economic question. -/
theorem common_native_allowance (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : Formalism.FrobeniusOrbits.HostHyp q d) (P : Finset ℕ)
    {S : Type*} {n : ℕ} (w : Fin n → G e → ℝ) (α : Fin n → S →₀ ℕ) (hi : Function.Injective α)
    (r : Fin n → ℚ) (hr : ∀ i, 0 < r i) (h : Fin n → ℕ) (auxRank : ℕ) (ha : 1 ≤ auxRank) :
    let A := fun i => wheel e q d N P (w i)
    let M := rowLCM fun i => payment (α i) (r i) 1 (A i)
    let γ := fun p => (M.factorization p:ℝ)*Real.log p
    (∀ T : Finset ℕ, ∑ p ∈ T, γ p ≤ Real.log M) ∧
      ∀ p : ℕ, ∀ [Fact p.Prime], ∀ ι : ℂ →+* PadicAlgCl p,
        let z := fun i => readAt e q d N P (w i) p
        let rz := fun (χ : Fin n → AddChar ((alpogeNativeHostData e q d).inertia p) ℂ) i => z i (χ i)
        (∀ i χ ψ, ‖ι (tested (α i) (r i) (h i) (z i χ) (z i ψ))‖ ≤ Real.exp (γ p)) ∧
        ∀ χ ψ U V, ‖ι ((rowMatrix α r (rz χ) (rz ψ) U V).det)‖ ≤
          Real.exp ((n:ℝ)*(auxRank*γ p)) := by
  let A := fun i => wheel e q d N P (w i)
  let Q := fun i => payment (α i) (r i) 1 (A i)
  let M := rowLCM Q
  let γ := fun p => (M.factorization p:ℝ)*Real.log p
  refine ⟨finite_row_budget M, ?_⟩
  intro p _ ι
  apply (joint_budget_iff e q d N p hH ι P w α hi r hr h auxRank (γ p)).2
  have localBound (i) : (padicNorm p (Q i):ℝ) ≤ Real.exp (γ p) := rowLCM_local Q i p
  constructor
  · intro i
    have eq : payment (α i) (r i) (h i) (A i) = (h i:ℚ)*Q i := by dsimp [Q, payment]; ring
    rw [eq, padicNorm.mul, Rat.cast_mul]
    have hunit : padicNorm p (h i:ℚ) ≤ 1 := by exact_mod_cast padicNorm.of_int (p := p) (h i:ℤ)
    exact (mul_le_of_le_one_left (by exact_mod_cast padicNorm.nonneg (p := p) (Q i))
      (by exact_mod_cast hunit)).trans (localBound i)
  · calc
      _ ≤ ∏ _i : Fin n, Real.exp (γ p) := Finset.prod_le_prod₀
        (fun i _ => by exact_mod_cast padicNorm.nonneg (p := p) (Q i)) fun i _ => localBound i
      _ = Real.exp ((n:ℝ)*γ p) := by simp [Real.exp_nat_mul]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hg : 0 ≤ γ p := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hg (by exact_mod_cast ha))
          (Nat.cast_nonneg _)

/-- Measured nominal derivative orders for a prescribed thick mask on
the actual host. -/
def maskOrders {e : ℕ} (T : Finset (AlpogeNativeDyadicH e)) (t : AlpogeNativeDyadicH e)
    (b l : ℝ) : G e →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun σ => if alpogeNativeInPhi σ then
    ⌈alpogeNativeFreezeThick T t b (fun _ => l) σ⌉₊ else 0)

/-- Two proposed directions coincide exactly when the translated
thick masks coincide. This tests joint rank on the supplied mask. -/
theorem maskOrders_eq_iff {e : ℕ} (T U : Finset (AlpogeNativeDyadicH e)) (t u : AlpogeNativeDyadicH e)
    (b l : ℝ) (hne : ⌈b⌉₊ ≠ ⌈l⌉₊) :
    maskOrders T t b l = maskOrders U u b l ↔
      alpogeNativeThickPositiveSites T t = alpogeNativeThickPositiveSites U u := by
  have phi {V : Finset (AlpogeNativeDyadicH e)} {v σ} (hv : σ ∈ alpogeNativeThickPositiveSites V v) :
      alpogeNativeInPhi σ := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    rfl
  constructor
  · intro he
    ext σ
    have atσ := DFunLike.congr_fun he σ
    by_cases ht : σ ∈ alpogeNativeThickPositiveSites T t
    · by_cases hu : σ ∈ alpogeNativeThickPositiveSites U u
      · exact iff_of_true ht hu
      · exact (hne (by simpa [maskOrders, alpogeNativeFreezeThick, phi ht, ht, hu] using atσ)).elim
    · by_cases hu : σ ∈ alpogeNativeThickPositiveSites U u
      · exact (hne (by simpa [maskOrders, alpogeNativeFreezeThick, phi hu, ht, hu] using atσ.symm)).elim
      · exact iff_of_false ht hu
  · intro he
    ext σ
    simp [maskOrders, alpogeNativeFreezeThick, he]

/-- A distinct thick-site translate gives a distinct measured direction
when the two integral orders differ. This family realizes joint rank on
the actual modular-unit host and uses its original thick-site mask. -/
def singletonOrders {e : ℕ} (t : AlpogeNativeDyadicH e) (b l : ℝ) : G e →₀ ℕ :=
  maskOrders {0} t b l

theorem singletonOrders_injective {e : ℕ} (b l : ℝ) (h : ⌈b⌉₊ ≠ ⌈l⌉₊) :
    Function.Injective (fun t : AlpogeNativeDyadicH e => singletonOrders t b l) := by
  intro t u hu
  by_contra hne
  have eq := DFunLike.congr_fun hu (((0,1),t) : G e)
  apply h
  simpa [singletonOrders, maskOrders, alpogeNativeInPhi, alpogeNativeFreezeThick, alpogeNativeThickPositiveSites,
    zero_add t, zero_add u, hne] using eq

end RHLean.Analysis.AlpogeThin.WheelFit
