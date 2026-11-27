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
    simpa [padicNorm.padicNorm_of_prime_of_ne (p := p) (q := 2) hp] using hr2
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

private theorem phi_read (e q d N p : ℕ) [Fact q.Prime] [Fact d.Prime] (w : G e → ℝ)
    (u : G e) (hu : alpogeNativeInPhi u) (hF : alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p)) :
    chartRead w (alpogeNativeHostData e q d).frob N p u = 1 := by
  rw [chartRead_eq]
  suffices h : chartDepth w (alpogeNativeHostData e q d).frob N p u = 0 by rw [h, pow_zero]
  unfold chartDepth
  refine Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun i _ => ?_
  apply ite_eq_left
  change i • ((alpogeNativeHostData e q d).frob p).1.1 + u.1.1 = 0
  rw [show ((alpogeNativeHostData e q d).frob p).1.1 = 0 from hF, show u.1.1 = 0 from hu,
    nsmul_zero, add_zero]

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
  · exact constant fun v => congrArg f (Subtype.ext (by
      have hv := v.property
      change v.val ∈ (alpogeNativeHostData e q d).inertia p at hv
      rwa [nativeDyadicHostData_inertia_unramified e q d p Fact.out hbad, AddSubgroup.mem_bot] at hv))

end RHLean.Analysis.AlpogeThin.WheelFit
