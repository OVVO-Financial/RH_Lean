import «research.oai_434.VF919ActualSlotMinRetighten»

/-!
# Fixed explicit slot count through the original detector

This file uses the original pinned 7/8 analytic theorems. Unlike an
existential HighData witness, the source count here is a closed natural
number calculated from the detector mesh at delta=1e-6, t=1e-8.
No new source moments or zero-freeness hypotheses are introduced.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Parameters

def explicitDelta : ℝ := 1 / 1000000
def explicitT : ℝ := 1 / 100000000

def explicitFineLength : ℝ :=
  (1 / 200 : ℝ) *
    min (min explicitT
      (ProbeFinalAssemblyCertifiedBands.detectorMesh explicitDelta explicitT))
      explicitT

theorem explicitFineLength_pos : 0 < explicitFineLength := by
  have hm : 0 < ProbeFinalAssemblyCertifiedBands.detectorMesh
      explicitDelta explicitT :=
    ProbeFinalAssemblyCertifiedBands.detectorMesh_pos
      (by norm_num [explicitDelta]) (by norm_num [explicitT])
  unfold explicitFineLength
  exact mul_pos (by norm_num)
    (lt_min (lt_min (by norm_num [explicitT]) hm)
      (by norm_num [explicitT]))

def explicitSlotCount : ℕ :=
  ⌈max (1 : ℝ) (1 / (3 * explicitFineLength))⌉₊ + 2

theorem explicitSlotCount_two_le : 2 ≤ explicitSlotCount := by
  unfold explicitSlotCount
  omega

theorem explicitSlotCount_gt :
    1 / (3 * explicitFineLength) < (explicitSlotCount : ℝ) := by
  have hceil := Nat.le_ceil (max (1 : ℝ) (1 / (3 * explicitFineLength)))
  have hmax : 1 / (3 * explicitFineLength) ≤
      max (1 : ℝ) (1 / (3 * explicitFineLength)) := le_max_right _ _
  unfold explicitSlotCount
  push_cast
  linarith only [hceil, hmax]

theorem explicit_distinct_slot_lengths (L : ℝ) (hL : 0 < L)
    (N : ℕ) (hN1 : (1 : ℝ) < N) (hNL : 1 / (3 * L) < (N : ℝ)) :
    ∃ ell : Fin N → ℝ, Function.Injective ell ∧
      (∀ j, 0 < ell j ∧ ell j < L) ∧ (∑ j, ell j) = 1 / 6 ∧
      (∀ j, (1 : ℝ) / (12 * (N : ℝ)) ≤ ell j) := by

  have hNp : 0<(N:ℝ) := by linarith
  have hNnat : 0<N := by exact_mod_cast hNp
  have hsmall : 1/(3*(N:ℝ))<L := by
    have hh := (div_lt_iff₀ (show 0<3*L by positivity)).mp hNL
    apply (div_lt_iff₀ (show 0<3*(N:ℝ) by positivity)).mpr
    nlinarith
  let w : Fin N→ℝ := fun j=>1+(j.val:ℝ)/(N:ℝ)
  let A : ℝ := ∑j,w j
  have hw (j : Fin N) : 1≤w j ∧ w j<2 := by
    have hj : (j.val:ℝ)<N := by exact_mod_cast j.isLt
    have hdiv : (j.val:ℝ)/(N:ℝ)<1 := (div_lt_one hNp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
    · linarith
  have hA : (N:ℝ)≤A := by
    calc
      _ = ∑_j : Fin N,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _=>(hw j).1
  have hAp : 0<A := hNp.trans_le hA
  let ell : Fin N→ℝ := fun j=>w j/(6*A)
  have hAup : A ≤ 2 * (N : ℝ) := by
    dsimp [A]
    calc
      (∑ j : Fin N, w j) ≤ ∑ _j : Fin N, (2 : ℝ) :=
        Finset.sum_le_sum (fun j _ => (hw j).2.le)
      _ = 2 * (N : ℝ) := by simp [mul_comm]
  refine ⟨ell,?_,?_,?_,?_⟩
  · intro j k he
    have hden : 6*A≠0 := by positivity
    have hwjk : w j=w k := (div_left_inj' hden).mp he
    have hjk : (j.val:ℝ)/(N:ℝ)=(k.val:ℝ)/(N:ℝ) := by dsimp [w] at hwjk;linarith
    have he' : (j.val:ℝ)=(k.val:ℝ) := (div_left_inj' hNp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · intro j
    constructor
    · exact div_pos (by linarith [(hw j).1]) (by positivity)
    · calc
        ell j < 2/(6*A) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (hw j).2
        _ ≤ 2/(6*(N:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        _ = 1/(3*(N:ℝ)) := by ring
        _ < L := hsmall
  · dsimp only [ell]
    rw [←Finset.sum_div]
    change A/(6*A)=1/6
    field_simp
  · intro j
    dsimp [ell]
    have hNj : 0 ≤ (N : ℝ) * (w j - 1) :=
      mul_nonneg hNp.le (by linarith only [(hw j).1])
    have hD : (0 : ℝ) < 12 * (N : ℝ) := by positivity
    have hAden : (0 : ℝ) < 6 * A := by positivity
    apply (div_le_div_iff₀ hD hAden).mpr
    nlinarith only [hAup, hNj, hNp]

theorem explicit_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0 < dmin) (hd : dmin ≤ dmax) (hm : 0 < mesh) (hR : 0 < R)
    (N : ℕ) (hN1 : (1 : ℝ) < N)
    (hNL : 1 / (3 * (dmin * min mesh R)) < (N : ℝ)) :
    ∃ ell : Fin N → ℝ, ∃ rmin : ℝ, 0 < rmin ∧
      Function.Injective ell ∧ (∑ j, ell j) = 1 / 6 ∧
      (∀ j, 0 < ell j ∧ dmax*rmin ≤ ell j ∧
        ell j ≤ dmin*mesh ∧ ell j ≤ dmin*R) ∧
      (∀ d : ℝ, dmin ≤ d → d ≤ dmax →
        ∀ j, rmin ≤ ell j/d ∧ ell j/d ≤ mesh ∧ ell j/d ≤ R) ∧
      (∀ j, (1 : ℝ)/(12 * (N : ℝ)) ≤ ell j) := by
  have hN : 0 < N := by exact_mod_cast (lt_trans zero_lt_one hN1)
  obtain ⟨ell,hi,he,hS,hslotLower⟩ :=
    explicit_distinct_slot_lengths (dmin*min mesh R)
      (mul_pos hdmin (lt_min hm hR)) N hN1 hNL
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0<dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0<rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin≤ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k≤dmin*mesh ∧ ell k≤dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_,hslotLower⟩
  intro d hd' hd'' k
  have hd0 : 0<d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d≤dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

theorem exists_explicit_high_data_fine :
    ∃ D : HighData explicitDelta,
      (∀ j, D.ell j ≤
        ProbeFinalAssemblyCertifiedBands.detectorMesh explicitDelta D.t / 200) ∧
      (∀ j, (1 : ℝ) / (12 * (explicitSlotCount : ℝ)) ≤ D.ell j) ∧
      D.N = explicitSlotCount ∧ D.t = explicitT := by
  let t : ℝ := explicitT
  let mesh : ℝ → ℝ := fun t =>
    ProbeFinalAssemblyCertifiedBands.detectorMesh explicitDelta t
  have ht : 0 < t := by norm_num [t, explicitT]
  have htΔ : t < explicitDelta / 4 := by norm_num [t, explicitT, explicitDelta]
  have ht1 : t ≤ 1 / 100000000 := by norm_num [t, explicitT]
  have hmesh : ∀ s : ℝ, 0 < s → 0 < mesh s := by
    intro s hs
    exact ProbeFinalAssemblyCertifiedBands.detectorMesh_pos
      (by norm_num [explicitDelta]) hs
  have hallow : ∀ N : ℕ, ∃ allowance : ℝ, 0 < allowance ∧
      ∀ ε e eps : ℝ, 0 ≤ ε → ε ≤ allowance → 0 ≤ e → e ≤ allowance →
        0 ≤ eps → eps ≤ allowance →
        159*ε+t+t+7*t ≤ 1/32 ∧
        (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
          (26*e+((N:ℝ)+8)*eps+t+t/6)+(t+t+t)+t ≤ 49/440640 := by
    intro N
    let allowance := t/((N:ℝ)+2000)
    have hden : 0<(N:ℝ)+2000 := by positivity
    have ha : 0<allowance := div_pos ht hden
    have ha0 : allowance≤t/2000 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
    have hap : allowance*((N:ℝ)+2000)=t := by dsimp [allowance];field_simp
    refine ⟨allowance,ha,?_⟩
    intro ε e eps hε hεa he hea heps hepsa
    have hεt : 2000*ε≤t := by linarith
    have het : 2000*e≤t := by linarith
    have hepsN : ((N:ℝ)+2000)*eps≤t := by
      have h := mul_le_mul_of_nonneg_left hepsa hden.le
      nlinarith
    have heps8 : ((N:ℝ)+8)*eps≤t := by nlinarith
    constructor <;> nlinarith
  let N : ℕ := explicitSlotCount
  have hN1 : (1 : ℝ) < N := by
    have h := explicitSlotCount_two_le
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) h)
  have hN : 0 < N := by
    exact_mod_cast (lt_trans zero_lt_one hN1)
  have hNL :
      1/(3*((1/200:ℝ)*min (min t (mesh t)) t)) < (N : ℝ) := by
    simpa [N, t, mesh, explicitFineLength] using explicitSlotCount_gt
  obtain ⟨ell,rmin,hr,hell,hsum,hbounds,_,hslotLower⟩ :=
    explicit_physical_slot_lengths (1/200) (7/8) (min t (mesh t)) t
      (by norm_num) (by norm_num) (lt_min ht (hmesh t ht)) ht N hN1 hNL
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤allowance := min_le_left _ _
  have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤t/2 := min_le_left _ _
  have hsell : sigma≤ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.2⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=hbud'.1,central_budget:=hbud'.2
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by change sigma+e≤(7/8)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, ht1]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ },?_,?_,rfl,rfl⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ≤t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7))≤t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0≤τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · intro j
    change ell j≤mesh t/200
    calc
      ell j≤(1/200:ℝ)*min t (mesh t):=(hbounds j).2.2.1
      _≤(1/200:ℝ)*mesh t:=mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _=mesh t/200:=by ring
  · intro j
    change (1 : ℝ) / (12 * (explicitSlotCount : ℝ)) ≤ ell j
    exact hslotLower j

end Parameters
end SevenEighths
end OAI

namespace OAI
noncomputable section
open SevenEighths.Parameters
open SevenEighths.RHLeanActualSlotMin
open SevenEighths.RHLeanNativeSevenEighthsReplay
open SevenEighths.RHLeanFullPhysicalTilt
open SevenEighths.ProbeFinalAssemblyCertifiedBands
open SevenEighths.ProbeFinalAssembly
namespace SevenEighths

theorem native_beta_le_explicit_slot_count :
    HeckeZeroSupremum.beta ≤
      (7 / 8 : ℝ) - (1 : ℝ) / (288 * (explicitSlotCount : ℝ)) := by
  obtain ⟨D, hfine, hslotLower, hN, ht⟩ :=
    Parameters.exists_explicit_high_data_fine
  let Dstar := RHLeanActualSlotMin.sourceWithExactSlotMinimum D
  let E := RHLeanFullPhysicalTilt.slotCalibratedHighDataLowFirst Dstar
  have hfineE : ∀ i, E.ell i ≤
      detectorMesh (1/1000000) E.t / 200 := by
    exact hfine
  have hreserves := RHLeanFullPhysicalTilt.slotCalibratedHighDataLowFirst_reserves Dstar
  change E.ε ≤ E.t / 2000 ∧ E.e ≤ E.t / 2000 ∧
    ((E.N : ℝ) + 8) * E.eps ≤ E.t ∧
    E.sigma = 6 * RHLeanFullPhysicalTilt.slotTiltLowFirst E at hreserves
  obtain ⟨hepsilon, he, heps, hsigma⟩ := hreserves
  have htpos : 0 < RHLeanFullPhysicalTilt.slotTiltLowFirst E :=
    (RHLeanFullPhysicalTilt.slot_tilt_budget_low_first E).1
  have hreserve : RHLeanFullPhysicalTilt.slotTiltLowFirst E ≤ E.sigma := by
    linarith only [hsigma, htpos]
  obtain ⟨F⟩ := exists_source_data E
  obtain ⟨counts⟩ := source_count_parameters F
  have hbound := RHLeanNativeSevenEighthsReplay.native_beta_le_slot_calibrated_boundary_low_first
    E hfineE hepsilon he heps hreserve F counts
  change HeckeZeroSupremum.beta ≤
    7/8 - RHLeanFullPhysicalTilt.slotTiltLowFirst
      (RHLeanFullPhysicalTilt.slotCalibratedHighDataLowFirst
        (RHLeanActualSlotMin.sourceWithExactSlotMinimum D)) at hbound
  rw [RHLeanActualSlotMin.recalibrated_tilt_eq_true_minimum D] at hbound
  have hmin : (1 : ℝ) / (12 * (explicitSlotCount : ℝ)) ≤
      RHLeanActualSlotMin.actualSlotMinimum D := by
    exact hslotLower (RHLeanActualSlotMin.leastSlotIndex D)
  have hident : (1 : ℝ) / (288 * (explicitSlotCount : ℝ)) =
      ((1 : ℝ) / (12 * (explicitSlotCount : ℝ))) / 24 := by ring
  rw [hident]
  linarith only [hbound, hmin]

#print axioms native_beta_le_explicit_slot_count
end SevenEighths
end OAI
