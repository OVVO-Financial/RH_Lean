import «research.oai_434.VF919ExplicitSlotTotalMass»

/-!
# Square-block-guided finite analytic slot packing

Two independent, noncircular facts:

1. The exact partition of an integer interval into its consecutive natural
   square blocks preserves ANY signed arithmetic weights.
2. A near-uniform, distinct real exponent-slot family fits the ORIGINAL
   fixed detector with roughly half the slot count of the old explicit seed.

The analytic source remains the pinned original Hecke/prime-ideal source.
The square-block partition does not automatically identify rational primes
with prime ideals or replace their weighted moments. The complete native
source transfer below uses the ORIGINAL compensated endpoint unchanged.
-/

open scoped Classical BigOperators

namespace RHLean.Proof

/-- Grouped consecutive square blocks reproduce the exact finite integer
    interval; valid for arbitrary signed weights, not only the Mobius sum. -/
theorem groupedSquareBlocks_sum (f : ℕ → ℤ) (a b : ℕ) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ico (a ^ 2) (b ^ 2), f n) =
      ∑ r ∈ Finset.Ico a b,
        ∑ n ∈ Finset.Ico (r ^ 2) ((r + 1) ^ 2), f n := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp
  | succ b hab ih =>
      have hsq : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
      have hnext : b ^ 2 ≤ (b + 1) ^ 2 := by nlinarith
      rw [Finset.sum_Ico_succ_top hab, ← ih]
      exact (Finset.sum_Ico_consecutive (f := f) hsq hnext).symm

end RHLean.Proof

namespace OAI
noncomputable section
namespace SevenEighths.Parameters

/-- The original detector fine-length bound from the certified OAI source. -/
def nearUniformSlotCount : ℕ :=
  ⌈max (1 : ℝ) (1 / (6 * explicitFineLength))⌉₊ + 2

theorem nearUniformSlotCount_three_le : 3 ≤ nearUniformSlotCount := by
  have hmax : (1 : ℝ) ≤ max (1 : ℝ) (1 / (6 * explicitFineLength)) :=
    le_max_left _ _
  have hceil := Nat.le_ceil (max (1 : ℝ) (1 / (6 * explicitFineLength)))
  have hnat : 1 ≤ ⌈max (1 : ℝ) (1 / (6 * explicitFineLength))⌉₊ := by
    exact_mod_cast (hmax.trans hceil)
  unfold nearUniformSlotCount
  omega

/-- The +2 ceiling buffer gives room for distinct but nearly equal slots. -/
theorem nearUniformSlotCount_threshold :
    1 / (6 * explicitFineLength) + 1 < (nearUniformSlotCount : ℝ) := by
  have hceil := Nat.le_ceil (max (1 : ℝ) (1 / (6 * explicitFineLength)))
  have hmax : 1 / (6 * explicitFineLength) ≤
      max (1 : ℝ) (1 / (6 * explicitFineLength)) := le_max_right _ _
  unfold nearUniformSlotCount
  push_cast
  linarith only [hceil, hmax]

/-- The actual source uses N *distinct* exponent slots summing to 1/6.
Near-uniform weights 1+j/N² keep the maxima below L using N>1+1/(6L)
and leave every slot at least 1/(8N). -/
theorem near_uniform_distinct_slot_lengths (L : ℝ) (hL : 0 < L)
    (N : ℕ) (hN3 : (3 : ℝ) ≤ N)
    (hNL : 1 / (6 * L) + 1 < (N : ℝ)) :
    ∃ ell : Fin N → ℝ, Function.Injective ell ∧
      (∀ j, 0 < ell j ∧ ell j < L) ∧
      (∑ j, ell j) = 1 / 6 ∧
      (∀ j, (1 : ℝ) / (8 * (N : ℝ)) ≤ ell j) := by
  have hNp : 0 < (N : ℝ) := by linarith only [hN3]
  let w : Fin N → ℝ := fun j => 1 + (j.val : ℝ) / (N : ℝ) ^ 2
  let A : ℝ := ∑ j, w j
  have hw (j : Fin N) :
      1 ≤ w j ∧ w j < 1 + 1 / (N : ℝ) := by
    have hj : (j.val : ℝ) < N := by exact_mod_cast j.isLt
    have hj0 : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
    have hdiv : (j.val : ℝ) / (N : ℝ) ^ 2 < 1 / (N : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hj hNp
      apply (div_lt_div_iff₀ (pow_pos hNp 2) hNp).mpr
      nlinarith only [hmul]
    have hdiv0 : 0 ≤ (j.val : ℝ) / (N : ℝ) ^ 2 :=
      div_nonneg hj0 (sq_nonneg _)
    dsimp only [w]
    exact ⟨by linarith only [hdiv0], by linarith only [hdiv]⟩
  have hAlo : (N : ℝ) ≤ A := by
    calc
      (N : ℝ) = ∑ _j : Fin N, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => (hw j).1)
  have hAup : A ≤ (N : ℝ) + 1 := by
    calc
      A ≤ ∑ _j : Fin N, (1 + 1 / (N : ℝ)) :=
        Finset.sum_le_sum (fun j _ => (hw j).2.le)
      _ = (N : ℝ) * (1 + 1 / (N : ℝ)) := by simp; ring
      _ = (N : ℝ) + 1 := by field_simp
  have hAp : 0 < A := hNp.trans_le hAlo
  have hLpack : (1 + 1 / (N : ℝ)) / (6 * (N : ℝ)) < L := by
    have hdist : 1 / (6 * L) < (N : ℝ) - 1 := by
      linarith only [hNL]
    have hprod0 : (1 : ℝ) < ((N : ℝ) - 1) * (6 * L) :=
      (div_lt_iff₀ (by positivity : 0 < 6 * L)).mp hdist
    have hprod : (1 : ℝ) < 6 * L * ((N : ℝ) - 1) := by
      nlinarith only [hprod0]
    have hplus : 0 < (N : ℝ) + 1 := by linarith only [hNp]
    have hmul := mul_lt_mul_of_pos_right hprod hplus
    have hquad : ((N : ℝ) - 1) * ((N : ℝ) + 1) < (N : ℝ) ^ 2 := by
      nlinarith
    have hmul2 := mul_lt_mul_of_pos_left hquad (by positivity : 0 < 6 * L)
    have hmain : (N : ℝ) + 1 < 6 * L * (N : ℝ) ^ 2 := by
      nlinarith only [hmul, hmul2]
    have hfrac : ((N : ℝ) + 1) / (6 * (N : ℝ) ^ 2) < L :=
      (div_lt_iff₀ (by positivity : 0 < 6 * (N : ℝ) ^ 2)).mpr
        (by nlinarith only [hmain])
    have heq : (1 + 1 / (N : ℝ)) / (6 * (N : ℝ)) =
        ((N : ℝ) + 1) / (6 * (N : ℝ) ^ 2) := by
      field_simp
    rw [heq]
    exact hfrac
  let ell : Fin N → ℝ := fun j => w j / (6 * A)
  refine ⟨ell, ?_, ?_, ?_, ?_⟩
  · intro j k he
    have hden : 6 * A ≠ 0 := by positivity
    have hwjk : w j = w k := (div_left_inj' hden).mp he
    have hjk : (j.val : ℝ) / (N : ℝ) ^ 2 =
        (k.val : ℝ) / (N : ℝ) ^ 2 := by
      dsimp only [w] at hwjk
      linarith only [hwjk]
    have he' : (j.val : ℝ) = (k.val : ℝ) :=
      (div_left_inj' (by positivity : (N : ℝ) ^ 2 ≠ 0)).mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · intro j
    constructor
    · exact div_pos (by linarith only [(hw j).1])
        (by positivity)
    · calc
        ell j < (1 + 1 / (N : ℝ)) / (6 * A) :=
          (div_lt_div_iff_of_pos_right (by positivity)).mpr (hw j).2
        _ ≤ (1 + 1 / (N : ℝ)) / (6 * (N : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (by linarith only [hAlo])
        _ < L := hLpack
  · dsimp only [ell]
    rw [← Finset.sum_div]
    change A / (6 * A) = 1 / 6
    field_simp
  · intro j
    have hAj : A ≤ ((N : ℝ) + 1) * w j := by
      calc
        A ≤ (N : ℝ) + 1 := hAup
        _ = ((N : ℝ) + 1) * 1 := by ring
        _ ≤ ((N : ℝ) + 1) * w j :=
          mul_le_mul_of_nonneg_left (hw j).1 (by positivity)
    have hbase : 6 * ((N : ℝ) + 1) ≤ 8 * (N : ℝ) := by
      linarith only [hN3]
    have hmul1 := mul_le_mul_of_nonneg_left hAj (by norm_num : (0 : ℝ) ≤ 6)
    have hmul2 := mul_le_mul_of_nonneg_right hbase
      (by linarith only [(hw j).1] : 0 ≤ w j)
    dsimp only [ell]
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * (N : ℝ))
      (by positivity : 0 < 6 * A)).mpr
    nlinarith only [hmul1, hmul2]

theorem near_uniform_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0 < dmin) (hd : dmin ≤ dmax) (hm : 0 < mesh) (hR : 0 < R)
    (N : ℕ) (hN1 : (3 : ℝ) ≤ N)
    (hNL : 1 / (6 * (dmin * min mesh R)) + 1 < (N : ℝ)) :
    ∃ ell : Fin N → ℝ, ∃ rmin : ℝ, 0 < rmin ∧
      Function.Injective ell ∧ (∑ j, ell j) = 1 / 6 ∧
      (∀ j, 0 < ell j ∧ dmax*rmin ≤ ell j ∧
        ell j ≤ dmin*mesh ∧ ell j ≤ dmin*R) ∧
      (∀ d : ℝ, dmin ≤ d → d ≤ dmax →
        ∀ j, rmin ≤ ell j/d ∧ ell j/d ≤ mesh ∧ ell j/d ≤ R) ∧
      (∀ j, (1 : ℝ)/(8 * (N : ℝ)) ≤ ell j) := by
  have hN : 0 < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hN1)
  obtain ⟨ell,hi,he,hS,hslotLower⟩ :=
    near_uniform_distinct_slot_lengths (dmin*min mesh R)
      (mul_pos hdmin (lt_min hm hR)) N hN1 hNL
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0<dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0<rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin≤ ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k≤ dmin*mesh ∧ ell k≤ dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_,hslotLower⟩
  intro d hd' hd'' k
  have hd0 : 0<d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d≤ dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

theorem exists_near_uniform_high_data_fine :
    ∃ D : HighData explicitDelta,
      (∀ j, D.ell j ≤
        ProbeFinalAssemblyCertifiedBands.detectorMesh explicitDelta D.t / 200) ∧
      (∀ j, (1 : ℝ) / (8 * (nearUniformSlotCount : ℝ)) ≤ D.ell j) ∧
      D.N = nearUniformSlotCount ∧ D.t = explicitT := by
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
    have ha0 : allowance≤ t/2000 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
    have hap : allowance*((N:ℝ)+2000)=t := by dsimp [allowance];field_simp
    refine ⟨allowance,ha,?_⟩
    intro ε e eps hε hεa he hea heps hepsa
    have hεt : 2000*ε≤ t := by linarith
    have het : 2000*e≤ t := by linarith
    have hepsN : ((N:ℝ)+2000)*eps≤ t := by
      have h := mul_le_mul_of_nonneg_left hepsa hden.le
      nlinarith
    have heps8 : ((N:ℝ)+8)*eps≤ t := by nlinarith
    constructor <;> nlinarith
  let N : ℕ := nearUniformSlotCount
  have hN1 : (3 : ℝ) ≤ N := by
    have h := nearUniformSlotCount_three_le
    exact_mod_cast h
  have hN : 0 < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hN1)
  have hNL :
      1/(6*((1/200:ℝ)*min (min t (mesh t)) t)) + 1 < (N : ℝ) := by
    simpa [N, t, mesh, explicitFineLength] using nearUniformSlotCount_threshold
  obtain ⟨ell,rmin,hr,hell,hsum,hbounds,_,hslotLower⟩ :=
    near_uniform_physical_slot_lengths (1/200) (7/8) (min t (mesh t)) t
      (by norm_num) (by norm_num) (lt_min ht (hmesh t ht)) ht N hN1 hNL
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤ allowance := min_le_left _ _
  have hst : small≤ t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤ t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤ small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤ t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤ t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤ t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤ t/2 := min_le_left _ _
  have hsell : sigma≤ ellMin/4 := min_le_right _ _
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
    have hτt : τ≤ t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7))≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0≤ τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · intro j
    change ell j≤ mesh t/200
    calc
      ell j≤(1/200:ℝ)*min t (mesh t):=(hbounds j).2.2.1
      _≤(1/200:ℝ)*mesh t:=mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _=mesh t/200:=by ring
  · intro j
    change (1 : ℝ) / (8 * (nearUniformSlotCount : ℝ)) ≤ ell j
    exact hslotLower j


end SevenEighths.Parameters
end
end OAI

namespace OAI
noncomputable section
namespace SevenEighths.RHLeanNearUniformSlotPacking

open Parameters RHLeanActualSlotMin RHLeanExplicitSlotTotalMass
open RHLeanNativeSevenEighthsReplay

/-- A finite source with fewer, nearly uniform slots, still satisfying the
    ORIGINAL detector and all the original LOW/HIGH/principal budgets. -/
theorem native_beta_le_near_uniform_slots :
    HeckeZeroSupremum.beta ≤
      (7 / 8 : ℝ) - 1 / (32 * (nearUniformSlotCount : ℝ)) := by
  obtain ⟨D, hfine, hslot, _hN, _ht⟩ :=
    exists_near_uniform_high_data_fine
  have hbound :=
    native_beta_le_true_physical_slot_minimum_total_mass_of_fine D hfine
  have hmin : (1 : ℝ) / (8 * (nearUniformSlotCount : ℝ)) ≤
      actualSlotMinimum D := by
    exact hslot (leastSlotIndex D)
  have hident : (1 : ℝ) / (32 * (nearUniformSlotCount : ℝ)) =
      ((1 : ℝ) / (8 * (nearUniformSlotCount : ℝ))) / 4 := by ring
  rw [hident]
  exact hbound.trans
    (sub_le_sub_left
      (div_le_div_of_nonneg_right hmin (by norm_num : (0 : ℝ) ≤ 4))
      (7 / 8))

end SevenEighths.RHLeanNearUniformSlotPacking
end
end OAI

namespace RHLean.Analysis
open MertensExponent OAI.SevenEighths
open OAI.SevenEighths.Parameters
open OAI.SevenEighths.RHLeanNearUniformSlotPacking
open OAI.SevenEighths.RHLeanNativeSevenEighthsReplay

/-- Full original arithmetic Mertens consequence of the *same* analytic
    endpoint and exact pinned OAI-to-rational transfer. -/
theorem native_mertens_near_uniform_slots :
    MertensGrowthAtMost
      ((7 / 8 : ℝ) - 1 / (32 * (nearUniformSlotCount : ℝ))) := by
  exact growthAtMost_mono native_beta_le_near_uniform_slots
    native_mertens_growth_at_hecke_beta

end RHLean.Analysis

