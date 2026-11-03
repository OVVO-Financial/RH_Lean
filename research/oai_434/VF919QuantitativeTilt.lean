import «research.oai_434.VF919QuantitativeHighAssembly»
import «research.oai_434.VF919NativeStrictMertens»

/-!
# Quantitative source-relative contraction

One fixed source supplies physical tilt e/2. The LOW estimate keeps its
arbitrary loss; the HIGH estimate is extended to beta >= 7/8-e/2 with its
extra floor and tail costs paid explicitly. This relates the physical tilt
to the global boundary, rather than only excluding equality at 7/8.
-/
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Asymptotics
namespace SevenEighths.RHLeanNativeSevenEighthsReplay
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open ProbeFinalAssembly PrincipalSignalComparison RHLeanFiniteSlotGap
open ProbeFinalAssemblyCertifiedBands
open CenteredMomentDetectorPlainMomentParameters

/-- The internally supplied native moments yield the complete identical-probe
pair throughout the enlarged near-endpoint range. -/
theorem native_quantitative_probe_bounds
    (D : HighData (1/1000000:ℝ))
    (hfine : ∀j,D.ell j≤detectorMesh (1/1000000) D.t/200)
    (hepsilon : D.ε≤D.t/2000) (he : D.e≤D.t/2000)
    (heps : ((D.N:ℝ)+8)*D.eps≤D.t) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t)
    (hβ : (7/8:ℝ)-D.e/2≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8+1/1000000) :
    ∀η : Character,
      (∀loss : ℝ,0<loss →
        F.tiltedProbe (D.e/2) η=O[atTop]
          (fun Z : ℝ=>Z^(3/16-9*(D.e/2)+loss))) ∧
      (fun Z=>F.tiltedProbe (D.e/2) η Z-
        HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection η F.S) (-11/16-8*(D.e/2)) Z)=O[atTop]
        (fun Z : ℝ=>Z^(HeckeZeroSupremum.beta-11/16-8*(D.e/2)-D.sigma)) := by
  obtain ⟨J,hJ,hmom⟩ := native_uniform_fixed_source_moments D
    (by linarith only [hβ,D.e_small]) hβhi hfine F counts
  have hsource : ∀η : Character,∃C : ℝ,0<C ∧
      ∀τ : ℝ,0<τ → τ≤1 → ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
    intro η
    obtain ⟨C,hC,Z0,hZ0,hb⟩ := hmom η
    refine ⟨C,hC,?_⟩
    intro τ _ _
    filter_upwards [eventually_ge_atTop Z0] with Z hZ
    exact (nativeSourceMomentBound_iff F counts η Z τ _ _).mp
      (hb Z hZ τ (Z^(2*τ)) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ :=
    chosen_data_height D F counts J hJ hsource
  obtain ⟨C,hC,hhigh⟩ := fixed_tilted_high_bound_near_endpoint D hβ
    hepsilon he heps F counts τ hτ hτd hτcost hτt hτ2 hτeps
  obtain ⟨htilt,hcharge,htilt1,_⟩ := enlarged_source_gain_budgets D
  intro η
  refine ⟨fun loss hloss=>F.tiltedProbe_low (D.e/2) htilt.le htilt1 hcharge.le loss hloss η,?_⟩
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource] with Z hh hs
  exact hh Cm hCm.le hs

/-- For each fully admissible fixed source, its actual e/2 tilt is a global
boundary gain. There is no assumed moment, probe estimate, or improved
zero-free region in the hypotheses. -/
theorem native_beta_le_half_source_e
    (D : HighData (1/1000000:ℝ))
    (hfine : ∀j,D.ell j≤detectorMesh (1/1000000) D.t/200)
    (hepsilon : D.ε≤D.t/2000) (he : D.e≤D.t/2000)
    (heps : ((D.N:ℝ)+8)*D.eps≤D.t) :
    HeckeZeroSupremum.beta≤7/8-D.e/2 := by
  by_contra hn
  let tilt := D.e/2
  have hgt : 7/8-tilt<HeckeZeroSupremum.beta := lt_of_not_ge hn
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := source_count_parameters F
  have hprobes := native_quantitative_probe_bounds D hfine hepsilon he heps F counts
    hgt.le (by linarith only [native_beta_le_seven_eighths])
  obtain ⟨htilt,_hcharge,htilt1,_htiltCut,_⟩ := enlarged_source_gain_budgets D
  change 0<tilt at htilt
  change tilt<1/960 at htilt1
  let omega := (HeckeZeroSupremum.beta-(7/8-tilt))/2
  have homega : 0<omega := by dsimp [omega];linarith only [hgt]
  let gapMargin : ℝ := min omega D.sigma
  have hmargin : 0 < gapMargin := lt_min homega D.sigma_pos
  have hmleft : gapMargin ≤ omega := min_le_left _ _
  have hmright : gapMargin ≤ D.sigma := min_le_right _ _
  have hmleft_explicit :
      gapMargin ≤ (HeckeZeroSupremum.beta - (7/8-tilt))/2 := hmleft
  obtain ⟨η,ρ,_hprimitive,hhalf,_hstrip,hpole,hzero,hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin
      (by linarith only [hgt,htilt1,hmleft_explicit])
  let χ := η.excludePrimes F.S F.exclusions.prime
  have hmask := excludePrimes_mask η F.S F.exclusions.prime
  have hχpole : ρ≠1 ∨ χ.residue≠1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr
        (fun hc=>hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : LFunction χ ρ=0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by linarith only [hhalf]) hχpole,hzero,zero_mul]
  have hboundary : max (7/8-tilt+omega) (HeckeZeroSupremum.beta-D.sigma)<ρ.re := by
    dsimp [omega] at hmleft ⊢
    exact max_lt (by linarith only [hnear,hmleft]) (by linarith only [hnear,hmright])
  obtain ⟨hlow,hhigh⟩ := hprobes η
  apply (HeckeSignal.nonzero_of_probe_bounds_variable_boundary
    χ (sourceCorrection η F.S) (F.tiltedProbe tilt η)
    (21/25) (7/8-tilt) HeckeZeroSupremum.beta omega D.sigma (-11/16-8*tilt)
    (by norm_num) (by linarith only [htilt1]) (by linarith only [htilt1])
    HeckeZeroSupremum.beta_le_one homega
    (by dsimp [omega];linarith only [hgt]) D.sigma_pos
    (sourceCorrection_analytic_wide η F.S F.exclusions)
    (sourceCorrection_bound_wide η F.S F.exclusions)
    ?_ ?_ hboundary hχpole) hzχ
  · convert hlow omega homega using 1;dsimp [tilt];ring_nf
  · convert hhigh using 1;dsimp [tilt,χ];ring_nf

/-- The source exists before all characters and physical scales. Its positive
physical tilt is now explicitly a certified global boundary reduction. -/
theorem native_quantitative_source_gap :
    ∃D : HighData (1/1000000:ℝ),
      0<D.e/2 ∧ HeckeZeroSupremum.beta≤7/8-D.e/2 := by
  obtain ⟨D,hfine,hepsilon,he,heps,_hsigma,_hemin⟩ :=
    exists_fine_high_data_with_reserve (1/1000000) (by norm_num)
      (detectorMesh (1/1000000))
      (fun t ht=>detectorMesh_pos (by norm_num) ht)
  exact ⟨D,div_pos D.e_pos (by norm_num),
    native_beta_le_half_source_e D hfine hepsilon he heps⟩

#check native_quantitative_source_gap
#print axioms native_quantitative_probe_bounds
#print axioms native_beta_le_half_source_e
#print axioms native_quantitative_source_gap
end SevenEighths.RHLeanNativeSevenEighthsReplay
end
end OAI

namespace RHLean.Analysis
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.RHLeanNativeSevenEighthsReplay

/-- The same source-relative saving transfers to the actual integer Moebius
prefix via the already proved native converse. -/
theorem native_mertens_quantitative_source_gap :
    ∃D : Parameters.HighData (1/1000000:ℝ),
      0<D.e/2 ∧ MertensExponent.MertensGrowthAtMost (7/8-D.e/2) := by
  obtain ⟨D,hpos,hbound⟩ := native_quantitative_source_gap
  exact ⟨D,hpos,MertensExponent.growthAtMost_mono hbound native_mertens_growth_at_hecke_beta⟩

#check native_mertens_quantitative_source_gap
#print axioms native_mertens_quantitative_source_gap
end
end RHLean.Analysis
