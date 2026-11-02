import «research.oai_434.VF919TiltedHighAssembly»
import «research.oai_434.VF919NativeSevenEighthsReplay»

/-!
# Strict endpoint exclusion from the actual native moments and tilted probe

One positive auxiliary arithmetic parameter and one physical tilt are fixed
before all characters. Both normalized estimates concern exactly the same
compensated physical probe. The final contradiction uses a primitive zero
arbitrarily near the supremum, with all moment input supplied internally.
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

/-- The fixed native source moments supply the complete pair of estimates;
there is no probe bound or moment certificate among the hypotheses. -/
theorem native_fixed_tilted_probe_bounds
    (D : HighData (1/1000000:ℝ))
    (hfine : ∀j,D.ell j≤detectorMesh (1/1000000) D.t/200)
    (hepsilon : D.ε≤D.t/2000) (he : D.e≤D.t/2000)
    (heps : ((D.N:ℝ)+8)*D.eps≤D.t) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8+1/1000000) :
    ∀η : Character,
      (∀loss : ℝ,0<loss →
        F.tiltedProbe (D.e/48) η=O[atTop]
          (fun Z : ℝ=>Z^(3/16-9*(D.e/48)+loss))) ∧
      (fun Z=>F.tiltedProbe (D.e/48) η Z-
        HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection η F.S) (-11/16-8*(D.e/48)) Z)=O[atTop]
        (fun Z : ℝ=>Z^(HeckeZeroSupremum.beta-11/16-8*(D.e/48)-D.sigma)) := by
  obtain ⟨J,hJ,hmom⟩ := native_uniform_fixed_source_moments D (by linarith) hβhi hfine F counts
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
  obtain ⟨C,hC,hhigh⟩ :=
    fixed_tilted_high_bound hβ D hepsilon he heps F counts τ hτ hτd hτcost hτt hτ2 hτeps
  intro η
  refine ⟨fun loss hloss=>F.fixed_tiltedProbe_low loss hloss η,?_⟩
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource] with Z hh hs
  exact hh Cm hCm.le hs

/-- The endpoint cannot equal 7/8. All LOW/HIGH estimates, arithmetic
moments, normalizers and positive margins are supplied by proved lemmas. -/
theorem native_beta_lt_seven_eighths : HeckeZeroSupremum.beta<7/8 := by
  by_contra hn
  have hβ : HeckeZeroSupremum.beta=7/8 :=
    le_antisymm native_beta_le_seven_eighths (le_of_not_gt hn)
  obtain ⟨D,hfine,hepsilon,he,heps,_hsigma,_hemin⟩ :=
    exists_fine_high_data_with_reserve (1/1000000) (by norm_num)
      (detectorMesh (1/1000000))
      (fun t ht=>detectorMesh_pos (by norm_num) ht)
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := source_count_parameters F
  have hprobes := native_fixed_tilted_probe_bounds D hfine hepsilon he heps F counts
    (by linarith) (by linarith)
  let tilt := D.e/48
  obtain ⟨htilt,_hcharge,htilt1,_htiltCut,_⟩ := source_gain_budgets D
  change 0<tilt at htilt
  change tilt<1/960 at htilt1
  let margin := min (tilt/2) D.sigma
  have hmargin : 0<margin := lt_min (by positivity) D.sigma_pos
  have hmleft : margin≤tilt/2 := min_le_left _ _
  have hmright : margin≤D.sigma := min_le_right _ _
  obtain ⟨η,ρ,_hprimitive,hhalf,_hstrip,hpole,hzero,hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin (by linarith)
  let χ := η.excludePrimes F.S F.exclusions.prime
  have hmask := excludePrimes_mask η F.S F.exclusions.prime
  have hχpole : ρ≠1 ∨ χ.residue≠1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr
        (fun hc=>hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : LFunction χ ρ=0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask
      (by linarith) hχpole,hzero,zero_mul]
  have hboundary : max (7/8-tilt+tilt/2) (HeckeZeroSupremum.beta-D.sigma)<ρ.re :=
    max_lt (by linarith) (by linarith)
  obtain ⟨hlow,hhigh⟩ := hprobes η
  apply (HeckeSignal.nonzero_of_probe_bounds_variable_boundary
    χ (sourceCorrection η F.S) (F.tiltedProbe tilt η)
    (21/25) (7/8-tilt) HeckeZeroSupremum.beta (tilt/2) D.sigma (-11/16-8*tilt)
    (by norm_num) (by linarith) (by linarith) HeckeZeroSupremum.beta_le_one
    (by positivity) (by linarith) D.sigma_pos
    (sourceCorrection_analytic_wide η F.S F.exclusions)
    (sourceCorrection_bound_wide η F.S F.exclusions)
    ?_ ?_ hboundary hχpole) hzχ
  · convert hlow (tilt/2) (by positivity) using 1; dsimp [tilt]; ring_nf
  · convert hhigh using 1; dsimp [tilt,χ]; ring_nf

/-- Strictness provides a single positive global gap, without asserting a
numerical value equal to the physical tilt chosen in the endpoint argument. -/
theorem native_uniform_positive_gap :
    ∃gap : ℝ,0<gap ∧ HeckeZeroSupremum.beta≤7/8-gap := by
  refine ⟨(7/8-HeckeZeroSupremum.beta)/2,?_,?_⟩ <;>
    linarith only [native_beta_lt_seven_eighths]

/-- One strict zero-free boundary is shared by all characters. -/
theorem native_uniform_hecke_gap :
    ∃gap : ℝ,0<gap ∧ ∀(χ : Character) (s : ℂ),
      7/8-gap<s.re → (s≠1 ∨ χ.residue≠1) → LFunction χ s≠0 := by
  obtain ⟨gap,hgap,hbound⟩ := native_uniform_positive_gap
  refine ⟨gap,hgap,?_⟩
  intro χ s hs hpole
  exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ (hbound.trans_lt hs) hpole

#print axioms native_fixed_tilted_probe_bounds
#check native_beta_lt_seven_eighths
#print axioms native_beta_lt_seven_eighths
#check native_uniform_positive_gap
#print axioms native_uniform_positive_gap
#print axioms native_uniform_hecke_gap
end SevenEighths.RHLeanNativeSevenEighthsReplay
end
end OAI
