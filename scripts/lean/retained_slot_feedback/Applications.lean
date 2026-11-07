import research.oai_434.Feedback.SourceMoments
import research.oai_434.Feedback.RowCount

/-! Feedback licenses and source-mesh reuse. No terminal exponent is assumed. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.RetainedSlotApplications
open HeckeFamily ProbeFinalAssembly Parameters RetainedSlotDetector
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentDetectorPlainMomentParameters

lemma detectorMeshAt_antitone (kappa1 kappa2 t : ℝ)
    (hk : 0 ≤ kappa1) (h12 : kappa1 ≤ kappa2) (ht : 0 < t) :
    detectorMeshAt kappa2 t ≤ detectorMeshAt kappa1 t := by
  have hb := sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) (count 2 (t/4))
  have hr := (bounds 2 (finalSourceCap 2 0 1 (t/4)) kappa1 (t/4)
    (by norm_num) hb hk (by positivity)).2.2.2.1
  change reserve 2 (finalSourceCap 2 0 1 (t/4)) (t/4)/(kappa2+1) ≤
    reserve 2 (finalSourceCap 2 0 1 (t/4)) (t/4)/(kappa1+1)
  exact div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)

lemma original_source_fineness_preserved {Delta : ℝ} (D : HighData Delta)
    (kappa : ℝ) (hk : 0 ≤ kappa) (hupper : kappa ≤ kappaPlain D)
    (hfine : ∀ j, D.ell j ≤ detectorMeshAt (kappaPlain D) D.t/200) :
    ∀ j, D.ell j ≤ detectorMeshAt kappa D.t/200 := by
  have hm := detectorMeshAt_antitone kappa (kappaPlain D) D.t hk hupper D.t_pos
  intro j
  linarith [hfine j]

lemma strict_family_boundary_has_feedback_parameter
    (hbeta : HeckeZeroSupremum.beta < 7/8) :
    ∃ kappa : ℝ, 1/2 < kappa ∧ kappa < 3/4 ∧
      2*HeckeZeroSupremum.beta-1 ≤ kappa := by
  let lower : ℝ := max (1/2) (2*HeckeZeroSupremum.beta-1)
  have hl : lower < 3/4 := max_lt (by norm_num) (by linarith)
  have hhalf : (1/2 : ℝ) ≤ lower := le_max_left _ _
  have hlicense : 2*HeckeZeroSupremum.beta-1 ≤ lower := le_max_right _ _
  refine ⟨(lower+3/4)/2, ?_, ?_, ?_⟩ <;> linarith

#print axioms detectorMeshAt_antitone
#print axioms original_source_fineness_preserved
#print axioms strict_family_boundary_has_feedback_parameter
end SevenEighths.RetainedSlotApplications
end
end OAI
