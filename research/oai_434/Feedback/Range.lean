import research.oai_434.RetainedSlotFeedback

/-! A fixed lower parameter is chosen before all analytic constants. -/
namespace RHLeanFeedback

class KappaRange where
  lower : Real
  lower_gt_half : (1/2 : Real) < lower

noncomputable def kappaFloor [KappaRange] : Real := KappaRange.lower

theorem kappaFloor_gt [KappaRange] : (1/2 : Real) < kappaFloor :=
  KappaRange.lower_gt_half

theorem kappa_gt [KappaRange] {kappa : Real} (h : kappaFloor <= kappa) :
    (1/2 : Real) < kappa := lt_of_lt_of_le kappaFloor_gt h

noncomputable def allowance [KappaRange] (rho : Real) : Real :=
  rho * min (1/100 : Real) ((6*kappaFloor-3)/(24*(6*kappaFloor)))

theorem allowance_pos [KappaRange] (rho : Real) (hrho : 0 < rho) :
    0 < allowance rho := by
  have hf := kappaFloor_gt
  have hn : 0 < 6*kappaFloor-3 := by linarith
  have hd : 0 < 24*(6*kappaFloor) := by linarith
  exact mul_pos hrho (lt_min (by norm_num) (div_pos hn hd))

theorem allowance_le [KappaRange] (rho : Real) (hrho : 0 <= rho) :
    allowance rho <= rho/100 := by
  unfold allowance
  have h := mul_le_mul_of_nonneg_left
    (min_le_left (1/100 : Real) ((6*kappaFloor-3)/(24*(6*kappaFloor)))) hrho
  linarith

theorem uniform_reserve [KappaRange]
    (rho kappa width xi defect : Real)
    (hrho : 0 < rho) (hk : kappaFloor <= kappa)
    (hwidth : rho <= width) (_hxi : 0 <= xi) (_he : 0 <= defect)
    (hxiCap : xi <= allowance rho) (heCap : defect <= allowance rho) :
    (6*kappa-1)*xi+(6*kappa+1)*defect <= (6*kappa-3)*width/6 := by
  have hf := kappaFloor_gt
  have hkp := kappa_gt hk
  have hr := allowance_pos rho hrho
  have hrsmall := allowance_le rho hrho.le
  have hden : 0 < 24*(6*kappaFloor) := by linarith
  have hfrac : allowance rho <= (rho*(6*kappaFloor-3))/(24*(6*kappaFloor)) := by
    unfold allowance
    have h := mul_le_mul_of_nonneg_left
      (min_le_right (1/100 : Real) ((6*kappaFloor-3)/(24*(6*kappaFloor)))) hrho.le
    simpa only [mul_div_assoc] using h
  have hp := (le_div_iff₀ hden).mp hfrac
  have hbase : 12*kappaFloor*allowance rho <= (kappaFloor-1/2)*rho := by
    nlinarith [mul_nonneg (show 0 <= kappaFloor by linarith) hr.le]
  have hdelta : 0 <= (kappa-kappaFloor)*(rho-12*allowance rho) :=
    mul_nonneg (sub_nonneg.mpr hk) (by linarith)
  have hscale : 0 <= (kappa-1/2)*(width-rho) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hwidth)
  have hxiWeight := mul_le_mul_of_nonneg_left hxiCap (show 0 <= 6*kappa-1 by linarith)
  have heWeight := mul_le_mul_of_nonneg_left heCap (show 0 <= 6*kappa+1 by linarith)
  nlinarith only [hbase,hdelta,hscale,hxiWeight,heWeight]

theorem slot_budgets_no_defect [KappaRange]
    (width total ell kappa : Real) (_hwidth : 0 <= width)
    (hell : 0 <= ell) (hk : kappaFloor <= kappa)
    (hlarge : 5*width/6 <= total+ell)
    (hcap : total+ell+(6*kappa-1)*ell <= width) :
    ell <= width/12 /\ (6*kappa-1)*ell <= width/6 := by
  have hkp := kappa_gt hk
  have hb : (6*kappa-1)*ell <= width/6 := by nlinarith only [hlarge,hcap]
  have hp : 0 <= (6*kappa-3)*ell := mul_nonneg (by linarith) hell
  constructor <;> nlinarith only [hb,hp]

end RHLeanFeedback
