import Mathlib

/-!
# Retained-slot scalar feedback

The source width W is not the Mertens function. These lemmas preserve the
original selected mass, clipping cases, and kappa-dependent reserve.
Analytic propagation is checked separately against the pinned OAI sources.
-/
namespace RHLeanFeedback

 theorem current_feedback_clipped (b : Real) (hb : b <= 7/8) :
    max (3/4 : Real) (2*b-1) = 3/4 := by
  apply max_eq_left
  linarith

 theorem improved_boundary_licenses_kappa (beta gap : Real)
    (hgap : 0 < gap) (hgapTop : gap < 1/8)
    (hbeta : beta <= 7/8-gap) :
    And (1/2 < 3/4-2*gap)
      (And (3/4-2*gap < 3/4) (2*beta-1 <= 3/4-2*gap)) := by
  constructor
  · linarith
  · constructor <;> linarith

 theorem parent_slot_budget (W total ell kappa defect : Real)
    (hlarge : 5*W/6-defect <= total+ell)
    (hcap : total+6*kappa*ell <= W) :
    (6*kappa-1)*ell <= W/6+defect := by
  nlinarith

 theorem retained_slot_gate_of_reserve (W ell kappa xi defect : Real)
    (hk : 1/2 < kappa)
    (hbudget : (6*kappa-1)*ell <= W/6+defect)
    (hreserve : (6*kappa-1)*xi+(6*kappa+1)*defect <= (6*kappa-3)*W/6) :
    2*ell+xi+defect <= W/6 := by
  have hd : 0 < 6*kappa-1 := by linarith
  apply (mul_le_mul_left hd).mp
  nlinarith only [hbudget, hreserve]

 theorem reflected_low_of_retained_slot
    (W short along ell z kappa xi defect reflected : Real)
    (hW : 0 <= W) (hshort : short <= W/4)
    (hz : 0 <= z) (hze : z <= ell) (hk : 1/6 <= kappa)
    (hxi : 0 <= xi) (he : 0 <= defect)
    (hsmall : 2*ell+xi+defect <= W/6)
    (hbudget : (6*kappa-1)*ell <= W/6+defect)
    (hhigh : 5*W/6 < short+max 0 along+z)
    (href : reflected <= max 0 (W-along+xi)) :
    And (0 < along)
      (And (reflected+short+z <= 5*W/6)
           (reflected+short+6*kappa*z <= W)) := by
  have hzsmall : 2*z+xi+defect <= W/6 := by linarith
  have hzbudget : (6*kappa-1)*z <= W/6+defect :=
    (mul_le_mul_of_nonneg_left hze (by linarith : 0 <= 6*kappa-1)).trans hbudget
  have hapos : 0 < along := by
    by_contra hn
    have ha : along <= 0 := le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right hapos.le] at hhigh
  refine And.intro hapos ?_
  by_cases hr : 0 <= W-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

 theorem original_reserve_recovered (W xi defect : Real) :
    ((6*(3/4 : Real)-1)*xi+(6*(3/4 : Real)+1)*defect <=
      (6*(3/4 : Real)-3)*W/6) <->
    xi+(11/7 : Real)*defect <= W/14 := by
  constructor <;> intro h <;> nlinarith

#print axioms current_feedback_clipped
#print axioms improved_boundary_licenses_kappa
#print axioms parent_slot_budget
#print axioms retained_slot_gate_of_reserve
#print axioms reflected_low_of_retained_slot
#print axioms original_reserve_recovered
end RHLeanFeedback
