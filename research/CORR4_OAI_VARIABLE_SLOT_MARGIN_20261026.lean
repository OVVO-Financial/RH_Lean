import Mathlib

/-!
# CORR-4 / OpenAI: variable selected-slot length and high endpoint margin

This is an exact real-arithmetic audit of the original OpenAI
compensated-probe energy bookkeeping (paper equations 5.3, 5.4,
5.11, 6.6 and the final high exponent).

At ell=1/6 the manuscript simplifies a reflected-row positive part
to zero. The general expression is (5*ell-1+d)_+/4 for rescaled
subset length d. The rescaled-subset normalization gives a further
Z^(-d). This file proves that after Cauchy-Schwarz the positive part
does not consume ANY additional positive exponent if ell<=1/5.

A candidate ell=1/6+4*eps changes the crossing to 7/8-eps,
while retaining X*Y*slot=Z and the same principal exponent
C(s)=s-11/16.

The high endpoint E(h) changes by
4*eps*(-1/4+delta+q+3*R/2). Under the *numeric* original-bin
ranges, its rise is at most 10*eps. The existing endpoint
certificate has margin 49/440640, so a tiny perturbation does not
break this ONE algebraic margin.

IMPORTANT: These are precise necessary arithmetic checks, NOT a
proof that OpenAI's actual reflected-energy lemma, the selected
slot family, original theta phases, moment/capacity bounds,
principal correction or all other high-bin conditions extend to
the variable ell. No strict zero-free exponent is asserted here.
-/

noncomputable section
namespace RHLean.Analysis

/-- The retained reflected-energy branch from the source's
  (1+3*ell'-2*M')/4 formula after the full physical budget
  M+ell=1 and a rescaled subset of length d. -/
theorem corr4_oai_reflected_variable_slot_identity (ell d : ℝ) :
    ((1 + 3 * (ell - d) - 2 * ((1 - ell) - 2 * d)) / 4) =
      (5 * ell - 1 + d) / 4 := by
  ring

/-- Critical: the genuine original -d subset payment absorbs the
  extra reflected-row exponent after taking the Cauchy square root.
  This is uniform over all d>=0 when the total slot length <=1/5. -/
theorem corr4_oai_low_subset_variable_slot_no_loss
    (ell d : ℝ) (hell : ell ≤ 1 / 5) (hd : 0 ≤ d) :
    -d + (max 0 (5 * ell - 1 + d)) / 8 ≤ 0 := by
  have hpos : (0 : ℝ) ≤ d := hd
  have hright : 5 * ell - 1 + d ≤ d := by linarith
  have hmax : max 0 (5 * ell - 1 + d) ≤ d :=
    max_le hpos hright
  linarith

/-- The exact perturbed Stage-II geometry. None of the displayed
  resource equations changes with epsilon. -/
theorem corr4_oai_candidate_slot_geometry (eps : ℝ) :
    let ell : ℝ := 1 / 6 + 4 * eps
    let lx : ℝ := 17 / 48 - 2 * eps
    let ly : ℝ := 23 / 48 - 2 * eps
    let h : ℝ := 13 / 16 + 6 * eps
    let theta : ℝ := 7 / 8 - eps
    lx + ly + ell = 1 ∧
    ly = lx + 1 / 8 ∧
    h = 1 + ell - lx ∧
    theta = 11 / 12 - ell / 4 ∧
    lx / 2 - 1 + h / 6 = -11 / 16 := by
  dsimp
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

/-- The simple open source gates are still strictly satisfied for
  eps <=1/1000000, including small Q, positive length and low-gram
  P_a^2/Y' payment. This checks geometry, not analytic theorems. -/
theorem corr4_oai_candidate_low_scale_gates (eps : ℝ)
    (_heps : 0 ≤ eps) (hepsSmall : eps ≤ 1 / 1000000) :
    let ell : ℝ := 1 / 6 + 4 * eps
    let lx : ℝ := 17 / 48 - 2 * eps
    let ly : ℝ := 23 / 48 - 2 * eps
    let M : ℝ := 5 / 6 - 4 * eps
    ell ≤ 1 / 5 ∧
    0 < M - 2 * ell ∧
    0 < lx - ell ∧
    0 < ly - ell ∧
    0 < ly - ell - 11 * (1 / 8) / 6 := by
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- At the original compensated high row height h, the exact
  source exponent E(h) has the stated Lipschitz response in ell.
  The source's 'a' parameter is (1+delta)/2, and z0=17/50. -/
theorem corr4_oai_high_endpoint_perturb_identity
    (eps delta q R : ℝ) :
    let ell0 : ℝ := 1 / 6
    let ell : ℝ := ell0 + 4 * eps
    let ly0 : ℝ := 23 / 48
    let ly : ℝ := ly0 - 2 * eps
    let h0 : ℝ := 13 / 16
    let h : ℝ := h0 + 6 * eps
    let theta0 : ℝ := 7 / 8
    let theta : ℝ := theta0 - eps
    let a : ℝ := (1 + delta) / 2
    let z0 : ℝ := 17 / 50
    (a - theta + h * (z0 - 1 / 6) - a * ly - ell / 2 +
        ell * q + h * (R + delta / 2 - z0)) -
      (a - theta0 + h0 * (z0 - 1 / 6) - a * ly0 - ell0 / 2 +
        ell0 * q + h0 * (R + delta / 2 - z0)) =
    4 * eps * (-1 / 4 + delta + q + 3 * R / 2) := by
  dsimp
  ring

/-- Uses only the actual original paper's bin ranges
  0<=delta<=5/6, 0<=q<=delta/2, and R<=1. -/
theorem corr4_oai_high_endpoint_slope_le_five_halves
    (delta q R : ℝ)
    (hdelta : 0 ≤ delta ∧ delta ≤ 5 / 6)
    (hq : 0 ≤ q ∧ q ≤ delta / 2)
    (hR : R ≤ 1) :
    -1 / 4 + delta + q + 3 * R / 2 ≤ 5 / 2 := by
  linarith

/-- The worst-bin endpoint certificate's strictly positive
  49/440640 margin has room for a 4e-6 slot perturbation,
  PROVIDED the original arithmetic R,q bounds survive. -/
theorem corr4_oai_margin_survives_tiny_perturbation
    (eps delta q R : ℝ)
    (heps : 0 ≤ eps) (hepsSmall : eps ≤ 1 / 1000000)
    (hdelta : 0 ≤ delta ∧ delta ≤ 5 / 6)
    (hq : 0 ≤ q ∧ q ≤ delta / 2)
    (hR : R ≤ 1) :
    4 * eps * (-1 / 4 + delta + q + 3 * R / 2) <
      49 / 440640 := by
  have hslope := corr4_oai_high_endpoint_slope_le_five_halves
    delta q R hdelta hq hR
  have hup : 4 * eps * (-1 / 4 + delta + q + 3 * R / 2) ≤
      4 * eps * (5 / 2) := by
    exact mul_le_mul_of_nonneg_left hslope (by linarith)
  nlinarith

#print axioms corr4_oai_reflected_variable_slot_identity
#print axioms corr4_oai_low_subset_variable_slot_no_loss
#print axioms corr4_oai_candidate_slot_geometry
#print axioms corr4_oai_candidate_low_scale_gates
#print axioms corr4_oai_high_endpoint_perturb_identity
#print axioms corr4_oai_margin_survives_tiny_perturbation

end RHLean.Analysis
