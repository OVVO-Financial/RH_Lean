import Mathlib

/-!
# Exponent accounting for original sharp square-block localization

H is the physical square-root scale (x~H^2), delta>0 the target
saving below H^(5/2-delta), and kappa>=0 collar slack.

Pick physical collar Delta=H^(3/4-delta/2-kappa). Then the trivial
collar energy is H*Delta^2=H^(5/2-delta-2*kappa).

Normalized log transition width is Delta/H^2, so effective Mellin
frequency is H^2/Delta=H^(5/4+delta/2+kappa). It is an EFFECTIVE
frequency, not a compact Mellin Fourier support.

A squared-derivative Sobolev trace on u_R=2 log R costs
(T/H)^2=H^(1/2+delta+2*kappa), but it is NONOPTIMAL:
the first-derivative / Plancherel--Polya trace costs only
(T/H)=H^(1/4+delta/2+kappa). With an additional hypothetical
RELATIVE profile factor (T/H)^beta, the full budget requires

  delta0 >= 1/2 + 2*delta + 2*kappa + beta*(1/4+delta/2+kappa).

The actual pinned OAI raw moment permits a different polynomial
ABSOLUTE height factor T^J, which may be larger. The final source
certificate chooses T=Z^(2*tau), tau<1/400. If the physical scale
were identified as Z~H^2, its root-height power is <1/100, much below
the sharp collar power. That scale identification is NOT certified here.

No analytic moment, frequency localization, root-indexed Plancherel,
or power saving is assumed or claimed in this file.
-/

noncomputable section

namespace RHLean.Analysis

def oaiCollarPower (delta kappa : Real) : Real :=
  3 / 4 - delta / 2 - kappa

def oaiMellinPower (delta kappa : Real) : Real :=
  2 - oaiCollarPower delta kappa

def oaiGridTracePower (delta kappa : Real) : Real :=
  2 * (oaiMellinPower delta kappa - 1)

def oaiRelativeProfilePower (delta kappa beta : Real) : Real :=
  beta * (oaiMellinPower delta kappa - 1)

def oaiAbsoluteHeightPower (delta kappa J : Real) : Real :=
  J * oaiMellinPower delta kappa

theorem oaiCollarRoundingPower (delta kappa : Real) :
    1 + 2 * oaiCollarPower delta kappa =
      5 / 2 - delta - 2 * kappa := by
  unfold oaiCollarPower
  ring

theorem oaiMellinPower_eq (delta kappa : Real) :
    oaiMellinPower delta kappa = 5 / 4 + delta / 2 + kappa := by
  unfold oaiMellinPower oaiCollarPower
  ring

theorem oaiGridTracePower_eq (delta kappa : Real) :
    oaiGridTracePower delta kappa = 1 / 2 + delta + 2 * kappa := by
  unfold oaiGridTracePower oaiMellinPower oaiCollarPower
  ring

theorem oaiRelativeProfilePower_eq (delta kappa beta : Real) :
    oaiRelativeProfilePower delta kappa beta =
      beta * (1 / 4 + delta / 2 + kappa) := by
  unfold oaiRelativeProfilePower oaiMellinPower oaiCollarPower
  ring

theorem oaiAbsoluteHeightPower_eq (delta kappa J : Real) :
    oaiAbsoluteHeightPower delta kappa J =
      J * (5 / 4 + delta / 2 + kappa) := by
  unfold oaiAbsoluteHeightPower oaiMellinPower oaiCollarPower
  ring

/-- Within the GENERIC Sobolev-trace strategy only, a smooth
H^(5/2-delta0) moment gives target H^(5/2-delta) after the trace and
relative profile charges precisely when this budget holds.
Other genuinely arithmetic methods may bypass these charges. -/
theorem oaiGenericRelativeBudget_iff
    (delta delta0 kappa beta : Real) :
    (5 / 2 - delta0 + oaiGridTracePower delta kappa +
        oaiRelativeProfilePower delta kappa beta ≤ 5 / 2 - delta) ↔
    (1 / 2 + 2 * delta + 2 * kappa +
        beta * (1 / 4 + delta / 2 + kappa) ≤ delta0) := by
  rw [oaiGridTracePower_eq, oaiRelativeProfilePower_eq]
  constructor <;> intro h <;> linarith

/-- Same audit with the pinned absolute height factor T^J. -/
theorem oaiGenericAbsoluteBudget_iff
    (delta delta0 kappa J : Real) :
    (5 / 2 - delta0 + oaiGridTracePower delta kappa +
        oaiAbsoluteHeightPower delta kappa J ≤ 5 / 2 - delta) ↔
    (1 / 2 + 2 * delta + 2 * kappa +
        J * (5 / 4 + delta / 2 + kappa) ≤ delta0) := by
  rw [oaiGridTracePower_eq, oaiAbsoluteHeightPower_eq]
  constructor <;> intro h <;> linarith

/-- Under an independently established Z~H^2, chosen OAI
height Z^(2*tau), tau<1/400, has H-exponent <1/100. -/
theorem oaiChosenHeightRootPower_lt
    (tau : Real) (htau : tau < 1 / 400) :
    4 * tau < 1 / 100 := by
  linarith

/-- Natural-scale comparison only, not a source-scale equality. -/
theorem oaiChosenHeightRootPower_lt_mellin
    (delta kappa tau : Real) (hdelta : 0 ≤ delta)
    (hkappa : 0 ≤ kappa) (htau : tau < 1 / 400) :
    4 * tau < oaiMellinPower delta kappa := by
  rw [oaiMellinPower_eq]
  linarith


/-!
## Refined first-derivative grid trace: a +1/4, not compulsory +1/2, tax

The earlier squared-derivative Sobolev trace is VALID but suboptimal.
For an absolutely continuous F, the fundamental theorem for |F|^2
gives a first-derivative sampling estimate

  sum_R |F(u_R)|^2
    <= H * integral_I |F(u)|^2
       + 2 * sqrt(integral_I |F(u)|^2)
             * sqrt(integral_I |F'(u)|^2).

This uses the exact nonuniform log-grid spacing 1/H <= h_R <= 2/H.
If F is globally T-bandlimited, global Plancherel and Cauchy imply

  sum_R |F(u_R)|^2 <= (H + 4*pi*T)*||F||_L2(R)^2.

The high-frequency price RELATIVE to H*||F||^2 is now (T/H),
NOT (T/H)^2. This is the elementary Plancherel--Polya/Bessel
sampling bound. Its proof at the integral level is given explicitly
in the accompanying audit, not claimed as a Lean theorem here.

The following Lean results prove the revised exact EXPONENT BUDGET;
the OAI source family and bandlimited derivative hypotheses remain open.
-/

/-- Grid cost for the sharper Plancherel--Polya / first-derivative trace. -/
def oaiLinearTracePower (delta kappa : Real) : Real :=
  oaiMellinPower delta kappa - 1

theorem oaiLinearTracePower_eq (delta kappa : Real) :
    oaiLinearTracePower delta kappa =
      1 / 4 + delta / 2 + kappa := by
  unfold oaiLinearTracePower oaiMellinPower oaiCollarPower
  ring

/-- When the smoothed source estimate is normalized by H, the
first-derivative trace incurs linear frequency inflation. With a
hypothetical relative profile penalty (T/H)^beta the exact budget
is delta0>=1/4+3*delta/2+kappa+beta*(1/4+delta/2+kappa). -/
theorem oaiLinearGridRelativeBudget_iff
    (delta delta0 kappa beta : Real) :
    (5 / 2 - delta0 + oaiLinearTracePower delta kappa +
        oaiRelativeProfilePower delta kappa beta ≤ 5 / 2 - delta) ↔
    (1 / 4 + 3 * delta / 2 + kappa +
        beta * (1 / 4 + delta / 2 + kappa) ≤ delta0) := by
  rw [oaiLinearTracePower_eq, oaiRelativeProfilePower_eq]
  constructor <;> intro h <;> linarith

/-- With the pinned polynomial ABSOLUTE height factor T^J the
corresponding bound is more expensive. No identification of profile
Mellin variable with OAI row-height is assumed. -/
theorem oaiLinearGridAbsoluteBudget_iff
    (delta delta0 kappa J : Real) :
    (5 / 2 - delta0 + oaiLinearTracePower delta kappa +
        oaiAbsoluteHeightPower delta kappa J ≤ 5 / 2 - delta) ↔
    (1 / 4 + 3 * delta / 2 + kappa +
        J * (5 / 4 + delta / 2 + kappa) ≤ delta0) := by
  rw [oaiLinearTracePower_eq, oaiAbsoluteHeightPower_eq]
  constructor <;> intro h <;> linarith

/-!
## NNS sampling/partial moments as a LOSSLESS measure bridge

For the original deterministic samples x(R), NNS degree-zero LPM
recovers the empirical CDF, and higher LPMs give continuous functions
of the TARGET. The original second moment is exactly the unnormalized
sum of degree-two LPM and UPM at target zero. This is an exact
discrete-to-continuous *distributional* representation; it is NOT an
OAI smooth-root-source moment inequality, since target and physical
square-root scale are different variables. No simulated Mobius signs.
-/

def oaiNNSLowerSecond (s : Finset ℕ) (x : ℕ → Real)
    (target : Real) : Real :=
  ∑ R ∈ s, (max (target - x R) 0) ^ 2

def oaiNNSUpperSecond (s : Finset ℕ) (x : ℕ → Real)
    (target : Real) : Real :=
  ∑ R ∈ s, (max (x R - target) 0) ^ 2

/-- All deterministic signed data, with no sampling approximation or
loss, satisfy the exact NNS LPM2+UPM2 energy identity. -/
theorem oaiNNSTwoSidedSecond_eq_energy
    (s : Finset ℕ) (x : ℕ → Real) (target : Real) :
    oaiNNSLowerSecond s x target +
      oaiNNSUpperSecond s x target =
        ∑ R ∈ s, (x R - target) ^ 2 := by
  unfold oaiNNSLowerSecond oaiNNSUpperSecond
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R _hR
  by_cases h : x R ≤ target
  · have hlt : 0 ≤ target - x R := sub_nonneg.mpr h
    have hut : x R - target ≤ 0 := sub_nonpos.mpr h
    rw [max_eq_left hlt, max_eq_right hut]
    ring
  · have hgt : target ≤ x R := (le_of_lt (lt_of_not_ge h))
    have hlt : target - x R ≤ 0 := sub_nonpos.mpr hgt
    have hut : 0 ≤ x R - target := sub_nonneg.mpr hgt
    rw [max_eq_right hlt, max_eq_left hut]
    ring

/-- The NNS degree-two target-zero moment is EXACTLY the native
dyadic second moment for ANY deterministic shell coefficient sequence. -/
theorem oaiNNSDyadicTwoSided_eq_energy (H : ℕ) (x : ℕ → Real) :
    oaiNNSLowerSecond (Finset.Ico H (2 * H)) x 0 +
      oaiNNSUpperSecond (Finset.Ico H (2 * H)) x 0 =
        ∑ R ∈ Finset.Ico H (2 * H), (x R) ^ 2 := by
  simpa only [sub_zero] using
    oaiNNSTwoSidedSecond_eq_energy (Finset.Ico H (2 * H)) x 0

#print axioms oaiCollarRoundingPower
#print axioms oaiMellinPower_eq
#print axioms oaiGridTracePower_eq
#print axioms oaiLinearTracePower_eq
#print axioms oaiLinearGridRelativeBudget_iff
#print axioms oaiLinearGridAbsoluteBudget_iff
#print axioms oaiNNSTwoSidedSecond_eq_energy
#print axioms oaiNNSDyadicTwoSided_eq_energy
#print axioms oaiRelativeProfilePower_eq
#print axioms oaiAbsoluteHeightPower_eq
#print axioms oaiGenericRelativeBudget_iff
#print axioms oaiGenericAbsoluteBudget_iff
#print axioms oaiChosenHeightRootPower_lt
#print axioms oaiChosenHeightRootPower_lt_mellin

end RHLean.Analysis
