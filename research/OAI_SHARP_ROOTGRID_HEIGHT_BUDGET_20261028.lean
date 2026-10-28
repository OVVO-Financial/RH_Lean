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

The generic Sobolev trace on u_R=2 log R with actual band-limit T
costs (T/H)^2=H^(1/2+delta+2*kappa). With an additional hypothetical
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

#print axioms oaiCollarRoundingPower
#print axioms oaiMellinPower_eq
#print axioms oaiGridTracePower_eq
#print axioms oaiRelativeProfilePower_eq
#print axioms oaiAbsoluteHeightPower_eq
#print axioms oaiGenericRelativeBudget_iff
#print axioms oaiGenericAbsoluteBudget_iff
#print axioms oaiChosenHeightRootPower_lt
#print axioms oaiChosenHeightRootPower_lt_mellin

end RHLean.Analysis
