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


/-!
## Fourth partial moments: conditional half-trace budget, not a free saving

NNS LPM4+UPM4 exactly equals the original fourth signed moment.
Cauchy for a finite set gives (sum x²)^2<=card*sum x⁴.
For a globally T-bandlimited smooth function, first-derivative trace
applied to |F|⁴ and the L4 Bernstein inequality yield
sum_grid|F|⁴ <= (H+C*T)*integral_R|F|⁴.
Thus the GRID factor (T/H)^(1/2) enters the second moment after
Cauchy. This gains only IF a sufficiently strong *root-source fourth
moment* is independently available. In a bounded-width spike model,
the continuous L4 baseline itself grows by sqrt(T/H) against L2,
exactly canceling the apparent trace gain.

The original OAI marked fourth-moment theorem controls a Hecke-row
marked product, NOT by definition this root-indexed |F|^4 moment.
No source identity or uniform fourth-moment estimate is assumed here.
-/

def oaiNNSLowerFourth (s : Finset ℕ) (x : ℕ → Real)
    (target : Real) : Real :=
  ∑ R ∈ s, (max (target - x R) 0) ^ 4

def oaiNNSUpperFourth (s : Finset ℕ) (x : ℕ → Real)
    (target : Real) : Real :=
  ∑ R ∈ s, (max (x R - target) 0) ^ 4

theorem oaiNNSTwoSidedFourth_eq_energy
    (s : Finset ℕ) (x : ℕ → Real) (target : Real) :
    oaiNNSLowerFourth s x target +
      oaiNNSUpperFourth s x target =
        ∑ R ∈ s, (x R - target) ^ 4 := by
  unfold oaiNNSLowerFourth oaiNNSUpperFourth
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R _hR
  by_cases h : x R ≤ target
  · have hlt : 0 ≤ target - x R := sub_nonneg.mpr h
    have hut : x R - target ≤ 0 := sub_nonpos.mpr h
    rw [max_eq_left hlt, max_eq_right hut]
    ring
  · have hgt : target ≤ x R := le_of_lt (lt_of_not_ge h)
    have hlt : target - x R ≤ 0 := sub_nonpos.mpr hgt
    have hut : 0 ≤ x R - target := sub_nonneg.mpr hgt
    rw [max_eq_right hlt, max_eq_left hut]
    ring

theorem oaiNNSEnergy2_sq_le_card_energy4
    (s : Finset ℕ) (x : ℕ → Real) :
    (∑ R ∈ s, (x R) ^ 2) ^ 2 ≤
      (s.card : Real) * ∑ R ∈ s, (x R) ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (R := Real) s (fun _ => (1 : Real)) (fun R => (x R) ^ 2)
  have hsquare (R : ℕ) : ((x R) ^ 2) ^ 2 = (x R) ^ 4 := by ring
  simp_rw [hsquare] at h
  simpa using h

theorem oaiNNSDyadicEnergy2_sq_le_H_energy4
    (H : ℕ) (x : ℕ → Real) :
    (∑ R ∈ Finset.Ico H (2 * H), (x R) ^ 2) ^ 2 ≤
      (H : Real) * ∑ R ∈ Finset.Ico H (2 * H), (x R) ^ 4 := by
  have hcard : (Finset.Ico H (2 * H)).card = H := by
    simp [Nat.card_Ico]
    omega
  simpa [hcard] using
    oaiNNSEnergy2_sq_le_card_energy4 (Finset.Ico H (2 * H)) x

def oaiFourthGridTracePower (delta kappa : Real) : Real :=
  (oaiMellinPower delta kappa - 1) / 2

theorem oaiFourthGridTracePower_eq (delta kappa : Real) :
    oaiFourthGridTracePower delta kappa =
      1 / 8 + delta / 4 + kappa / 2 := by
  unfold oaiFourthGridTracePower oaiMellinPower oaiCollarPower
  ring

/-- Here delta0 is the HALF saving of an independently proven
FOURTH-MOMENT scale H^(4-2*delta0), and beta4 is the profile
penalty exponent in that FOURTH moment BEFORE taking its square root.
Neither is supplied by the existing pinned OAI marked-moment theorem. -/
theorem oaiFourthGridRelativeBudget_iff
    (delta delta0 kappa beta4 : Real) :
    (5 / 2 - delta0 + oaiFourthGridTracePower delta kappa +
        beta4 / 2 * (oaiMellinPower delta kappa - 1) ≤
          5 / 2 - delta) ↔
      (1 / 8 + 5 * delta / 4 + kappa / 2 +
          beta4 / 2 * (1 / 4 + delta / 2 + kappa) ≤ delta0) := by
  rw [oaiFourthGridTracePower_eq, oaiMellinPower_eq]
  constructor <;> intro h <;> linarith

/-- A spiky root-source fourth-moment baseline may already cost
the missing half grid power, eliminating the apparent advantage. -/
theorem oaiFourthGridTwice_eq_LinearTrace (delta kappa : Real) :
    2 * oaiFourthGridTracePower delta kappa =
      oaiLinearTracePower delta kappa := by
  unfold oaiFourthGridTracePower oaiLinearTracePower
  ring

/-!
## Fourier jumps at exact squares: no error for original Möbius

The periodic fractional root factor
 exp(-2*pi*i*theta*{u}) has jumps at integer u when theta is
not integral. At u=m, its ordinary Fourier series converges to
the midpoint, not to the right-continuous value. For n=m²>=4,
however, actual mu(n)=0. The zero is proved below.
-/

open scoped ArithmeticFunction.Moebius

theorem oaiMobiusOfPerfectSquare_zero
    (m : ℕ) (hm : 2 ≤ m) :
    μ (m ^ 2) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsf
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (by omega : m ≠ 1)
  have hp2 : p ^ 2 ∣ m ^ 2 := by
    obtain ⟨k, hk⟩ := hpd
    exact ⟨k ^ 2, by rw [hk]; ring⟩
  exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp) hp2

/-- There is not even an O(H) square-jump error in the genuine
Mobius-weighted root-phase series, since square terms vanish exactly. -/
theorem oaiMobiusSquareJumpContribution_zero
    (H : ℕ) (hH : 2 ≤ H) (F : ℕ → ℤ) :
    (∑ m ∈ Finset.Ico H (2 * H), (μ (m ^ 2)) * F m) = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  have hm2 : 2 ≤ m := hH.trans (Finset.mem_Ico.mp hm).1
  rw [oaiMobiusOfPerfectSquare_zero m hm2]
  ring

#print axioms oaiCollarRoundingPower
#print axioms oaiMellinPower_eq
#print axioms oaiGridTracePower_eq
#print axioms oaiLinearTracePower_eq
#print axioms oaiLinearGridRelativeBudget_iff
#print axioms oaiLinearGridAbsoluteBudget_iff
#print axioms oaiNNSTwoSidedSecond_eq_energy
#print axioms oaiNNSDyadicTwoSided_eq_energy
#print axioms oaiNNSTwoSidedFourth_eq_energy
#print axioms oaiNNSEnergy2_sq_le_card_energy4
#print axioms oaiNNSDyadicEnergy2_sq_le_H_energy4
#print axioms oaiFourthGridTracePower_eq
#print axioms oaiFourthGridRelativeBudget_iff
#print axioms oaiFourthGridTwice_eq_LinearTrace
#print axioms oaiMobiusOfPerfectSquare_zero
#print axioms oaiMobiusSquareJumpContribution_zero
#print axioms oaiRelativeProfilePower_eq
#print axioms oaiAbsoluteHeightPower_eq
#print axioms oaiGenericRelativeBudget_iff
#print axioms oaiGenericAbsoluteBudget_iff
#print axioms oaiChosenHeightRootPower_lt
#print axioms oaiChosenHeightRootPower_lt_mellin

end RHLean.Analysis
