import Mathlib

/-!
# Pre-norm directional NNS and phase-correct Euler pairing for marked Hecke rows

Every declaration here is unconditional finite algebra, with NO RH hypothesis,
no random sign/independence axiom, and no PNT-to-Hecke inference.

The complex-to-real map Phi is already proved in
research/STABLE_FAR_PERRON_REALIFICATION.lean. We retain its real pair kernel
and the *separate* upper/lower partial moments of signed ideal pairs.

This module includes the correct POLARIZED fourth moment for j+k<=2:
it never takes the fourth power of the product Pj*Pk*W.
The source coefficients and actual ideals must be admitted independently;
none of these abstract equalities asserts a uniform analytic power saving.
-/

open scoped BigOperators

namespace RHLean.MarkedRealNNS

/-- Viole's Phi dot product is the Hermitian real Gram, expressed in R. -/
theorem phi_real_pair_kernel (a b c d : ℝ) :
    ((a-b)*(c-d)+(a+b)*(c+d))/2 = a*c+b*d := by
  ring

def posPart (x : ℝ) : ℝ := max x 0
def negPart (x : ℝ) : ℝ := max (-x) 0

/-- Degree-one signed unnormalized NNS identity. -/
theorem posPart_sub_negPart (x : ℝ) :
    posPart x - negPart x = x := by
  unfold posPart negPart
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (show -x ≤ 0 by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (show 0 ≤ -x by linarith)]
    ring

/-- The agreement and disagreement mixed quadrants before pooling. -/
def pairAgreement (x y : ℝ) : ℝ :=
  posPart x * posPart y + negPart x * negPart y

def pairDisagreement (x y : ℝ) : ℝ :=
  posPart x * negPart y + negPart x * posPart y

theorem pairAgreement_sub_disagreement (x y : ℝ) :
    pairAgreement x y - pairDisagreement x y = x*y := by
  calc
    _ = (posPart x-negPart x)*(posPart y-negPart y) := by
      unfold pairAgreement pairDisagreement
      ring
    _ = x*y := by
      rw [posPart_sub_negPart, posPart_sub_negPart]

/-- The complete eight real mixed quadrants yield a signed Gram kernel. -/
theorem two_axis_mixed_quadrants (x1 y1 x2 y2 : ℝ) :
    ((pairAgreement x1 x2 - pairDisagreement x1 x2) +
      (pairAgreement y1 y2 - pairDisagreement y1 y2))/2 =
      (x1*x2+y1*y2)/2 := by
  rw [pairAgreement_sub_disagreement, pairAgreement_sub_disagreement]

/-- Fourth power of one polynomial row, after its labelled ideal atoms
have already been added but before any source-independent inequality. -/
theorem nns_fourth_moment_identity (E K P N : ℝ)
    (hE : E = K + 2*P - 2*N) :
    E^2 = K^2 + 4*K*P - 4*K*N + 4*(P-N)^2 := by
  rw [hE]
  ring

/-- The genuinely MIXED fourth moment for the actual OAI cases j+k<=2.
The two polynomial rows are polarized separately; no artificial eighth
power of Pj*Pk is created. -/
theorem nns_polarized_fourth_moment_identity
    (Ej Ek Kj Pj Nj Kk Pk Nk : ℝ)
    (hEj : Ej = Kj + 2*Pj - 2*Nj)
    (hEk : Ek = Kk + 2*Pk - 2*Nk) :
    Ej*Ek =
      Kj*Kk + 2*(Kj*Pk+Kk*Pj) -
      2*(Kj*Nk+Kk*Nj) + 4*(Pj-Nj)*(Pk-Nk) := by
  rw [hEj, hEk]
  ring

/-- The original selected rows and arbitrary unnormalized weights stay
unchanged; the two mixed energy equalities are supplied at their true rows. -/
theorem nns_weighted_polarized_fourth
    {ι : Type*} (rows : Finset ι)
    (w Ej Ek Kj Pj Nj Kk Pk Nk : ι → ℝ)
    (hj : ∀ u ∈ rows, Ej u = Kj u+2*Pj u-2*Nj u)
    (hk : ∀ u ∈ rows, Ek u = Kk u+2*Pk u-2*Nk u) :
    (∑ u ∈ rows, w u*(Ej u*Ek u)) =
      ∑ u ∈ rows, w u*
        (Kj u*Kk u+2*(Kj u*Pk u+Kk u*Pj u) -
        2*(Kj u*Nk u+Kk u*Nj u) +
        4*(Pj u-Nj u)*(Pk u-Nk u)) := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [nns_polarized_fourth_moment_identity
    (Ej u) (Ek u) (Kj u) (Pj u) (Nj u) (Kk u) (Pk u) (Nk u)
    (hj u hu) (hk u hu)]

/-- The exact rearrangement of the KNOWN moment bound. This supplies the
already certified negative payment but never improves the exponent itself. -/
theorem negative_payment_of_known_bound
    (M4 S A B Q budget : ℝ)
    (hM4 : M4 = S + 4*A - 4*B + 4*Q)
    (hBound : M4 ≤ budget) :
    B ≥ A+S/4+Q-budget/4 := by
  linarith

/-- Good-row gain conditional on a NEW weighted directional estimate. -/
theorem good_row_energy_le
    (E K P N c : ℝ)
    (hE : E = K+2*P-2*N)
    (hGood : N-P ≥ (1-c)*K/2) :
    E ≤ c*K := by
  linarith

/-- CORRECT Euler phase pairing. Ignoring the character value at the
toggled ideal prime silently drops the second, potentially large term. -/
theorem phase_correct_euler_pair (a0 a1 phase : ℂ) :
    a0-phase*a1=(a0-a1)+(1-phase)*a1 := by
  ring

/-- The same compensation holds over the exact, possibly unequally weighted
original finite ideal-pair source, not a hypothetical uniform population. -/
theorem phase_correct_euler_pair_sum
    {ι : Type*} (s : Finset ι)
    (sign a0 a1 : ι → ℂ) (phase : ℂ) :
    (∑ v ∈ s, sign v*(a0 v-phase*a1 v)) =
      ∑ v ∈ s, sign v*
        ((a0 v-a1 v)+(1-phase)*a1 v) := by
  apply Finset.sum_congr rfl
  intro v _
  rw [phase_correct_euler_pair]

/-- Exact discrete logarithmic Leibniz remainder for the j=1 profile:
the toggled prime contributes its OWN logarithm, even with smooth weights. -/
theorem phase_correct_log_one (a0 a1 phase x ell : ℂ) :
    a0*x - phase*a1*(x+ell) =
      (a0-phase*a1)*x-phase*a1*ell := by
  ring

/-- j=2 derivative-profile remainder, retaining all phase-weighted terms.
The error is first degree in log N(T), not zero. -/
theorem phase_correct_log_two (a0 a1 phase x ell : ℂ) :
    a0*x^2-phase*a1*(x+ell)^2 =
      (a0-phase*a1)*x^2-phase*a1*(2*x*ell+ell^2) := by
  ring

/-- Ordinary parity pairing is NOT phase cancellation: with matching
arithmetic weights, a character phase -1 doubles the residual. -/
theorem equal_weights_phase_minus_one_residual :
    (1:ℂ)-(-1:ℂ)*1=2 := by
  ring

/-- On a restricted character family the nonresonant fourth-moment term may
CANCEL the positive resonant contribution. For coefficients 1,-1 at ideals
1,p and the trivial character, the whole fourth moment is zero while
the norm of the multiplicative convolution a*a is 1+4+1=6. -/
theorem restricted_character_resonance_not_floor :
    ((1:ℂ)+(-1:ℂ)) = 0 ∧
      (0:ℝ)<(1:ℝ)^2+(-2:ℝ)^2+(1:ℝ)^2 := by
  norm_num

end RHLean.MarkedRealNNS

#print axioms RHLean.MarkedRealNNS.phi_real_pair_kernel
#print axioms RHLean.MarkedRealNNS.two_axis_mixed_quadrants
#print axioms RHLean.MarkedRealNNS.nns_polarized_fourth_moment_identity
#print axioms RHLean.MarkedRealNNS.nns_weighted_polarized_fourth
#print axioms RHLean.MarkedRealNNS.phase_correct_log_two
