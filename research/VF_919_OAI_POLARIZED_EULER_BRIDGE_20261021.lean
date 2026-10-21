import Mathlib

/-!
# OAI actual marked rows: polarized NNS fourth moment and phase-correct Euler toggle

These are all exact, unconditional finite algebraic theorems.  They retain
unnormalized partial moments and all mixed j,k derivative rows.

There is NO assumption of Euler-density power saving, no claim that generic
atom lists are already OpenAI's actual F.rows, and no new L-zero theorem.

Crucial point: when a character is multiplicative, toggling a prime in
an IDEAL-LABELLED term changes the character by theta = chi(p).
The source difference is a(T) - theta * a(T union {p}), not generally
a(T) - a(T union {p}).

Also, the resonant contribution of an incomplete, weighted character family
is NOT an unconditional lower bound for its total fourth moment.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Fred Viole's Phi pair Gram, expressed without complex syntax. -/
def vf919PolarPhiGram (x y r s : ℝ) : ℝ :=
  (x * r + y * s) / 2

/-- When Phi(a+ib)=(a-b,a+b), the dot product is exactly
the Hermitian real part a*c+b*d. All phases survive. -/
theorem vf919PolarPhiGram_of_re_im (a b c d : ℝ) :
    vf919PolarPhiGram (a-b) (a+b) (c-d) (c+d) =
      a*c+b*d := by
  unfold vf919PolarPhiGram
  ring

/-- Signed zero-target decomposition underlying NNS LPM/UPM. -/
theorem vf919Polar_positive_sub_negative (g : ℝ) :
    max g 0 - max (-g) 0 = g := by
  rcases le_total 0 g with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

/-- The two favorable mixed sign quadrants enter with +, the two
unfavorable ones with -. This is NOT the sum of four positive squares. -/
theorem vf919Polar_signed_quadrants (x y : ℝ) :
    (max x 0 * max y 0 + max (-x) 0 * max (-y) 0) -
      (max x 0 * max (-y) 0 + max (-x) 0 * max y 0) =
      x*y := by
  calc
    _ = (max x 0-max (-x) 0)*(max y 0-max (-y) 0) := by ring
    _ = x*y := by
      rw [vf919Polar_positive_sub_negative,
          vf919Polar_positive_sub_negative]

/-- Exact degree-four pure-row identity; P,N denote OFF-DIAGONAL
unnormalized upper/lower partial moments of each ideal pair. -/
theorem vf919Polar_pure_fourth
    (E K P N : ℝ) (hE : E=K+2*P-2*N) :
    E^2=K^2+4*K*P-4*K*N+4*(P-N)^2 := by
  rw [hE]
  ring

/-- Correct degree-four polarization for the REAL actual OAI input
  |W(u)|² |P_j(u)|² |P_k(u)|² (j+k<=2).
We do NOT take the fourth power of P_j*P_k*W. -/
theorem vf919Polar_mixed_fourth
    (Ej Ek Kj Pj Nj Kk Pk Nk : ℝ)
    (hj : Ej=Kj+2*Pj-2*Nj)
    (hk : Ek=Kk+2*Pk-2*Nk) :
    Ej*Ek=Kj*Kk+
      2*(Kj*Pk+Kk*Pj)-
      2*(Kj*Nk+Kk*Nj)+
      4*(Pj-Nj)*(Pk-Nk) := by
  rw [hj, hk]
  ring

/-- All source rows and their exact physical weights survive polarization.
No equal-size or independence condition is imposed. -/
theorem vf919Polar_weighted_mixed_fourth
    {ι : Type*} (rows : Finset ι)
    (weight Ej Ek Kj Pj Nj Kk Pk Nk : ι → ℝ)
    (hj : ∀ u ∈ rows, Ej u=Kj u+2*Pj u-2*Nj u)
    (hk : ∀ u ∈ rows, Ek u=Kk u+2*Pk u-2*Nk u) :
    (∑ u ∈ rows, weight u*(Ej u*Ek u)) =
      ∑ u ∈ rows, weight u*
        (Kj u*Kk u+
          2*(Kj u*Pk u+Kk u*Pj u)-
          2*(Kj u*Nk u+Kk u*Nj u)+
          4*(Pj u-Nj u)*(Pk u-Nk u)) := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [vf919Polar_mixed_fourth (Ej u) (Ek u) (Kj u) (Pj u)
      (Nj u) (Kk u) (Pk u) (Nk u) (hj u hu) (hk u hu)]

/-- Lower bound on signed negative compensation ALREADY entailed by
a known upper bound. It is not an independent new moment estimate. -/
theorem vf919Polar_negative_payment_of_known_bound
    (M4 S A B Q budget : ℝ)
    (hM4 : M4=S+4*A-4*B+4*Q)
    (hb : M4 ≤ budget) :
    B ≥ A+S/4+Q-budget/4 := by
  linarith

/-- A good-row NNS corridor, conditioned on an INDEPENDENT estimate
for its negative pair alignment. -/
theorem vf919Polar_good_row
    (E K P N c : ℝ)
    (hE : E=K+2*P-2*N)
    (hCorridor : N-P ≥ ((1-c)/2)*K) :
    E ≤ c*K := by
  linarith

/-- The exact phase-correct Euler-prime toggle. Multiplicativity says
chi(T union {p})=chi(T)*theta; thus theta is mandatory. -/
theorem vf919Polar_character_toggle
    (chiT theta aT aTp : ℂ) :
    chiT*aT-(chiT*theta)*aTp =
      chiT*(aT-theta*aTp) := by
  ring

/-- The exact first log-derivative product rule under a prime toggle.
L=log N(T), ell=log N(p), theta=chi(p). -/
theorem vf919Polar_character_toggle_log1
    (L ell theta aT aTp : ℂ) :
    L*aT-theta*(L+ell)*aTp =
      L*(aT-theta*aTp)-ell*theta*aTp := by
  ring

/-- The exact SECOND log-derivative product rule, including the ell² term. -/
theorem vf919Polar_character_toggle_log2
    (L ell theta aT aTp : ℂ) :
    L^2*aT-theta*(L+ell)^2*aTp =
      L^2*(aT-theta*aTp)-
      (2*L*ell+ell^2)*theta*aTp := by
  ring

/-- A concrete finite counterexample to any claim that the resonant
fourth-moment term is automatically a LOWER bound for a RESTRICTED
character subfamily. a(1)=1,a(g)=-1 on the group Z/2. With only the
trivial character, the full row vanishes although the resonance is 8.
With both characters orthogonality restores the exact resonant total. -/
theorem vf919Polar_restricted_char_resonance_counterexample :
    ((1:ℝ)+(-1))^4=0 ∧
    ((1:ℝ)^2+(-1)^2)^2+(2*(1:ℝ)*(-1))^2=8 ∧
    ((1:ℝ)+(-1))^4+((1:ℝ)-(-1))^4=2*8 := by
  norm_num

end RHLean.Analysis

#print axioms RHLean.Analysis.vf919Polar_mixed_fourth
#print axioms RHLean.Analysis.vf919Polar_weighted_mixed_fourth
#print axioms RHLean.Analysis.vf919Polar_character_toggle_log2
#print axioms RHLean.Analysis.vf919Polar_restricted_char_resonance_counterexample
