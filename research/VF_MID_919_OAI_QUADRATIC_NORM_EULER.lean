import Mathlib

/-!
# #919: exact split/inert/ramified norm-Euler coefficient dictionary

For F = Q(sqrt(-3)), the rational prime p splits when p = 1 mod 3,
is inert when p = 2 mod 3, and is ramified at 3. The formal local
Euler factor of 1/zeta_F(s), grouped by rational norm, is

  split:    (1-t)^2
  inert:    1-t^2
  ramified: 1-t,

where t=p^(-s). This module kernel-checks the exact algebraic local
comparison with the quadratic character chi_{-3}(p):

  NormMobiusEuler_p(t) = (1-t) * (1-chi_{-3}(p)*t).

Consequently the rational Mobius Euler polynomial is the ideal-norm
Mobius Euler polynomial times the quadratic L Euler factor; globally
the standard analytic identity is zeta_F=zeta*L(chi_{-3}).

The prime-splitting classification, ideal-norm interpretation, and
analytic Euler-product passage are NOT proved by this Mathlib-only
polynomial file. These are explicit obligations for the full
coefficient-level Hecke-to-VF transport.
-/

namespace RHLean.Analysis

/-- On prime arguments: the real quadratic character of conductor 3. -/
def vf919QuadraticMinusThreePrimeValue (p : ℕ) : ℝ :=
  if p % 3 = 0 then 0 else if p % 3 = 1 then 1 else -1

/-- Formal norm-grouped inverse Dedekind-zeta Euler polynomial. -/
def vf919EisensteinNormMobiusEulerFactor (p : ℕ) (t : ℝ) : ℝ :=
  if p % 3 = 0 then 1 - t
  else if p % 3 = 1 then (1 - t) ^ 2
  else 1 - t ^ 2

/-- A genuinely coefficient-level local equality, not a C-to-R
change of basis. The quadratic Euler correction is retained. -/
theorem vf919EisensteinNormMobiusEuler_eq_rational_mul_quadratic
    (p : ℕ) (t : ℝ) :
    vf919EisensteinNormMobiusEulerFactor p t =
      (1 - t) * (1 - vf919QuadraticMinusThreePrimeValue p * t) := by
  unfold vf919EisensteinNormMobiusEulerFactor
    vf919QuadraticMinusThreePrimeValue
  split_ifs <;> ring

/-- At an inert prime (e.g. 2), no norm-p ideal contributes a
linear Mobius coefficient; the quadratic Dirichlet correction does. -/
theorem vf919EisensteinNormMobiusEuler_two (t : ℝ) :
    vf919EisensteinNormMobiusEulerFactor 2 t = 1 - t ^ 2 := by
  norm_num [vf919EisensteinNormMobiusEulerFactor]

/-- At the ramified prime 3 the Euler factor has a linear term. -/
theorem vf919EisensteinNormMobiusEuler_three (t : ℝ) :
    vf919EisensteinNormMobiusEulerFactor 3 t = 1 - t := by
  norm_num [vf919EisensteinNormMobiusEulerFactor]

/-- At a split rational prime 7 there are two norm-seven ideal factors. -/
theorem vf919EisensteinNormMobiusEuler_seven (t : ℝ) :
    vf919EisensteinNormMobiusEulerFactor 7 t = (1 - t) ^ 2 := by
  norm_num [vf919EisensteinNormMobiusEulerFactor]

/-- The local polynomial dictionary reassembles across an arbitrary
FINITE set of distinct rational prime labels, with multiplicity of
split ideal factors preserved in the norm Euler polynomial. -/
theorem vf919FiniteNormMobiusEulerProduct_eq_rational_times_quadratic
    (ps : Finset ℕ) (t : ℕ → ℝ) :
    (∏ p ∈ ps, vf919EisensteinNormMobiusEulerFactor p (t p)) =
      (∏ p ∈ ps, (1 - t p)) *
      (∏ p ∈ ps, (1 - vf919QuadraticMinusThreePrimeValue p * t p)) := by
  simp_rw [vf919EisensteinNormMobiusEuler_eq_rational_mul_quadratic]
  rw [Finset.prod_mul_distrib]

end RHLean.Analysis
