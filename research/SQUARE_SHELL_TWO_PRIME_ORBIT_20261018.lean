import Mathlib
import RHLean.Arithmetic.SignedBuchstabRecursion

/-!
# Strict square-shell two-prime orbit obstruction

This module formalizes the genuine Möbius-sign consequence of the independently
accepted claim `20261018-wheel-1`. The shell divisibility antichain itself is
already compiled on `main` as
`RHLean.Analysis.vfMidSquareBandSites_dvd_iff_eq`, so it is not duplicated here.

These are structural no-go statements only. They do not provide a shell-energy
estimate, a covariance exponent gain, or a bridge to the original #915 carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Two fresh prime faces over one cofactor have the same genuine Möbius sign.
The inequalities retain the strict physical square-shell carrier; the sign
identity itself is the exact fresh-prime law on each face. -/
theorem squareShell_twoPrimeOrbit_moebius_eq
    {R p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (_hpmL : R ^ 2 < p * m) (_hpmU : p * m < (R + 1) ^ 2)
    (_hqmL : R ^ 2 < q * m) (_hqmU : q * m < (R + 1) ^ 2)
    (hpc : ¬ p ∣ m) (hqc : ¬ q ∣ m) :
    μ (p * m) = μ (q * m) := by
  rw [moebius_prime_mul hp hpc, moebius_prime_mul hq hqc]

/-- The original signed pair product of a two-prime shell orbit is exactly the
square of the common cofactor sign, so this orbit cannot contribute negative
covariance. -/
theorem squareShell_twoPrimeOrbit_pairProduct_eq_sq
    {R p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (_hpmL : R ^ 2 < p * m) (_hpmU : p * m < (R + 1) ^ 2)
    (_hqmL : R ^ 2 < q * m) (_hqmU : q * m < (R + 1) ^ 2)
    (hpc : ¬ p ∣ m) (hqc : ¬ q ∣ m) :
    μ (p * m) * μ (q * m) = (μ m) ^ 2 := by
  rw [moebius_prime_mul hp hpc, moebius_prime_mul hq hqc]
  ring

/-- On the genuine squarefree carrier, every two-site two-prime orbit has
strictly positive pair product. -/
theorem squareShell_twoPrimeOrbit_pairProduct_pos
    {R p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hpmL : R ^ 2 < p * m) (hpmU : p * m < (R + 1) ^ 2)
    (hqmL : R ^ 2 < q * m) (hqmU : q * m < (R + 1) ^ 2)
    (hpc : ¬ p ∣ m) (hqc : ¬ q ∣ m)
    (hm : Squarefree m) :
    0 < μ (p * m) * μ (q * m) := by
  rw [squareShell_twoPrimeOrbit_pairProduct_eq_sq
    hp hq hpmL hpmU hqmL hqmU hpc hqc]
  have hmu : μ m ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hm
  simpa [pow_two] using! (mul_self_pos.mpr hmu)

end RHLean.Analysis

#print axioms RHLean.Analysis.squareShell_twoPrimeOrbit_moebius_eq
#print axioms RHLean.Analysis.squareShell_twoPrimeOrbit_pairProduct_eq_sq
#print axioms RHLean.Analysis.squareShell_twoPrimeOrbit_pairProduct_pos
