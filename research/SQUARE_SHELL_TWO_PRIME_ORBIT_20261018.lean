import Mathlib
import RHLean.Arithmetic.SignedBuchstabRecursion
import «research.VF_MID_DYADIC_OWNER_EXACT»

/-!
# Strict square-shell two-prime orbit obstruction

This module reuses the already-compiled square-band divisibility antichain and
adds the exact divisor-factor and Möbius-sign consequences requested by claim
`20261018-wheel-1`.

These are structural no-go statements only. They do not provide a shell-energy
estimate, a covariance exponent gain, or a bridge to the original #915 carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-- If two multiples of the same positive base lie in one strict square shell,
then distinct multiplier factors are incomparable under divisibility. -/
theorem squareShell_activeDivisorFactors_incomparable
    {R m d e : ℕ}
    (hmd : m * d ∈ vfMidSquareBandSites R)
    (hme : m * e ∈ vfMidSquareBandSites R)
    (hde : d ≠ e) :
    ¬ d ∣ e := by
  intro hdiv
  have hprodDvd : m * d ∣ m * e :=
    Nat.mul_dvd_mul_left m hdiv
  have hprodEq : m * d = m * e :=
    (vfMidSquareBandSites_dvd_iff_eq hmd hme).1 hprodDvd
  have hmPos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp [vfMidSquareBandSites] at hmd
  exact hde (Nat.eq_of_mul_eq_mul_left hmPos hprodEq)

/-- Two fresh prime faces over one cofactor have the same genuine Möbius sign.
The shell hypotheses retain the physical carrier; the sign identity itself is
the exact fresh-prime law on each face. -/
theorem squareShell_twoPrimeOrbit_moebius_eq
    {R p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (_hpm : p * m ∈ vfMidSquareBandSites R)
    (_hqm : q * m ∈ vfMidSquareBandSites R)
    (hpc : ¬ p ∣ m) (hqc : ¬ q ∣ m) :
    μ (p * m) = μ (q * m) := by
  rw [moebius_prime_mul hp hpc, moebius_prime_mul hq hqc]

/-- The original signed pair product of a two-prime shell orbit is exactly the
square of the common cofactor sign, so this orbit cannot contribute negative
covariance. -/
theorem squareShell_twoPrimeOrbit_pairProduct_eq_sq
    {R p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hpm : p * m ∈ vfMidSquareBandSites R)
    (hqm : q * m ∈ vfMidSquareBandSites R)
    (hpc : ¬ p ∣ m) (hqc : ¬ q ∣ m) :
    μ (p * m) * μ (q * m) = (μ m) ^ 2 := by
  rw [moebius_prime_mul hp hpc, moebius_prime_mul hq hqc]
  ring

/-- On the genuine squarefree carrier, every two-site two-prime orbit has
strictly positive pair product. -/
theorem squareShell_twoPrimeOrbit_pairProduct_pos
    {R p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hpm : p * m ∈ vfMidSquareBandSites R)
    (hqm : q * m ∈ vfMidSquareBandSites R)
    (hpc : ¬ p ∣ m) (hqc : ¬ q ∣ m)
    (hm : Squarefree m) :
    0 < μ (p * m) * μ (q * m) := by
  rw [squareShell_twoPrimeOrbit_pairProduct_eq_sq
    hp hq hpm hqm hpc hqc]
  have hmu : μ m ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hm
  simpa [pow_two] using (mul_self_pos.mpr hmu)

end RHLean.Analysis

#print axioms RHLean.Analysis.squareShell_activeDivisorFactors_incomparable
#print axioms RHLean.Analysis.squareShell_twoPrimeOrbit_moebius_eq
#print axioms RHLean.Analysis.squareShell_twoPrimeOrbit_pairProduct_eq_sq
#print axioms RHLean.Analysis.squareShell_twoPrimeOrbit_pairProduct_pos
