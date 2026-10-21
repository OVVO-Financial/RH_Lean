import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»
import «research.VF_919_OAI_EXACT_MARKED_RESCALED_LOCAL_20261019»

/-!
# Exact integer-Moebius site-to-norm/character convolution for both OAI legs

The repository already proved, with actual ArithmeticFunction coefficients,
    vf919QuadraticCharacter * vf919EisensteinNormCoefficients
      = vf919RationalMobius.
We APPLY that theorem at every physical integer, BEFORE summing, without
assuming that a constructed norm coefficient equals a particular
Eisenstein ideal's mu_F. We do not collapse distinct equal-norm ideal
sextic phases into a rational scalar.

Every original sharp mark and rescale value is retained independently
at every n. This gives the exact full-mixed covariance in the integer
carrier, without pretending it is an already established analytic
identification of the cubic-theta OAI probe with an integer Mobius row.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- True integer mu_Z equals the explicit (chi_-3 * a_F) coefficient at
    EACH n, paired with the distinct marked and rescaled observables. -/
theorem vf919OAI_actualMobius_Hecke_two_legs_at_site
    (n : ℕ) (marked rescaled : ℕ → ℂ) :
    vf919RationalMobius n * (marked n - rescaled n) =
      ∑ t ∈ Nat.divisorsAntidiagonal n,
        (vf919ChiMinusThree t.1 *
          vf919EisensteinNormCoefficients t.2) *
          (marked n - rescaled n) := by
  calc
    vf919RationalMobius n * (marked n - rescaled n) =
      (vf919QuadraticCharacter * vf919EisensteinNormCoefficients) n *
        (marked n - rescaled n) := by
          rw [vf919QuadraticCharacter_mul_norm_eq_mobius]
    _ = (∑ t ∈ Nat.divisorsAntidiagonal n,
          vf919QuadraticCharacter t.1 *
            vf919EisensteinNormCoefficients t.2) *
            (marked n - rescaled n) := by
          rw [ArithmeticFunction.mul_apply]
    _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          rw [vf919QuadraticCharacter_apply]

/-- Finite all-original-site transport: the full signed two-leg source is
    the exact arithmetic norm/character sum, with no dropped terms. -/
theorem vf919OAI_actualMobius_Hecke_two_legs_all_sites
    (ns : Finset ℕ) (marked rescaled : ℕ → ℂ) :
    (∑ n ∈ ns,
      vf919RationalMobius n * (marked n - rescaled n)) =
      ∑ n ∈ ns, ∑ t ∈ Nat.divisorsAntidiagonal n,
        (vf919ChiMinusThree t.1 *
          vf919EisensteinNormCoefficients t.2) *
          (marked n - rescaled n) := by
  apply Finset.sum_congr rfl
  intro n _
  exact vf919OAI_actualMobius_Hecke_two_legs_at_site n marked rescaled

/-- Marked and rescaled are two distinct original physical amplitudes.
    This identity retains the complex signed covariance cross-bill.
    It is the exact NNS zero-target Gram BEFORE any analytic bound. -/
theorem vf919OAI_actualMobius_full_mixed_mark_rescale_gram
    (ns : Finset ℕ) (marked rescaled : ℕ → ℂ) :
    ‖∑ n ∈ ns, vf919RationalMobius n *
        (marked n - rescaled n)‖ ^ 2 =
      ‖∑ n ∈ ns, vf919RationalMobius n * marked n‖ ^ 2 +
      ‖∑ n ∈ ns, vf919RationalMobius n * rescaled n‖ ^ 2 -
      2 * ((∑ n ∈ ns, vf919RationalMobius n * marked n) *
        star (∑ n ∈ ns, vf919RationalMobius n * rescaled n)).re := by
  have hsource :
      (∑ n ∈ ns, vf919RationalMobius n *
        (marked n - rescaled n)) =
      (∑ n ∈ ns, vf919RationalMobius n * marked n) -
        (∑ n ∈ ns, vf919RationalMobius n * rescaled n) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsource]
  simpa [Complex.sq_norm] using
    Complex.normSq_sub
      (∑ n ∈ ns, vf919RationalMobius n * marked n)
      (∑ n ∈ ns, vf919RationalMobius n * rescaled n)

#print axioms vf919OAI_actualMobius_Hecke_two_legs_at_site
#print axioms vf919OAI_actualMobius_Hecke_two_legs_all_sites
#print axioms vf919OAI_actualMobius_full_mixed_mark_rescale_gram

end RHLean.Analysis
