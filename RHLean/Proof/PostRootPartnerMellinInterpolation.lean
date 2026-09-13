import Mathlib
import RHLean.Proof.CanonicalRoughAdaptiveWeightedIteration

/-!
# Mellin interpolation of the raw and reciprocal fresh-prime laws

The zero-factor raw/Othello step and the reciprocal Euler step are not separate
mechanisms.  They are the two endpoint specializations of one exact weighted
fresh-prime identity.

Let

```text
r_R(n) = raw critical correlation atom at n
```

and let `w` be any scalar weight for which adjoining the current fresh prime
multiplies the weight by `z`:

```text
w(c * p) = z * w(c).
```

The exact raw pair law

```text
r_R(c) + r_R(c*p) = Boundary_R(c,p)
```

then gives

```text
w(c) r_R(c) + w(c*p) r_R(c*p)
  = (1-z) w(c) r_R(c) + z w(c) Boundary_R(c,p).
```

For the Mellin weight `w_s(n)=n^{-s}`, one has `z=p^{-s}`.  Hence

```text
u_s(c) + u_s(c*p)
  = (1-p^{-s}) u_s(c) + Boundary_R(c,p)/(c*p)^s.
```

At `s=0` the parent coefficient is zero: this is exactly the raw annihilation.
At `s=1` the parent coefficient is `1-1/p`: this is exactly the reciprocal
Euler law.  Thus the #685 memory factor is the endpoint difference of one
multiplicative interpolation, and differentiation in `s` necessarily produces
the logarithmic prime weight `log p`.

The final theorem below checks the important physical compatibility: on the
actual evolved raw chronology after a complete descending prefix, multiplying
by an arbitrary extra coordinate weight does not recreate the coefficient
mismatch.  The same four-corner argument works for every Mellin parameter.

No Perron inversion, prime-number-theorem estimate, norm, or RH-scale
hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Raw signed physical boundary charge of one fresh-prime pair. -/
def squareRootCanonicalRoughRawPairBoundaryCharge
    (R c p : ℕ) : ℂ :=
  canonicalMoebiusWeight c *
    (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
      ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ))

/-- The native raw pair law, repackaged with a named boundary charge. -/
theorem squareRootCanonicalRoughRawPair_add_eq_boundaryCharge
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughRawCorrelationSummand R c +
        squareRootCanonicalRoughRawCorrelationSummand R (c * p) =
      squareRootCanonicalRoughRawPairBoundaryCharge R c p := by
  simpa [squareRootCanonicalRoughRawPairBoundaryCharge] using
    squareRootCanonicalRoughRawCorrelationSummand_add_mul_freshPrime
      hR hc hp hfresh

/-- **Abstract Mellin/Euler interpolation law.**

Whenever the chosen multiplicative coordinate has local ratio `z` under
`c -> c*p`, the fresh-prime pair splits into a retained parent with coefficient
`1-z` and the same signed physical boundary with coefficient `z`.

Taking `z = p^{-s}` is the Mellin family.  The theorem is stated with an
abstract ratio so the exact algebra does not depend on any particular real or
complex power API. -/
theorem weightedRawPair_eq_one_sub_ratio_parent_add_ratio_boundary
    {R c p : ℕ} (w : ℕ → ℂ) (z : ℂ)
    (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p)
    (hscale : w (c * p) = z * w c) :
    w c * squareRootCanonicalRoughRawCorrelationSummand R c +
        w (c * p) *
          squareRootCanonicalRoughRawCorrelationSummand R (c * p) =
      (1 - z) *
          (w c * squareRootCanonicalRoughRawCorrelationSummand R c) +
        z * w c * squareRootCanonicalRoughRawPairBoundaryCharge R c p := by
  have hpair :=
    squareRootCanonicalRoughRawPair_add_eq_boundaryCharge hR hc hp hfresh
  rw [hscale]
  linear_combination z * w c * hpair

/-- Coefficient-weighted version of the same interpolation.  The final term is
exactly the inherited-coefficient mismatch. -/
theorem coefficientWeightedRawPair_eq_mellin_parent_add_boundary_add_mismatch
    {R c p : ℕ} (a w : ℕ → ℂ) (z : ℂ)
    (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p)
    (hscale : w (c * p) = z * w c) :
    a c * w c * squareRootCanonicalRoughRawCorrelationSummand R c +
        a (c * p) * w (c * p) *
          squareRootCanonicalRoughRawCorrelationSummand R (c * p) =
      (1 - z) *
          (a c * w c * squareRootCanonicalRoughRawCorrelationSummand R c) +
        z * a c * w c * squareRootCanonicalRoughRawPairBoundaryCharge R c p +
        (a (c * p) - a c) * w (c * p) *
          squareRootCanonicalRoughRawCorrelationSummand R (c * p) := by
  have hpair :=
    squareRootCanonicalRoughRawPair_add_eq_boundaryCharge hR hc hp hfresh
  rw [hscale]
  linear_combination z * a c * w c * hpair

/-- The raw/Othello endpoint of the interpolation: unit multiplicative ratio
kills the retained parent completely and leaves the signed boundary charge. -/
theorem weightedRawPair_ratio_one_eq_boundary
    {R c p : ℕ} (w : ℕ → ℂ)
    (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p)
    (hscale : w (c * p) = w c) :
    w c * squareRootCanonicalRoughRawCorrelationSummand R c +
        w (c * p) *
          squareRootCanonicalRoughRawCorrelationSummand R (c * p) =
      w c * squareRootCanonicalRoughRawPairBoundaryCharge R c p := by
  have h :=
    weightedRawPair_eq_one_sub_ratio_parent_add_ratio_boundary
      w (1 : ℂ) hR hc hp hfresh (by simpa using hscale)
  simpa using h

/-- Mellin-weighted form of the evolved coefficient-mismatch ledger. -/
def squareRootCanonicalRoughEvolvedMellinMismatchMass
    (R p : ℕ) (U : Finset ℕ) (a w : ℕ → ℂ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    (a (c * p) - a c) * w (c * p) *
      squareRootCanonicalRoughRawCorrelationSummand R (c * p)

/-- **Actual-carrier Mellin compatibility.**  A complete descending prefix
kills the Mellin-weighted coefficient mismatch for *every* extra coordinate
weight `w`.

If the current child still has a larger prime extension, the existing
four-corner theorem has already zeroed both evolved raw coefficients.  If it
has no such extension, the child raw atom is itself zero.  Multiplying by an
arbitrary `w(c*p)` therefore cannot recreate a mismatch.  This is the key fact
needed to carry the full `p^{-s}` interpolation on the physical chronology,
not merely on a complete canonical cube. -/
theorem squareRootCanonicalRoughEvolvedMellinMismatchMass_eq_zero_of_completeDescendingPrefix
    (R : ℕ) {p : ℕ} (qs : List ℕ) (w : ℕ → ℂ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    squareRootCanonicalRoughEvolvedMellinMismatchMass R p
        (squareRootCanonicalRoughAdaptiveCarrier qs
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient qs
          (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))) w = 0 := by
  unfold squareRootCanonicalRoughEvolvedMellinMismatchMass
  apply Finset.sum_eq_zero
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcV, hcpos, hrough, _hcpV⟩
  by_cases hchild :
      squareRootCanonicalRoughHasPrimeExtensionAbove R p (c * p)
  · rcases hchild with ⟨q, hqPrime, hpq, hupper⟩
    have hcpPos : 0 < c * p := Nat.mul_pos hcpos hp.pos
    have hqProd : q ≤ q * (c * p) := Nat.le_mul_of_pos_right q hcpPos
    have hqUpper : q ≤ squareRootEndpoint R := by
      have hqProd' : q ≤ (c * p) * q := by
        simpa [Nat.mul_comm] using hqProd
      exact hqProd'.trans hupper
    rcases hcomplete.2 q hqPrime hpq hqUpper with
      ⟨pre, post, hsplit, hprePrime, hpreLarger⟩
    have hzero :=
      squareRootCanonicalRoughAdaptiveRawCoefficient_pair_eq_zero_of_larger_extension_split
        pre post hcpos hp hqPrime hrough hpq hupper hprePrime hpreLarger
    rw [← hsplit] at hzero
    rw [hzero.1, hzero.2]
    simp
  · have hraw :=
      squareRootCanonicalRoughRawCorrelationSummand_mul_freshPrime_eq_zero_of_no_extension
        hR hcpos hp hrough hchild
    rw [hraw]
    simp

/-- Pure scalar identity behind the logarithmic interpolation:
`1 - z` is exactly the amount lost between the `z=1` raw endpoint and the
retained-parent coordinate. -/
theorem one_sub_ratio_add_ratio (z : ℂ) :
    (1 - z) + z = 1 := by
  ring

end RHLean.Proof
