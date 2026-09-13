import Mathlib
import RHLean.Proof.CanonicalRoughAdaptiveRawAnnihilation

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

Only the abstract finite algebra is formalized here.  No Perron inversion,
prime-number-theorem estimate, norm, or RH-scale hypothesis is used.
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

/-- Pure scalar identity behind the logarithmic interpolation:
`1 - z` is exactly the amount lost between the `z=1` raw endpoint and the
retained-parent coordinate.  This small lemma is useful when the ratio is later
specialized to `p^{-s}`. -/
theorem one_sub_ratio_add_ratio (z : ℂ) :
    (1 - z) + z = 1 := by
  ring

end RHLean.Proof
