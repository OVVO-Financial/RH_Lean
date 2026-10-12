import Mathlib
import RHLean.Geometry.ComplexSquareRecovery

/-!
# Correct complex -> real physical projection of an OAI-style character twist

The existing native Fermat point is
  Psi(c,q) = (c+q)/2 + I*(q-c)/2.
It has EXACT real squared projection c*q and imaginary
squared coordinate (q^2-c^2)/2.

A complex multiplier m=a+b*I acting BEFORE the physical
squared projection does NOT generally preserve c*q.
Its projected real output has BOTH a product channel AND
an imbalance channel:
  Re((m*Psi(c,q))^2)
    = (a^2-b^2)*c*q - (2*a*b)*(q^2-c^2)/2.

For a unit sextic phase, a^2-b^2 and 2ab are
the real/imaginary parts of m^2, so this is a
CUBIC-phase projection. In particular m and -m have
identical squared projections, so the scalar
complex -> real map would LOSE sextic sign information
if applied before the complex character rows were
reassembled. The existing INVERTIBLE two-real-coordinate
map in STABLE_FAR_PERRON_REALIFICATION.lean preserves that
information; this module only formalizes the *terminal*
squared-Fermat projection.

None of these exact finite identities proves an
extra character-moment saving or a stronger zero-free region.
-/

noncomputable section

namespace RHLean.Geometry

/-- Physical product-channel projection after a complex character twist. -/
def vf919TwistedFermatProduct (c q : ℝ) (m : ℂ) : ℝ :=
  ((m * fermatPoint c q) ^ 2).re

/-- The full character twist mixes physical cofactor product and
factor imbalance. This is the exact product/gap spectral bridge;
taking only the product channel before the twist is NOT valid. -/
theorem vf919TwistedFermatProduct_eq_product_sub_gap
    (c q a b : ℝ) :
    vf919TwistedFermatProduct c q ⟨a, b⟩ =
      (a ^ 2 - b ^ 2) * (c * q) -
        (2 * a * b) * ((q ^ 2 - c ^ 2) / 2) := by
  simp [vf919TwistedFermatProduct, fermatPoint, fermatA, fermatB,
    pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- The untwisted physical projection returns the exact genuine
cofactor times its distinguished prime. -/
theorem vf919TwistedFermatProduct_one (c q : ℝ) :
    vf919TwistedFermatProduct c q 1 = c * q := by
  unfold vf919TwistedFermatProduct
  simpa using fermatPoint_sq_re c q

/-- The squared-Fermat scalar projection IDENTIFIES opposite
complex phases: m and -m have the same physical real value.
Therefore a proof carrying genuine sextic characters MUST keep
the invertible two-real-coordinate map until AFTER its analytic
character moments are formed. -/
theorem vf919TwistedFermatProduct_neg_phase
    (c q : ℝ) (m : ℂ) :
    vf919TwistedFermatProduct c q (-m) =
      vf919TwistedFermatProduct c q m := by
  unfold vf919TwistedFermatProduct
  have h :
      (-m) * fermatPoint c q = -(m * fermatPoint c q) := by ring
  rw [h, neg_sq]

/-- The Hermitian analytic energy is NOT the physical signed
real-squared channel alone. The missing nonnegative payment
is exactly the square of the real-pair anti-diagonal, divided
by two. This identity prevents using a scalar product
projection as an upper bound on a complex large-sieve moment. -/
theorem vf919ComplexNorm_sq_eq_signedProjection_add_antiDiagonal
    (z : ℂ) :
    ‖z‖ ^ 2 = (z ^ 2).re +
      ((z.re - z.im) - (z.re + z.im)) ^ 2 / 2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two, Complex.mul_re]
  ring

/-- For a genuine physical (cofactor, prime) pair, the exact
gap between the Hermitian energy and the C->R product
projection is (q-c)^2/2. This gap can be LARGE in the
high-prime/low-cofactor sector; it cannot be discarded. -/
theorem vf919FermatNorm_sq_eq_product_add_gap
    (c q : ℝ) :
    ‖fermatPoint c q‖ ^ 2 =
      c * q + (q - c) ^ 2 / 2 := by
  rw [Complex.sq_norm]
  simp [fermatPoint, fermatA, fermatB, Complex.normSq_apply]
  ring

end RHLean.Geometry
