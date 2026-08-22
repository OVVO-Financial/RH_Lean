import Mathlib
import RHLean.Proof.LowWheelSurvivorFloorExpansion

/-!
# Triple carrier for prime-count-free square-root transport

After the low-wheel survivor and Boolean-cube expansions, the upper-prime
transport contains no irreducible prime-count coefficient.  Each floor
difference is the cardinality of a finite quotient interval, so the entire
transport becomes a signed sum on triples

`(c, t, k)`

with

* `1 <= c < R`,
* `t` a Boolean face of the low primes through `R`,
* `R < primeFaceProduct t * k`,
* `c * primeFaceProduct t * k <= R^2 - 1`.

The signed weight is simply `mu(c) * (-1)^|t|`.  Thus all arithmetic signs are
low-wheel signs; the high region survives only as the two hyperbolic cutoff
inequalities.

No norm or analytic estimate appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Nested finite triple carrier.  Keeping the quotient interval explicit makes
both cutoff faces visible to the later sign-reversing move. -/
def lowWheelTransportTripleLedger (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    ∑ t ∈ (primesUpTo R).powerset,
      ∑ k ∈ Finset.Ioc
          (R / primeFaceProduct t)
          (squareRootEndpoint R / (c * primeFaceProduct t)),
        canonicalMoebiusWeight c * (booleanCubeSign t : ℂ)

/-- Membership in the quotient interval is exactly the physical high-boundary
and square-endpoint pair of inequalities. -/
theorem mem_lowWheelTransport_quotientInterval_iff
    {R c k : ℕ} {t : Finset ℕ}
    (hc : 0 < c) (ht : t ∈ (primesUpTo R).powerset) :
    k ∈ Finset.Ioc
        (R / primeFaceProduct t)
        (squareRootEndpoint R / (c * primeFaceProduct t)) ↔
      R < primeFaceProduct t * k ∧
        (c * primeFaceProduct t) * k ≤ squareRootEndpoint R := by
  have hdpos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset ht
  have hcdpos : 0 < c * primeFaceProduct t := Nat.mul_pos hc hdpos
  constructor
  · intro hk
    rcases Finset.mem_Ioc.mp hk with ⟨hlow, hupp⟩
    constructor
    · exact (Nat.div_lt_iff_lt_mul hdpos).1 hlow
    · exact (Nat.le_div_iff_mul_le hcdpos).1 hupp
  · rintro ⟨hlow, hupp⟩
    apply Finset.mem_Ioc.mpr
    exact ⟨(Nat.div_lt_iff_lt_mul hdpos).2 hlow,
      (Nat.le_div_iff_mul_le hcdpos).2 hupp⟩

/-- A constant signed weight summed over one quotient interval is exactly the
corresponding floor-difference term from the Boolean-cube expansion. -/
theorem lowWheelTransport_floorTerm_eq_quotientSum
    (R c : ℕ) {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    canonicalMoebiusWeight c * (booleanCubeSign t : ℂ) *
        ((squareRootEndpoint R / (c * primeFaceProduct t) -
            R / primeFaceProduct t : ℕ) : ℂ) =
      ∑ k ∈ Finset.Ioc
          (R / primeFaceProduct t)
          (squareRootEndpoint R / (c * primeFaceProduct t)),
        canonicalMoebiusWeight c * (booleanCubeSign t : ℂ) := by
  have hcard :
      (Finset.Ioc
        (R / primeFaceProduct t)
        (squareRootEndpoint R / (c * primeFaceProduct t))).card =
        squareRootEndpoint R / (c * primeFaceProduct t) -
          R / primeFaceProduct t := by simp
  rw [Finset.sum_const, nsmul_eq_mul, hcard]
  push_cast
  ring

/-- **Triple-carrier realization.**  The entire cofactor-first high transport is
exactly the finite signed triple ledger.  There is no prime-count function left
and no absolute value has been introduced. -/
theorem squareRootTransportCofactorFirst_eq_lowWheelTransportTripleLedger
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportCofactorFirst R =
      lowWheelTransportTripleLedger R := by
  rw [squareRootTransportCofactorFirst_eq_lowWheelFaceFloorSum R hR]
  unfold lowWheelTransportTripleLedger
  apply Finset.sum_congr rfl
  intro c _hc
  apply Finset.sum_congr rfl
  intro t ht
  exact lowWheelTransport_floorTerm_eq_quotientSum R c ht

end RHLean.Proof
