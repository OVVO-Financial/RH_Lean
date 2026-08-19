import Mathlib
import RHLean.Analysis.SquareRootTransportRealization
import RHLean.Analysis.SquareRootTransportTopFibreNoGo

/-!
# Square-root middle / inert transport decomposition

This module isolates the exact three-section identity suggested by the
prime-by-prime square-root sieve geometry.

At the complete square endpoint

```text
X_R = R^2 - 1,
```

the already-realized transport is the prime-first Mertens transform

```text
T_R = sum_{R < q <= X_R, q prime} M(floor(X_R / q)).
```

We split it at `X_R / 2`.

* **Middle fibres:** `R < q <= X_R / 2`.  Their reciprocal quotient satisfies
  `2 <= floor(X_R / q) < R`, so every Mertens value is strictly lower-scale.
* **Inert fibres:** `X_R / 2 < q <= X_R`.  Their reciprocal quotient is exactly
  `1`, hence every prime contributes `M(1) = 1`.

Combining this with the kernel-proved square-block identity

```text
M(X_R) = smooth_R - transport_R
```

gives

```text
M(X_R) = smooth_R - middle_R - inert_R.
```

Equivalently, the signed residual between the middle tail and the two already
identified edge sections is exactly `-M(X_R)`.  Thus a bound on that residual is
not an auxiliary estimate: it is precisely the Mertens bound at the square
endpoint.

No analytic estimate, PNT error bound, or independence assumption is introduced
here.  Everything is finite arithmetic on the existing square-block and
prime-wheel transport identities.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The middle prime fibres between the square-root cutoff and the inert top
half.  Every Mertens argument in this sum is strictly below `R`. -/
def squareRootMiddleMertensTail (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc R (squareRootEndpoint R / 2),
    if q.Prime then
      mertensSummatory (squareRootEndpoint R / q)
    else
      0

/-- The inert top-half prime mass.  This is written as an indicator sum so the
transport split is literal; below we identify it with the cardinality of the
existing `squareRootTopFibrePrimes` set. -/
def squareRootInertPrimeMass (R : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R),
    if q.Prime then (1 : ℂ) else 0

/-- The edge contribution that is known once the square-root smooth block and
the inert top-prime block are known. -/
def squareRootKnownEdgeMass (R : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) - squareRootInertPrimeMass R

/-- The exact signed quantity that the middle section must cancel. -/
def squareRootMiddleCancellationResidual (R : ℕ) : ℂ :=
  squareRootMiddleMertensTail R - squareRootKnownEdgeMass R

private theorem mertensSummatory_one : mertensSummatory 1 = 1 := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]

/-- A middle reciprocal quotient is at least two, so the cofactor-one inert atom
has not yet been reached. -/
theorem two_le_squareRootEndpoint_div_of_middle
    {R q : ℕ}
    (hq : q ∈ Finset.Ioc R (squareRootEndpoint R / 2)) :
    2 ≤ squareRootEndpoint R / q := by
  rcases Finset.mem_Ioc.mp hq with ⟨_hRq, hqhalf⟩
  have hqpos : 0 < q := by omega
  apply (Nat.le_div_iff_mul_le hqpos).2
  have htwo : q * 2 ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 hqhalf
  simpa [Nat.mul_comm] using htwo

/-- Every middle reciprocal quotient is strictly below the square-root scale.
This is the formal lower-universe closure used by any inductive middle-tail
estimate. -/
theorem squareRootEndpoint_div_lt_root_of_middle
    {R q : ℕ} (hR : 1 ≤ R)
    (hq : q ∈ Finset.Ioc R (squareRootEndpoint R / 2)) :
    squareRootEndpoint R / q < R := by
  rcases Finset.mem_Ioc.mp hq with ⟨hRq, _hqhalf⟩
  have hqpos : 0 < q := by omega
  apply (Nat.div_lt_iff_lt_mul hqpos).2
  have hRRlt : R * R < R * q :=
    Nat.mul_lt_mul_of_pos_left hRq (by omega)
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hpow : R ^ 2 = R * R := by ring
    omega
  exact hXlt.trans hRRlt

/-- Middle fibres land exactly in the lower reciprocal range `[2,R)`. -/
theorem squareRootMiddleQuotient_range
    {R q : ℕ} (hR : 1 ≤ R)
    (hq : q ∈ Finset.Ioc R (squareRootEndpoint R / 2)) :
    2 ≤ squareRootEndpoint R / q ∧ squareRootEndpoint R / q < R :=
  ⟨two_le_squareRootEndpoint_div_of_middle hq,
    squareRootEndpoint_div_lt_root_of_middle hR hq⟩

/-- The inert indicator sum is literally the cardinality of the existing top
fibre prime set. -/
theorem squareRootInertPrimeMass_eq_card (R : ℕ) :
    squareRootInertPrimeMass R = ((squareRootTopFibrePrimes R).card : ℂ) := by
  classical
  unfold squareRootInertPrimeMass squareRootTopFibrePrimes
  rw [Finset.sum_filter]
  simp

/-- On the top half, the Mertens prime transform collapses to the inert unit
prime mass because every reciprocal quotient is exactly one. -/
theorem squareRootTopMertensTail_eq_inertPrimeMass (R : ℕ) :
    (∑ q ∈ Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R),
      if q.Prime then
        mertensSummatory (squareRootEndpoint R / q)
      else
        0) = squareRootInertPrimeMass R := by
  classical
  unfold squareRootInertPrimeMass
  apply Finset.sum_congr rfl
  intro q hq
  rcases Finset.mem_Ioc.mp hq with ⟨hlow, hhigh⟩
  by_cases hprime : q.Prime
  · have hdiv : squareRootEndpoint R / q = 1 :=
      squareRootEndpoint_div_eq_one_of_top_fibre
        hprime.pos (by omega) hhigh
    rw [if_pos hprime, if_pos hprime, hdiv, mertensSummatory_one]
  · simp [hprime]

/-- **Exact middle/inert split.**  At a complete square endpoint, the original
prime-first transport is the middle lower-scale Mertens tail plus the inert
unit-prime mass. -/
theorem squareRootTransportPrimeFirst_eq_middleMertensTail_add_inertPrimeMass
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTransportPrimeFirst R =
      squareRootMiddleMertensTail R + squareRootInertPrimeMass R := by
  classical
  have hpow : R ^ 2 = R * R := by ring
  have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 hmul
  have hsplit :
      Finset.Ioc R (squareRootEndpoint R) =
        Finset.Ioc R (squareRootEndpoint R / 2) ∪
          Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj :
      Disjoint (Finset.Ioc R (squareRootEndpoint R / 2))
        (Finset.Ioc (squareRootEndpoint R / 2) (squareRootEndpoint R)) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    rcases Finset.mem_Ioc.mp hq1 with ⟨_, hqhalf⟩
    rcases Finset.mem_Ioc.mp hq2 with ⟨hhalfq, _⟩
    omega
  rw [squareRootTransportPrimeFirst_eq_mertensTransform R (by omega),
    hsplit, Finset.sum_union hdisj]
  unfold squareRootMiddleMertensTail
  rw [squareRootTopMertensTail_eq_inertPrimeMass R]

/-- **Exact three-section Mertens identity.**  The square-prefix Mertens value is
the already-built smooth square-root section minus the middle lower-scale tail
minus the inert top-prime section. -/
theorem squarePrefixMertens_eq_smooth_sub_middle_sub_inert
    (R : ℕ) (hR : 3 ≤ R) :
    squarePrefixMertens (R - 1) =
      squareRootSmoothMass (R - 1) -
        squareRootMiddleMertensTail R - squareRootInertPrimeMass R := by
  rw [squarePrefixMertens_eq_squareRootSmooth_sub_transport]
  rw [squareRootTransportMass_pred_eq_cofactorFirst R (by omega)]
  rw [squareRootTransportCofactorFirst_eq_primeFirst]
  rw [squareRootTransportPrimeFirst_eq_middleMertensTail_add_inertPrimeMass R hR]
  ring

/-- The same identity grouped as `M = known edges - middle`. -/
theorem squarePrefixMertens_eq_knownEdgeMass_sub_middle
    (R : ℕ) (hR : 3 ≤ R) :
    squarePrefixMertens (R - 1) =
      squareRootKnownEdgeMass R - squareRootMiddleMertensTail R := by
  rw [squarePrefixMertens_eq_smooth_sub_middle_sub_inert R hR]
  unfold squareRootKnownEdgeMass
  ring

/-- **Middle cancellation target.**  The discrepancy between the middle tail
and the known edge mass is exactly the negative Mertens value.  Consequently a
bound on this residual is exactly a bound on `M(R^2-1)`. -/
theorem squareRootMiddleCancellationResidual_eq_neg_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleCancellationResidual R =
      -squarePrefixMertens (R - 1) := by
  unfold squareRootMiddleCancellationResidual
  rw [squarePrefixMertens_eq_knownEdgeMass_sub_middle R hR]
  ring

/-- Norm form of the exact reduction: no triangle inequality is lost. -/
theorem norm_squareRootMiddleCancellationResidual_eq_mertens
    (R : ℕ) (hR : 3 ≤ R) :
    ‖squareRootMiddleCancellationResidual R‖ =
      ‖squarePrefixMertens (R - 1)‖ := by
  rw [squareRootMiddleCancellationResidual_eq_neg_mertens R hR]
  simp

end RHLean.Proof
