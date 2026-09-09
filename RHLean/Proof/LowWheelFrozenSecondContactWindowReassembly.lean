import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactDescent
import RHLean.Proof.SquareRootLowPrimeGoHyperbolicStripRecursion

/-!
# Window-difference recurrence and child-owner reassembly of the frozen
second-contact ledger

`LowWheelFrozenSecondContactDescent` hands one second-contact owner `q` a single
signed native Go window

`D_q = F_{q^-}(X_R/q) - F_{q^-}(X_R/q^2)`,

with `X_R = squareRootEndpoint R`.  This file performs, without any estimate,
the two exact moves that must precede any attempt to bound the ledger.

## The two identities

The first subtracts the recursive Go law at both endpoints of one window.  Both
copies of the completed anchor `M(q-1)` and both fixed lower-prefix columns
cancel identically, leaving only strictly smaller owners:

`D_q = -sum_{r<q} (F_{r^-}(X_R/(q*r)) - F_{r^-}(X_R/(q^2*r)))`.

The second interchanges the finite double sum so that the *child* owner `r`,
not the source owner `q`, indexes the outer column.

## The gate is not cosmetic

The endpoint form of the Go law requires the *lower* cutoff to be unfinished at
its own owner, i.e. `q <= X_R/q^2`.  `..._gate_iff_cube_le` proves that this is
exactly the cube condition `q^3 <= X_R`.  Only inside that gate do both anchors
cancel.  Outside it the window is still exact, but
`..._eq_mertensGap_sub_childOwnerWindowSum` shows that what survives at the
lower endpoint is an *unrestricted* Mertens gap

`M(q-1) - M(X_R/q^2)`,

which is a terminal leaf of the original open problem, not a descended one.  The
two theorems are stated separately so that this distinction cannot be lost when
the ledger is summed.

No norm, cardinality estimate, density input, PNT input, Mertens hypothesis, or
RH-scale bound is introduced here.  Every statement is a finite identity.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## The fourth-power gate on one owner -/

/-- The lower endpoint of the second-contact window is still unfinished at its
own owner exactly when the owner cube fits under the physical endpoint. -/
theorem lowWheelFrozenSecondContactOwner_gate_iff_cube_le
    {R q : ℕ} (hq : q.Prime) :
    q ≤ squareRootEndpoint R / (q * q) ↔ q ^ 3 ≤ squareRootEndpoint R := by
  have hcube : q * (q * q) = q ^ 3 := by ring
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos hq.pos hq.pos), hcube]

/-- Inside the gate the upper endpoint is unfinished as well. -/
theorem lowWheelFrozenSecondContactOwner_upper_unfinished_of_gate
    {R q : ℕ} (hq : q.Prime)
    (hgate : q ≤ squareRootEndpoint R / (q * q)) :
    q ≤ squareRootEndpoint R / q :=
  hgate.trans (Nat.div_le_div_left (by nlinarith [hq.two_le]) hq.pos)

/-! ## First identity: the window-difference Go recurrence -/

/-- **Exact window-difference Go recurrence.**  Subtracting the recursive Go law
at the two endpoints of one second-contact owner window cancels both copies of
the completed anchor `M(q-1)` and both fixed lower-prefix columns.  What remains
is a single signed sum of strictly smaller-owner windows, at the two inherited
cutoffs `X_R/(q*r)` and `X_R/(q*q*r)`.

Neither `F_{q^-}(X_R/q)` nor `F_{q^-}(X_R/q^2)` is bounded separately; the
identity is applied to their difference only. -/
theorem lowWheelFrozenSecondContactOwnerWindowMass_eq_neg_childOwnerWindowSum
    {R q : ℕ} (hq : q.Prime)
    (hgate : q ^ 3 ≤ squareRootEndpoint R) :
    lowWheelFrozenSecondContactOwnerWindowMass R q =
      -∑ r ∈ primesUpTo (q - 1),
        (frozenPrimeUniverseMass (primesUpTo (r - 1))
            (squareRootEndpoint R / (q * r)) -
          frozenPrimeUniverseMass (primesUpTo (r - 1))
            (squareRootEndpoint R / (q * q * r))) := by
  have hL : q ≤ squareRootEndpoint R / (q * q) :=
    (lowWheelFrozenSecondContactOwner_gate_iff_cube_le hq).2 hgate
  have hU : q ≤ squareRootEndpoint R / q :=
    lowWheelFrozenSecondContactOwner_upper_unfinished_of_gate hq hL
  rw [lowWheelFrozenSecondContactOwnerWindowMass_eq_frozenDifference hq,
    frozenPrimeUniverseMass_sub_eq_neg_smallerOwnerStripSum hq hU hL]
  simp only [Nat.div_div_eq_div_mul]

/-- **Outside the gate the lower anchor does not cancel.**  When the owner cube
already exceeds the physical endpoint, the lower cutoff `X_R/q^2` has completed
below `q`, and the exact window carries a residual *unrestricted* Mertens gap
`M(q-1) - M(X_R/q^2)`.

This is recorded as a separate theorem precisely because it is the failure mode:
a terminal leaf of this shape is the original Mertens problem, not a descended
window. -/
theorem lowWheelFrozenSecondContactOwnerWindowMass_eq_mertensGap_sub_childOwnerWindowSum
    {R q : ℕ} (hq : q.Prime)
    (hsquare : q ^ 2 ≤ squareRootEndpoint R)
    (hgate : squareRootEndpoint R < q ^ 3) :
    lowWheelFrozenSecondContactOwnerWindowMass R q =
      (mertensSummatoryInt (q - 1) -
          mertensSummatoryInt (squareRootEndpoint R / (q * q))) -
        ∑ r ∈ primesUpTo (q - 1),
          (frozenPrimeUniverseMass (primesUpTo (r - 1))
              (squareRootEndpoint R / (q * r)) -
            frozenPrimeUniverseMass (primesUpTo (r - 1)) ((q - 1) / r)) := by
  have hU : q ≤ squareRootEndpoint R / q := by
    have hsq : q * q ≤ squareRootEndpoint R := by
      calc q * q = q ^ 2 := by ring
        _ ≤ squareRootEndpoint R := hsquare
    exact (Nat.le_div_iff_mul_le hq.pos).2 hsq
  have hLlt : squareRootEndpoint R / (q * q) < q := by
    apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hq.pos hq.pos)).2
    calc squareRootEndpoint R < q ^ 3 := hgate
      _ = q * (q * q) := by ring
  rw [lowWheelFrozenSecondContactOwnerWindowMass_eq_frozenDifference hq,
    frozenPrimeUniverseMass_sub_eq_mertensGap_sub_smallerOwnerStrips hq hU hLlt]
  simp only [Nat.div_div_eq_div_mul]

/-! ## Second identity: global reassembly by the child owner -/

/-- The second-contact owners below the root whose window admits the
base-cancelling recurrence, i.e. those inside the cube gate. -/
def lowWheelFrozenSecondContactGatedOwners (R : ℕ) : Finset ℕ :=
  (primesUpTo (R - 1)).filter fun q => q ^ 3 ≤ squareRootEndpoint R

theorem mem_lowWheelFrozenSecondContactGatedOwners {R q : ℕ} :
    q ∈ lowWheelFrozenSecondContactGatedOwners R ↔
      q.Prime ∧ q ≤ R - 1 ∧ q ^ 3 ≤ squareRootEndpoint R := by
  simp [lowWheelFrozenSecondContactGatedOwners, and_assoc]

/-- The predecessor prime universe of an owner below the root is the root
universe cut at that owner. -/
theorem primesUpTo_pred_eq_primesUpTo_root_filter_lt
    {R q : ℕ} (hq : q.Prime) (hqR : q ≤ R - 1) :
    primesUpTo (q - 1) = (primesUpTo (R - 1)).filter fun r => r < q := by
  have h2 := hq.two_le
  ext r
  simp only [Finset.mem_filter, mem_primesUpTo]
  constructor
  · rintro ⟨hrPrime, hrq⟩
    exact ⟨⟨hrPrime, by omega⟩, by omega⟩
  · rintro ⟨⟨hrPrime, _hrR⟩, hrq⟩
    exact ⟨hrPrime, by omega⟩

/-- **Global reassembly by the child owner.**  Substituting the window-difference
recurrence into the gated ledger and interchanging the two finite sums makes the
*child* owner `r` index the outer column.  Each fixed-`r` column collects every
inherited window `(X_R/(q^2*r), X_R/(q*r)]` contributed by the source owners
`q > r`.

The identity is exact: no term is bounded, dropped, or replaced by its absolute
value.  It is the last exact move available before an estimate, and it is what
must be inspected for further cancellation before any triangle inequality. -/
theorem lowWheelFrozenSecondContactGatedLedger_eq_neg_childOwnerReassembly
    (R : ℕ) :
    ∑ q ∈ lowWheelFrozenSecondContactGatedOwners R,
        lowWheelFrozenSecondContactOwnerWindowMass R q =
      -∑ r ∈ primesUpTo (R - 1),
          ∑ q ∈ (lowWheelFrozenSecondContactGatedOwners R).filter
              fun q => r < q,
            (frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * r)) -
              frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * q * r))) := by
  have hstep :
      ∀ q ∈ lowWheelFrozenSecondContactGatedOwners R,
        lowWheelFrozenSecondContactOwnerWindowMass R q =
          -∑ r ∈ primesUpTo (R - 1),
            (if r < q then
              frozenPrimeUniverseMass (primesUpTo (r - 1))
                  (squareRootEndpoint R / (q * r)) -
                frozenPrimeUniverseMass (primesUpTo (r - 1))
                  (squareRootEndpoint R / (q * q * r))
             else 0) := by
    intro q hqMem
    obtain ⟨hqPrime, hqR, hgate⟩ :=
      mem_lowWheelFrozenSecondContactGatedOwners.mp hqMem
    rw [lowWheelFrozenSecondContactOwnerWindowMass_eq_neg_childOwnerWindowSum
        hqPrime hgate,
      primesUpTo_pred_eq_primesUpTo_root_filter_lt hqPrime hqR,
      Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [← Finset.sum_filter]

end RHLean.Proof
