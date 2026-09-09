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

## The gate, and why the carrier had to be tightened

The endpoint form of the Go law requires the *lower* cutoff to be unfinished at
its own owner, i.e. `q <= X_R/q^2`.  `..._gate_iff_cube_le` proves that this is
exactly the cube condition `q^3 <= X_R`.  On the `X_R/q^2` carrier only owners
inside that gate cancel both anchors; outside it
`..._eq_mertensGap_sub_childOwnerWindowSum` exhibits a surviving *unrestricted*
Mertens gap `M(q-1) - M(X_R/q^2)`, a terminal leaf of the original open problem
rather than a descended one.

The final section removes that defect at its source.  The `X_R/q^2` carrier is
not tight: `..._ParentFaceProduct_gt_root` proves the second-contact image lies
strictly above `R`, so the lower endpoint may be raised to
`max R (X_R/q^2)`.  On the resulting rooted window the owner is below the lower
cutoff for free, the cube gate disappears, and
`..._RootedOwnerWindowMass_eq_neg_childOwnerWindowSum` cancels both anchors at
*every* prime owner below the root.  The gate was a defect of the carrier, not
of the object.

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

/-! ## The second-contact image lies strictly above the root

The window carrier of #627/#628 has lower endpoint `X_R/q^2`.  That is not
tight.  A frozen downcross state carries a lower wall of its own,

`R < primeFaceProduct y.1 * y.2.2`,

from `LowWheelTransportPairCarrier`, and on a frozen repeated-cofactor state the
high quotient `y.2.2` is the pivot `p`.  Erasing the top cofactor prime `q` from
the product-one face leaves

`P(V) = (c/q) * p * P(t) >= p * P(t) > R`,

because `q ∣ c`.  So the whole image sits above `R`, the lower endpoint may be
raised to `max R (X_R/q^2)`, and — the consequence that matters — the owner is
then below the lower cutoff automatically.  The cube gate of the previous
section is a defect of the loose carrier, not of the object. -/

/-- **The parent face product exceeds the root.**  The downcross lower wall
survives the erasure of the top cofactor prime, because the erased prime divides
the cofactor and the wall is carried by the pivot and the Boolean face. -/
theorem lowWheelFrozenSecondContactParentFaceProduct_gt_root
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    R < primeFaceProduct (lowWheelFrozenSecondContactParentFace y) := by
  obtain ⟨hqPrime, hqDvd, _hpq⟩ := lowWheelFrozenCofactorTopPrime_data hy
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hy
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hdown := mem_lowWheelCanonicalDowncrossPart.mp htag.2
  have hphys := mem_lowWheelCanonicalPhysicalStateSet.mp hdown.1
  have hpair : LowWheelTransportPairCarrier R y.1 y.2 := hphys.2.2.2
  have hwall : R < primeFaceProduct y.1 * y.2.2 := hpair.2.2.1
  have hwallPivot :
      R < primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y := by
    rw [← hsource.1]
    exact hwall
  obtain ⟨d, hd⟩ := hqDvd
  have hc1 : 1 < y.2.1 := hsource.2.2.2.2.1
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [h0, Nat.mul_zero] at hd
      omega
    · exact hpos
  have hfull := lowWheelCanonicalRepeatedFrozenProductOneFace_product hy
  have herase := lowWheelFrozenSecondContact_owner_mul_parentFaceProduct hy
  have hkey :
      lowWheelFrozenCofactorTopPrime y *
          primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
        lowWheelFrozenCofactorTopPrime y *
          (d * (primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y)) := by
    rw [herase, hfull, hd]
    ring
  have hPV :
      primeFaceProduct (lowWheelFrozenSecondContactParentFace y) =
        d * (primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y) :=
    Nat.eq_of_mul_eq_mul_left hqPrime.pos hkey
  calc
    R < primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y := hwallPivot
    _ ≤ d * (primeFaceProduct y.1 * lowWheelTaggedDowncrossPivot y) :=
        Nat.le_mul_of_pos_left _ hdpos
    _ = primeFaceProduct (lowWheelFrozenSecondContactParentFace y) := hPV.symm

/-- **Rooted annulus.**  The genuine second-contact target is confined to the
window with lower endpoint raised to the root. -/
theorem lowWheelFrozenSecondContactParentMap_rooted_annulus
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    max R (squareRootEndpoint R /
        (lowWheelFrozenCofactorTopPrime y * lowWheelFrozenCofactorTopPrime y)) <
      primeFaceProduct (lowWheelFrozenSecondContactParentFace y) ∧
    primeFaceProduct (lowWheelFrozenSecondContactParentFace y) ≤
      squareRootEndpoint R / lowWheelFrozenCofactorTopPrime y := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  obtain ⟨hlower, hupper⟩ :=
    lowWheelFrozenSecondContactParentMap_division_annulus hy
  exact ⟨max_lt (lowWheelFrozenSecondContactParentFaceProduct_gt_root hyFrozen)
    hlower, hupper⟩

/-- The tightened native owner window: the #628 window with its lower endpoint
raised to the root. -/
def lowWheelFrozenSecondContactRootedOwnerWindow (R q : ℕ) : Finset (Finset ℕ) :=
  frozenPrimeUniverseWindowFaces
    (primesUpTo (q - 1))
    (max R (squareRootEndpoint R / (q * q)))
    (squareRootEndpoint R / q)

/-- Every genuine frozen second-contact source lands in the rooted window. -/
theorem lowWheelFrozenSecondContactParentFace_mem_rootedOwnerWindow
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    lowWheelFrozenSecondContactParentFace y ∈
      lowWheelFrozenSecondContactRootedOwnerWindow R
        (lowWheelFrozenCofactorTopPrime y) := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  obtain ⟨hlower, hupper⟩ :=
    lowWheelFrozenSecondContactParentMap_rooted_annulus hy
  exact mem_frozenPrimeUniverseWindowFaces.mpr
    ⟨lowWheelFrozenSecondContactParentFace_mem_predecessor hyFrozen,
      hlower, hupper⟩

/-- Signed mass of one rooted owner window. -/
def lowWheelFrozenSecondContactRootedOwnerWindowMass (R q : ℕ) : ℤ :=
  frozenPrimeUniverseWindowMass
    (primesUpTo (q - 1))
    (max R (squareRootEndpoint R / (q * q)))
    (squareRootEndpoint R / q)

/-- Below the root the physical endpoint still admits `R` copies of the owner. -/
theorem lowWheelFrozenSecondContactRootedOwner_root_le_upperCutoff
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    R ≤ squareRootEndpoint R / q := by
  have hsucc : q + 1 ≤ R := hqR
  have hR2 : 2 ≤ q := hq.two_le
  have hstep : R * (q + 1) ≤ R * R := mul_le_mul_left' hsucc R
  have hexpand : R * (q + 1) = R * q + R := by ring
  rw [hexpand] at hstep
  have hRq : R * q + 1 ≤ R * R := by linarith
  have hpow : squareRootEndpoint R = R * R - 1 := by
    unfold squareRootEndpoint
    rw [pow_two]
  apply (Nat.le_div_iff_mul_le hq.pos).2
  rw [hpow]
  exact Nat.le_sub_of_add_le hRq

/-- The rooted window is a genuine window: its raised lower endpoint is still
below its upper endpoint. -/
theorem lowWheelFrozenSecondContactRootedOwner_lower_le_upper
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    max R (squareRootEndpoint R / (q * q)) ≤ squareRootEndpoint R / q :=
  max_le (lowWheelFrozenSecondContactRootedOwner_root_le_upperCutoff hq hqR)
    (Nat.div_le_div_left (by nlinarith [hq.two_le]) hq.pos)

/-- **The rooted window is an exact frozen difference.** -/
theorem lowWheelFrozenSecondContactRootedOwnerWindowMass_eq_frozenDifference
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    lowWheelFrozenSecondContactRootedOwnerWindowMass R q =
      frozenPrimeUniverseMass (primesUpTo (q - 1)) (squareRootEndpoint R / q) -
        frozenPrimeUniverseMass (primesUpTo (q - 1))
          (max R (squareRootEndpoint R / (q * q))) := by
  unfold lowWheelFrozenSecondContactRootedOwnerWindowMass
  exact frozenPrimeUniverseWindowMass_eq_sub
    (lowWheelFrozenSecondContactRootedOwner_lower_le_upper hq hqR)

/-- **The cube gate is free on the rooted window.**  Raising the lower endpoint
to the root puts it above every owner below the root, so the base-cancelling
form of the Go law applies at every owner, with no condition on `q^3`. -/
theorem lowWheelFrozenSecondContactRootedOwner_gate
    {R q : ℕ} (hqR : q < R) :
    q ≤ max R (squareRootEndpoint R / (q * q)) :=
  le_max_of_le_left hqR.le

/-- **Ungated window-difference Go recurrence.**  On the rooted window both
copies of `M(q-1)` and both fixed lower-prefix columns cancel at every prime
owner below the root.  No unrestricted Mertens leaf survives. -/
theorem lowWheelFrozenSecondContactRootedOwnerWindowMass_eq_neg_childOwnerWindowSum
    {R q : ℕ} (hq : q.Prime) (hqR : q < R) :
    lowWheelFrozenSecondContactRootedOwnerWindowMass R q =
      -∑ r ∈ primesUpTo (q - 1),
        (frozenPrimeUniverseMass (primesUpTo (r - 1))
            (squareRootEndpoint R / (q * r)) -
          frozenPrimeUniverseMass (primesUpTo (r - 1))
            (max R (squareRootEndpoint R / (q * q)) / r)) := by
  have hL : q ≤ max R (squareRootEndpoint R / (q * q)) :=
    lowWheelFrozenSecondContactRootedOwner_gate hqR
  have hU : q ≤ squareRootEndpoint R / q :=
    hqR.le.trans (lowWheelFrozenSecondContactRootedOwner_root_le_upperCutoff hq hqR)
  rw [lowWheelFrozenSecondContactRootedOwnerWindowMass_eq_frozenDifference hq hqR,
    frozenPrimeUniverseMass_sub_eq_neg_smallerOwnerStripSum hq hU hL]
  simp only [Nat.div_div_eq_div_mul]

/-- **Ungated global reassembly by the child owner.**  Every prime owner below
the root contributes, and the child owner indexes the outer column. -/
theorem lowWheelFrozenSecondContactRootedLedger_eq_neg_childOwnerReassembly
    (R : ℕ) :
    ∑ q ∈ primesUpTo (R - 1),
        lowWheelFrozenSecondContactRootedOwnerWindowMass R q =
      -∑ r ∈ primesUpTo (R - 1),
          ∑ q ∈ (primesUpTo (R - 1)).filter fun q => r < q,
            (frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * r)) -
              frozenPrimeUniverseMass (primesUpTo (r - 1))
                (max R (squareRootEndpoint R / (q * q)) / r)) := by
  have hstep :
      ∀ q ∈ primesUpTo (R - 1),
        lowWheelFrozenSecondContactRootedOwnerWindowMass R q =
          -∑ r ∈ primesUpTo (R - 1),
            (if r < q then
              frozenPrimeUniverseMass (primesUpTo (r - 1))
                  (squareRootEndpoint R / (q * r)) -
                frozenPrimeUniverseMass (primesUpTo (r - 1))
                  (max R (squareRootEndpoint R / (q * q)) / r)
             else 0) := by
    intro q hqMem
    obtain ⟨hqPrime, hqLe⟩ := mem_primesUpTo.mp hqMem
    have h2 := hqPrime.two_le
    have hqR : q < R := by omega
    rw [lowWheelFrozenSecondContactRootedOwnerWindowMass_eq_neg_childOwnerWindowSum
        hqPrime hqR,
      primesUpTo_pred_eq_primesUpTo_root_filter_lt hqPrime hqLe,
      Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [← Finset.sum_filter]

end RHLean.Proof
