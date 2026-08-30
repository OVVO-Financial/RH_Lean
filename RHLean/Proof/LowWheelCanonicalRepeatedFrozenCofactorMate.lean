import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedParentClassification
import RHLean.Proof.SquareRootLowPrimeGoCrossingMateLedger

/-!
# Existing physical mate for frozen repeated-parent states with c > 1

For a frozen repeated-parent state `y = (t,(c,k))`, classification gives
`k = p`, where `p = minFac(c*k)`, and every Boolean-face prime is below `p`.
When `c > 1`, choose the concrete prime `q = minFac(c)` and remove it from the
cofactor into the quotient:

`(t,(c,p)) -> (t,(c/q,q*p))`.

This is not a new recursive family.  The fixed-prime transport theorem already
proves that removing any prime divisor from the cofactor stays inside the
existing physical transport carrier.  Squarefreeness gives sign reversal and
also makes the mate distinct.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Canonical physical removal prime for a frozen nontrivial cofactor. -/
def lowWheelCanonicalRepeatedFrozenCofactorPrime
    (y : LowWheelTaggedDowncrossState) : ℕ :=
  Nat.minFac y.2.1

/-- The existing physical transport mate, retaining the Boolean face tag. -/
def lowWheelCanonicalRepeatedFrozenCofactorMate
    (y : LowWheelTaggedDowncrossState) : LowWheelTaggedCofactorQuotientState :=
  (y.1, lowWheelCofactorQuotientToggleAt
    (lowWheelCanonicalRepeatedFrozenCofactorPrime y) y.2)

/-- The chosen removal coordinate is prime and divides the source cofactor. -/
theorem lowWheelCanonicalRepeatedFrozenCofactorPrime_spec
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    (lowWheelCanonicalRepeatedFrozenCofactorPrime y).Prime ∧
      lowWheelCanonicalRepeatedFrozenCofactorPrime y ∣ y.2.1 := by
  have hcgt := (Finset.mem_filter.mp hy).2
  have hcne : y.2.1 ≠ 1 := by omega
  constructor
  · simpa [lowWheelCanonicalRepeatedFrozenCofactorPrime] using
      Nat.minFac_prime hcne
  · simpa [lowWheelCanonicalRepeatedFrozenCofactorPrime] using
      Nat.minFac_dvd y.2.1

/-- Frozen shape turns the abstract mate into the requested concrete formula
`(t,(c/q,q*p))`. -/
theorem lowWheelCanonicalRepeatedFrozenCofactorMate_eq
    {R c k : ℕ} {t : Finset ℕ}
    (hy : (t, (c, k)) ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    let p := lowWheelTaggedDowncrossPivot (t, (c, k))
    let q := Nat.minFac c
    lowWheelCanonicalRepeatedFrozenCofactorMate (t, (c, k)) =
      (t, (c / q, q * p)) := by
  let p := lowWheelTaggedDowncrossPivot (t, (c, k))
  let q := Nat.minFac c
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hshape := (Finset.mem_filter.mp hfrozen).2
  have hk : k = p := by simpa [p] using hshape.1
  have hqd : q ∣ c := by
    simpa [q] using (lowWheelCanonicalRepeatedFrozenCofactorPrime_spec hy).2
  simp [lowWheelCanonicalRepeatedFrozenCofactorMate,
    lowWheelCanonicalRepeatedFrozenCofactorPrime, q, hqd, hk, p]

/-- The frozen `c>1` mate is a literal occurrence of the already-existing
physical transport ledger on the same Boolean face. -/
theorem lowWheelCanonicalRepeatedFrozenCofactorMate_mem_transport
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelCanonicalRepeatedFrozenCofactorMate y ∈
      lowWheelCanonicalTaggedPhysicalCarrier R := by
  rcases y with ⟨t, ⟨c, k⟩⟩
  have hprime := lowWheelCanonicalRepeatedFrozenCofactorPrime_spec hy
  let q := Nat.minFac c
  have hqPrime : q.Prime := by simpa [q] using hprime.1
  have hqc : q ∣ c := by simpa [q] using hprime.2
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hxData := mem_lowWheelCanonicalDowncrossPart.mp htag.2
  have hphysData := mem_lowWheelCanonicalPhysicalStateSet.mp hxData.1
  have hcarrier := hphysData.2.2.2
  have hmateCarrier : LowWheelTransportPairCarrier R t
      (lowWheelCofactorQuotientToggleAt q (c, k)) :=
    lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
      hqPrime hcarrier hqc
  have hmateRanges := lowWheelTransportPairCarrier_mem_ranges hmateCarrier
  have hcdiv : c / q ∣ c := ⟨q, (Nat.div_mul_cancel hqc).symm⟩
  have hmateSq : Squarefree (c / q) :=
    hphysData.2.2.1.squarefree_of_dvd hcdiv
  have hmatePhysical : lowWheelCofactorQuotientToggleAt q (c, k) ∈
      lowWheelCanonicalPhysicalStateSet R t := by
    apply mem_lowWheelCanonicalPhysicalStateSet.mpr
    unfold lowWheelCofactorQuotientToggleAt
    simp only [hqc, if_true]
    exact ⟨hmateRanges.1, hmateRanges.2, hmateSq, by
      simpa [lowWheelCofactorQuotientToggleAt, hqc] using hmateCarrier⟩
  apply mem_lowWheelCanonicalTaggedPhysicalCarrier.mpr
  refine ⟨htag.1, ?_⟩
  simpa [lowWheelCanonicalRepeatedFrozenCofactorMate,
    lowWheelCanonicalRepeatedFrozenCofactorPrime, q] using hmatePhysical

/-- The existing mate has exactly the opposite signed physical weight. -/
theorem lowWheelCanonicalRepeatedFrozenCofactorMate_weight_neg
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelTaggedCanonicalWeight
        (lowWheelCanonicalRepeatedFrozenCofactorMate y) =
      -lowWheelTaggedCanonicalWeight (y.1, y.2) := by
  rcases y with ⟨t, ⟨c, k⟩⟩
  have hprime := lowWheelCanonicalRepeatedFrozenCofactorPrime_spec hy
  let q := Nat.minFac c
  have hqPrime : q.Prime := by simpa [q] using hprime.1
  have hqc : q ∣ c := by simpa [q] using hprime.2
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hphys := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hsq := (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.2.1
  unfold lowWheelTaggedCanonicalWeight
  simpa [lowWheelCanonicalRepeatedFrozenCofactorMate,
    lowWheelCanonicalRepeatedFrozenCofactorPrime, q] using
    (lowWheelCofactorQuotientToggleAt_weight_neg
      (t := t) hqPrime hsq (Or.inl hqc))

/-- Squarefreeness makes the removal mate pointwise distinct from its source. -/
theorem lowWheelCanonicalRepeatedFrozenCofactorMate_ne
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenCofactorPart R) :
    lowWheelCanonicalRepeatedFrozenCofactorMate y ≠ (y.1, y.2) := by
  rcases y with ⟨t, ⟨c, k⟩⟩
  have hprime := lowWheelCanonicalRepeatedFrozenCofactorPrime_spec hy
  let q := Nat.minFac c
  have hqPrime : q.Prime := by simpa [q] using hprime.1
  have hqc : q ∣ c := by simpa [q] using hprime.2
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hphys := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hsq := (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.2.1
  have hnot : ¬ q ∣ c / q :=
    prime_not_dvd_div_of_squarefree hqPrime hsq hqc
  intro heq
  have hstate := congrArg Prod.snd heq
  have hcofactor := congrArg Prod.fst hstate
  change (lowWheelCofactorQuotientToggleAt q (c, k)).1 = c at hcofactor
  simp only [lowWheelCofactorQuotientToggleAt, hqc, if_true] at hcofactor
  have hqdSource : q ∣ c := hqc
  rw [← hcofactor] at hqdSource
  exact hnot hqdSource

end RHLean.Proof
