import Mathlib
import RHLean.Proof.SquareRootLowPrimeCanonicalLiberty

/-!
# Exact fixed-owner fallout widths

After the canonical Euler matching of `SquareRootLowPrimeCanonicalLiberty`, a
terminal non-head state is assigned to the first chronological prime `p` for
which its `p`-child is intrinsically absent from the original processed carrier.
This file opens that intrinsic absence completely at one fixed owner.

For a processed cofactor `c` with `P⁺(c) < p`, every parent seat has the form
`some (c,s)`, `0 <= s < CombinedFreshResponse(c)`.  There are exactly two ways
its canonical `p`-child can be absent from the original carrier:

* the cofactor itself crosses the square wall, `X_R < p*c`; or
* the child remains under the square wall but its response fibre ends before
  the inherited seat index `s`.

Consequently the literal fallout fibre over `c` is an interval of seat indices.
Its width is exactly

```text
CombinedFreshResponse(c)                         if X_R < p*c,
CombinedFreshResponse(c) - CombinedFreshResponse(p*c) otherwise.
```

The complete fixed-owner fallout is the disjoint union of these cofactor
fibres, so its signed mass is one cofactor sum with this exact width.  No
absolute value, asymptotic estimate, PNT input, Mertens bound, or chain-parity
argument is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Processed cofactors which can genuinely be extended in the canonical
Euler direction at owner `p`. -/
def squareRootLowPrimeCanonicalOwnerParentCofactors
    (R U p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeProcessedSignedCofactors R U).filter fun c =>
    canonicalLargestPrimeFactor c < p

@[simp] theorem mem_squareRootLowPrimeCanonicalOwnerParentCofactors
    {R U p c : ℕ} :
    c ∈ squareRootLowPrimeCanonicalOwnerParentCofactors R U p ↔
      c ∈ squareRootLowPrimeProcessedSignedCofactors R U ∧
        canonicalLargestPrimeFactor c < p := by
  simp [squareRootLowPrimeCanonicalOwnerParentCofactors]

/-- Exact number of inherited parent seats which have no `p`-child in the
original processed carrier. -/
def squareRootLowPrimeCanonicalOwnerFalloutWidth
    (R K j p c : ℕ) : ℕ :=
  if squareRootEndpoint R < p * c then
    squareRootLowPrimeCombinedFreshResponse R K j c
  else
    squareRootLowPrimeCombinedFreshResponse R K j c -
      squareRootLowPrimeCombinedFreshResponse R K j (p * c)

/-- Literal inherited seat indices lost at owner `p` over one cofactor `c`. -/
def squareRootLowPrimeCanonicalOwnerFalloutSeatIndices
    (R K j p c : ℕ) : Finset ℕ :=
  if squareRootEndpoint R < p * c then
    Finset.range (squareRootLowPrimeCombinedFreshResponse R K j c)
  else
    Finset.Ico
      (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
      (squareRootLowPrimeCombinedFreshResponse R K j c)

@[simp] theorem card_squareRootLowPrimeCanonicalOwnerFalloutSeatIndices
    (R K j p c : ℕ) :
    (squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c).card =
      squareRootLowPrimeCanonicalOwnerFalloutWidth R K j p c := by
  by_cases hwall : squareRootEndpoint R < p * c <;>
    simp [squareRootLowPrimeCanonicalOwnerFalloutSeatIndices,
      squareRootLowPrimeCanonicalOwnerFalloutWidth, hwall]

/-- One cofactor's literal fixed-owner fallout states. -/
def squareRootLowPrimeCanonicalOwnerFalloutFiber
    (R K j p c : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c).image
    fun s => some (c, s)

@[simp] theorem mem_squareRootLowPrimeCanonicalOwnerFalloutFiber
    {R K j p c s : ℕ} :
    some (c, s) ∈ squareRootLowPrimeCanonicalOwnerFalloutFiber R K j p c ↔
      s ∈ squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c := by
  simp [squareRootLowPrimeCanonicalOwnerFalloutFiber]

/-- A prime strictly above the largest prime factor of a positive integer is
fresh for that integer. -/
theorem squareRootLowPrimePrime_fresh_of_lpf_lt
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    ¬ p ∣ c := by
  intro hdiv
  by_cases hcOne : c = 1
  · subst c
    exact hp.not_dvd_one hdiv
  · have hcGt : 1 < c := by omega
    have hmem : p ∈ c.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hdiv, by omega⟩
    have hle : p ≤ canonicalLargestPrimeFactor c := by
      unfold canonicalLargestPrimeFactor
      rw [dif_pos hcGt]
      exact Finset.le_max' c.primeFactors p hmem
    omega

/-- **Pointwise fallout = exact seat tail.**

Under canonical arithmetic legality of the parent, membership in the intrinsic
fixed-owner fallout set is equivalent to membership in the explicit lost-seat
interval. -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_iff_seatIndex
    {R K j U p c s : ℕ}
    (hp : p.Prime) (hpU : p ≤ U)
    (hcSigned : c ∈ squareRootLowPrimeProcessedSignedCofactors R U)
    (hrough : canonicalLargestPrimeFactor c < p) :
    some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p ↔
      s ∈ squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c := by
  have hcRange := (Finset.mem_filter.mp hcSigned).1
  have hcOne : 1 ≤ c := (Finset.mem_Icc.mp hcRange).1
  have hcPos : 0 < c := by omega
  have hpFresh : ¬ p ∣ c :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hcPos hp hrough
  constructor
  · intro hfall
    rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
      ⟨hparent, _hhead, _hpFresh, _hmissing, _hrough⟩
    have hparentAtom :
        (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
    have hsParent :
        s < squareRootLowPrimeCombinedFreshResponse R K j c :=
      (mem_squareRootLowPrimeProcessedSeatAtoms.mp hparentAtom).2
    have hobs :=
      squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_carrierObstruction
        hp hpU hfall
    by_cases hwall : squareRootEndpoint R < p * c
    · simpa [squareRootLowPrimeCanonicalOwnerFalloutSeatIndices, hwall]
        using hsParent
    · have hseat :
          squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s :=
        hobs.resolve_left hwall
      exact Finset.mem_Ico.mpr ⟨hseat, hsParent⟩
  · intro hsLost
    by_cases hwall : squareRootEndpoint R < p * c
    · have hsParent :
          s < squareRootLowPrimeCombinedFreshResponse R K j c := by
        simpa [squareRootLowPrimeCanonicalOwnerFalloutSeatIndices, hwall]
          using hsLost
      have hparentAtom :
          (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U :=
        mem_squareRootLowPrimeProcessedSeatAtoms.mpr ⟨hcSigned, hsParent⟩
      have hparent :
          some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
        unfold squareRootLowPrimeProcessedSeatCarrier
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨(c, s), hparentAtom, rfl⟩)
      have hchildMissing :
          squareRootLowPrimeProcessedSeatExtend p (some (c, s)) ∉
            squareRootLowPrimeProcessedSeatCarrier R K j U := by
        intro hchild
        have hchild' :
            some (p * c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
          simpa [squareRootLowPrimeProcessedSeatExtend] using hchild
        have hchildAtom :
            (p * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
          simpa [squareRootLowPrimeProcessedSeatCarrier] using hchild'
        have hpcSigned :=
          (mem_squareRootLowPrimeProcessedSeatAtoms.mp hchildAtom).1
        have hpcRange := (Finset.mem_filter.mp hpcSigned).1
        have hpcUpper := (Finset.mem_Icc.mp hpcRange).2
        omega
      exact mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
        ⟨hparent, by simp, by simpa [squareRootLowPrimeProcessedStateCofactor],
          hchildMissing,
          by simpa [squareRootLowPrimeProcessedStateCofactor]⟩
    · have hsData :
          squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s ∧
            s < squareRootLowPrimeCombinedFreshResponse R K j c := by
        simpa [squareRootLowPrimeCanonicalOwnerFalloutSeatIndices, hwall]
          using hsLost
      have hparentAtom :
          (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U :=
        mem_squareRootLowPrimeProcessedSeatAtoms.mpr ⟨hcSigned, hsData.2⟩
      have hparent :
          some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
        unfold squareRootLowPrimeProcessedSeatCarrier
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨(c, s), hparentAtom, rfl⟩)
      have hchildMissing :
          squareRootLowPrimeProcessedSeatExtend p (some (c, s)) ∉
            squareRootLowPrimeProcessedSeatCarrier R K j U := by
        intro hchild
        have hchild' :
            some (p * c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
          simpa [squareRootLowPrimeProcessedSeatExtend] using hchild
        have hchildAtom :
            (p * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
          simpa [squareRootLowPrimeProcessedSeatCarrier] using hchild'
        have hsChild :
            s < squareRootLowPrimeCombinedFreshResponse R K j (p * c) :=
          (mem_squareRootLowPrimeProcessedSeatAtoms.mp hchildAtom).2
        omega
      exact mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
        ⟨hparent, by simp, by simpa [squareRootLowPrimeProcessedStateCofactor],
          hchildMissing,
          by simpa [squareRootLowPrimeProcessedStateCofactor]⟩

/-- Fallout fibres over distinct cofactors are disjoint. -/
theorem squareRootLowPrimeCanonicalOwnerFalloutFiber_pairwiseDisjoint
    (R K j U p : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeCanonicalOwnerParentCofactors R U p))
      (squareRootLowPrimeCanonicalOwnerFalloutFiber R K j p) := by
  intro c _hc d _hd hcd
  rw [Finset.disjoint_left]
  intro x hxc hxd
  rcases Finset.mem_image.mp hxc with ⟨s, _hs, hsx⟩
  rcases Finset.mem_image.mp hxd with ⟨t, _ht, htx⟩
  have hpair : (c, s) = (d, t) :=
    Option.some.inj (hsx.trans htx.symm)
  exact hcd (congrArg Prod.fst hpair)

/-- **The complete fixed-owner fallout is the disjoint union of its exact
cofactor seat tails.** -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_eq_biUnion
    {R K j U p : ℕ} (hp : p.Prime) (hpU : p ≤ U) :
    squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p =
      (squareRootLowPrimeCanonicalOwnerParentCofactors R U p).biUnion
        (squareRootLowPrimeCanonicalOwnerFalloutFiber R K j p) := by
  ext x
  constructor
  · intro hfall
    rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
      ⟨hparent, hhead, _hpFresh, _hmissing, hrough0⟩
    rcases x with _ | z
    · exact (hhead rfl).elim
    · rcases z with ⟨c, s⟩
      have hparentAtom :
          (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
        simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
      have hcSigned :=
        (mem_squareRootLowPrimeProcessedSeatAtoms.mp hparentAtom).1
      have hrough : canonicalLargestPrimeFactor c < p := by
        simpa [squareRootLowPrimeProcessedStateCofactor] using hrough0
      have hsLost :=
        (squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_iff_seatIndex
          hp hpU hcSigned hrough).mp hfall
      apply Finset.mem_biUnion.mpr
      refine ⟨c,
        mem_squareRootLowPrimeCanonicalOwnerParentCofactors.mpr
          ⟨hcSigned, hrough⟩, ?_⟩
      exact mem_squareRootLowPrimeCanonicalOwnerFalloutFiber.mpr hsLost
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨c, hcEligible, hxc⟩
    rcases Finset.mem_image.mp hxc with ⟨s, hsLost, hsx⟩
    have hcData :=
      mem_squareRootLowPrimeCanonicalOwnerParentCofactors.mp hcEligible
    rw [← hsx]
    exact
      (squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_iff_seatIndex
        hp hpU hcData.1 hcData.2).mpr hsLost

/-- Signed mass of one cofactor fallout fibre. -/
theorem squareRootLowPrimeCanonicalOwnerFalloutFiber_weight_sum
    (R K j p c : ℕ) :
    (∑ x ∈ squareRootLowPrimeCanonicalOwnerFalloutFiber R K j p c,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeCanonicalOwnerFalloutWidth R K j p c : ℝ) := by
  unfold squareRootLowPrimeCanonicalOwnerFalloutFiber
  calc
    (∑ x ∈
        (squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c).image
          (fun s => some (c, s)),
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ s ∈ squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c,
        squareRootLowPrimeProcessedSeatWeightReal (some (c, s)) := by
      apply Finset.sum_image
      intro a _ha b _hb hab
      simpa using hab
    _ = ∑ _s ∈ squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c,
        ((-μ c : ℤ) : ℝ) := by
      rfl
    _ = ((-μ c : ℤ) : ℝ) *
        ((squareRootLowPrimeCanonicalOwnerFalloutSeatIndices R K j p c).card : ℝ) := by
      simp
      ring
    _ = ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeCanonicalOwnerFalloutWidth R K j p c : ℝ) := by
      rw [card_squareRootLowPrimeCanonicalOwnerFalloutSeatIndices]

/-- **Exact fixed-owner signed fallout mass.**  Literal seat multiplicity has
been compressed to one arithmetic width per canonical parent cofactor. -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_weight_sum
    {R K j U p : ℕ} (hp : p.Prime) (hpU : p ≤ U) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ c ∈ squareRootLowPrimeCanonicalOwnerParentCofactors R U p,
        ((-μ c : ℤ) : ℝ) *
          (squareRootLowPrimeCanonicalOwnerFalloutWidth R K j p c : ℝ) := by
  rw [squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_eq_biUnion hp hpU]
  rw [Finset.sum_biUnion
    (squareRootLowPrimeCanonicalOwnerFalloutFiber_pairwiseDisjoint R K j U p)]
  apply Finset.sum_congr rfl
  intro c _hc
  exact squareRootLowPrimeCanonicalOwnerFalloutFiber_weight_sum R K j p c

/-- Every chronological first-owner slice is contained in the corresponding
fixed-owner fallout set.  Thus the exact width formula above is the ambient
horizontal carrier for the disjoint terminal slices. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice_subset_falloff
    {ps : List ℕ} {S T : Finset SquareRootLowPrimeProcessedState} {p : ℕ} :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p ⊆
      squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p := by
  intro x hx
  have howner :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hx).2
  exact (squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_some_mem howner).2

end RHLean.Proof
