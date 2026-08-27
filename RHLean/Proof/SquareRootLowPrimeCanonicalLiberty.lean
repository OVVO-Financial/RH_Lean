import Mathlib
import RHLean.Proof.SquareRootLowPrimeHorizontalTerminalCoverage

/-!
# Canonical prime liberties for finite processed-seat matching

Every state removed by the processed-seat matching is removed in one concrete
fresh-prime pair.  The only states without such an owned prime stage are the
states in the final matching frontier.

For the horizontal first-owner cut, intrinsic child absence in the original
processed carrier is also opened here.  Once the proposed owner `p` is prime,
within the terminal owner cutoff, fresh for the parent, and above the parent's
canonical largest prime, all arithmetic legality of the child is automatic.
Consequently an intrinsically missing child can fail only at one of the two
literal carrier walls:

* its cofactor `p*c` lies beyond the square endpoint; or
* the fixed seat index lies beyond the child's combined response fibre.

The second alternative is the existing parent/child response-window boundary,
not a mutable-row matching skip.

Finally, the first scheduled prime strictly above a terminal cofactor's
canonical largest prime is singled out.  If a non-head intrinsic residual has
such a prime, the child must have existed in the original carrier, hence was
consumed earlier.  Because this is the *first* scheduled prime above the
canonical owner, its earlier blocker is already at or below that owner.  Thus
the residual is exactly split into a no-later-owner case or a low-owner blocker
case; there is no unclassified interior skip.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A concrete prime liberty, together with its chronological location in the
matching list. -/
def SquareRootLowPrimePrimeLibertyData
    (ps : List ℕ) (S : Finset (Option (ℕ × ℕ)))
    (x : Option (ℕ × ℕ)) : Prop :=
  ∃ pre p post,
    ps = pre ++ p :: post ∧
      x ∈ squareRootLowPrimeProcessedSeatPaired
        (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p

/-- The exposed no-liberty boundary after every listed prime has been
processed. -/
def squareRootLowPrimeNoLibertyBoundary
    (ps : List ℕ) (S : Finset (Option (ℕ × ℕ))) :
    Finset (Option (ℕ × ℕ)) :=
  squareRootLowPrimeProcessedSeatMatchingFrontier ps S

/-- **Canonical-liberty dichotomy.** -/
theorem squareRootLowPrime_mem_noLibertyBoundary_or_primeLiberty
    (ps : List ℕ) (S : Finset (Option (ℕ × ℕ)))
    {x : Option (ℕ × ℕ)} (hx : x ∈ S) :
    x ∈ squareRootLowPrimeNoLibertyBoundary ps S ∨
      SquareRootLowPrimePrimeLibertyData ps S x := by
  by_cases hterminal :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S
  · exact Or.inl hterminal
  · exact Or.inr
      (squareRootLowPrimeProcessedSeat_removed_has_owner
        ps S hx hterminal)

/-- **Intrinsic processed-seat fallout has only genuine carrier obstructions.**

Suppose `some (c,s)` is canonical fallout at owner `p` relative to the original
processed carrier at cutoff `U`.  If `p` is prime and `p ≤ U`, then freshness
and `P⁺(c) < p` force the child cofactor `p*c` to have largest prime `p` and
nonzero Möbius weight.  Therefore the child can be absent from the original
carrier only because

`X_R < p*c`

or because its response fibre is too short for the inherited seat index:

`CombinedResponse(p*c) ≤ s`.

In particular, disappearance from a mutable matching row is not one of the
intrinsic obstruction cases. -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_carrierObstruction
    {R K j U p c s : ℕ}
    (hp : p.Prime) (hpU : p ≤ U)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootEndpoint R < p * c ∨
      squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s := by
  rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
    ⟨hparent, _hhead, hpFresh0, hchildMissing0, hrough0⟩
  have hpFresh : ¬ p ∣ c := by
    simpa [squareRootLowPrimeProcessedStateCofactor] using hpFresh0
  have hrough : canonicalLargestPrimeFactor c < p := by
    simpa [squareRootLowPrimeProcessedStateCofactor] using hrough0
  have hchildMissing :
      some (p * c, s) ∉ squareRootLowPrimeProcessedSeatCarrier R K j U := by
    simpa [squareRootLowPrimeProcessedSeatExtend] using hchildMissing0
  have hparentAtom :
      (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
  have hcSigned : c ∈ squareRootLowPrimeProcessedSignedCofactors R U :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hparentAtom).1
  rcases Finset.mem_filter.mp hcSigned with
    ⟨hcRange, _hcOwner, hcMu⟩
  have hcPos : 0 < c := by
    have hcOne : 1 ≤ c := (Finset.mem_Icc.mp hcRange).1
    omega
  by_cases hwall : squareRootEndpoint R < p * c
  · exact Or.inl hwall
  by_cases hseat :
      squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s
  · exact Or.inr hseat
  exfalso
  apply hchildMissing
  have hpcX : p * c ≤ squareRootEndpoint R := Nat.le_of_not_gt hwall
  have hsChild :
      s < squareRootLowPrimeCombinedFreshResponse R K j (p * c) :=
    Nat.lt_of_not_ge hseat
  have hlpfChild : canonicalLargestPrimeFactor (p * c) = p := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcPos hp hrough
    simpa [Nat.mul_comm] using h
  have hmuChild : μ (p * c) ≠ 0 := by
    rw [moebius_prime_mul_eq_neg_of_not_dvd hp hpFresh]
    exact neg_ne_zero.mpr hcMu
  have hchildSigned :
      p * c ∈ squareRootLowPrimeProcessedSignedCofactors R U := by
    unfold squareRootLowPrimeProcessedSignedCofactors
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hpcX⟩, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hp.ne_zero (Nat.ne_of_gt hcPos))
    · exact ⟨by rw [hlpfChild]; exact hpU, hmuChild⟩
  have hchildAtom :
      (p * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U :=
    mem_squareRootLowPrimeProcessedSeatAtoms.mpr ⟨hchildSigned, hsChild⟩
  unfold squareRootLowPrimeProcessedSeatCarrier
  exact Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨(p * c, s), hchildAtom, rfl⟩)

/-! ## First scheduled owner above the canonical cofactor owner -/

/-- First listed owner strictly above a numerical cutoff. -/
def squareRootLowPrimeFirstOwnerAbove : List ℕ → ℕ → Option ℕ
  | [], _L => none
  | p :: ps, L =>
      if L < p then some p else squareRootLowPrimeFirstOwnerAbove ps L

/-- There is no later owner exactly when every listed owner is at or below the
cutoff. -/
theorem squareRootLowPrimeFirstOwnerAbove_eq_none_iff
    (ps : List ℕ) (L : ℕ) :
    squareRootLowPrimeFirstOwnerAbove ps L = none ↔
      ∀ p ∈ ps, p ≤ L := by
  induction ps with
  | nil => simp [squareRootLowPrimeFirstOwnerAbove]
  | cons p ps ih =>
      by_cases hLp : L < p
      · simp [squareRootLowPrimeFirstOwnerAbove, hLp]
      · have hpL : p ≤ L := Nat.le_of_not_gt hLp
        simp [squareRootLowPrimeFirstOwnerAbove, hLp, hpL, ih]

/-- If a first owner above `L` exists, the list splits at it and every earlier
coordinate is at or below `L`. -/
theorem squareRootLowPrimeFirstOwnerAbove_some_split
    {ps : List ℕ} {L p : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove ps L = some p) :
    ∃ pre post,
      ps = pre ++ p :: post ∧
        (∀ q ∈ pre, q ≤ L) ∧
        L < p := by
  induction ps with
  | nil =>
      simp [squareRootLowPrimeFirstOwnerAbove] at hfirst
  | cons q qs ih =>
      by_cases hLq : L < q
      · have hqp : q = p := by
          apply Option.some.inj
          simpa [squareRootLowPrimeFirstOwnerAbove, hLq] using hfirst
        subst p
        exact ⟨[], qs, by simp, by simp, hLq⟩
      · have hqL : q ≤ L := Nat.le_of_not_gt hLq
        have htail : squareRootLowPrimeFirstOwnerAbove qs L = some p := by
          simpa [squareRootLowPrimeFirstOwnerAbove, hLq] using hfirst
        rcases ih htail with ⟨pre, post, hsplit, hpre, hLp⟩
        refine ⟨q :: pre, post, ?_, ?_, hLp⟩
        · simp [hsplit]
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hqL
          · exact hpre r hr

/-- Positive processed-seat cofactors really are positive arithmetic states. -/
private theorem squareRootLowPrimeProcessedSeatCofactor_pos_of_mem_carrier
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hxHead : x ≠ none) :
    0 < squareRootLowPrimeProcessedStateCofactor x := by
  rcases x with _ | z
  · exact (hxHead rfl).elim
  · have hzAtom : z ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
      simpa [squareRootLowPrimeProcessedSeatCarrier] using hx
    have hcSigned := (mem_squareRootLowPrimeProcessedSeatAtoms.mp hzAtom).1
    have hcRange := (Finset.mem_filter.mp hcSigned).1
    have hcOne := (Finset.mem_Icc.mp hcRange).1
    change 0 < z.1
    omega

/-- A prime strictly above the largest prime factor of a positive cofactor is
fresh for that cofactor. -/
private theorem squareRootLowPrimePrime_not_dvd_of_lpf_lt
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

/-- **First-later-owner skip lands immediately on the low-owner boundary.**

Take the first scheduled fresh prime `p` strictly above the canonical largest
prime of a non-head terminal intrinsic residual.  The residual condition says
`p` is not intrinsic fallout, so its child existed in the original carrier.
Terminal survival therefore forces that child to have been consumed earlier.
Every earlier scheduled coordinate is at most the parent's canonical largest
prime by firstness of `p`; hence the concrete blocker supplied by displacement
already lies on the low-owner side. -/
theorem squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_firstOwnerAbove_blocker
    {R K j U p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxResidual :
      x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U))
    (hfirst :
      squareRootLowPrimeFirstOwnerAbove
          (squareRootLowPrimeFreshPrimeList K U)
          (canonicalLargestPrimeFactor
            (squareRootLowPrimeProcessedStateCofactor x)) = some p) :
    ∃ pre post pre' q post' z,
      squareRootLowPrimeFreshPrimeList K U = pre ++ p :: post ∧
        pre = pre' ++ q :: post' ∧
        p.Prime ∧ q.Prime ∧
        q ≤ canonicalLargestPrimeFactor
          (squareRootLowPrimeProcessedStateCofactor x) ∧
        q < p ∧
        z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre'
          (squareRootLowPrimeProcessedSeatCarrier R K j U) ∧
        ((squareRootLowPrimeProcessedSeatExtend p x ∈
              squareRootLowPrimeProcessedSeatPairLower
                (squareRootLowPrimeProcessedSeatMatchingFrontier pre'
                  (squareRootLowPrimeProcessedSeatCarrier R K j U)) q ∧
            z = squareRootLowPrimeProcessedSeatExtend q
              (squareRootLowPrimeProcessedSeatExtend p x)) ∨
          (z ∈ squareRootLowPrimeProcessedSeatPairLower
              (squareRootLowPrimeProcessedSeatMatchingFrontier pre'
                (squareRootLowPrimeProcessedSeatCarrier R K j U)) q ∧
            squareRootLowPrimeProcessedSeatExtend p x =
              squareRootLowPrimeProcessedSeatExtend q z)) := by
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, hpre, hLp⟩
  have hpMem : p ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hsplit]
    simp
  have hpPrime : p.Prime := prime_of_mem_squareRootLowPrimeFreshPrimeList hpMem
  have hxResidualData :=
    mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp hxResidual
  have hxTargetData := Finset.mem_erase.mp hxResidualData.1
  have hxHead : x ≠ none := hxTargetData.1
  have hxTerminal := hxTargetData.2
  have hxCarrier :
      x ∈ squareRootLowPrimeProcessedSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset'
      (squareRootLowPrimeFreshPrimeList K U)
      (squareRootLowPrimeProcessedSeatCarrier R K j U) hxTerminal
  have hcPos := squareRootLowPrimeProcessedSeatCofactor_pos_of_mem_carrier
    hxCarrier hxHead
  have hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x :=
    squareRootLowPrimePrime_not_dvd_of_lpf_lt hcPos hpPrime hLp
  have hpreLt : ∀ q ∈ pre, q < p := by
    intro q hq
    exact lt_of_le_of_lt (hpre q hq) hLp
  rcases
      squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_has_earlier_blocker
        (squareRootLowPrimeFreshPrimeList K U) pre post
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        hxResidual hsplit hpFresh hLp hpreLt with
    ⟨pre', q, post', z, hpreSplit, hqp, hz, hedge⟩
  have hqPre : q ∈ pre := by
    rw [hpreSplit]
    simp
  have hqLe := hpre q hqPre
  have hqMem : q ∈ squareRootLowPrimeFreshPrimeList K U := by
    rw [hsplit]
    simp [hqPre]
  have hqPrime : q.Prime := prime_of_mem_squareRootLowPrimeFreshPrimeList hqMem
  exact ⟨pre, post, pre', q, post', z, hsplit, hpreSplit,
    hpPrime, hqPrime, hqLe, hqp, hz, hedge⟩

/-- **Complete non-head intrinsic-residual classification before estimation.**

Every non-head terminal residual is in exactly the intended qualitative
position: either there is no scheduled owner above its canonical largest prime,
or the first such owner has a concrete earlier prime blocker already at or
below that canonical owner boundary.  There is no free interior skip term. -/
theorem squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_noLaterOwner_or_lowBlocker
    {R K j U : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxResidual :
      x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)) :
    (∀ p ∈ squareRootLowPrimeFreshPrimeList K U,
        p ≤ canonicalLargestPrimeFactor
          (squareRootLowPrimeProcessedStateCofactor x)) ∨
      ∃ p pre post pre' q post' z,
        squareRootLowPrimeFreshPrimeList K U = pre ++ p :: post ∧
          pre = pre' ++ q :: post' ∧
          p.Prime ∧ q.Prime ∧
          q ≤ canonicalLargestPrimeFactor
            (squareRootLowPrimeProcessedStateCofactor x) ∧
          q < p ∧
          z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre'
            (squareRootLowPrimeProcessedSeatCarrier R K j U) ∧
          ((squareRootLowPrimeProcessedSeatExtend p x ∈
                squareRootLowPrimeProcessedSeatPairLower
                  (squareRootLowPrimeProcessedSeatMatchingFrontier pre'
                    (squareRootLowPrimeProcessedSeatCarrier R K j U)) q ∧
              z = squareRootLowPrimeProcessedSeatExtend q
                (squareRootLowPrimeProcessedSeatExtend p x)) ∨
            (z ∈ squareRootLowPrimeProcessedSeatPairLower
                (squareRootLowPrimeProcessedSeatMatchingFrontier pre'
                  (squareRootLowPrimeProcessedSeatCarrier R K j U)) q ∧
              squareRootLowPrimeProcessedSeatExtend p x =
                squareRootLowPrimeProcessedSeatExtend q z)) := by
  let L := canonicalLargestPrimeFactor
    (squareRootLowPrimeProcessedStateCofactor x)
  cases hfirst :
      squareRootLowPrimeFirstOwnerAbove
        (squareRootLowPrimeFreshPrimeList K U) L with
  | none =>
      left
      simpa [L] using
        (squareRootLowPrimeFirstOwnerAbove_eq_none_iff
          (squareRootLowPrimeFreshPrimeList K U) L).mp hfirst
  | some p =>
      right
      simpa [L] using
        (squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_firstOwnerAbove_blocker
          hxResidual hfirst)

end RHLean.Proof
