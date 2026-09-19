import Mathlib
import RHLean.Proof.SquareRootLowPrimeResponseReentryBirthWitness
import RHLean.Proof.SquareRootLowPrimeResponseForestOthelloInvolution
import RHLean.Proof.SquareRootLowPrimeCanonicalLiberty
import RHLean.Proof.SquareRootLowPrimeGoTwoBoundaryShell
import RHLean.Proof.SquareRootLowPrimeGoFullFacePartner
import RHLean.Proof.SquareRootLowPrimeGoRootEqualityBoundary
import RHLean.Proof.SquareRootLowPrimeDeepProcessedSeatBridge
import RHLean.Proof.SquareRootLowPrimeNoTogglePopulationBound

/-!
# Response re-entry routes canonically into the Go two-boundary shell

This file formalizes the arithmetic bridge exposed by the finite X=210 model.

A non-born processed seat can survive a first-owner fallout only through the
inherited response tail. If it later re-enters at a larger scheduled owner,
SquareRootLowPrimeResponseReentryBirthWitness produces a strictly larger newly
born prime. Read that newborn prime as the Go outer owner, the later scheduled
prime as the Go smaller owner, and retain the original cofactor as the Go
parent.

The birth witness is then exactly a member of the full Go birth boundary.
The existing two-boundary theorem splits that parent into:

* a physically completed second-contact terminal parent; or
* a genuine SecondBoundaryDefectParents occurrence.

The latter is already consumed by the full-face transport mate theorem, so this
bridge introduces no new estimate and never sends a completed second contact
(such as the X=210 example) into the hard carrier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A born re-entry witness is literally a full Go birth-boundary parent. -/
theorem squareRootLowPrimeReentryBirthBoundary_mem_goFullBirthBoundary
    {R p q c t : ℕ}
    (hc : 0 < c)
    (_hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpq : p < q)
    (hsq : Squarefree c)
    (htBirth : t ∈ squareRootBornPartnerBirthBoundary R c (q * c)) :
    c ∈ squareRootLowPrimeGoFullBirthBoundaryParents t q := by
  rcases mem_squareRootBornPartnerBirthBoundary.mp htBirth with
    ⟨htBorn, hct⟩
  rcases Finset.mem_filter.mp htBorn with
    ⟨_htRange, _htPrime, _hroughChild, htqc, _hprod⟩
  apply mem_squareRootLowPrimeGoFullBirthBoundaryParents.mpr
  refine ⟨by omega, ?_, hsq, hrough.trans hpq, ?_⟩
  · omega
  · apply (Nat.div_lt_iff_lt_mul hq.pos).2
    have htqc' : t ≤ c * q := by
      simpa [Nat.mul_comm] using htqc
    omega

/-- Every re-entry birth witness has exactly the two physical Go outcomes:
second contact already completed, or a genuine second-boundary defect. -/
theorem squareRootLowPrimeReentryBirthBoundary_goTerminal_or_secondBoundary
    {R X p q c t : ℕ}
    (hc : 0 < c)
    (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpq : p < q)
    (hsq : Squarefree c)
    (htBirth : t ∈ squareRootBornPartnerBirthBoundary R c (q * c)) :
    c ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents
          t (X / (t * t)) q ∨
      c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents t X q := by
  have hfull :
      c ∈ squareRootLowPrimeGoFullBirthBoundaryParents t q :=
    squareRootLowPrimeReentryBirthBoundary_mem_goFullBirthBoundary
      hc hp hq hrough hpq hsq htBirth
  have hsplit :=
    squareRootLowPrimeGoFullBirthBoundaryParents_eq_terminal_union_defect
      t X q
  rw [hsplit] at hfull
  exact Finset.mem_union.mp hfull

/-- Dynamic processed-seat to Go-shell bridge. -/
theorem squareRootLowPrimeNonBornFalloutReentry_goTerminal_or_secondBoundary
    {R K j U p q c s : ℕ}
    (hR : 1 ≤ R) (hc : 0 < c)
    (hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) (hpq : p < q)
    (hpU : p ≤ U) (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hqAlive : s < squareRootLowPrimeCombinedFreshResponse R K j (q * c)) :
    ∃ t,
      t.Prime ∧ q < t ∧ p * c < t ∧
        (c ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents
              t (squareRootEndpoint R / (t * t)) q ∨
          c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
              t (squareRootEndpoint R) q) := by
  have hparent :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U :=
    (mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall).1
  have hseat :
      (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
  have hcProcessed :
      c ∈ squareRootLowPrimeProcessedSignedCofactors R U :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hseat).1
  have hcMuNe : μ c ≠ 0 := by
    exact (Finset.mem_filter.mp hcProcessed).2.2
  have hsq : Squarefree c :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hcMuNe
  obtain ⟨t, htBirth, hqt, hpct⟩ :=
    squareRootLowPrimeNonBornFalloutReentry_birthWitness
      hR hc hp hq hrough hpq hpU hUR hs hnb hfall hqAlive
  have htBorn := (mem_squareRootBornPartnerBirthBoundary.mp htBirth).1
  have htPrime : t.Prime := (Finset.mem_filter.mp htBorn).2.1
  have hsplit :=
    squareRootLowPrimeReentryBirthBoundary_goTerminal_or_secondBoundary
      (X := squareRootEndpoint R)
      hc hp hq hrough hpq hsq htBirth
  exact ⟨t, htPrime, hqt, hpct, hsplit⟩

/-- The hard branch is already consumed pointwise by the full-face Go mate. -/
theorem squareRootLowPrimeSecondBoundaryDefect_fullFace_cancel
    {R t q c : ℕ}
    (hR : 2 ≤ R)
    (ht : t.Prime) (hq : q.Prime) (hqt : q < t)
    (hcube : t ^ 3 ≤ squareRootEndpoint R)
    (hcDefect : c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
      t (squareRootEndpoint R) q) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource q t c) +
      lowWheelFullTaggedPhysicalWeight
        (lowWheelFullFaceQuotientMate R
          (squareRootLowPrimeGoSecondBoundaryFullFaceSource q t c)) = 0 := by
  exact squareRootLowPrimeGoSecondBoundaryFullFaceSource_mate_cancel
    hR ht hq hqt hcube hcDefect

/-! ## Re-entry closes inside the response forest -/

/-- **A scheduled non-born re-entry is already a response-forest event.**
The newborn prime supplied by the re-entry theorem is a literal born response
atom over the re-entered cofactor `q*c`.  It is therefore either internal to
the processed prime interval, where the response-forest Othello involution
cancels it against its arithmetic child, or it has crossed the owner cutoff and
is literally a `BornNoSuccessor` / BornExit atom.

This route has no Go cube hypothesis. -/
theorem squareRootLowPrimeNonBornFalloutScheduledReentry_birthAtom_internal_or_exit
    {R K j U p q c s : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hc : 0 < c)
    (hp : p.Prime)
    (hqSet : q ∈ squareRootLowPrimeFreshPrimeSet K U)
    (hrough : canonicalLargestPrimeFactor c < p) (hpq : p < q)
    (hpU : p ≤ U) (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hqAlive : s < squareRootLowPrimeCombinedFreshResponse R K j (q * c)) :
    ∃ t,
      t.Prime ∧ q < t ∧ p * c < t ∧
        ((q * c, t) ∈ squareRootLowPrimeBornInternalAtoms R K U ∨
          (q * c, t) ∈ squareRootLowPrimeBornNoSuccessorAtoms R K U) := by
  have hqData := Finset.mem_filter.mp hqSet
  have hqPrime : q.Prime := hqData.2
  have hqIoc := Finset.mem_Ioc.mp hqData.1
  have hKq : K < q := hqIoc.1
  have hqU : q ≤ U := hqIoc.2
  obtain ⟨t, htBirth, hqt, hpct⟩ :=
    squareRootLowPrimeNonBornFalloutReentry_birthWitness
      (by omega) hc hp hqPrime hrough hpq hpU hUR hs hnb hfall hqAlive
  have htBorn : t ∈ squareRootBornPartnerSet R (q * c) :=
    (mem_squareRootBornPartnerBirthBoundary.mp htBirth).1
  have htData := Finset.mem_filter.mp htBorn
  have htPrime : t.Prime := htData.2.1
  have hqcX : q * c ≤ squareRootEndpoint R := by
    have hprod : (q * c) * t ≤ squareRootEndpoint R :=
      htData.2.2.2.2
    calc
      q * c = (q * c) * 1 := by simp
      _ ≤ (q * c) * t := Nat.mul_le_mul_left (q * c) (by omega)
      _ ≤ squareRootEndpoint R := hprod
  have hparent :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U :=
    (mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall).1
  have hseat : (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
  have hcProcessed :
      c ∈ squareRootLowPrimeProcessedSignedCofactors R U :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hseat).1
  have hcMuNe : μ c ≠ 0 :=
    (Finset.mem_filter.mp hcProcessed).2.2
  have hsqC : Squarefree c :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hcMuNe
  have hqRough : canonicalLargestPrimeFactor c < q :=
    hrough.trans hpq
  have hqFresh : ¬ q ∣ c :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hc hqPrime hqRough
  have hcop : Nat.Coprime q c :=
    (hqPrime.coprime_iff_not_dvd).2 hqFresh
  have hsqQC : Squarefree (q * c) :=
    (Nat.squarefree_mul hcop).2 ⟨hqPrime.squarefree, hsqC⟩
  have hmuQC : μ (q * c) ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsqQC
  have hlpfQC : canonicalLargestPrimeFactor (q * c) = q := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hqPrime hqRough
  have hqcProcessed :
      q * c ∈ squareRootLowPrimeProcessedSignedCofactors R U := by
    unfold squareRootLowPrimeProcessedSignedCofactors
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hqPrime.pos hc, hqcX⟩, ?_, hmuQC⟩
    simpa [hlpfQC] using hqU
  have hqcSeat :
      (q * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U :=
    mem_squareRootLowPrimeProcessedSeatAtoms.mpr ⟨hqcProcessed, hqAlive⟩
  have hqcCarrier :
      some (q * c, s) ∈ squareRootLowPrimeProcessedSeatCarrier R K j U := by
    unfold squareRootLowPrimeProcessedSeatCarrier
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_image.mpr ⟨(q * c, s), hqcSeat, rfl⟩))
  have hdeep : K < canonicalLargestPrimeFactor (q * c) := by
    simpa [hlpfQC] using hKq
  have hownedSeat :
      (q * c, s) ∈ squareRootLowPrimeOwnedResponseSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeat_mem_ownedResponseSeatCarrier_of_deep
      hK hqcCarrier hdeep
  have hownedSigned :
      q * c ∈ squareRootLowPrimeOwnedSignedCofactors R K U :=
    (mem_squareRootLowPrimeOwnedResponseSeatCarrier_iff.mp hownedSeat).1
  have htDeep :
      t ∈ squareRootLowPrimeDeepPartnerSet R (q * c) := by
    unfold squareRootLowPrimeDeepPartnerSet
    exact Finset.mem_union.mpr (Or.inl htBorn)
  have hAtom :
      (q * c, t) ∈ squareRootLowPrimeOwnedResponseAtoms R K U :=
    mem_squareRootLowPrimeOwnedResponseAtoms_iff.mpr
      ⟨hownedSigned, htDeep⟩
  have hBornResponse :
      (q * c, t) ∈ squareRootLowPrimeBornResponseAtoms R K U :=
    mem_squareRootLowPrimeBornResponseAtoms.mpr ⟨hAtom, htBorn⟩
  have hcut : squareRootBornPostTailLowPrimeCutoff R < R := by
    unfold squareRootBornPostTailLowPrimeCutoff
    have hsqrtPos : 0 < Nat.sqrt R := Nat.sqrt_pos.2 (by omega)
    omega
  have hURlt : U < R := lt_of_le_of_lt hUR hcut
  refine ⟨t, htPrime, hqt, hpct, ?_⟩
  by_cases htU : t ≤ U
  · exact Or.inl
      (mem_squareRootLowPrimeBornInternalAtoms.mpr
        ⟨hAtom, htBorn, htU⟩)
  · right
    rw [squareRootLowPrimeBornNoSuccessorAtoms_eq_frontier hURlt]
    exact mem_squareRootLowPrimeBornFrontierAtoms.mpr
      ⟨hAtom, htBorn, Nat.lt_of_not_ge htU⟩


/-- An internal born response atom is not residual: the response-forest
Othello mate sends it to its literal arithmetic child, and the two tagged
weights cancel pointwise. -/
theorem squareRootLowPrimeBornInternalAtom_responseForest_cancel
    {R K U : ℕ} (hUR : U < R) {a : ℕ × ℕ}
    (ha : a ∈ squareRootLowPrimeBornInternalAtoms R K U) :
    squareRootLowPrimeResponseForestOthelloMate R K U (Sum.inl a) =
        Sum.inr (squareRootLowPrimeBadAtomChild a) ∧
      squareRootLowPrimeResponseForestOthelloWeight (Sum.inl a) +
        squareRootLowPrimeResponseForestOthelloWeight
          (squareRootLowPrimeResponseForestOthelloMate R K U (Sum.inl a)) = 0 := by
  have hmate :
      squareRootLowPrimeResponseForestOthelloMate R K U (Sum.inl a) =
        Sum.inr (squareRootLowPrimeBadAtomChild a) := by
    simp [squareRootLowPrimeResponseForestOthelloMate,
      creationResponseOthelloMate, ha]
  have hne :
      squareRootLowPrimeResponseForestOthelloMate R K U (Sum.inl a) ≠
        Sum.inl a := by
    rw [hmate]
    simp
  refine ⟨hmate, ?_⟩
  rw [squareRootLowPrimeResponseForestOthelloMate_weight_neg hUR
    (Sum.inl a) hne]
  abel

/-! ## Exhaustive dynamic split -/

/-- No later same-seat re-entry after the first failed owner.  Every later
processed prime has response fibre too short to recover the inherited seat. -/
def squareRootLowPrimeNoLaterSeatReentry
    (R K j U p c s : ℕ) : Prop :=
  ∀ q ∈ squareRootLowPrimeFreshPrimeSet K U, p < q →
    squareRootLowPrimeCombinedFreshResponse R K j (q * c) ≤ s

/-- Maximum response height attained by any later processed prime.
The empty later-prime set has ceiling zero via `Finset.sup`. -/
def squareRootLowPrimeLaterResponseCeiling
    (R K j U p c : ℕ) : ℕ :=
  (((squareRootLowPrimeFreshPrimeSet K U).filter fun q => p < q).image
      fun q => squareRootLowPrimeCombinedFreshResponse R K j (q * c)).sup id

/-- Every later response is bounded by the finite later-response ceiling. -/
theorem squareRootLowPrimeCombinedFreshResponse_le_laterResponseCeiling
    {R K j U p c q : ℕ}
    (hq : q ∈ squareRootLowPrimeFreshPrimeSet K U)
    (hpq : p < q) :
    squareRootLowPrimeCombinedFreshResponse R K j (q * c) ≤
      squareRootLowPrimeLaterResponseCeiling R K j U p c := by
  unfold squareRootLowPrimeLaterResponseCeiling
  apply Finset.le_sup (f := id)
  exact Finset.mem_image.mpr
    ⟨q, Finset.mem_filter.mpr ⟨hq, hpq⟩, rfl⟩

/-- The negative universal no-re-entry condition is exactly one positive
inequality against the finite response ceiling. -/
theorem squareRootLowPrimeNoLaterSeatReentry_iff_ceiling_le
    {R K j U p c s : ℕ} :
    squareRootLowPrimeNoLaterSeatReentry R K j U p c s ↔
      squareRootLowPrimeLaterResponseCeiling R K j U p c ≤ s := by
  constructor
  · intro hno
    unfold squareRootLowPrimeLaterResponseCeiling
    apply Finset.sup_le
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
    rcases Finset.mem_filter.mp hq with ⟨hqSet, hpq⟩
    exact hno q hqSet hpq
  · intro hceil q hq hpq
    exact
      (squareRootLowPrimeCombinedFreshResponse_le_laterResponseCeiling
        hq hpq).trans hceil

/-- **Positive interval normal form for the terminal no-reentry branch.**
Once a non-born first-owner fallout has occurred, absence of every later
re-entry is equivalent to membership in one explicit finite seat interval. -/
theorem squareRootLowPrimeNonBornFallout_noLater_iff_mem_terminalResponseTail
    {R K j U p c s : ℕ}
    (hR : 1 ≤ R)
    (hp : p.Prime) (hpU : p ≤ U)
    (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootLowPrimeNoLaterSeatReentry R K j U p c s ↔
      s ∈ Finset.Ico
        (max (squareRootBornPartnerCount R c)
          (max
            (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
            (squareRootLowPrimeLaterResponseCeiling R K j U p c)))
        (squareRootLowPrimeCombinedFreshResponse R K j c) := by
  have htail :=
    squareRootLowPrimeNonBornFirstOwnerFalloff_is_responseTail
      hR hp hpU hUR hs hnb hfall
  have hborn : squareRootBornPartnerCount R c ≤ s :=
    Nat.le_of_not_gt hnb
  rw [Finset.mem_Ico]
  rw [squareRootLowPrimeNoLaterSeatReentry_iff_ceiling_le]
  constructor
  · intro hceil
    exact ⟨max_le hborn (max_le htail.1 hceil), htail.2⟩
  · intro h
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h.1)

/-! ## Exact terminal no-reentry fibre -/

/-- Exact lower endpoint of the non-born terminal response tail.  It enforces
all three constraints simultaneously: outside the born prefix, dead at the first
failed owner, and never alive at any later processed owner. -/
def squareRootLowPrimeTerminalNoReentryLower
    (R K j U p c : ℕ) : ℕ :=
  max (squareRootBornPartnerCount R c)
    (max
      (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
      (squareRootLowPrimeLaterResponseCeiling R K j U p c))

/-- Literal terminal seat interval after the born prefix, the first failed owner,
and every later response height have all been accounted for. -/
def squareRootLowPrimeTerminalNoReentrySeatIndices
    (R K j U p c : ℕ) : Finset ℕ :=
  Finset.Ico
    (squareRootLowPrimeTerminalNoReentryLower R K j U p c)
    (squareRootLowPrimeCombinedFreshResponse R K j c)

/-- Exact width of the non-born terminal no-reentry response tail. -/
def squareRootLowPrimeTerminalNoReentryWidth
    (R K j U p c : ℕ) : ℕ :=
  squareRootLowPrimeCombinedFreshResponse R K j c -
    squareRootLowPrimeTerminalNoReentryLower R K j U p c

@[simp] theorem card_squareRootLowPrimeTerminalNoReentrySeatIndices
    (R K j U p c : ℕ) :
    (squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).card =
      squareRootLowPrimeTerminalNoReentryWidth R K j U p c := by
  simp [squareRootLowPrimeTerminalNoReentrySeatIndices,
    squareRootLowPrimeTerminalNoReentryWidth,
    squareRootLowPrimeTerminalNoReentryLower]

/-- One cofactor's terminal no-reentry unit-seat fibre. -/
def squareRootLowPrimeTerminalNoReentryFiber
    (R K j U p c : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).image
    fun s => some (c, s)

@[simp] theorem mem_squareRootLowPrimeTerminalNoReentryFiber
    {R K j U p c s : ℕ} :
    some (c, s) ∈ squareRootLowPrimeTerminalNoReentryFiber R K j U p c ↔
      s ∈ squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c := by
  simp [squareRootLowPrimeTerminalNoReentryFiber]

/-- On an actual non-born first-owner fallout, the negative no-reentry
predicate is *literally* membership in the finite terminal fibre. -/
theorem squareRootLowPrimeNonBornFallout_noLater_iff_mem_terminalFiber
    {R K j U p c s : ℕ}
    (hR : 1 ≤ R)
    (hp : p.Prime) (hpU : p ≤ U)
    (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootLowPrimeNoLaterSeatReentry R K j U p c s ↔
      some (c, s) ∈ squareRootLowPrimeTerminalNoReentryFiber R K j U p c := by
  rw [mem_squareRootLowPrimeTerminalNoReentryFiber]
  unfold squareRootLowPrimeTerminalNoReentrySeatIndices
    squareRootLowPrimeTerminalNoReentryLower
  exact squareRootLowPrimeNonBornFallout_noLater_iff_mem_terminalResponseTail
    hR hp hpU hUR hs hnb hfall

/-- The terminal no-reentry fibre has no hidden multiplicity: its signed mass is
one native cofactor sign times the exact terminal response width. -/
theorem squareRootLowPrimeTerminalNoReentryFiber_weight_sum
    (R K j U p c : ℕ) :
    (∑ x ∈ squareRootLowPrimeTerminalNoReentryFiber R K j U p c,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeTerminalNoReentryWidth R K j U p c : ℝ) := by
  unfold squareRootLowPrimeTerminalNoReentryFiber
  calc
    (∑ x ∈
        (squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).image
          (fun s => some (c, s)),
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ s ∈ squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c,
        squareRootLowPrimeProcessedSeatWeightReal (some (c, s)) := by
      apply Finset.sum_image
      intro a _ha b _hb hab
      simpa using hab
    _ = ∑ _s ∈ squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c,
        ((-μ c : ℤ) : ℝ) := by
      rfl
    _ = ((-μ c : ℤ) : ℝ) *
        ((squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).card : ℝ) := by
      simp
      ring
    _ = ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeTerminalNoReentryWidth R K j U p c : ℝ) := by
      rw [card_squareRootLowPrimeTerminalNoReentrySeatIndices]


/-! ## Global terminal no-reentry ledger -/


/-- If a state falls out at the first scheduled prime strictly above its
canonical largest prime, then the static intrinsic-owner scan returns exactly
that prime.  Earlier listed coordinates cannot be canonical fallout owners
because they lie at or below the largest-prime threshold. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_eq_firstOwnerAbove_of_falloff
    {ps : List ℕ} {S : Finset SquareRootLowPrimeProcessedState}
    {x : SquareRootLowPrimeProcessedState} {p : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove ps
      (canonicalLargestPrimeFactor
        (squareRootLowPrimeProcessedStateCofactor x)) = some p)
    (hfall : x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p) :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = some p := by
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, hpre, _hrough⟩
  have hpreNo :
      ∀ q ∈ pre,
        x ∉ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S q := by
    intro q hq hqFall
    rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hqFall with
      ⟨_hxS, _hxHead, _hqFresh, _hqMissing, hqRough⟩
    exact (Nat.not_lt_of_ge (hpre q hq)) hqRough
  rw [hsplit]
  induction pre with
  | nil =>
      simp [squareRootLowPrimeProcessedSeatIntrinsicFirstOwner, hfall]
  | cons q qs ih =>
      have hqNo :
          x ∉ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S q :=
        hpreNo q (by simp)
      have hrest :
          ∀ r ∈ qs,
            x ∉ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S r := by
        intro r hr
        exact hpreNo r (by simp [hr])
      simp only [List.cons_append,
        squareRootLowPrimeProcessedSeatIntrinsicFirstOwner, if_neg hqNo]
      exact ih hrest

/-- On an actual assigned terminal, the intrinsic owner is therefore the
cofactor-level first eligible owner.  This recovers the cofactor-first picture
after terminal survival has been imposed. -/
theorem squareRootLowPrimeCanonicalAssigned_intrinsicFirstOwner_eq_firstOwnerAbove
    {R K j U c s p : ℕ}
    (hx : some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p) :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (some (c, s)) = some p := by
  have hxTerminal :
      some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U :=
    (Finset.mem_sdiff.mp hx).1
  have hfall :=
    squareRootLowPrimeProcessedSeatCanonicalTerminal_firstOwnerAbove_mem_falloff
      hxTerminal (by simp) hfirst
  exact
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_eq_firstOwnerAbove_of_falloff
      hfirst hfall

/-- Seat-level no-reentry indices after imposing the actual terminal target and
the unique intrinsic first-owner assignment.  The first owner is a property of
the processed seat, not of the cofactor alone. -/
def squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
    (R K j U p c : ℕ) : Finset ℕ :=
  (squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).filter fun s =>
    some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U ∧
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (some (c, s)) = some p

/-- Exact multiplicity of one first-owner/cofactor terminal no-reentry slice. -/
def squareRootLowPrimeFirstOwnerTerminalNoReentryWidth
    (R K j U p c : ℕ) : ℕ :=
  (squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
    R K j U p c).card

/-- Literal processed states in one disjoint first-owner/cofactor no-reentry
slice. -/
def squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
    (R K j U p c : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
      R K j U p c).image fun s => some (c, s)

@[simp] theorem mem_squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
    {R K j U p c s : ℕ} :
    some (c, s) ∈
        squareRootLowPrimeFirstOwnerTerminalNoReentryFiber R K j U p c ↔
      s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
        R K j U p c := by
  simp [squareRootLowPrimeFirstOwnerTerminalNoReentryFiber]

/-- Membership exposes both pieces that make the global ledger canonical:
actual terminal membership and the unique seat-level first owner. -/
theorem squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices_data
    {R K j U p c s : ℕ}
    (hs : s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
      R K j U p c) :
    s ∈ squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c ∧
      some (c, s) ∈
        squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U ∧
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (some (c, s)) = some p := by
  simpa [squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices] using
    Finset.mem_filter.mp hs

/-- Each first-owner/cofactor no-reentry slice has one native Möbius sign, so
its exact signed mass is sign times width. -/
theorem squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_weight_sum
    (R K j U p c : ℕ) :
    (∑ x ∈ squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
        R K j U p c, squareRootLowPrimeProcessedSeatWeightReal x) =
      ((-μ c : ℤ) : ℝ) *
        (squareRootLowPrimeFirstOwnerTerminalNoReentryWidth
          R K j U p c : ℝ) := by
  unfold squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
    squareRootLowPrimeFirstOwnerTerminalNoReentryWidth
  calc
    (∑ x ∈
        (squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
          R K j U p c).image (fun s => some (c, s)),
        squareRootLowPrimeProcessedSeatWeightReal x) =
      ∑ s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
          R K j U p c,
        squareRootLowPrimeProcessedSeatWeightReal (some (c, s)) := by
      apply Finset.sum_image
      intro a _ha b _hb hab
      simpa using hab
    _ = ∑ _s ∈ squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
          R K j U p c, ((-μ c : ℤ) : ℝ) := by
      rfl
    _ = ((-μ c : ℤ) : ℝ) *
        ((squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices
          R K j U p c).card : ℝ) := by
      simp
      ring

/-- Two terminal no-reentry fibres with different first-owner/cofactor labels
are disjoint.  This is the global no-double-counting statement that the
cofactor-only ledger lacks. -/
theorem squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_disjoint
    {R K j U p q c d : ℕ} (hpcqd : (p, c) ≠ (q, d)) :
    Disjoint
      (squareRootLowPrimeFirstOwnerTerminalNoReentryFiber R K j U p c)
      (squareRootLowPrimeFirstOwnerTerminalNoReentryFiber R K j U q d) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨t, ht, hEq⟩
  have hpair : (c, s) = (d, t) := Option.some.inj hEq
  have hcd : c = d := congrArg Prod.fst hpair
  have hst : s = t := congrArg Prod.snd hpair
  subst d
  subst t
  have hsData :=
    squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices_data hs
  have htData :=
    squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices_data ht
  have hpq : p = q := Option.some.inj (hsData.2.2.symm.trans htData.2.2)
  exact hpcqd (by simp [hpq])

/-- Index set for the global no-reentry ledger. -/
def squareRootLowPrimeFirstOwnerTerminalNoReentryIndex
    (R K j U : ℕ) : Finset (ℕ × ℕ) :=
  (squareRootLowPrimeFreshPrimeList K U).toFinset ×ˢ
    squareRootLowPrimeProcessedSignedCofactors R U

/-- The genuine global terminal no-reentry ledger.  It is indexed by the
seat-level first owner and cofactor; summing only over cofactors would merge
distinct chronological fallout layers. -/
def squareRootLowPrimeGlobalTerminalNoReentryLedger
    (R K j U : ℕ) : ℝ :=
  ∑ pc ∈ squareRootLowPrimeFirstOwnerTerminalNoReentryIndex R K j U,
    ((-μ pc.2 : ℤ) : ℝ) *
      (squareRootLowPrimeFirstOwnerTerminalNoReentryWidth
        R K j U pc.1 pc.2 : ℝ)

/-- The global ledger is literally the signed mass of its disjoint
first-owner/cofactor fibres. -/
theorem squareRootLowPrimeGlobalTerminalNoReentryLedger_eq_fiberMass
    (R K j U : ℕ) :
    squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U =
      ∑ pc ∈ squareRootLowPrimeFirstOwnerTerminalNoReentryIndex R K j U,
        ∑ x ∈ squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
          R K j U pc.1 pc.2,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  unfold squareRootLowPrimeGlobalTerminalNoReentryLedger
  apply Finset.sum_congr rfl
  intro pc _hpc
  rw [squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_weight_sum]


/-- Literal union of all genuine terminal no-reentry first-owner/cofactor
fibres.  Pairwise disjointness of the labelled fibres makes this a true carrier,
not merely a support upper bound. -/
def squareRootLowPrimeGlobalTerminalNoReentryCarrier
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeFirstOwnerTerminalNoReentryIndex R K j U).biUnion fun pc =>
    squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
      R K j U pc.1 pc.2

/-- The labelled fibre family used in the global carrier is pairwise disjoint. -/
theorem squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_pairwiseDisjoint
    (R K j U : ℕ) :
    Set.PairwiseDisjoint
      (↑(squareRootLowPrimeFirstOwnerTerminalNoReentryIndex R K j U))
      (fun pc => squareRootLowPrimeFirstOwnerTerminalNoReentryFiber
        R K j U pc.1 pc.2) := by
  intro a _ha b _hb hab
  exact squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_disjoint hab

/-- The literal global no-reentry carrier has exactly the compiled ledger mass. -/
theorem squareRootLowPrimeGlobalTerminalNoReentryCarrier_weight_sum
    (R K j U : ℕ) :
    (∑ x ∈ squareRootLowPrimeGlobalTerminalNoReentryCarrier R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U := by
  unfold squareRootLowPrimeGlobalTerminalNoReentryCarrier
  rw [Finset.sum_biUnion
    (squareRootLowPrimeFirstOwnerTerminalNoReentryFiber_pairwiseDisjoint
      R K j U)]
  exact (squareRootLowPrimeGlobalTerminalNoReentryLedger_eq_fiberMass
    R K j U).symm

/-- Every state in the global no-reentry carrier is an actual assigned
canonical terminal. -/
theorem squareRootLowPrimeGlobalTerminalNoReentryCarrier_subset_assigned
    (R K j U : ℕ) :
    squareRootLowPrimeGlobalTerminalNoReentryCarrier R K j U ⊆
      squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨pc, _hpc, hxpc⟩
  rcases Finset.mem_image.mp hxpc with ⟨s, hs, rfl⟩
  exact
    (squareRootLowPrimeFirstOwnerTerminalNoReentrySeatIndices_data hs).2.1

/-- The remaining assigned-terminal carrier after deleting genuine no-reentry
states.  This is the concrete population to which the response-forest/BornExit
classification must now be applied. -/
def squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier
    (R K j U : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U \
    squareRootLowPrimeGlobalTerminalNoReentryCarrier R K j U

/-- Exact signed partition of the assigned terminal population. -/
theorem squareRootLowPrimeCanonicalAssigned_weight_sum_eq_noReentry_add_complement
    (R K j U : ℕ) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U,
        squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U +
        ∑ x ∈ squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier
            R K j U,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  have hsub :=
    squareRootLowPrimeGlobalTerminalNoReentryCarrier_subset_assigned R K j U
  have hsplit := Finset.sum_sdiff hsub
    (f := squareRootLowPrimeProcessedSeatWeightReal)
  rw [squareRootLowPrimeGlobalTerminalNoReentryCarrier_weight_sum] at hsplit
  simpa [squareRootLowPrimeFirstOwnerNonNoReentryComplementCarrier,
    add_comm] using hsplit.symm

/-- The part of the exact intrinsic first-owner mass not belonging to genuine
terminal no-reentry fibres.  The response-forest layer identifies this
complement pointwise with already-existing born/boundary mechanisms; defining
it by subtraction keeps the global accounting exact before that identification
is assembled. -/
def squareRootLowPrimeFirstOwnerNonNoReentryComplementLedger
    (R K j U : ℕ) : ℝ :=
  squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass
      (squareRootLowPrimeFreshPrimeList K U)
      (squareRootLowPrimeProcessedSeatCarrier R K j U)
      (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U) -
    squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U

/-- **Exact global accounting after the re-entry closure.**  The running
imbalance is the genuine no-reentry ledger, plus the complementary first-owner
mass, plus the explicit no-owner heads.  No transport term is duplicated and no
seat can be counted under two first owners. -/
theorem squareRootLowPrimeRunningImbalanceReal_eq_terminalNoReentry_add_complement_add_heads
    {R K j U : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeRunningImbalanceReal R K j U =
      squareRootLowPrimeGlobalTerminalNoReentryLedger R K j U +
        squareRootLowPrimeFirstOwnerNonNoReentryComplementLedger R K j U +
        ∑ x ∈ squareRootLowPrimeProcessedSeatCanonicalTerminalHeads R K j U,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  rw [squareRootLowPrimeRunningImbalanceReal_eq_firstOwnerMass_add_heads hR]
  unfold squareRootLowPrimeFirstOwnerNonNoReentryComplementLedger
  ring

/-- The proposed sum of the post-root downcross ledger and transport would
double-count the same exact object: the repository already identifies them. -/
theorem lowWheelCanonicalPostRootDowncrossLedger_add_transport_eq_two_transport
    {R : ℕ} (hR : 2 ≤ R) :
    lowWheelCanonicalPostRootDowncrossLedger R +
        squareRootTransportCofactorFirst R =
      2 * squareRootTransportCofactorFirst R := by
  rw [lowWheelCanonicalPostRootDowncrossLedger_eq_transport R hR]
  ring


/-- **Exact dynamic exhaustiveness.**  A non-born first-owner fallout either
never re-enters at any later processed prime, or the first witnessed re-entry
routes pointwise into the already-compiled Go two-boundary shell.

No count, norm, or asymptotic input is used. -/
theorem squareRootLowPrimeNonBornFallout_noLater_or_goShell
    {R K j U p c s : ℕ}
    (hR : 1 ≤ R) (hc : 0 < c)
    (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpU : p ≤ U) (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootLowPrimeNoLaterSeatReentry R K j U p c s ∨
      ∃ q t,
        q ∈ squareRootLowPrimeFreshPrimeSet K U ∧
        p < q ∧
        t.Prime ∧ q < t ∧ p * c < t ∧
          (c ∈ squareRootLowPrimeGoSmallerOwnerBirthBoundaryParents
                t (squareRootEndpoint R / (t * t)) q ∨
            c ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
                t (squareRootEndpoint R) q) := by
  classical
  by_cases hno : squareRootLowPrimeNoLaterSeatReentry R K j U p c s
  · exact Or.inl hno
  · right
    have hex :
        ∃ q,
          q ∈ squareRootLowPrimeFreshPrimeSet K U ∧
          p < q ∧
          s < squareRootLowPrimeCombinedFreshResponse R K j (q * c) := by
      by_contra h
      push_neg at h
      apply hno
      intro q hq hpq
      exact Nat.le_of_not_gt (h q hq hpq)
    obtain ⟨q, hqSet, hpq, hqAlive⟩ := hex
    have hqPrime : q.Prime := (Finset.mem_filter.mp hqSet).2
    obtain ⟨t, htPrime, hqt, hpct, hsplit⟩ :=
      squareRootLowPrimeNonBornFalloutReentry_goTerminal_or_secondBoundary
        hR hc hp hqPrime hrough hpq hpU hUR hs hnb hfall hqAlive
    exact ⟨q, t, hqSet, hpq, htPrime, hqt, hpct, hsplit⟩

/-- **Re-entry is completely consumed by the existing response forest.**
After a non-born first-owner fallout, there are only three possibilities:

* the seat never re-enters at a later processed owner;
* a later re-entry produces an internal born atom, paired pointwise with its
  arithmetic child by the response-forest Othello involution;
* a later re-entry produces a born no-successor atom, i.e. the existing
  BornExit frontier.

Thus no re-entry term needs the Go cube hypothesis or a new quantitative
estimate. -/
theorem squareRootLowPrimeNonBornFallout_noLater_or_responseForestCancel_or_bornExit
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hK : 1 ≤ K) (hc : 0 < c)
    (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpU : p ≤ U) (hUR : U ≤ squareRootBornPostTailLowPrimeCutoff R)
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c)
    (hfall : some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootLowPrimeNoLaterSeatReentry R K j U p c s ∨
      ∃ q t,
        q ∈ squareRootLowPrimeFreshPrimeSet K U ∧
        p < q ∧
        t.Prime ∧ q < t ∧ p * c < t ∧
          (((q * c, t) ∈ squareRootLowPrimeBornInternalAtoms R K U ∧
              squareRootLowPrimeResponseForestOthelloWeight
                  (Sum.inl (q * c, t)) +
                squareRootLowPrimeResponseForestOthelloWeight
                  (squareRootLowPrimeResponseForestOthelloMate R K U
                    (Sum.inl (q * c, t))) = 0) ∨
            (q * c, t) ∈ squareRootLowPrimeBornNoSuccessorAtoms R K U) := by
  classical
  have hcut : squareRootBornPostTailLowPrimeCutoff R < R := by
    unfold squareRootBornPostTailLowPrimeCutoff
    have hsqrtPos : 0 < Nat.sqrt R := Nat.sqrt_pos.2 (by omega)
    omega
  have hURlt : U < R := lt_of_le_of_lt hUR hcut
  by_cases hno : squareRootLowPrimeNoLaterSeatReentry R K j U p c s
  · exact Or.inl hno
  · right
    have hex :
        ∃ q,
          q ∈ squareRootLowPrimeFreshPrimeSet K U ∧
          p < q ∧
          s < squareRootLowPrimeCombinedFreshResponse R K j (q * c) := by
      by_contra h
      push_neg at h
      apply hno
      intro q hq hpq
      exact Nat.le_of_not_gt (h q hq hpq)
    obtain ⟨q, hqSet, hpq, hqAlive⟩ := hex
    obtain ⟨t, htPrime, hqt, hpct, hroute⟩ :=
      squareRootLowPrimeNonBornFalloutScheduledReentry_birthAtom_internal_or_exit
        hR hK hc hp hqSet hrough hpq hpU hUR hs hnb hfall hqAlive
    refine ⟨q, t, hqSet, hpq, htPrime, hqt, hpct, ?_⟩
    rcases hroute with hInternal | hExit
    · exact Or.inl
        ⟨hInternal,
          (squareRootLowPrimeBornInternalAtom_responseForest_cancel
            hURlt hInternal).2⟩
    · exact Or.inr hExit

/-- The old root-equality exception is no longer exceptional once the complete
Boolean face is used: every such incidence is already a genuine second-boundary
defect and therefore has an opposite-sign physical full-face mate. -/
theorem squareRootLowPrimeGoRootEquality_fullFace_cancel
    {R r q d : ℕ} (hR : 2 ≤ R)
    (hz : ((r, q), d) ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R) :
    lowWheelFullTaggedPhysicalWeight
        (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d) +
      lowWheelFullTaggedPhysicalWeight
        (lowWheelFullFaceQuotientMate R
          (squareRootLowPrimeGoSecondBoundaryFullFaceSource r q d)) = 0 := by
  rcases mem_squareRootLowPrimeGoRootEqualityDefectCarrier.mp hz with
    ⟨_hrR, _hqR, _hdR, hr, hq, hrq, _heq, hcube, hd⟩
  exact squareRootLowPrimeSecondBoundaryDefect_fullFace_cancel
    hR hq hr hrq hcube hd

end RHLean.Proof
