import Mathlib
import RHLean.Proof.SquareRootLowPrimeResponseReentryBirthWitness
import RHLean.Proof.SquareRootLowPrimeGoTwoBoundaryShell
import RHLean.Proof.SquareRootLowPrimeGoFullFacePartner
import RHLean.Proof.SquareRootLowPrimeGoRootEqualityBoundary

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
        (max
          (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
          (squareRootLowPrimeLaterResponseCeiling R K j U p c))
        (squareRootLowPrimeCombinedFreshResponse R K j c) := by
  have htail :=
    squareRootLowPrimeNonBornFirstOwnerFalloff_is_responseTail
      hR hp hpU hUR hs hnb hfall
  rw [Finset.mem_Ico]
  rw [squareRootLowPrimeNoLaterSeatReentry_iff_ceiling_le]
  constructor
  · intro hceil
    exact ⟨max_le htail.1 hceil, htail.2⟩
  · intro h
    exact le_trans (le_max_right _ _) h.1

/-! ## Exact terminal no-reentry fibre -/

/-- Literal terminal seat interval after the first failed owner and every later
response height have both been accounted for. -/
def squareRootLowPrimeTerminalNoReentrySeatIndices
    (R K j U p c : ℕ) : Finset ℕ :=
  Finset.Ico
    (max
      (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
      (squareRootLowPrimeLaterResponseCeiling R K j U p c))
    (squareRootLowPrimeCombinedFreshResponse R K j c)

/-- Exact width of the terminal no-reentry response tail. -/
def squareRootLowPrimeTerminalNoReentryWidth
    (R K j U p c : ℕ) : ℕ :=
  squareRootLowPrimeCombinedFreshResponse R K j c -
    max
      (squareRootLowPrimeCombinedFreshResponse R K j (p * c))
      (squareRootLowPrimeLaterResponseCeiling R K j U p c)

@[simp] theorem card_squareRootLowPrimeTerminalNoReentrySeatIndices
    (R K j U p c : ℕ) :
    (squareRootLowPrimeTerminalNoReentrySeatIndices R K j U p c).card =
      squareRootLowPrimeTerminalNoReentryWidth R K j U p c := by
  simp [squareRootLowPrimeTerminalNoReentrySeatIndices,
    squareRootLowPrimeTerminalNoReentryWidth]

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
