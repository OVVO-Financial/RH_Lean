import Mathlib
import «research.VF_MID_INTEGER_BLOCK_CAPTURE»

/-!
# Literal VF-mid square-block crossing

This file formalizes the geometry visible in the VF/prime-count plot.

For the R-th square block let

  K_R = floor(vfMidFinishedMass R).

The purple horizontal block level is literally crossed by the prime-counting
staircase exactly when there is an integer x in [R^2,(R+1)^2] with

  pi(x) = K_R.

Because prime counting is monotone and can increase by at most one at each
integer step, this literal crossing is equivalent to the existing endpoint
capture sandwich

  pi(R^2) <= K_R <= pi((R+1)^2).

No prime-distribution estimate is used in this equivalence.
-/

noncomputable section

namespace RHLean.Analysis

/-- Literal plot-level crossing: the integer VF-mid level is actually attained
by the prime-counting staircase somewhere inside its own square block. -/
def VFMidIntegerBlockCrossed (R : ℕ) : Prop :=
  ∃ x : ℕ,
    R ^ 2 ≤ x ∧
    x ≤ (R + 1) ^ 2 ∧
    Nat.primeCounting x = vfMidIntegerBlockLevel R

/-- Endpoint capture forces an actual crossing of the horizontal integer VF
level by the monotone prime-counting staircase inside the same square block. -/
theorem vfMidIntegerBlockCrossed_of_captured
    (R : ℕ) (hcap : VFMidIntegerBlockCaptured R) :
    VFMidIntegerBlockCrossed R := by
  rcases hcap with ⟨hlow, hupp⟩
  by_cases hleft :
      Nat.primeCounting (R ^ 2) = vfMidIntegerBlockLevel R
  · refine ⟨R ^ 2, le_rfl, ?_, hleft⟩
    exact Nat.pow_le_pow_left (by omega) 2
  · have hleftlt :
        Nat.primeCounting (R ^ 2) < vfMidIntegerBlockLevel R := by
      omega
    let P : ℕ → Prop :=
      fun x => vfMidIntegerBlockLevel R ≤ Nat.primeCounting x
    have hex : ∃ x : ℕ, P x :=
      ⟨(R + 1) ^ 2, hupp⟩
    let x : ℕ := Nat.find hex
    have hxP : P x := Nat.find_spec hex
    have hxupper : x ≤ (R + 1) ^ 2 :=
      Nat.find_min' hex hupp
    have hxlower : R ^ 2 < x := by
      by_contra hnot
      have hxle : x ≤ R ^ 2 := le_of_not_gt hnot
      have hmono :=
        Nat.monotone_primeCounting hxle
      dsimp [P] at hxP
      omega
    have hxpos : 0 < x := by omega
    have hprev :
        Nat.primeCounting (x - 1) < vfMidIntegerBlockLevel R := by
      by_contra hnot
      have hPprev : P (x - 1) := by
        dsimp [P]
        omega
      have hmin := Nat.find_min' hex hPprev
      have hbad : x ≤ x - 1 := by
        simpa [x] using hmin
      omega
    have hstep :=
      vfMid_primeCounting_add_le (x - 1) 1
    have hpredsucc : x - 1 + 1 = x := by omega
    rw [hpredsucc] at hstep
    dsimp [P] at hxP
    have hxeq :
        Nat.primeCounting x = vfMidIntegerBlockLevel R := by
      omega
    exact ⟨x, hxlower.le, hxupper, hxeq⟩

/-- A literal crossing inside the square block immediately gives the endpoint
capture sandwich by monotonicity of prime counting. -/
theorem vfMidIntegerBlockCaptured_of_crossed
    (R : ℕ) (hcross : VFMidIntegerBlockCrossed R) :
    VFMidIntegerBlockCaptured R := by
  rcases hcross with ⟨x, hxlow, hxhigh, hxeq⟩
  constructor
  · have hmono :=
      Nat.monotone_primeCounting hxlow
    rw [hxeq] at hmono
    exact hmono
  · have hmono :=
      Nat.monotone_primeCounting hxhigh
    rw [hxeq] at hmono
    exact hmono

/-- **Exact plot theorem.**  The purple VF square-block level intersects the
red prime-counting staircase in its own block if and only if the already
formalized endpoint capture sandwich holds. -/
theorem vfMidIntegerBlockCrossed_iff_captured (R : ℕ) :
    VFMidIntegerBlockCrossed R ↔ VFMidIntegerBlockCaptured R := by
  constructor
  · exact vfMidIntegerBlockCaptured_of_crossed R
  · exact vfMidIntegerBlockCrossed_of_captured R

/-- Universal literal square-block crossing statement. -/
def VFMidIntegerBlockCrossingStatement : Prop :=
  ∀ R : ℕ, 2 ≤ R → VFMidIntegerBlockCrossed R

/-- Universal plot crossing is exactly universal integer-block capture. -/
theorem vfMidIntegerBlockCrossingStatement_iff_captureStatement :
    VFMidIntegerBlockCrossingStatement ↔ VFMidIntegerBlockCaptureStatement := by
  constructor
  · intro hcross R hR
    exact vfMidIntegerBlockCaptured_of_crossed R (hcross R hR)
  · intro hcap R hR
    exact vfMidIntegerBlockCrossed_of_captured R (hcap R hR)

/-- Hence proving the literal plot-crossing statement closes the existing
von-Koch/RH consumer with no additional analytic work. -/
theorem riemannHypothesis_of_vfMidIntegerBlockCrossing
    (criterion : ClassicalVonKochRHCriterion)
    (hcross : VFMidIntegerBlockCrossingStatement) :
    VFMidRiemannHypothesisStatement := by
  apply riemannHypothesis_of_vfMidIntegerBlockCapture criterion
  exact
    vfMidIntegerBlockCrossingStatement_iff_captureStatement.mp hcross


/-! ## Explicit prime-count envelope reduction

A convenient sufficient condition for literal block crossing is to sandwich the
true prime-counting staircase between deterministic integer-valued envelopes
`L` and `U`, then place the VF level between the two envelopes at the square
endpoints.  This is exactly the rigorous version of the proposed
`U(R^2) <= K_R <= L((R+1)^2)` attack.
-/

/-- A pointwise deterministic lower envelope for the prime-counting function. -/
def PrimeCountingLowerEnvelope (L : ℕ → ℕ) : Prop :=
  ∀ x : ℕ, L x ≤ Nat.primeCounting x

/-- A pointwise deterministic upper envelope for the prime-counting function. -/
def PrimeCountingUpperEnvelope (U : ℕ → ℕ) : Prop :=
  ∀ x : ℕ, Nat.primeCounting x ≤ U x

/-- If a valid upper envelope lies below the VF level at the left square and a
valid lower envelope lies above the VF level at the right square, then the VF
integer level is captured by that square block. -/
theorem vfMidIntegerBlockCaptured_of_primeCount_envelopes
    (L U : ℕ → ℕ)
    (hL : PrimeCountingLowerEnvelope L)
    (hU : PrimeCountingUpperEnvelope U)
    (R : ℕ)
    (hleft : U (R ^ 2) ≤ vfMidIntegerBlockLevel R)
    (hright : vfMidIntegerBlockLevel R ≤ L ((R + 1) ^ 2)) :
    VFMidIntegerBlockCaptured R := by
  constructor
  · exact le_trans (hU (R ^ 2)) hleft
  · exact le_trans hright (hL ((R + 1) ^ 2))

/-- The same envelope certificate forces the literal prime-staircase crossing
inside the square block. -/
theorem vfMidIntegerBlockCrossed_of_primeCount_envelopes
    (L U : ℕ → ℕ)
    (hL : PrimeCountingLowerEnvelope L)
    (hU : PrimeCountingUpperEnvelope U)
    (R : ℕ)
    (hleft : U (R ^ 2) ≤ vfMidIntegerBlockLevel R)
    (hright : vfMidIntegerBlockLevel R ≤ L ((R + 1) ^ 2)) :
    VFMidIntegerBlockCrossed R :=
  vfMidIntegerBlockCrossed_of_captured R
    (vfMidIntegerBlockCaptured_of_primeCount_envelopes
      L U hL hU R hleft hright)

end RHLean.Analysis
