import Mathlib
import RHLean.Proof.PrimeCombVisualizationRecurrence
import «research.VF_919_OAI_POLARIZED_EULER_BRIDGE_20261021»

/-!
# One simultaneous chronological prime-wheel / OAI-Hecke NNS payment ledger

This theorem displays TWO proven operations SIDE BY SIDE:
1. actual primeComb integer-frame insertion, with all square kills / flips;
2. original phase-correct Hecke Euler pair, retaining theta=chi(p).

They share the identical real unnormalized zero-target Co/Div polarization,
but the rational integers and Hecke ideals are NOT declared identical.
The actual OAI source-coefficient lift and its analytic power saving remain
separate and are NOT axioms of this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- The real unnormalized NNS cross term for two signed scalar increments. -/
def vf919WheelOAIAligned (s d : ℝ) : ℝ :=
  max s 0 * max d 0 + max (-s) 0 * max (-d) 0

def vf919WheelOAIDivergent (s d : ℝ) : ℝ :=
  max s 0 * max (-d) 0 + max (-s) 0 * max d 0

theorem vf919WheelOAIAligned_sub_divergent (s d : ℝ) :
    vf919WheelOAIAligned s d - vf919WheelOAIDivergent s d = s * d := by
  exact vf919Polar_signed_quadrants s d

/-- Every integer prime-wheel insertion has the exact signed NNS energy
increment, including the negative mixed Co/Div cross term. -/
theorem vf919WheelOAIPrimeStage_energy
    (S : Finset ℕ) (p X : ℕ) (hp : p.Prime)
    (hSprime : ∀ q ∈ S, q.Prime)
    (hSlt : ∀ q ∈ S, q < p) :
    let old : ℝ := (RHLean.Proof.primeCombFramePrefixMass S X : ℝ)
    let d : ℝ :=
      - (RHLean.Proof.primeCombFrameKillChannelMass S p X : ℝ) -
        2 * (RHLean.Proof.primeCombFrameFlipChannelMass S p X : ℝ)
    (RHLean.Proof.primeCombFramePrefixMass (insert p S) X : ℝ) ^ 2 =
      old ^ 2 +
        2 * (vf919WheelOAIAligned old d -
          vf919WheelOAIDivergent old d) + d ^ 2 := by
  dsimp
  have h := RHLean.Proof.primeCombFramePrefixMass_insert_eq_old_sub_channels
    S p X hp hSprime hSlt
  have hreal :
      (RHLean.Proof.primeCombFramePrefixMass (insert p S) X : ℝ) =
      (RHLean.Proof.primeCombFramePrefixMass S X : ℝ) -
      (RHLean.Proof.primeCombFrameKillChannelMass S p X : ℝ) -
        2 * (RHLean.Proof.primeCombFrameFlipChannelMass S p X : ℝ) := by
    exact_mod_cast h
  rw [hreal]
  rw [vf919WheelOAIAligned_sub_divergent]
  ring

/-- The OAI local Euler pair is the PHASE-CORRECT marked-minus-rescaled
operation; the phase theta is not silently converted into Mobius -1. -/
theorem vf919WheelOAIHeckeStage_phase
    (chi theta aT aTp : ℂ) :
    chi * aT - (chi * theta) * aTp =
      chi * (aT - theta * aTp) :=
  vf919Polar_character_toggle chi theta aT aTp

/-- Same native finite NNS payment for the two real Phi coordinates of
a phase-correct matched pair. This is NOT a source-specific moment bound. -/
theorem vf919WheelOAIHeckePair_realNNS
    (ax ay bx byCoord : ℝ) :
    ((ax-bx)^2+(ay-byCoord)^2)/2 =
      (ax^2+ay^2+bx^2+byCoord^2)/2 -
      ((vf919WheelOAIAligned ax bx - vf919WheelOAIDivergent ax bx) +
       (vf919WheelOAIAligned ay byCoord - vf919WheelOAIDivergent ay byCoord)) := by
  rw [vf919WheelOAIAligned_sub_divergent,
      vf919WheelOAIAligned_sub_divergent]
  ring

/-- A single certified snapshot records wheel chronology and OAI phase
transport SIMULTANEOUSLY. Two source populations are not equated. -/
theorem vf919WheelOAIStage_sideBySide
    (S : Finset ℕ) (p X : ℕ) (hp : p.Prime)
    (hSprime : ∀ q ∈ S, q.Prime)
    (hSlt : ∀ q ∈ S, q < p)
    (chi theta aT aTp : ℂ) :
    (RHLean.Proof.primeCombFramePrefixMass (insert p S) X =
      RHLean.Proof.primeCombFramePrefixMass S X -
        RHLean.Proof.primeCombFrameKillChannelMass S p X -
          2 * RHLean.Proof.primeCombFrameFlipChannelMass S p X) ∧
    (chi*aT - (chi*theta)*aTp = chi*(aT-theta*aTp)) := by
  constructor
  · exact RHLean.Proof.primeCombFramePrefixMass_insert_eq_old_sub_channels
      S p X hp hSprime hSlt
  · exact vf919WheelOAIHeckeStage_phase chi theta aT aTp

end RHLean.Analysis

#print axioms RHLean.Analysis.vf919WheelOAIPrimeStage_energy
#print axioms RHLean.Analysis.vf919WheelOAIHeckePair_realNNS
#print axioms RHLean.Analysis.vf919WheelOAIStage_sideBySide
