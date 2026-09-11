import RHLean.Analysis.PhysicalDegreeOneHigherSquareRecurrences
import RHLean.Proof.JointDaughterCrossEnergyAudit

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# Compile-time certificates separating contact masks from recursive Mertens energy

This module is a regression guard for the physical `q^2` descent.

There are three separate facts which must not be conflated:

1. the six physical contact offsets induce explicit residue masks for `q=3,5,7`;
2. forgetting arithmetic weights and summing the two compatible tags in one
   affine daughter fibre has sharp squared `l2` synthesis factor `2`;
3. the coefficient square mass of genuine physical `q^2` daughter increments
   can be positive when their signed lower endpoint is exactly zero.

The third fact rules out any universal finite multiplicative normalization from
raw coefficient square mass to recursive Mertens endpoint energy.  Therefore
signed physical reassembly must occur before the recursive energy is formed.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-! ## The exceptional contact residues are the physical divisibility residues -/

/-- The `3^2` contact is exactly the six compiled residues modulo `9`. -/
theorem exceptionalThree_contactResidues (k : ℕ) :
    physicalSquarePrimeAtEdge k 3 ↔ k % 9 ∈ physicalNineChannelResidues :=
  physicalSquarePrimeAtEdge_three_iff k

/-- The `5^2` contact is exactly the six compiled residues modulo `25`. -/
theorem exceptionalFive_contactResidues (k : ℕ) :
    physicalSquarePrimeAtEdge k 5 ↔ k % 25 ∈ physicalTwentyFiveHitResidues :=
  physicalSquarePrimeAtEdge_five_iff k

/-- The `7^2` contact is exactly the six compiled residues modulo `49`. -/
theorem exceptionalSeven_contactResidues (k : ℕ) :
    physicalSquarePrimeAtEdge k 7 ↔ k % 49 ∈ physicalFortyNineHitResidues :=
  physicalSquarePrimeAtEdge_seven_iff k

/-- The six active offsets split into the three affine congruence pairs
`{1,5}`, `{2,6}`, `{3,7}` and no class `0 mod 4`. -/
theorem physicalTransitionActiveOffsets_mod_four_zero :
    physicalTransitionActiveOffsets.filter (fun a => a % 4 = 0) = ∅ := by
  native_decide

theorem physicalTransitionActiveOffsets_mod_four_one :
    physicalTransitionActiveOffsets.filter (fun a => a % 4 = 1) = {1, 5} := by
  native_decide

theorem physicalTransitionActiveOffsets_mod_four_two :
    physicalTransitionActiveOffsets.filter (fun a => a % 4 = 2) = {2, 6} := by
  native_decide

theorem physicalTransitionActiveOffsets_mod_four_three :
    physicalTransitionActiveOffsets.filter (fun a => a % 4 = 3) = {3, 7} := by
  native_decide

/-- For every exceptional owner, `q^2` is `1 mod 4`, so affine source
integrality has the same mod-four tag condition as the daughter index. -/
theorem exceptionalSquare_mod_four_eq_one
    {q : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) : q * q % 4 = 1 := by
  rcases hq with rfl | rfl | rfl <;> norm_num

/-! ## The full contact mask has sharp squared synthesis factor two -/

/-- Pure incidence sum on one affine daughter fibre.  This is a mask operator,
not a periodic Mobius field. -/
def fullContactFibreSum (x : ℕ → ℚ) (d : ℕ) : ℚ :=
  ∑ a ∈ physicalTransitionActiveOffsets,
    if a % 4 = d % 4 then x a else 0

/-- Coefficient square mass on the same tagged fibre. -/
def fullContactFibreTaggedEnergy (x : ℕ → ℚ) (d : ℕ) : ℚ :=
  ∑ a ∈ physicalTransitionActiveOffsets,
    if a % 4 = d % 4 then (x a) ^ 2 else 0

/-- Every full affine fibre has at most two tags, hence the squared synthesis
factor is at most `2`. -/
theorem fullContactFibreSum_sq_le_two_taggedEnergy
    (x : ℕ → ℚ) (d : ℕ) :
    (fullContactFibreSum x d) ^ 2 ≤
      2 * fullContactFibreTaggedEnergy x d := by
  have hmod : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
    omega
  rcases hmod with h0 | h1 | h2 | h3
  · simp [fullContactFibreSum, fullContactFibreTaggedEnergy,
      physicalTransitionActiveOffsets, h0]
  · simp [fullContactFibreSum, fullContactFibreTaggedEnergy,
      physicalTransitionActiveOffsets, h1]
    nlinarith [sq_nonneg (x 1 - x 5)]
  · simp [fullContactFibreSum, fullContactFibreTaggedEnergy,
      physicalTransitionActiveOffsets, h2]
    nlinarith [sq_nonneg (x 2 - x 6)]
  · simp [fullContactFibreSum, fullContactFibreTaggedEnergy,
      physicalTransitionActiveOffsets, h3]
    nlinarith [sq_nonneg (x 3 - x 7)]

/-- Deleting arbitrary tags, as least-owner restriction can do, cannot increase
the universal squared synthesis factor beyond `2`. -/
theorem restrictedContactFibreSum_sq_le_two_taggedEnergy
    (keep : Finset ℕ) (x : ℕ → ℚ) (d : ℕ) :
    (fullContactFibreSum (fun a => if a ∈ keep then x a else 0) d) ^ 2 ≤
      2 * fullContactFibreTaggedEnergy
        (fun a => if a ∈ keep then x a else 0) d :=
  fullContactFibreSum_sq_le_two_taggedEnergy
    (fun a => if a ∈ keep then x a else 0) d

/-- A two-tag equal-amplitude fibre attains factor `2`. -/
def fullContactFactorTwoWitness (a : ℕ) : ℚ :=
  if a = 1 ∨ a = 5 then 1 else 0

theorem fullContactFactorTwoWitness_energy :
    fullContactFibreTaggedEnergy fullContactFactorTwoWitness 1 = 2 := by
  native_decide

theorem fullContactFactorTwoWitness_sum :
    fullContactFibreSum fullContactFactorTwoWitness 1 = 2 := by
  native_decide

/-- Squared operator factor `2`, expressed without introducing an artificial
finite-torus Mobius vector: the factor-two bound is universal and is attained. -/
theorem fullContactFibre_squaredSynthesisFactor_two_sharp :
    (∀ (x : ℕ → ℚ) (d : ℕ),
      (fullContactFibreSum x d) ^ 2 ≤
        2 * fullContactFibreTaggedEnergy x d) ∧
    0 < fullContactFibreTaggedEnergy fullContactFactorTwoWitness 1 ∧
    (fullContactFibreSum fullContactFactorTwoWitness 1) ^ 2 =
      2 * fullContactFibreTaggedEnergy fullContactFactorTwoWitness 1 := by
  refine ⟨fullContactFibreSum_sq_le_two_taggedEnergy, ?_, ?_⟩
  · rw [fullContactFactorTwoWitness_energy]
    norm_num
  · rw [fullContactFactorTwoWitness_energy, fullContactFactorTwoWitness_sum]
    norm_num

/-! ## Positive coefficient square mass at a zero signed Mertens endpoint -/

/-- Unsigned coefficient square mass of the genuine coefficient-level physical
`q^2` daughter increments. -/
def physicalQ2DaughterPrefixCoefficientEnergy (q K : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, (physicalQ2DaughterCellIncrement q k) ^ 2

/-- The signed lower endpoint reached by the same consecutive physical
increments.  It is deliberately a signed prefix, not a coefficient norm. -/
def physicalQ2DaughterLowerEndpoint (q K : ℕ) : ℤ :=
  moebiusPositivePrefix (4 * K / (q * q))

/-- At `q=3`, the first five physical cells descend to lower cutoff `2`, whose
Mertens value is zero. -/
theorem physicalQ2DaughterLowerEndpoint_three_five_eq_zero :
    physicalQ2DaughterLowerEndpoint 3 5 = 0 := by
  native_decide

/-- The corresponding genuine coefficient square mass is nevertheless `2`. -/
theorem physicalQ2DaughterPrefixCoefficientEnergy_three_five_eq_two :
    physicalQ2DaughterPrefixCoefficientEnergy 3 5 = 2 := by
  native_decide

/-- The physical coefficient increments themselves reassemble with signs to the
same zero endpoint at this finite witness. -/
theorem physicalQ2DaughterPrefix_signedSum_three_five_eq_zero :
    (∑ k ∈ Finset.range 5, physicalQ2DaughterCellIncrement 3 k) = 0 := by
  native_decide

/-- **No coefficient-energy normalization into recursive Mertens energy.**
There is no finite rational multiplier that can bound all genuine physical
coefficient square masses by the square of their signed lower endpoint. -/
theorem no_universal_coefficientEnergy_le_lowerEndpoint_sq :
    ¬ ∃ α : ℚ, ∀ q K : ℕ,
      (physicalQ2DaughterPrefixCoefficientEnergy q K : ℚ) ≤
        α * (physicalQ2DaughterLowerEndpoint q K : ℚ) ^ 2 := by
  rintro ⟨α, hα⟩
  have h := hα 3 5
  rw [physicalQ2DaughterPrefixCoefficientEnergy_three_five_eq_two,
    physicalQ2DaughterLowerEndpoint_three_five_eq_zero] at h
  norm_num at h

end RHLean.Proof
