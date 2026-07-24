import Mathlib
import RHLean.Analysis.ActualResidualDecomposition
import RHLean.Proof.NormalizedCofactorExpansion

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Convert one ordered factor pair into the cofactor-channel type used by the residual layer. -/
def actualChannelOfPair (p : ℕ × ℕ) : RHLean.Analysis.ActualCofactorChannel where
  lowerCofactor := p.1
  upperFactor := p.2

@[simp] theorem actualChannelOfPair_lowerCofactor (p : ℕ × ℕ) :
    (actualChannelOfPair p).lowerCofactor = p.1 := by
  rfl

@[simp] theorem actualChannelOfPair_upperFactor (p : ℕ × ℕ) :
    (actualChannelOfPair p).upperFactor = p.2 := by
  rfl

/--
The coefficient left after removing the lower-cofactor Möbius factor already
supplied by `actualResidualEntry`.
-/
def normalizedChannelAmplitudeRat
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℚ :=
  alphaWeightRat (channel.lowerCofactor * channel.upperFactor) *
    (((μ channel.upperFactor : ℤ) : ℚ))

/-- Complex cast of the normalized channel amplitude for residual synthesis. -/
def normalizedChannelAmplitude
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  (normalizedChannelAmplitudeRat channel : ℂ)

/--
The full normalized arithmetic contribution in the same convention as
`actualResidualEntry`: lower Möbius factor times the remaining amplitude.
-/
def normalizedChannelValue
    (channel : RHLean.Analysis.ActualCofactorChannel) : ℂ :=
  (((μ channel.lowerCofactor : ℤ) : ℂ)) *
    normalizedChannelAmplitude channel

/-- The residual-layer coefficient split exactly recovers the normalized rational weight. -/
theorem lowerMoebius_mul_normalizedChannelAmplitudeRat (c q : ℕ) :
    (((μ c : ℤ) : ℚ)) *
        normalizedChannelAmplitudeRat (actualChannelOfPair (c, q)) =
      normalizedCofactorWeightRat c q := by
  unfold normalizedChannelAmplitudeRat normalizedCofactorWeightRat
  ring

/-- The cofactor-channel value of an ordered pair is exactly its normalized complex weight. -/
@[simp] theorem normalizedChannelValue_actualChannelOfPair (p : ℕ × ℕ) :
    normalizedChannelValue (actualChannelOfPair p) =
      normalizedCofactorWeight p.1 p.2 := by
  rcases p with ⟨c, q⟩
  unfold normalizedChannelValue normalizedChannelAmplitude
  unfold normalizedChannelAmplitudeRat normalizedCofactorWeight
  push_cast
  exact_mod_cast lowerMoebius_mul_normalizedChannelAmplitudeRat c q

/--
The normalized fiber expansion at the exact complete-square endpoint is the
concrete square-prefix Mertens value.
-/
theorem normalizedFiberExpansion_squarePrefix (n : ℕ) :
    ((normalizedFiberExpansionRat
        (RHLean.Analysis.squarePrefixEndpoint n) : ℚ) : ℂ) =
      RHLean.Analysis.squarePrefixMertens n := by
  simpa [RHLean.Analysis.squarePrefixMertens] using
    normalizedFiberExpansion_cast_eq_mertens
      (RHLean.Analysis.squarePrefixEndpoint n)

/-- The exact normalized cofactor-channel sum at the square-prefix endpoint. -/
def squarePrefixNormalizedChannelSum (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (RHLean.Analysis.squarePrefixEndpoint n + 1),
    ∑ p ∈ orderedCoprimeFactorPairs m,
      normalizedChannelValue (actualChannelOfPair p)

/--
Exact recombination of the concrete square-prefix Mertens value from normalized
ordered cofactor channels. No shell, mode, packet, or high/low realization is
asserted here.
-/
theorem squarePrefixNormalizedChannelSum_eq_mertens (n : ℕ) :
    squarePrefixNormalizedChannelSum n =
      RHLean.Analysis.squarePrefixMertens n := by
  rw [← normalizedFiberExpansion_squarePrefix n]
  unfold squarePrefixNormalizedChannelSum normalizedFiberExpansionRat
  push_cast
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro p _
  simpa [normalizedCofactorWeight] using
    normalizedChannelValue_actualChannelOfPair p

/-- Symmetric form of the exact concrete cofactor-channel recombination. -/
theorem squarePrefixMertens_eq_normalizedChannelSum (n : ℕ) :
    RHLean.Analysis.squarePrefixMertens n =
      squarePrefixNormalizedChannelSum n := by
  exact (squarePrefixNormalizedChannelSum_eq_mertens n).symm

end RHLean.Proof
