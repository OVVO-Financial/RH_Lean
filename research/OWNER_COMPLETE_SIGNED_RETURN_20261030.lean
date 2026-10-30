import Mathlib
import «research.COVARIANCE_REMAINDER_OWNER_FUBINI»
import «research.ZERO_TARGET_SQUARE_FINITE_DIFFERENCE_REDUCTION»

/-!
# Exact signed return on the original owner fibres

A sum of squared reciprocal amplitudes is not the square of their signed sum.
All children of one fixed parent have the OPPOSITE parent sign, so their
within-fibre mixed terms reinforce. This module retains that fact and the
complete return weights, rather than treating the 79/81 diagonal estimate as
a signed scalar contraction.

No global Mertens improvement is asserted. The finite witness uses the exact
original physical remainder and owner map; it is not an arbitrary sign model.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Exact amplitude law on the actual admitted fixed-owner child fibre. -/
theorem ownerReturn_child_reciprocalAmplitude
    {W p : ℕ} {parent mn : ℕ × ℕ}
    (hmnMem : mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p) :
    postRootCovarianceReciprocalPairAmplitude mn =
      -(1 / (p : ℝ)) * postRootCovarianceReciprocalPairAmplitude parent := by
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hmnMem with ⟨hownerFilter, hparent⟩
  rcases Finset.mem_filter.mp hownerFilter with ⟨hweightFilter, howner⟩
  rcases Finset.mem_filter.mp hweightFilter with ⟨hrec, hweight⟩
  rcases Finset.mem_filter.mp hrec with ⟨hremainder, _hparentNe⟩
  have hphysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hremainder).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hphysical with
    ⟨hm1, _hmW, hn1, _hnW, hmnlt⟩
  have hmstep : realMoebiusStep m ≠ 0 := by
    intro hmzero
    exact hweight (by rw [hmzero, zero_mul])
  have hnstep : realMoebiusStep n ≠ 0 := by
    intro hnzero
    exact hweight (by rw [hnzero, mul_zero])
  have hmsq := squarefree_of_realMoebiusStep_ne_zero hmstep
  have hnsq := squarefree_of_realMoebiusStep_ne_zero hnstep
  have ha := postRootCovarianceReciprocalPairAmplitude_owner_descent
    hmsq hnsq (ne_of_lt hmnlt) (by omega) (by omega)
  dsimp only at ha
  rw [howner] at ha
  have hp' : covarianceOrderedPair
      (squarefreePrimeFamilyParent p m)
      (squarefreePrimeFamilyParent p n) = parent := by
    unfold squarefreePairFreshPrimeOrderedParent at hparent
    simpa [howner] using! hparent
  rwa [hp'] at ha

/-- Signed amplitudes in a single owner fibre add with ONE sign; the factor
is k/p, not sqrt(k/p^2) and not k/p^2. -/
theorem ownerReturn_fixedOwner_signed_sum
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
      postRootCovarianceReciprocalPairAmplitude mn) =
      -((postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
        (p : ℝ)) * postRootCovarianceReciprocalPairAmplitude parent := by
  calc
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
      postRootCovarianceReciprocalPairAmplitude mn) =
      ∑ _mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        -(1 / (p : ℝ)) * postRootCovarianceReciprocalPairAmplitude parent := by
      apply Finset.sum_congr rfl
      intro mn hmn
      exact ownerReturn_child_reciprocalAmplitude hmn
    _ = _ := by
      unfold postRootCovarianceFixedOwnerChildMultiplicity
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Exact outgoing coherent amplitude over ALL original owner primes. -/
def ownerReturnSignedReciprocalOutgoing (W : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ p ∈ primesUpTo W,
    ∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
      postRootCovarianceReciprocalPairAmplitude mn

/-- The actual harmonic multiplicity controlling coherent outgoing amplitudes. -/
def ownerReturnHarmonicMultiplicity (W : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ p ∈ primesUpTo W,
    (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) / (p : ℝ)

theorem ownerReturnSignedReciprocalOutgoing_eq
    (W : ℕ) (parent : ℕ × ℕ) :
    ownerReturnSignedReciprocalOutgoing W parent =
      -ownerReturnHarmonicMultiplicity W parent *
        postRootCovarianceReciprocalPairAmplitude parent := by
  unfold ownerReturnSignedReciprocalOutgoing ownerReturnHarmonicMultiplicity
  simp_rw [ownerReturn_fixedOwner_signed_sum]
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

/-- The exact physical inverse weight; it removes, rather than preserves,
the reciprocal p suppression. This is a source identity, not an inequality. -/
theorem ownerReturn_pair_unweight (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ((m : ℝ) * (n : ℝ)) *
      postRootCovarianceReciprocalPairAmplitude (m, n) =
        realMoebiusStep m * realMoebiusStep n := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  unfold postRootCovarianceReciprocalPairAmplitude
  dsimp only
  field_simp [hm0, hn0]

/-- A finite exact decomposition retaining all coherent cross terms, valid
for any physical family and in particular for every original owner fibre. -/
theorem ownerReturn_signed_square_eq_diagonal_add_cross
    (S : Finset (ℕ × ℕ)) :
    (∑ mn ∈ S, postRootCovarianceReciprocalPairAmplitude mn) ^ 2 =
      (∑ mn ∈ S, postRootCovarianceReciprocalPairEnergy mn) +
      ∑ mn ∈ S, ∑ uv ∈ S.erase mn,
        postRootCovarianceReciprocalPairAmplitude mn *
          postRootCovarianceReciprocalPairAmplitude uv := by
  let a := postRootCovarianceReciprocalPairAmplitude
  have hsplit (mn : ℕ × ℕ) (hmn : mn ∈ S) :
      (∑ uv ∈ S, a mn * a uv) = a mn ^ 2 +
        ∑ uv ∈ S.erase mn, a mn * a uv := by
    rw [← Finset.sum_erase_add _ _ hmn]
    ring
  change (∑ mn ∈ S, a mn) ^ 2 =
    (∑ mn ∈ S, a mn ^ 2) + ∑ mn ∈ S, ∑ uv ∈ S.erase mn, a mn * a uv
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    (∑ mn ∈ S, ∑ uv ∈ S, a mn * a uv) =
      ∑ mn ∈ S, (a mn ^ 2 + ∑ uv ∈ S.erase mn, a mn * a uv) := by
      apply Finset.sum_congr rfl
      exact hsplit
    _ = _ := Finset.sum_add_distrib

/-! ## A literal arithmetic fibre, evaluated without native compiler axioms -/

/-- Same original physical recursive carrier, with the nonzero test in integers.
The following theorem identifies it with the original real-Mobius fibre. -/
def ownerReturnIntegerParentFiber (W : ℕ) (parent : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ((postRootCovarianceRemainderRecursivePairCarrier W).filter
    (fun mn => (μ mn.1 : ℤ) * (μ mn.2 : ℤ) ≠ 0)).filter
      (fun mn => squarefreePairFreshPrimeOrderedParent mn.1 mn.2 = parent)

theorem ownerReturnIntegerParentFiber_eq_physical
    (W : ℕ) (parent : ℕ × ℕ) :
    ownerReturnIntegerParentFiber W parent =
      postRootCovarianceFixedParentChildFiber W parent := by
  ext mn
  simp only [ownerReturnIntegerParentFiber, postRootCovarianceFixedParentChildFiber,
    Finset.mem_filter, realMoebiusStep]
  have hzero :
      (((μ mn.1 : ℤ) : ℝ) * ((μ mn.2 : ℤ) : ℝ) = 0) ↔
        (μ mn.1 : ℤ) * (μ mn.2 : ℤ) = 0 := by
    exact_mod_cast (Iff.rfl :
      (μ mn.1 : ℤ) * (μ mn.2 : ℤ) = 0 ↔
        (μ mn.1 : ℤ) * (μ mn.2 : ℤ) = 0)
  rw [hzero]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- Entire actual recursive parent fibre, including every admitted owner. -/
theorem ownerReturn_parent_one_seven_at_35 :
    postRootCovarianceFixedParentChildFiber 35 (1, 7) =
      {(1, 14), (1, 21), (1, 35), (2, 7), (3, 7), (5, 7)} := by
  rw [← ownerReturnIntegerParentFiber_eq_physical]
  decide +kernel

private theorem ownerReturn_mu_values :
    (μ 1 : ℤ) = 1 ∧ (μ 2 : ℤ) = -1 ∧ (μ 3 : ℤ) = -1 ∧
    (μ 5 : ℤ) = -1 ∧ (μ 7 : ℤ) = -1 ∧ (μ 14 : ℤ) = 1 ∧
    (μ 21 : ℤ) = 1 ∧ (μ 35 : ℤ) = 1 := by
  decide +kernel

/-- Strictly contractive diagonal reciprocal energy in this actual fibre. -/
theorem ownerReturn_fibre_diagonal_energy :
    (∑ mn ∈ postRootCovarianceFixedParentChildFiber 35 (1, 7),
      postRootCovarianceReciprocalPairEnergy mn) = (361 / 22050 : ℝ) := by
  rcases ownerReturn_mu_values with ⟨h1,h2,h3,h5,h7,h14,h21,h35⟩
  rw [ownerReturn_parent_one_seven_at_35]
  norm_num [postRootCovarianceReciprocalPairEnergy,
    postRootCovarianceReciprocalPairAmplitude, realMoebiusStep,
    h1,h2,h3,h5,h7,h14,h21,h35]

/-- Coherent reciprocal amplitude, BEFORE any physical inverse weights. -/
theorem ownerReturn_fibre_signed_amplitude :
    (∑ mn ∈ postRootCovarianceFixedParentChildFiber 35 (1, 7),
      postRootCovarianceReciprocalPairAmplitude mn) = (31 / 105 : ℝ) := by
  rcases ownerReturn_mu_values with ⟨h1,h2,h3,h5,h7,h14,h21,h35⟩
  rw [ownerReturn_parent_one_seven_at_35]
  norm_num [postRootCovarianceReciprocalPairAmplitude, realMoebiusStep,
    h1,h2,h3,h5,h7,h14,h21,h35]

/-- The complete unweighted signed child mass is +6; the parent mass is -1. -/
theorem ownerReturn_fibre_unweighted_mass :
    (∑ mn ∈ postRootCovarianceFixedParentChildFiber 35 (1, 7),
      realMoebiusStep mn.1 * realMoebiusStep mn.2) = 6 := by
  rcases ownerReturn_mu_values with ⟨h1,h2,h3,h5,h7,h14,h21,h35⟩
  rw [ownerReturn_parent_one_seven_at_35]
  norm_num [realMoebiusStep,h1,h2,h3,h5,h7,h14,h21,h35]

/-- On this genuine fibre, diagonal energy contracts but the signed-square
energy expands. This does NOT refute a global cross-parent cancellation law. -/
theorem ownerReturn_actual_diagonal_contracts_but_signed_square_expands :
    (∑ mn ∈ postRootCovarianceFixedParentChildFiber 35 (1, 7),
      postRootCovarianceReciprocalPairEnergy mn) <
        postRootCovarianceReciprocalPairEnergy (1, 7) ∧
    postRootCovarianceReciprocalPairEnergy (1, 7) <
      (∑ mn ∈ postRootCovarianceFixedParentChildFiber 35 (1, 7),
        postRootCovarianceReciprocalPairAmplitude mn) ^ 2 := by
  rcases ownerReturn_mu_values with ⟨h1,_h2,_h3,_h5,h7,_h14,_h21,_h35⟩
  rw [ownerReturn_fibre_diagonal_energy, ownerReturn_fibre_signed_amplitude]
  norm_num [postRootCovarianceReciprocalPairEnergy,
    postRootCovarianceReciprocalPairAmplitude, realMoebiusStep,h1,h7]

#print axioms ownerReturnSignedReciprocalOutgoing_eq
#print axioms ownerReturn_pair_unweight
#print axioms ownerReturn_signed_square_eq_diagonal_add_cross
#print axioms ownerReturn_parent_one_seven_at_35
#print axioms ownerReturn_actual_diagonal_contracts_but_signed_square_expands

end RHLean.Proof
