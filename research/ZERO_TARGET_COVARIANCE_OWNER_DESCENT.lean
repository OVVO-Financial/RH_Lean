import Mathlib
import RHLean.Proof.EndpointCubeAnalyticClosure
import «research.ZERO_TARGET_PARTIAL_MOMENT_COVARIANCE»

/-!
# Zero-target partial moments on the exact covariance owner descent

`EndpointCubeAnalyticClosure` already proves a triangular descent for every
nonzero pair in the literal post-root covariance remainder:

* the canonical owner-parent remains on the same physical remainder carrier;
* the owner strictly increases and the separation rank drops by one;
* the Möbius pair weight reverses sign exactly;
* equal-parent terminal pairs are nonpositive;
* aggregate descent retains the exact child multiplicity of each parent.

The zero-target partial-moment decomposition gives that sign reversal a direct
sector meaning.  Writing

  excess(x,y) = coPartial_0(x,y) - divergent_0(x,y),

we have `excess(x,y)=x*y`.  Hence every recursive owner step reverses the
zero-target excess exactly.  The full scalar remainder is therefore a
nonpositive terminal population minus the multiplicity-weighted parent excess.

No norm, absolute value, mean centering, multiplicity bound, RH assumption, or
Mertens estimate appears here.  The final upper bound deliberately leaves the
child multiplicity visible: this is the precise quantity that a later q^-2
owner-scale theorem must absorb rather than replace by unsigned counting.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Zero-target co-partial excess of one real pair. -/
def zeroTargetPairExcess (x y : ℝ) : ℝ :=
  zeroTargetCoPartialPair x y - zeroTargetDivergentPair x y

@[simp] theorem zeroTargetPairExcess_eq_mul (x y : ℝ) :
    zeroTargetPairExcess x y = x * y := by
  exact zeroTargetCoPartial_sub_divergent_eq_mul x y

/-- Zero-target excess of one physical Möbius pair. -/
def postRootZeroTargetPairExcess (mn : ℕ × ℕ) : ℝ :=
  zeroTargetPairExcess (realMoebiusStep mn.1) (realMoebiusStep mn.2)

@[simp] theorem postRootZeroTargetPairExcess_eq_weight (mn : ℕ × ℕ) :
    postRootZeroTargetPairExcess mn =
      realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  simp [postRootZeroTargetPairExcess]

/-- **Recursive owner descent swaps zero-target sector excess exactly.**
The old pair and its ordered parent carry opposite `co - divergent` mass. -/
theorem postRootCovarianceRemainderRecursivePair_zeroTargetExcess_owner_descent
    {W m n : ℕ}
    (hpair : (m, n) ∈ postRootCovarianceRemainderRecursivePairCarrier W)
    (hweight : realMoebiusStep m * realMoebiusStep n ≠ 0) :
    let parent := squarefreePairFreshPrimeOrderedParent m n
    postRootZeroTargetPairExcess (m, n) =
      -postRootZeroTargetPairExcess parent := by
  have hdesc :=
    postRootCovarianceRemainderRecursivePair_owner_descent hpair hweight
  dsimp only at hdesc ⊢
  simpa using hdesc.2.2.2

/-- Every equal-parent terminal pair is on the helpful/nonpositive side of the
zero-target co-minus-divergent decomposition. -/
theorem postRootCovarianceRemainderTerminalPair_zeroTargetExcess_nonpos
    {W : ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈ postRootCovarianceRemainderTerminalPairCarrier W) :
    postRootZeroTargetPairExcess mn ≤ 0 := by
  rw [postRootZeroTargetPairExcess_eq_weight]
  exact postRootCovarianceRemainderTerminalPair_weight_nonpos hmn

/-- The whole terminal zero-target excess is nonpositive. -/
theorem sum_postRootCovarianceRemainderTerminalPair_zeroTargetExcess_nonpos
    (W : ℕ) :
    (∑ mn ∈ postRootCovarianceRemainderTerminalPairCarrier W,
      postRootZeroTargetPairExcess mn) ≤ 0 := by
  apply Finset.sum_nonpos
  intro mn hmn
  exact postRootCovarianceRemainderTerminalPair_zeroTargetExcess_nonpos hmn

/-- **Aggregate zero-target owner descent with exact child multiplicities.**
This is the existing signed owner descent rewritten without changing carrier or
coefficient. -/
theorem sum_postRootCovarianceRemainderRecursive_zeroTargetExcess_eq_neg_parentMultiplicity
    (W : ℕ) :
    (∑ mn ∈ postRootCovarianceRemainderRecursivePairCarrier W,
      postRootZeroTargetPairExcess mn) =
      -∑ parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
        (postRootCovarianceRemainderOwnerChildMultiplicity W parent : ℝ) *
          postRootZeroTargetPairExcess parent := by
  simpa using sum_postRootCovarianceRemainderRecursive_eq_neg_parentMultiplicity W

/-- **Exact remainder in zero-target currency.**  The physical covariance
remainder is a nonpositive terminal excess minus the multiplicity-weighted
parent excess. -/
theorem postRootCovarianceRemainder_eq_terminalZeroTarget_sub_parentMultiplicity
    (W : ℕ) :
    postRootCovarianceRemainder W =
      (∑ mn ∈ postRootCovarianceRemainderTerminalPairCarrier W,
        postRootZeroTargetPairExcess mn) -
      ∑ parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
        (postRootCovarianceRemainderOwnerChildMultiplicity W parent : ℝ) *
          postRootZeroTargetPairExcess parent := by
  simpa using postRootCovarianceRemainder_eq_terminal_sub_parentMultiplicity W

/-- **One-sided zero-target reduction.**  Terminal pairs can only help, so every
positive remainder is forced by multiplicity-weighted reversal of the parent
zero-target excess.  No unsigned multiplicity estimate has been inserted. -/
theorem postRootCovarianceRemainder_le_neg_parentMultiplicityZeroTargetExcess
    (W : ℕ) :
    postRootCovarianceRemainder W ≤
      -∑ parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
        (postRootCovarianceRemainderOwnerChildMultiplicity W parent : ℝ) *
          postRootZeroTargetPairExcess parent := by
  rw [postRootCovarianceRemainder_eq_terminalZeroTarget_sub_parentMultiplicity]
  have hterminal :=
    sum_postRootCovarianceRemainderTerminalPair_zeroTargetExcess_nonpos W
  linarith

/-- Same one-sided reduction with the NNS sectors displayed explicitly:
positive covariance can only come from multiplicity-weighted
`divergent_0 - coPartial_0` parent mass. -/
theorem postRootCovarianceRemainder_le_parentMultiplicity_divergent_sub_coPartial
    (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ∑ parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
        (postRootCovarianceRemainderOwnerChildMultiplicity W parent : ℝ) *
          (zeroTargetDivergentPair
              (realMoebiusStep parent.1) (realMoebiusStep parent.2) -
            zeroTargetCoPartialPair
              (realMoebiusStep parent.1) (realMoebiusStep parent.2)) := by
  have h :=
    postRootCovarianceRemainder_le_neg_parentMultiplicityZeroTargetExcess W
  calc
    postRootCovarianceRemainder W ≤
        -∑ parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
          (postRootCovarianceRemainderOwnerChildMultiplicity W parent : ℝ) *
            postRootZeroTargetPairExcess parent := h
    _ = ∑ parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
          (postRootCovarianceRemainderOwnerChildMultiplicity W parent : ℝ) *
            (zeroTargetDivergentPair
                (realMoebiusStep parent.1) (realMoebiusStep parent.2) -
              zeroTargetCoPartialPair
                (realMoebiusStep parent.1) (realMoebiusStep parent.2)) := by
      symm
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro parent _hparent
      unfold postRootZeroTargetPairExcess zeroTargetPairExcess
      ring

end RHLean.Proof
