import Mathlib
import RHLean.Proof.SurvivorDyadicStaticCancellation
import RHLean.Proof.SurvivorResidueCovariance

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

/-!
# Parity residue fibres are the dyadic survivor channels

For an odd upper prime `q`, the signed doubled survivor height

`q^2 - c^2`

modulo `2` records exactly the parity of the cofactor `c`:

* odd cofactors lie in residue `0`;
* even cofactors lie in residue `1`.

Thus the two residue channels used by the survivor covariance formalism are not
an auxiliary partition.  They are exactly the odd-parent and even-child channels
of the static dyadic Möbius pairing.  In particular, for an odd parent `d`, the
pair `(d, 2*d)` moves from residue `0` to residue `1` while its Möbius weight
changes sign by the already-formalized doubling law.
-/

private theorem zmod_two_natCast_eq_one_of_odd
    (n : ℕ) (hn : Odd n) :
    (n : ZMod 2) = 1 := by
  have hn' : Odd (n : ZMod 2) := hn.natCast
  rcases hn' with ⟨k, hk⟩
  simpa using hk

private theorem zmod_two_natCast_eq_zero_of_even
    (n : ℕ) (hn : Even n) :
    (n : ZMod 2) = 0 := by
  rcases hn with ⟨k, hk⟩
  rw [hk]
  push_cast
  simp [two_mul]

/-- Odd upper prime and odd cofactor give height residue `0` modulo `2`. -/
theorem survivorHeightResidue_two_eq_zero_of_odd
    (c q : ℕ) (hc : Odd c) (hq : Odd q) :
    survivorHeightResidue 2 c q = 0 := by
  have hcCast := zmod_two_natCast_eq_one_of_odd c hc
  have hqCast := zmod_two_natCast_eq_one_of_odd q hq
  unfold survivorHeightResidue survivorHeightDifference
  push_cast
  rw [hcCast, hqCast]
  norm_num

/-- Odd upper prime and even cofactor give height residue `1` modulo `2`. -/
theorem survivorHeightResidue_two_eq_one_of_even
    (c q : ℕ) (hc : Even c) (hq : Odd q) :
    survivorHeightResidue 2 c q = 1 := by
  have hcCast := zmod_two_natCast_eq_zero_of_even c hc
  have hqCast := zmod_two_natCast_eq_one_of_odd q hq
  unfold survivorHeightResidue survivorHeightDifference
  push_cast
  rw [hcCast, hqCast]
  norm_num

/-- For odd `q`, residue `0` is exactly the odd-cofactor channel. -/
theorem survivorHeightResidue_two_eq_zero_iff_odd
    (c q : ℕ) (hq : Odd q) :
    survivorHeightResidue 2 c q = 0 ↔ Odd c := by
  constructor
  · intro hzero
    by_contra hnotOdd
    have hcEven : Even c := Nat.not_odd_iff_even.mp hnotOdd
    have hone := survivorHeightResidue_two_eq_one_of_even c q hcEven hq
    have h01 : (0 : ZMod 2) = 1 := hzero.symm.trans hone
    norm_num at h01
  · intro hc
    exact survivorHeightResidue_two_eq_zero_of_odd c q hc hq

/-- For odd `q`, residue `1` is exactly the even-cofactor channel. -/
theorem survivorHeightResidue_two_eq_one_iff_even
    (c q : ℕ) (hq : Odd q) :
    survivorHeightResidue 2 c q = 1 ↔ Even c := by
  constructor
  · intro hone
    by_contra hnotEven
    have hcOdd : Odd c := Nat.not_even_iff_odd.mp hnotEven
    have hzero := survivorHeightResidue_two_eq_zero_of_odd c q hcOdd hq
    have h01 : (0 : ZMod 2) = 1 := hzero.symm.trans hone
    norm_num at h01
  · intro hc
    exact survivorHeightResidue_two_eq_one_of_even c q hc hq

/-- An odd dyadic parent and its doubled child occupy the two opposite parity
residue channels for every odd upper prime. -/
theorem survivorHeightResidue_two_dyadic_pair
    (d q : ℕ) (hd : Odd d) (hq : Odd q) :
    survivorHeightResidue 2 d q = 0 ∧
      survivorHeightResidue 2 (2 * d) q = 1 := by
  constructor
  · exact survivorHeightResidue_two_eq_zero_of_odd d q hd hq
  · exact survivorHeightResidue_two_eq_one_of_even
      (2 * d) q (even_two_mul d) hq

/-- For an odd parent, the exact dyadic signed pair crosses from the residue-0
channel to the residue-1 channel.  The signed amplitude remains the already
formalized activity difference, so parity residue and Möbius sign pairing are
one and the same two-channel geometry. -/
theorem survivorDyadicPairContribution_eq_parityChannelDifference
    (Λ : ℝ) (t q d : ℕ) (hd : Odd d) (hq : Odd q) :
    survivorHeightResidue 2 d q = 0 ∧
      survivorHeightResidue 2 (2 * d) q = 1 ∧
      survivorDyadicPairContribution Λ t q d =
        canonicalMoebiusWeight d *
          (survivorFixedPrimeActivityIndicator Λ t q (2 * d) -
            survivorFixedPrimeActivityIndicator Λ t q d) := by
  refine ⟨survivorHeightResidue_two_eq_zero_of_odd d q hd hq,
    survivorHeightResidue_two_eq_one_of_even
      (2 * d) q (even_two_mul d) hq, ?_⟩
  exact survivorDyadicPairContribution_eq_activityDifference Λ t q d hd

end RHLean.Proof
