import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNATURE_PAIR_SUCCESSOR»

/-!
# Pair-energy realization of the prime-signature filtration

The signature energy is the ordered Gram sum over pairs that agree on all prime
coordinates below the current boundary prime.  After revealing the current
prime `p`, the split energy is the same ordered Gram restricted to pairs that
also agree on p-divisibility.

For consecutive primes `p < r`, the preceding module identifies that split
pair carrier with the next signature pair carrier.  Consequently

  SignatureEnergy(R,p)
    = SignatureEnergy(R,r) + 2 * sum_sig FirstOwnerCellGram(R,p,sig).

Thus the first-owner Gram is literally one energy decrement of a nested finite
prime filtration.  No inequality is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Square of one signature-cell amplitude as an ordered pair sum. -/
theorem lowOwnerFirstOwnerSignatureCellAmplitude_sq_eq_pairSum
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerSignatureCellAmplitude R p sig ^ 2 =
      ∑ mn ∈ (lowOwnerFirstOwnerSignatureCellCarrier R p sig).product
          (lowOwnerFirstOwnerSignatureCellCarrier R p sig),
        lowOwnerZeroFrequencyMobiusSite R mn.1 *
          lowOwnerZeroFrequencyMobiusSite R mn.2 := by
  unfold lowOwnerFirstOwnerSignatureCellAmplitude
  calc
    (∑ n ∈ lowOwnerFirstOwnerSignatureCellCarrier R p sig,
        lowOwnerZeroFrequencyMobiusSite R n) ^ 2 =
      (∑ m ∈ lowOwnerFirstOwnerSignatureCellCarrier R p sig,
        lowOwnerZeroFrequencyMobiusSite R m) *
      (∑ n ∈ lowOwnerFirstOwnerSignatureCellCarrier R p sig,
        lowOwnerZeroFrequencyMobiusSite R n) := by ring
    _ = ∑ m ∈ lowOwnerFirstOwnerSignatureCellCarrier R p sig,
        ∑ n ∈ lowOwnerFirstOwnerSignatureCellCarrier R p sig,
          lowOwnerZeroFrequencyMobiusSite R m *
            lowOwnerZeroFrequencyMobiusSite R n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.mul_sum]
    _ = _ := by
      symm
      simpa only using
        (Finset.sum_product
          (s := lowOwnerFirstOwnerSignatureCellCarrier R p sig)
          (t := lowOwnerFirstOwnerSignatureCellCarrier R p sig)
          (f := fun mn : ℕ × ℕ =>
            lowOwnerZeroFrequencyMobiusSite R mn.1 *
              lowOwnerZeroFrequencyMobiusSite R mn.2))

/-- One signature fibre of the global signature-pair carrier is exactly the
Cartesian square of that signature cell. -/
theorem lowOwnerSignaturePairCarrier_filter_signature_eq_cellProduct
    (R p : ℕ) (sig : Finset ℕ) :
    (lowOwnerSignaturePairCarrier R p).filter
        (fun mn => squarefreeLowerPrimeSignature p mn.1 = sig) =
      (lowOwnerFirstOwnerSignatureCellCarrier R p sig).product
        (lowOwnerFirstOwnerSignatureCellCarrier R p sig) := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hpair, hmSig⟩
    rcases Finset.mem_filter.mp hpair with ⟨hprod, hsame⟩
    rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
    have hnSig : squarefreeLowerPrimeSignature p n = sig := by
      rw [← hsame, hmSig]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hmCar, hmSig⟩,
        Finset.mem_filter.mpr ⟨hnCar, hnSig⟩⟩
  · intro hmn
    rcases Finset.mem_product.mp hmn with ⟨hmCell, hnCell⟩
    rcases Finset.mem_filter.mp hmCell with ⟨hmCar, hmSig⟩
    rcases Finset.mem_filter.mp hnCell with ⟨hnCar, hnSig⟩
    have hsame : squarefreeLowerPrimeSignature p m =
        squarefreeLowerPrimeSignature p n := by rw [hmSig, hnSig]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hmCar, hnCar⟩, hsame⟩,
        hmSig⟩

/-- **Signature energy is exactly the Gram on its pair carrier.** -/
theorem lowOwnerFirstOwnerSignatureEnergy_eq_pairCarrier
    (R p : ℕ) :
    lowOwnerFirstOwnerSignatureEnergy R p =
      ∑ mn ∈ lowOwnerSignaturePairCarrier R p,
        lowOwnerZeroFrequencyMobiusSite R mn.1 *
          lowOwnerZeroFrequencyMobiusSite R mn.2 := by
  let S := lowOwnerSignaturePairCarrier R p
  let T := lowOwnerFirstOwnerSignatureSet R p
  let g : ℕ × ℕ → Finset ℕ := fun mn =>
    squarefreeLowerPrimeSignature p mn.1
  let f : ℕ × ℕ → ℝ := fun mn =>
    lowOwnerZeroFrequencyMobiusSite R mn.1 *
      lowOwnerZeroFrequencyMobiusSite R mn.2
  have hmaps : ∀ mn ∈ S, g mn ∈ T := by
    intro mn hmn
    have hprod := (Finset.mem_filter.mp hmn).1
    have hmCar := (Finset.mem_product.mp hprod).1
    exact Finset.mem_image.mpr ⟨mn.1, hmCar, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmaps f
  unfold lowOwnerFirstOwnerSignatureEnergy
  calc
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignatureCellAmplitude R p sig ^ 2) =
      ∑ sig ∈ T,
        ∑ mn ∈ (lowOwnerFirstOwnerSignatureCellCarrier R p sig).product
            (lowOwnerFirstOwnerSignatureCellCarrier R p sig), f mn := by
          apply Finset.sum_congr rfl
          intro sig _hsig
          exact lowOwnerFirstOwnerSignatureCellAmplitude_sq_eq_pairSum R p sig
    _ = ∑ sig ∈ T,
        ∑ mn ∈ S with g mn = sig, f mn := by
          apply Finset.sum_congr rfl
          intro sig _hsig
          have hset :=
            lowOwnerSignaturePairCarrier_filter_signature_eq_cellProduct
              R p sig
          change
            (∑ mn ∈ (lowOwnerFirstOwnerSignatureCellCarrier R p sig).product
                (lowOwnerFirstOwnerSignatureCellCarrier R p sig), f mn) =
              ∑ mn ∈ S.filter (fun mn => g mn = sig), f mn
          rw [show S.filter (fun mn => g mn = sig) =
              (lowOwnerFirstOwnerSignatureCellCarrier R p sig).product
                (lowOwnerFirstOwnerSignatureCellCarrier R p sig) by
            simpa [S, g] using hset]
    _ = ∑ mn ∈ S, f mn := hfiber
    _ = _ := rfl

/-- Within one signature cell the same-branch products are disjoint. -/
theorem lowOwnerFirstOwner_baseProduct_disjoint_childProduct
    (R p : ℕ) (sig : Finset ℕ) :
    Disjoint
      ((lowOwnerFirstOwnerBaseFiber R p sig).product
        (lowOwnerFirstOwnerBaseFiber R p sig))
      ((lowOwnerFirstOwnerChildFiber R p sig).product
        (lowOwnerFirstOwnerChildFiber R p sig)) := by
  rw [Finset.disjoint_left]
  intro mn hbase hchild
  have hmBase := (Finset.mem_product.mp hbase).1
  have hmChild := (Finset.mem_product.mp hchild).1
  have hpFree := (Finset.mem_filter.mp hmBase).2.2
  have hpDiv := (Finset.mem_filter.mp hmChild).2.2
  exact hpFree hpDiv

/-- One signature fibre of the split pair carrier is the union of the two
same-p-branch Cartesian squares. -/
theorem lowOwnerSignatureSplitPairCarrier_filter_signature_eq_sameBranchUnion
    (R p : ℕ) (sig : Finset ℕ) :
    (lowOwnerSignatureSplitPairCarrier R p).filter
        (fun mn => squarefreeLowerPrimeSignature p mn.1 = sig) =
      ((lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerBaseFiber R p sig)) ∪
        ((lowOwnerFirstOwnerChildFiber R p sig).product
          (lowOwnerFirstOwnerChildFiber R p sig)) := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hsplit, hmSig⟩
    rcases Finset.mem_filter.mp hsplit with ⟨hprod, hdata⟩
    rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
    have hnSig : squarefreeLowerPrimeSignature p n = sig := by
      rw [← hdata.1, hmSig]
    by_cases hpm : p ∣ m
    · have hpn : p ∣ n := hdata.2.mp hpm
      exact Finset.mem_union_right _
        (Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨hmCar, ⟨hmSig, hpm⟩⟩,
            Finset.mem_filter.mpr ⟨hnCar, ⟨hnSig, hpn⟩⟩⟩)
    · have hpn : ¬ p ∣ n := by
        intro h
        exact hpm (hdata.2.mpr h)
      exact Finset.mem_union_left _
        (Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨hmCar, ⟨hmSig, hpm⟩⟩,
            Finset.mem_filter.mpr ⟨hnCar, ⟨hnSig, hpn⟩⟩⟩)
  · intro hmn
    rcases Finset.mem_union.mp hmn with hbase | hchild
    · rcases Finset.mem_product.mp hbase with ⟨hmBase, hnBase⟩
      rcases Finset.mem_filter.mp hmBase with ⟨hmCar, hmData⟩
      rcases Finset.mem_filter.mp hnBase with ⟨hnCar, hnData⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hmCar, hnCar⟩,
            ⟨by rw [hmData.1, hnData.1], by simp [hmData.2, hnData.2]⟩⟩,
          hmData.1⟩
    · rcases Finset.mem_product.mp hchild with ⟨hmChild, hnChild⟩
      rcases Finset.mem_filter.mp hmChild with ⟨hmCar, hmData⟩
      rcases Finset.mem_filter.mp hnChild with ⟨hnCar, hnData⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hmCar, hnCar⟩,
            ⟨by rw [hmData.1, hnData.1], by simp [hmData.2, hnData.2]⟩⟩,
          hmData.1⟩

/-- One split-cell energy is the ordered Gram on its two same-branch products. -/
theorem lowOwnerFirstOwnerSplitCellEnergy_eq_sameBranchPairSum
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 +
        lowOwnerFirstOwnerChildAmplitude R p sig ^ 2 =
      ∑ mn ∈
        ((lowOwnerFirstOwnerBaseFiber R p sig).product
            (lowOwnerFirstOwnerBaseFiber R p sig)) ∪
          ((lowOwnerFirstOwnerChildFiber R p sig).product
            (lowOwnerFirstOwnerChildFiber R p sig)),
        lowOwnerZeroFrequencyMobiusSite R mn.1 *
          lowOwnerZeroFrequencyMobiusSite R mn.2 := by
  have hdisj := lowOwnerFirstOwner_baseProduct_disjoint_childProduct R p sig
  rw [Finset.sum_union hdisj]
  unfold lowOwnerFirstOwnerBaseAmplitude lowOwnerFirstOwnerChildAmplitude
  have hbase :
      (∑ n ∈ lowOwnerFirstOwnerBaseFiber R p sig,
        lowOwnerZeroFrequencyMobiusSite R n) ^ 2 =
      ∑ mn ∈ (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerBaseFiber R p sig),
        lowOwnerZeroFrequencyMobiusSite R mn.1 *
          lowOwnerZeroFrequencyMobiusSite R mn.2 := by
    calc
      (∑ n ∈ lowOwnerFirstOwnerBaseFiber R p sig,
          lowOwnerZeroFrequencyMobiusSite R n) ^ 2 =
        (∑ m ∈ lowOwnerFirstOwnerBaseFiber R p sig,
          lowOwnerZeroFrequencyMobiusSite R m) *
        (∑ n ∈ lowOwnerFirstOwnerBaseFiber R p sig,
          lowOwnerZeroFrequencyMobiusSite R n) := by ring
      _ = ∑ m ∈ lowOwnerFirstOwnerBaseFiber R p sig,
          ∑ n ∈ lowOwnerFirstOwnerBaseFiber R p sig,
            lowOwnerZeroFrequencyMobiusSite R m *
              lowOwnerZeroFrequencyMobiusSite R n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _hm
        rw [Finset.mul_sum]
      _ = _ := by
        symm
        simpa only using
          (Finset.sum_product
            (s := lowOwnerFirstOwnerBaseFiber R p sig)
            (t := lowOwnerFirstOwnerBaseFiber R p sig)
            (f := fun mn : ℕ × ℕ =>
              lowOwnerZeroFrequencyMobiusSite R mn.1 *
                lowOwnerZeroFrequencyMobiusSite R mn.2))
  have hchild :
      (∑ n ∈ lowOwnerFirstOwnerChildFiber R p sig,
        lowOwnerZeroFrequencyMobiusSite R n) ^ 2 =
      ∑ mn ∈ (lowOwnerFirstOwnerChildFiber R p sig).product
          (lowOwnerFirstOwnerChildFiber R p sig),
        lowOwnerZeroFrequencyMobiusSite R mn.1 *
          lowOwnerZeroFrequencyMobiusSite R mn.2 := by
    calc
      (∑ n ∈ lowOwnerFirstOwnerChildFiber R p sig,
          lowOwnerZeroFrequencyMobiusSite R n) ^ 2 =
        (∑ m ∈ lowOwnerFirstOwnerChildFiber R p sig,
          lowOwnerZeroFrequencyMobiusSite R m) *
        (∑ n ∈ lowOwnerFirstOwnerChildFiber R p sig,
          lowOwnerZeroFrequencyMobiusSite R n) := by ring
      _ = ∑ m ∈ lowOwnerFirstOwnerChildFiber R p sig,
          ∑ n ∈ lowOwnerFirstOwnerChildFiber R p sig,
            lowOwnerZeroFrequencyMobiusSite R m *
              lowOwnerZeroFrequencyMobiusSite R n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _hm
        rw [Finset.mul_sum]
      _ = _ := by
        symm
        simpa only using
          (Finset.sum_product
            (s := lowOwnerFirstOwnerChildFiber R p sig)
            (t := lowOwnerFirstOwnerChildFiber R p sig)
            (f := fun mn : ℕ × ℕ =>
              lowOwnerZeroFrequencyMobiusSite R mn.1 *
                lowOwnerZeroFrequencyMobiusSite R mn.2))
  rw [hbase, hchild]

/-- **Split energy is exactly the Gram on the refined pair carrier.** -/
theorem lowOwnerFirstOwnerSignatureSplitEnergy_eq_pairCarrier
    (R p : ℕ) :
    lowOwnerFirstOwnerSignatureSplitEnergy R p =
      ∑ mn ∈ lowOwnerSignatureSplitPairCarrier R p,
        lowOwnerZeroFrequencyMobiusSite R mn.1 *
          lowOwnerZeroFrequencyMobiusSite R mn.2 := by
  let S := lowOwnerSignatureSplitPairCarrier R p
  let T := lowOwnerFirstOwnerSignatureSet R p
  let g : ℕ × ℕ → Finset ℕ := fun mn =>
    squarefreeLowerPrimeSignature p mn.1
  let f : ℕ × ℕ → ℝ := fun mn =>
    lowOwnerZeroFrequencyMobiusSite R mn.1 *
      lowOwnerZeroFrequencyMobiusSite R mn.2
  have hmaps : ∀ mn ∈ S, g mn ∈ T := by
    intro mn hmn
    have hprod := (Finset.mem_filter.mp hmn).1
    have hmCar := (Finset.mem_product.mp hprod).1
    exact Finset.mem_image.mpr ⟨mn.1, hmCar, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmaps f
  unfold lowOwnerFirstOwnerSignatureSplitEnergy
  calc
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      (lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 +
        lowOwnerFirstOwnerChildAmplitude R p sig ^ 2)) =
      ∑ sig ∈ T,
        ∑ mn ∈
          ((lowOwnerFirstOwnerBaseFiber R p sig).product
              (lowOwnerFirstOwnerBaseFiber R p sig)) ∪
            ((lowOwnerFirstOwnerChildFiber R p sig).product
              (lowOwnerFirstOwnerChildFiber R p sig)), f mn := by
          apply Finset.sum_congr rfl
          intro sig _hsig
          exact lowOwnerFirstOwnerSplitCellEnergy_eq_sameBranchPairSum R p sig
    _ = ∑ sig ∈ T,
        ∑ mn ∈ S with g mn = sig, f mn := by
          apply Finset.sum_congr rfl
          intro sig _hsig
          have hset :=
            lowOwnerSignatureSplitPairCarrier_filter_signature_eq_sameBranchUnion
              R p sig
          change
            (∑ mn ∈
              ((lowOwnerFirstOwnerBaseFiber R p sig).product
                  (lowOwnerFirstOwnerBaseFiber R p sig)) ∪
                ((lowOwnerFirstOwnerChildFiber R p sig).product
                  (lowOwnerFirstOwnerChildFiber R p sig)), f mn) =
              ∑ mn ∈ S.filter (fun mn => g mn = sig), f mn
          rw [show S.filter (fun mn => g mn = sig) =
              ((lowOwnerFirstOwnerBaseFiber R p sig).product
                  (lowOwnerFirstOwnerBaseFiber R p sig)) ∪
                ((lowOwnerFirstOwnerChildFiber R p sig).product
                  (lowOwnerFirstOwnerChildFiber R p sig)) by
            simpa [S, g] using hset]
    _ = ∑ mn ∈ S, f mn := hfiber
    _ = _ := rfl

/-- **Consecutive filtration levels match exactly after the split.** -/
theorem lowOwnerFirstOwnerSignatureSplitEnergy_eq_successorEnergy
    {R p r : ℕ} (hpr : ConsecutivePrimeCoordinates p r) :
    lowOwnerFirstOwnerSignatureSplitEnergy R p =
      lowOwnerFirstOwnerSignatureEnergy R r := by
  rw [lowOwnerFirstOwnerSignatureSplitEnergy_eq_pairCarrier,
    lowOwnerFirstOwnerSignatureEnergy_eq_pairCarrier,
    lowOwnerSignatureSplitPairCarrier_eq_successor hpr]

/-- **One-step prime-filtration telescope.**  The first-owner covariance at p is
exactly half the energy decrement between consecutive signature levels. -/
theorem lowOwnerFirstOwnerSignatureEnergy_eq_successor_add_two_gram
    {R p r : ℕ} (hpr : ConsecutivePrimeCoordinates p r) :
    lowOwnerFirstOwnerSignatureEnergy R p =
      lowOwnerFirstOwnerSignatureEnergy R r +
        2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCellGram R p sig := by
  rw [lowOwnerFirstOwnerSignatureEnergy_eq_split_add_two_cellGrams,
    lowOwnerFirstOwnerSignatureSplitEnergy_eq_successorEnergy hpr]

end RHLean.Proof
