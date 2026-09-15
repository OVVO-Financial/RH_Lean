import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_INCIDENCE_CLOSURE»

/-!
# Every owner Dirichlet lens reconstructs the same AMP amplitude

For a fixed prime owner `p`, lower-signature cells partition the p-free and
p-divisible branches of the nonzero common-clock Mobius carrier.  The Dirichlet
incidence amplitude of one cell is exactly `Base + Child`.

After summing signatures, every p-free physical site occurs once as a parent
and every p-divisible squarefree site occurs once as the p-child of its unique
p-free parent.  Therefore the aggregate Dirichlet incidence is independent of
`p` and reconstructs the entire zero-frequency AMP amplitude:

  sum_sig DirichletIncidence(R,p,sig) = AMPAmplitude(R).

This is an exact multi-lens identity, not a frame estimate.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- p-free part of the actual nonzero common-clock carrier. -/
def lowOwnerFirstOwnerPFreeCarrier (R p : ℕ) : Finset ℕ :=
  (lowOwnerNonzeroMobiusCarrier R).filter fun n => ¬ p ∣ n

/-- p-divisible part of the actual nonzero common-clock carrier. -/
def lowOwnerFirstOwnerPDivisibleCarrier (R p : ℕ) : Finset ℕ :=
  (lowOwnerNonzeroMobiusCarrier R).filter fun n => p ∣ n

/-- One base fibre is exactly the signature fibre of the global p-free carrier. -/
theorem lowOwnerFirstOwnerPFreeCarrier_filter_signature_eq_baseFiber
    (R p : ℕ) (sig : Finset ℕ) :
    (lowOwnerFirstOwnerPFreeCarrier R p).filter
        (fun n => squarefreeLowerPrimeSignature p n = sig) =
      lowOwnerFirstOwnerBaseFiber R p sig := by
  ext n
  simp [lowOwnerFirstOwnerPFreeCarrier, lowOwnerFirstOwnerBaseFiber,
    and_assoc, and_left_comm, and_comm]

/-- One child fibre is exactly the signature fibre of the global p-divisible
carrier. -/
theorem lowOwnerFirstOwnerPDivisibleCarrier_filter_signature_eq_childFiber
    (R p : ℕ) (sig : Finset ℕ) :
    (lowOwnerFirstOwnerPDivisibleCarrier R p).filter
        (fun n => squarefreeLowerPrimeSignature p n = sig) =
      lowOwnerFirstOwnerChildFiber R p sig := by
  ext n
  simp [lowOwnerFirstOwnerPDivisibleCarrier, lowOwnerFirstOwnerChildFiber,
    and_assoc, and_left_comm, and_comm]

/-- Signature Fubini for the p-free branch amplitudes. -/
theorem sum_lowOwnerFirstOwnerBaseAmplitude_eq_pFreeCarrier
    (R p : ℕ) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerBaseAmplitude R p sig) =
      ∑ n ∈ lowOwnerFirstOwnerPFreeCarrier R p,
        lowOwnerZeroFrequencyMobiusSite R n := by
  let S := lowOwnerFirstOwnerPFreeCarrier R p
  let T := lowOwnerFirstOwnerSignatureSet R p
  let g : ℕ → Finset ℕ := squarefreeLowerPrimeSignature p
  let f : ℕ → ℝ := lowOwnerZeroFrequencyMobiusSite R
  have hmaps : ∀ n ∈ S, g n ∈ T := by
    intro n hn
    have hnCar : n ∈ lowOwnerNonzeroMobiusCarrier R :=
      (Finset.mem_filter.mp hn).1
    exact Finset.mem_image.mpr ⟨n, hnCar, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmaps f
  calc
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerBaseAmplitude R p sig) =
      ∑ sig ∈ T,
        ∑ n ∈ lowOwnerFirstOwnerBaseFiber R p sig, f n := by
          rfl
    _ = ∑ sig ∈ T,
        ∑ n ∈ S with g n = sig, f n := by
          apply Finset.sum_congr rfl
          intro sig _hsig
          rw [show S.filter (fun n => g n = sig) =
              lowOwnerFirstOwnerBaseFiber R p sig by
            simpa [S, g] using
              lowOwnerFirstOwnerPFreeCarrier_filter_signature_eq_baseFiber
                R p sig]
    _ = ∑ n ∈ S, f n := hfiber
    _ = _ := rfl

/-- Signature Fubini for the p-divisible child branch amplitudes. -/
theorem sum_lowOwnerFirstOwnerChildAmplitude_eq_pDivisibleCarrier
    (R p : ℕ) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerChildAmplitude R p sig) =
      ∑ n ∈ lowOwnerFirstOwnerPDivisibleCarrier R p,
        lowOwnerZeroFrequencyMobiusSite R n := by
  let S := lowOwnerFirstOwnerPDivisibleCarrier R p
  let T := lowOwnerFirstOwnerSignatureSet R p
  let g : ℕ → Finset ℕ := squarefreeLowerPrimeSignature p
  let f : ℕ → ℝ := lowOwnerZeroFrequencyMobiusSite R
  have hmaps : ∀ n ∈ S, g n ∈ T := by
    intro n hn
    have hnCar : n ∈ lowOwnerNonzeroMobiusCarrier R :=
      (Finset.mem_filter.mp hn).1
    exact Finset.mem_image.mpr ⟨n, hnCar, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmaps f
  calc
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerChildAmplitude R p sig) =
      ∑ sig ∈ T,
        ∑ n ∈ lowOwnerFirstOwnerChildFiber R p sig, f n := by
          rfl
    _ = ∑ sig ∈ T,
        ∑ n ∈ S with g n = sig, f n := by
          apply Finset.sum_congr rfl
          intro sig _hsig
          rw [show S.filter (fun n => g n = sig) =
              lowOwnerFirstOwnerChildFiber R p sig by
            simpa [S, g] using
              lowOwnerFirstOwnerPDivisibleCarrier_filter_signature_eq_childFiber
                R p sig]
    _ = ∑ n ∈ S, f n := hfiber
    _ = _ := rfl

/-- The p-free and p-divisible carriers partition the nonzero Mobius carrier. -/
theorem sum_pFree_add_pDivisible_eq_nonzeroCarrier
    (R p : ℕ) :
    (∑ n ∈ lowOwnerFirstOwnerPFreeCarrier R p,
        lowOwnerZeroFrequencyMobiusSite R n) +
      (∑ n ∈ lowOwnerFirstOwnerPDivisibleCarrier R p,
        lowOwnerZeroFrequencyMobiusSite R n) =
      ∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
        lowOwnerZeroFrequencyMobiusSite R n := by
  unfold lowOwnerFirstOwnerPFreeCarrier lowOwnerFirstOwnerPDivisibleCarrier
  have h := Finset.sum_filter_add_sum_filter_not
    (s := lowOwnerNonzeroMobiusCarrier R)
    (p := fun n => p ∣ n)
    (f := lowOwnerZeroFrequencyMobiusSite R)
  simpa [add_comm] using h

/-- Removing the zero-Mobius sites does not change the AMP amplitude. -/
theorem sum_lowOwnerNonzeroMobiusCarrier_eq_amplitude
    (R : ℕ) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
        lowOwnerZeroFrequencyMobiusSite R n) =
      lowOwnerZeroFrequencyMobiusAmplitude R := by
  unfold lowOwnerNonzeroMobiusCarrier lowOwnerZeroFrequencyMobiusAmplitude
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hmu : realMoebiusStep n ≠ 0
  · simp [hmu, lowOwnerZeroFrequencyMobiusSite]
  · have hz : realMoebiusStep n = 0 := not_ne_iff.mp hmu
    simp [hmu, lowOwnerZeroFrequencyMobiusSite, hz]

/-- **Exact owner-lens reconstruction.**  For every prime owner, summing the
Dirichlet incidence over all lower-signature cells gives the same full AMP
amplitude. -/
theorem sum_lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_fullAmplitude
    {R p : ℕ} (hp : p.Prime) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig) =
      lowOwnerZeroFrequencyMobiusAmplitude R := by
  calc
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig) =
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        (lowOwnerFirstOwnerBaseAmplitude R p sig +
          lowOwnerFirstOwnerChildAmplitude R p sig) := by
            apply Finset.sum_congr rfl
            intro sig _hsig
            rw [lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_base_add_child hp]
    _ = (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerBaseAmplitude R p sig) +
        (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerChildAmplitude R p sig) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ n ∈ lowOwnerFirstOwnerPFreeCarrier R p,
          lowOwnerZeroFrequencyMobiusSite R n) +
        (∑ n ∈ lowOwnerFirstOwnerPDivisibleCarrier R p,
          lowOwnerZeroFrequencyMobiusSite R n) := by
            rw [sum_lowOwnerFirstOwnerBaseAmplitude_eq_pFreeCarrier,
              sum_lowOwnerFirstOwnerChildAmplitude_eq_pDivisibleCarrier]
    _ = ∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
          lowOwnerZeroFrequencyMobiusSite R n :=
      sum_pFree_add_pDivisible_eq_nonzeroCarrier R p
    _ = lowOwnerZeroFrequencyMobiusAmplitude R :=
      sum_lowOwnerNonzeroMobiusCarrier_eq_amplitude R

end RHLean.Proof
