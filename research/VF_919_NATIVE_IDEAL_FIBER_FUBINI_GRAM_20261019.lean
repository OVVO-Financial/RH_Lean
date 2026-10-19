import «research.VF_919_NATIVE_TWO_PRIME_COMPENSATION_20261019»

/-!
# Exact ideal-label -> rational-owner fiber projection, AFTER full Gram

This proves the literal finite commutative diagram needed by RH_Lean:
  labelled physical sources -> all pairwise complex correlations
                           -> rational norm/owner summation.

The integer owner map is allowed to have many different ideal labels
with the same norm. The coefficient is arbitrary and may include the
true sextic ideal character, ideal-Moebius sign, masks and normalizer;
the physical weight is any function of its integer owner.

The identity is unconditional and source-agnostic. Its right side
contains ALL i,j pairs, INCLUDING i!=j IN THE SAME rational fiber.
No Hecke large sieve, Gauss sum or uniform spectral saving is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Proof

/-- Exact norm/owner fiber-Fubini with arbitrary complex ideal phases.
    No injectivity of owner is required; hence same-norm ideal
    multiplicities cannot accidentally be discarded. -/
theorem vf919NativeIdealFiberFubini
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (owner : ι → ℕ)
    (c : ι → ℂ) (w : ℕ → ℂ) :
    (∑ i ∈ s, c i * w (owner i)) =
      ∑ n ∈ s.image owner,
        (∑ i ∈ s with owner i = n, c i) * w n := by
  classical
  have hmaps : ∀ i ∈ s, owner i ∈ s.image owner := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := s) (t := s.image owner) (g := owner) hmaps
      (fun i => c i * w (owner i))
  calc
    (∑ i ∈ s, c i * w (owner i)) =
      ∑ n ∈ s.image owner,
        ∑ i ∈ s with owner i = n, c i * w (owner i) :=
          hfiber.symm
    _ = ∑ n ∈ s.image owner,
          (∑ i ∈ s with owner i = n, c i) * w n := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

/-- Complete Hermitian source energy on the ideal-indexed carrier.
    A pair of different ideal labels in the SAME owner fiber is still
    present in the double sum; it is not an eliminated diagonal. -/
theorem vf919NativeIdealFiberFullHermitianGram
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (owner : ι → ℕ)
    (c : ι → ℂ) (w : ℕ → ℂ) :
    ‖∑ i ∈ s, c i * w (owner i)‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s,
        ((c i * w (owner i)) *
          star (c j * w (owner j))).re := by
  exact vf919FiniteHermitianGram s (fun i => c i * w (owner i))

/-- Norm-projected scalar signal, with *ALL* ideal-label cross
    correlations retained BEFORE the physical owner weight is paid. -/
theorem vf919NativeProjectedFiberFullHermitianGram
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (owner : ι → ℕ)
    (c : ι → ℂ) (w : ℕ → ℂ) :
    ‖∑ n ∈ s.image owner,
        (∑ i ∈ s with owner i = n, c i) * w n‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s,
        ((c i * w (owner i)) *
          star (c j * w (owner j))).re := by
  rw [← vf919NativeIdealFiberFubini s owner c w]
  exact vf919NativeIdealFiberFullHermitianGram s owner c w

#print axioms vf919NativeIdealFiberFubini
#print axioms vf919NativeIdealFiberFullHermitianGram
#print axioms vf919NativeProjectedFiberFullHermitianGram

end RHLean.Proof
