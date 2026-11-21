import Mathlib
import RHLean.Analysis.AlpogePhysicalCharacterHistory

/-!
# Exact real interpolation of original Frobenius/inertia character histories

Alpoge De evaluates GPsi at nonintegral arguments y=a/w. There is no
reason to pay a generic Lipschitz error when the ORIGINAL finite prime
kernel is piecewise affine between consecutive integers.

Let N=floor(y). Then, exactly and without signs being discarded:

  GPsi(y) = H_psi(N) + (y-N) * (ell_psi + sum_(n<=N) c_psi(n)/n)

for each nonprincipal ψ, with
c_psi(n)=Lambda(n)*primVal(inertia,frob,psi,n).

This eliminates separate smooth/sharp interpolation bookkeeping at
fixed cutoffs. The unresolved square-root estimate on the WHOLE
signed historical source is NOT inferred.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Piecewise-affine physical character polynomial, including exact ell. -/
def alpogePhysicalCharacterWeightedReal
    (c : ℕ → ℂ) (ell : ℂ) (y : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
    c n * ((y : ℂ) / (n : ℂ) - 1)) + (y : ℂ) * ell

theorem alpogePhysicalCharacterWeightedReal_eq_affine
    (c : ℕ → ℂ) (ell : ℂ) (y : ℝ) :
    alpogePhysicalCharacterWeightedReal c ell y =
      (y : ℂ) * (alpogePhysicalCharacterRecip c ⌊y⌋₊ + ell) -
        alpogePhysicalCharacterPsi c ⌊y⌋₊ := by
  unfold alpogePhysicalCharacterWeightedReal
    alpogePhysicalCharacterRecip alpogePhysicalCharacterPsi
  calc
    _ = (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
      ((y : ℂ) * (c n / (n : ℂ)) - c n)) +
        (y : ℂ) * ell := by
          congr 1
          apply Finset.sum_congr rfl
          intro n _hn
          ring
    _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
          ring

/-- Exact affine interpolation at the actual integer clock,
without a derivative approximation and without losing the old history. -/
theorem alpogePhysicalCharacterWeightedReal_eq_history_add_remainder
    (c : ℕ → ℂ) (ell : ℂ) (y : ℝ) :
    alpogePhysicalCharacterWeightedReal c ell y =
      alpogePhysicalCharacterHistory c ell ⌊y⌋₊ +
        ((y : ℂ) - (⌊y⌋₊ : ℂ)) *
          (alpogePhysicalCharacterRecip c ⌊y⌋₊ + ell) := by
  rw [alpogePhysicalCharacterWeightedReal_eq_affine]
  unfold alpogePhysicalCharacterHistory
  ring

/-- Native real-valued GPsi is EXACTLY a historical integer prefix
plus one signed reciprocal-prefix slope over the fractional collar.
Every genuine prime-power and inertia factor remains in c_psi. -/
theorem alpogeNativeFrobGPsi_real_eq_history_add_remainder
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ) (ψ : AddChar G ℂ) (y : ℝ)
    (hψ : ψ ≠ 0) :
    alpogeNativeFrobInertiaGPsi inertia frob ell ψ y =
      alpogePhysicalCharacterHistory
        (alpogePhysicalFrobCharacterCoefficient inertia frob ψ)
        (ell ψ) ⌊y⌋₊ +
        ((y : ℂ) - (⌊y⌋₊ : ℂ)) *
          (alpogePhysicalCharacterRecip
            (alpogePhysicalFrobCharacterCoefficient inertia frob ψ)
            ⌊y⌋₊ + ell ψ) := by
  rw [alpogeNativeFrobInertiaGPsi_nonprincipal
    inertia frob ell ψ y hψ]
  unfold alpogeNativeFrobInertiaPrimeSum
  have hsource :
      (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        ((Λ n : ℝ) : ℂ) *
          alpogeNativeFrobInertiaPrimeValue inertia frob ψ n *
            (((y / (n : ℝ) - 1 : ℝ)) : ℂ)) =
      (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        alpogePhysicalFrobCharacterCoefficient inertia frob ψ n *
          ((y : ℂ) / (n : ℂ) - 1)) := by
    apply Finset.sum_congr rfl
    intro n _hn
    unfold alpogePhysicalFrobCharacterCoefficient
    push_cast
    ring
  rw [hsource]
  exact alpogePhysicalCharacterWeightedReal_eq_history_add_remainder
    (alpogePhysicalFrobCharacterCoefficient inertia frob ψ)
    (ell ψ) y

end RHLean.Analysis
