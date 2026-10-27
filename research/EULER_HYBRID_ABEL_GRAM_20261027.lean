import Mathlib
import RHLean.Analysis.PrimeSieveAbelIdentity
import RHLean.Proof.RecursivePrimeReplacement
import «research.DYADIC_BUCHSTAB_OTHELLO_GLIDER_WALL»

/-!
# Euler square-root bilinear form: one-sided historical Abel transport

This module uses the *original* integer Mobius sequence. The original
bilinear floor form is not replaced with a model. One coordinate retains
mu(b), the other is summation-by-parts-transformed into M(a).

The truncated divisor annihilator and its post-root high-prime vanishing
were proved already in RecursivePrimeReplacement and
DYADIC_BUCHSTAB_OTHELLO_GLIDER_WALL; we consume them, rather than
re-prove the Euler divisor-cube lemma.

No finite-C estimate, power saving, or Riemann Hypothesis is asserted.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- Actual square-endpoint integer hyperbola kernel, cast to complex scalars. -/
def eulerSelfDualFloor (R a b : ℕ) : ℂ :=
  (squareRootEndpoint R / (a * b) : ℕ)

/-- Original, unnormalized historical bilinear floor form. -/
def eulerSelfDualBilinear (R : ℕ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    (((μ b : ℤ) : ℂ)) *
      ∑ a ∈ Finset.Icc 1 (R - 1),
        (((μ a : ℤ) : ℂ)) * eulerSelfDualFloor R a b

/-- One-sided Abel transport. The second coefficient stays literally mu(b). -/
def eulerHybridAbelMain (R : ℕ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    (((μ b : ℤ) : ℂ)) *
      ∑ a ∈ Finset.Icc 1 (R - 1),
        mertensSummatory a *
          (eulerSelfDualFloor R a b -
            eulerSelfDualFloor R (a + 1) b)

/-- The exact upper-boundary mass before using the square-root horizon. -/
def eulerHybridAbelEdge (R : ℕ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    (((μ b : ℤ) : ℂ)) * eulerSelfDualFloor R R b

/-- Exact asymmetric Abel identity, including the upper boundary term.
This holds at every R, with no bound or hypothesis. -/
theorem eulerSelfDualBilinear_eq_hybridAbel_add_edge (R : ℕ) :
    eulerSelfDualBilinear R =
      eulerHybridAbelMain R +
        mertensSummatory (R - 1) * eulerHybridAbelEdge R := by
  unfold eulerSelfDualBilinear eulerHybridAbelMain eulerHybridAbelEdge
  have hinner (b : ℕ) :
      (∑ a ∈ Finset.Icc 1 (R - 1),
          (((μ a : ℤ) : ℂ)) * eulerSelfDualFloor R a b) =
      (∑ a ∈ Finset.Icc 1 (R - 1),
          mertensSummatory a *
            (eulerSelfDualFloor R a b -
              eulerSelfDualFloor R (a + 1) b)) +
        mertensSummatory (R - 1) * eulerSelfDualFloor R R b := by
    have h := RHLean.Analysis.sum_mertensSummatory_mul_forwardDifference
      (fun a => eulerSelfDualFloor R a b) (R - 1)
    calc
      _ =
          ((∑ a ∈ Finset.Icc 1 (R - 1),
            (((μ a : ℤ) : ℂ)) * eulerSelfDualFloor R a b) -
              mertensSummatory (R - 1) * eulerSelfDualFloor R R b) +
          mertensSummatory (R - 1) * eulerSelfDualFloor R R b := by ring
      _ = _ := by rw [← h]
  calc
    (∑ b ∈ Finset.Icc 1 (R - 1),
        (((μ b : ℤ) : ℂ)) *
          ∑ a ∈ Finset.Icc 1 (R - 1),
            (((μ a : ℤ) : ℂ)) * eulerSelfDualFloor R a b) =
      ∑ b ∈ Finset.Icc 1 (R - 1),
        (((μ b : ℤ) : ℂ)) *
          ((∑ a ∈ Finset.Icc 1 (R - 1),
            mertensSummatory a *
              (eulerSelfDualFloor R a b -
                eulerSelfDualFloor R (a + 1) b)) +
          mertensSummatory (R - 1) * eulerSelfDualFloor R R b) := by
            apply Finset.sum_congr rfl
            intro b _hb
            rw [hinner b]
    _ =
      (∑ b ∈ Finset.Icc 1 (R - 1),
        (((μ b : ℤ) : ℂ)) *
          ∑ a ∈ Finset.Icc 1 (R - 1),
            mertensSummatory a *
              (eulerSelfDualFloor R a b -
                eulerSelfDualFloor R (a + 1) b)) +
      mertensSummatory (R - 1) *
        (∑ b ∈ Finset.Icc 1 (R - 1),
          (((μ b : ℤ) : ℂ)) * eulerSelfDualFloor R R b) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro b _hb
        ring

/-- The existing source-verified annihilator applies on the entire original
square-endpoint post-root carrier. The root-scale support c<R follows from
c*p<=R^2-1: it is not an extra arithmetic hypothesis. -/
theorem eulerTruncatedDivisor_annihilates_postRoot_composites
    {R c p : ℕ} (hR : 2 ≤ R)
    (hp : p.Prime) (hpRoot : R ≤ p) (hc : 2 ≤ c)
    (hfit : c * p ≤ squareRootEndpoint R) :
    squareRootReplacementKernel R (c * p) = 0 := by
  have hcR : c < R := by
    by_contra hnot
    have hRc : R ≤ c := Nat.le_of_not_gt hnot
    have hlow : R * R ≤ c * R := Nat.mul_le_mul_right R hRc
    have hhigh : c * R ≤ c * p := Nat.mul_le_mul_left c hpRoot
    have hXlt : squareRootEndpoint R < R * R := by
      have hsq : 0 < R ^ 2 := by positivity
      have hsub : R ^ 2 - 1 < R ^ 2 :=
        Nat.sub_lt hsq (by norm_num)
      simpa [squareRootEndpoint, pow_two] using hsub
    omega
  exact squareRootReplacementKernel_postRootReplication_eq_zero_of_nonunit
    hp hpRoot hc hcR

/-- The lower-scale recursive replacement identity was already proved:
this is the actual Möbius target whose signed kernel the hybrid Abel
coordinates aim to resolve. -/
theorem eulerHistoricalReplacement_exact (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) =
      RHLean.Analysis.mertensSummatory (R - 1) -
        squareRootRecursiveReplacementResidual R :=
  mertensEndpoint_eq_pred_sub_recursiveResidual R hR

#print axioms eulerSelfDualBilinear_eq_hybridAbel_add_edge
#print axioms eulerTruncatedDivisor_annihilates_postRoot_composites

end RHLean.Proof
