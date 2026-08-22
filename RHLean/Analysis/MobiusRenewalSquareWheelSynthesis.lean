import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Analysis.PrimeSievePNTCentering
import RHLean.Analysis.SquareRootTransportRealization
import RHLean.Proof.MatchedFarSurvivorBridge

/-!
# Renewal-telescope coordinates for the primorial square-wheel response

Cross-track synthesis witness. The g-weighted renewal telescope
(`RHLean.Analysis.sum_convolveOne_mul_mertensSummatory_div`), applied to the
far-prime reciprocal Mertens kernel

```text
g_n(d) = 1_{n+9 <= d <= X_n} * 1_{d prime} * M(floor (X_n / d)),
```

produces exactly the reciprocal Mertens transform whose negative global
far-upper rigidity
(`RHLean.Proof.survivorSixteenFarUpperPrimeMass_eq_neg_mertensTransform`)
identifies with the far-upper survivor sector of the square-prefix
decomposition. Substituting that renewal realization through the matched
square-prefix identity
(`RHLean.Proof.squarePrefixMertens_eq_positiveSmooth_add_matched` and
`squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near`)
into the primorial-wheel zero-mode center
(`RHLean.Analysis.primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter`)
yields one connected equality: at a synchronized wheel sample, the nonzero
wheel response is the square-prefix decomposition with its far-survivor
component realized as a renewal telescope, centered on the primorial block.

This is an exact coordinate identity. No estimate is asserted anywhere.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Renewal-telescope realization of the far-prime reciprocal Mertens kernel:
the left side of the g-weighted renewal telescope at `X = squarePrefixEndpoint t`
with kernel `g_t(d) = 1_{t+9 <= d <= X_t} * 1_{d prime} * M(floor (X_t / d))`. -/
def survivorFarUpperRenewalTelescope (t : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint t),
    (∑ d ∈ m.divisors,
      if d ∈ Finset.Icc (t + 9) (RHLean.Analysis.squarePrefixEndpoint t) then
        if d.Prime then
          RHLean.Analysis.mertensSummatory
            (RHLean.Analysis.squarePrefixEndpoint t / d)
        else 0
      else 0) *
      RHLean.Analysis.mertensSummatory
        (RHLean.Analysis.squarePrefixEndpoint t / m)

/-- **Renewal-telescope coordinates for the primorial wheel response.** At a
synchronized wheel sample, the far-survivor component of the square-prefix
decomposition is replaced by its renewal-telescope realization before applying
the existing wheel zero-mode center. Exact; no estimate is asserted. -/
theorem primorialMinimalSquareWheelNonzeroResponse_eq_renewalFarSurvivorCenter
    (k n : ℕ) (hn : 55 ≤ n)
    (hlower : primorialBlockLower k < RHLean.Analysis.squarePrefixEndpoint n)
    (hupper : RHLean.Analysis.squarePrefixEndpoint n ≤ primorialBlockUpper k) :
    RHLean.Analysis.squareWheelNonzeroSampleResponse
        (primorialMinimalWheelSystem k) n =
      ((squareRootPositiveSmoothMass (n + 1) +
            squareRootBornSmoothMass (n + 1) -
            survivorFarUpperRenewalTelescope n -
            squareRootNearPrimeTransport (n + 1)) -
          RHLean.Analysis.mertensSummatory (primorialBlockLower k)) -
        RHLean.Analysis.squareWheelSampleRatio
            (primorialMinimalWheelSystem k) n *
          (RHLean.Analysis.mertensSummatory (primorialBlockUpper k) -
            RHLean.Analysis.mertensSummatory (primorialBlockLower k)) := by
  classical
  -- Step 1: the telescope collapses the renewal realization to the
  -- far-prime reciprocal Mertens transform.
  have htel : survivorFarUpperRenewalTelescope n =
      ∑ q ∈ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n),
        if q.Prime then
          RHLean.Analysis.mertensSummatory
            (RHLean.Analysis.squarePrefixEndpoint n / q)
        else 0 := by
    have h0 := RHLean.Analysis.sum_convolveOne_mul_mertensSummatory_div
      (fun d =>
        if d ∈ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) then
          if d.Prime then
            RHLean.Analysis.mertensSummatory
              (RHLean.Analysis.squarePrefixEndpoint n / d)
          else 0
        else 0)
      (RHLean.Analysis.squarePrefixEndpoint n)
    have hsub : Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) ⊆
        Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint n) := by
      intro a ha
      rw [Finset.mem_Icc] at ha ⊢
      omega
    have hvanish : ∀ a ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint n),
        a ∉ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) →
        (if a ∈ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) then
          if a.Prime then
            RHLean.Analysis.mertensSummatory
              (RHLean.Analysis.squarePrefixEndpoint n / a)
          else 0
        else 0) = 0 := by
      intro a _ hnot
      simp [hnot]
    calc survivorFarUpperRenewalTelescope n
        = ∑ a ∈ Finset.Icc 1 (RHLean.Analysis.squarePrefixEndpoint n),
            (if a ∈
                Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) then
              if a.Prime then
                RHLean.Analysis.mertensSummatory
                  (RHLean.Analysis.squarePrefixEndpoint n / a)
              else 0
            else 0) := h0
      _ = ∑ q ∈ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n),
            (if q ∈
                Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n) then
              if q.Prime then
                RHLean.Analysis.mertensSummatory
                  (RHLean.Analysis.squarePrefixEndpoint n / q)
              else 0
            else 0) := (Finset.sum_subset hsub hvanish).symm
      _ = ∑ q ∈ Finset.Icc (n + 9) (RHLean.Analysis.squarePrefixEndpoint n),
            if q.Prime then
              RHLean.Analysis.mertensSummatory
                (RHLean.Analysis.squarePrefixEndpoint n / q)
            else 0 := by
          refine Finset.sum_congr rfl fun q hq => ?_
          simp [hq]
  -- Step 2: global far-upper rigidity identifies the far survivor with the
  -- negated telescope.
  have hsurv : survivorSixteenFarUpperPrimeMass n =
      -survivorFarUpperRenewalTelescope n := by
    rw [survivorSixteenFarUpperPrimeMass_eq_neg_mertensTransform n hn, htel]
  -- Step 3: the matched square-prefix decomposition with the far survivor in
  -- renewal coordinates.
  have hprefix : RHLean.Analysis.mertensSummatory
      (RHLean.Analysis.squarePrefixEndpoint n) =
      squareRootPositiveSmoothMass (n + 1) +
        squareRootBornSmoothMass (n + 1) -
        survivorFarUpperRenewalTelescope n -
        squareRootNearPrimeTransport (n + 1) := by
    have h1 := squarePrefixMertens_eq_positiveSmooth_add_matched (n + 1)
      (by omega)
    have h2 :=
      squareRootMatchedBornSmoothTransport_eq_bornSmooth_add_farSurvivor_sub_near
        (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h1 h2
    have h1' : RHLean.Analysis.mertensSummatory
        (RHLean.Analysis.squarePrefixEndpoint n) =
        squareRootPositiveSmoothMass (n + 1) +
          squareRootMatchedBornSmoothTransport (n + 1) := h1
    rw [h1', h2, hsurv]
    ring
  -- Step 4: substitute into the primorial-wheel zero-mode center.
  rw [RHLean.Analysis.primorialMinimalSquareWheelNonzeroResponse_eq_mertensCenter
    k n hlower hupper]
  simp only [RHLean.Analysis.primorialSquareZeroModeCenter]
  rw [hprefix]

end RHLean.Proof

namespace RHLean.Analysis

open scoped ArithmeticFunction.Moebius

/-- The corrected finite bootstrap split at `H = floor(R/2)`. The upper-half
Mertens correlation enters with a plus sign. -/
def frontierBootstrapRHS (R : ℕ) : ℂ :=
  let H := R / 2
  mertensSummatory H -
    ∑ n ∈ Finset.Icc 1 H,
      (((μ n : ℤ) : ℂ)) * canonicalFrontierMertensBundle R n +
    ∑ n ∈ Finset.Ioc H R,
      (((μ n : ℤ) : ℂ)) * mertensSummatory (squareRootEndpoint R / n)

/-- **Corrected frontier bootstrap self-consistency.** Splitting the completed
Möbius triangle at `H = floor(R/2)` gives the lower incidence bundle plus the
upper one-term Mertens fibres. Recombining is exactly the generic triangular
Möbius collapse. -/
theorem frontier_bootstrap_self_consistency
    {R : ℕ} (hR : 2 ≤ R) :
    mertensSummatory (squareRootEndpoint R) = frontierBootstrapRHS R := by
  classical
  let H := R / 2
  have hR1 : 1 ≤ R := by omega
  have hHR : H ≤ R := by
    dsimp [H]
    exact Nat.div_le_self R 2
  have hsplit :
      Finset.Icc 1 R = Finset.Icc 1 H ∪ Finset.Ioc H R := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 H) (Finset.Ioc H R) := by
    rw [Finset.disjoint_left]
    intro n hnLow hnHigh
    simp only [Finset.mem_Icc] at hnLow
    simp only [Finset.mem_Ioc] at hnHigh
    omega
  have hlow :
      mertensSummatory H -
          ∑ n ∈ Finset.Icc 1 H,
            (((μ n : ℤ) : ℂ)) * canonicalFrontierMertensBundle R n =
        ∑ n ∈ Finset.Icc 1 H,
          (((μ n : ℤ) : ℂ)) *
            ∑ q ∈ Finset.Icc 1 (R / n),
              mertensSummatory (squareRootEndpoint R / (n * q)) := by
    rw [mertensSummatory_eq_sum_Icc H, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    unfold canonicalFrontierMertensBundle
    ring
  have htop :
      (∑ n ∈ Finset.Ioc H R,
          (((μ n : ℤ) : ℂ)) * mertensSummatory (squareRootEndpoint R / n)) =
        ∑ n ∈ Finset.Ioc H R,
          (((μ n : ℤ) : ℂ)) *
            ∑ q ∈ Finset.Icc 1 (R / n),
              mertensSummatory (squareRootEndpoint R / (n * q)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnIoc := Finset.mem_Ioc.mp hn
    have hbundle := canonicalIncidence_eq_one_sub_mertens_of_half_lt
      hnIoc.2 (by simpa [H] using hnIoc.1)
    unfold canonicalFrontierMertensBundle at hbundle
    have hinner :
        (∑ q ∈ Finset.Icc 1 (R / n),
          mertensSummatory (squareRootEndpoint R / (n * q))) =
          mertensSummatory (squareRootEndpoint R / n) := by
      linarith
    rw [hinner]
  unfold frontierBootstrapRHS
  dsimp only
  rw [hlow, htop]
  rw [← Finset.sum_union hdisj, ← hsplit]
  exact (frontier_bootstrap_collapses_to_identity hR1).symm

/-- Positive weighted energy carried by the top half of the exact frontier
bundle. This definition makes no quantitative claim about its size. -/
def canonicalFrontierTopEnergy (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (R / 2) R,
    (n : ℝ) * ‖canonicalFrontierMertensBundle R n‖ ^ 2

/-- **Exact positive-norm obstruction.** On the entire top half, the frontier
energy contains the local Mertens energy verbatim. No `R^3` asymptotic or lower
bound is asserted. -/
theorem canonicalFrontierTopEnergy_eq_localMertensEnergy (R : ℕ) :
    canonicalFrontierTopEnergy R =
      ∑ n ∈ Finset.Ioc (R / 2) R,
        (n : ℝ) * ‖1 - mertensSummatory (squareRootEndpoint R / n)‖ ^ 2 := by
  unfold canonicalFrontierTopEnergy
  apply Finset.sum_congr rfl
  intro n hn
  have hnIoc := Finset.mem_Ioc.mp hn
  rw [canonicalIncidence_eq_one_sub_mertens_of_half_lt hnIoc.2 hnIoc.1]

end RHLean.Analysis

end
