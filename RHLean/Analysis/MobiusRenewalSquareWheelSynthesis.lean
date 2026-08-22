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
  have hsurv : survivorSixteenFarUpperPrimeMass n =
      -survivorFarUpperRenewalTelescope n := by
    rw [survivorSixteenFarUpperPrimeMass_eq_neg_mertensTransform n hn, htel]
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

/-- The completed pointwise frontier incidence before the cofactor cardinality
is collapsed. It is the signed mass of pairs `1 <= c < R` and
`floor(R/n) < q <= floor((R^2-1)/(n*c))`. -/
def canonicalFrontierIncidence (R n : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    ∑ _q ∈ Finset.Ioc (R / n) (squareRootEndpoint R / (n * c)),
      (((μ c : ℤ) : ℂ))

/-- **Centered cofactor-hyperbola form.** Summing the interval cardinality in
the second coordinate gives exactly the discovered pointwise kernel. -/
theorem canonicalIncidence_eq_centeredCofactorHyperbola
    {R n : ℕ} (hR : 2 ≤ R) (hn : 1 ≤ n) (hnR : n ≤ R) :
    canonicalFrontierIncidence R n =
      ∑ c ∈ Finset.Ico 1 R,
        (((μ c : ℤ) : ℂ)) *
          (((squareRootEndpoint R / (n * c) : ℕ) : ℂ) -
            ((R / n : ℕ) : ℂ)) := by
  classical
  have hnpos : 0 < n := by omega
  have hcut : ∀ c ∈ Finset.Ico 1 R,
      R / n ≤ squareRootEndpoint R / (n * c) := by
    intro c hc
    rcases Finset.mem_Ico.mp hc with ⟨hc1, hcR⟩
    have hcLe : c ≤ R - 1 := by omega
    have hdiv : (R / n) * n ≤ R := Nat.div_mul_le_self R n
    have hmul : ((R / n) * n) * c ≤ R * (R - 1) :=
      Nat.mul_le_mul hdiv hcLe
    have hRX : R * (R - 1) ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      rw [Nat.mul_sub_left_distrib]
      simp only [mul_one]
      rw [show R * R = R ^ 2 by ring]
      exact Nat.sub_le_sub_left (by omega : 1 ≤ R) (R ^ 2)
    have hfit : (R / n) * (n * c) ≤ squareRootEndpoint R := by
      calc
        (R / n) * (n * c) = ((R / n) * n) * c := by ring
        _ ≤ R * (R - 1) := hmul
        _ ≤ squareRootEndpoint R := hRX
    exact (Nat.le_div_iff_mul_le (by positivity : 0 < n * c)).2 hfit
  unfold canonicalFrontierIncidence
  apply Finset.sum_congr rfl
  intro c hc
  have hTc := hcut c hc
  calc
    (∑ _q ∈ Finset.Ioc (R / n) (squareRootEndpoint R / (n * c)),
        (((μ c : ℤ) : ℂ))) =
      (((Finset.Ioc (R / n) (squareRootEndpoint R / (n * c))).card : ℕ) : ℂ) *
        (((μ c : ℤ) : ℂ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (((squareRootEndpoint R / (n * c) - R / n : ℕ) : ℂ)) *
        (((μ c : ℤ) : ℂ)) := by rw [Nat.card_Ioc]
    _ = (((μ c : ℤ) : ℂ)) *
        (((squareRootEndpoint R / (n * c) : ℕ) : ℂ) -
          ((R / n : ℕ) : ℂ)) := by
            rw [Nat.cast_sub hTc]
            ring

/-- **Exact pointwise low/post closure.** The centered cofactor-hyperbola
incidence is exactly the finite Mertens bundle. The proof is a finite swap of
the pair region; the square endpoint forces every cofactor in the upper
`q`-strip to satisfy `c < R`. -/
theorem canonicalFrontierIncidence_eq_mertensBundle
    {R n : ℕ} (hR : 2 ≤ R) (hn : 1 ≤ n) (hnR : n ≤ R) :
    canonicalFrontierIncidence R n = canonicalFrontierMertensBundle R n := by
  classical
  let X := squareRootEndpoint R
  let N := X / n
  let T := R / n
  have hnpos : 0 < n := by omega
  have hR1 : 1 ≤ R := by omega
  have hRX : R ≤ X := by
    dsimp [X]
    unfold squareRootEndpoint
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hTN : T ≤ N := by
    dsimp [T, N, X]
    exact Nat.div_le_div_right hRX
  have hN1 : 1 ≤ N := by
    exact (Nat.one_le_div_iff hnpos).2 (hnR.trans hRX)
  have hset :
      Finset.Icc 1 N = Finset.Icc 1 T ∪ Finset.Ioc T N := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 T) (Finset.Ioc T N) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [Finset.mem_Icc] at hq1
    simp only [Finset.mem_Ioc] at hq2
    omega
  have hunit := sum_mertensSummatory_div_eq_one hN1
  rw [hset, Finset.sum_union hdisj] at hunit
  have hbundleUpper : canonicalFrontierMertensBundle R n =
      ∑ q ∈ Finset.Ioc T N, mertensSummatory (N / q) := by
    unfold canonicalFrontierMertensBundle
    have hlow :
        (∑ q ∈ Finset.Icc 1 (R / n),
            mertensSummatory (squareRootEndpoint R / (n * q))) =
          ∑ q ∈ Finset.Icc 1 T, mertensSummatory (N / q) := by
      apply Finset.sum_congr
      · rfl
      · intro q hq
        simp [T, N, X, Nat.div_div_eq_div_mul]
    rw [hlow, ← hunit]
    ring
  have hswap :
      (∑ q ∈ Finset.Ioc T N,
          ∑ c ∈ Finset.Icc 1 (N / q), (((μ c : ℤ) : ℂ))) =
        ∑ c ∈ Finset.Ico 1 R,
          ∑ q ∈ Finset.Ioc T (N / c), (((μ c : ℤ) : ℂ)) := by
    calc
      (∑ q ∈ Finset.Ioc T N,
          ∑ c ∈ Finset.Icc 1 (N / q), (((μ c : ℤ) : ℂ))) =
        ∑ z ∈ (Finset.Ioc T N).sigma (fun q => Finset.Icc 1 (N / q)),
          (((μ z.2 : ℤ) : ℂ)) :=
            Finset.sum_sigma' (Finset.Ioc T N)
              (fun q => Finset.Icc 1 (N / q)) (fun _ c => (((μ c : ℤ) : ℂ)))
      _ = ∑ w ∈ (Finset.Ico 1 R).sigma (fun c => Finset.Ioc T (N / c)),
          (((μ w.1 : ℤ) : ℂ)) := by
            refine Finset.sum_nbij' (i := fun z => ⟨z.2, z.1⟩)
              (j := fun w => ⟨w.2, w.1⟩) ?_ ?_ ?_ ?_ ?_
            · rintro ⟨q, c⟩ hz
              rw [Finset.mem_sigma] at hz ⊢
              obtain ⟨hq, hc⟩ := hz
              rcases Finset.mem_Ioc.mp hq with ⟨hTq, hqN⟩
              rcases Finset.mem_Icc.mp hc with ⟨hc1, hcDiv⟩
              have hqpos : 0 < q := by omega
              have hcpos : 0 < c := by omega
              have hcq : c * q ≤ N :=
                (Nat.le_div_iff_mul_le hqpos).1 hcDiv
              have hcR : c < R := by
                by_contra hnot
                have hcge : R ≤ c := Nat.le_of_not_gt hnot
                have hnq : R < n * q := by
                  have h := (Nat.div_lt_iff_lt_mul hnpos).1 hTq
                  simpa [T, Nat.mul_comm] using h
                have hlower : R * (R + 1) ≤ c * (n * q) :=
                  Nat.mul_le_mul hcge (by omega)
                have hupper : c * (n * q) ≤ X := by
                  have hx : n * (c * q) ≤ X :=
                    (Nat.le_div_iff_mul_le hnpos).1 hcq
                  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hx
                have hXRR : X < R * (R + 1) := by
                  have hsqpos : 0 < R ^ 2 := by positivity
                  have hXsq : X < R ^ 2 := by
                    dsimp [X]
                    unfold squareRootEndpoint
                    exact Nat.sub_lt hsqpos (by norm_num)
                  have hsqRR : R ^ 2 = R * R := by ring
                  rw [hsqRR] at hXsq
                  have hRR : R * R < R * (R + 1) :=
                    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
                  exact hXsq.trans hRR
                exact (not_le_of_gt hXRR) (hlower.trans hupper)
              have hqDiv : q ≤ N / c := by
                apply (Nat.le_div_iff_mul_le hcpos).2
                simpa [Nat.mul_comm] using hcq
              exact ⟨Finset.mem_Ico.mpr ⟨hc1, hcR⟩,
                Finset.mem_Ioc.mpr ⟨hTq, hqDiv⟩⟩
            · rintro ⟨c, q⟩ hw
              rw [Finset.mem_sigma] at hw ⊢
              obtain ⟨hc, hq⟩ := hw
              rcases Finset.mem_Ico.mp hc with ⟨hc1, hcR⟩
              rcases Finset.mem_Ioc.mp hq with ⟨hTq, hqDiv⟩
              have hcpos : 0 < c := by omega
              have hqpos : 0 < q := by omega
              have hqc : q * c ≤ N :=
                (Nat.le_div_iff_mul_le hcpos).1 hqDiv
              have hqN : q ≤ N :=
                hqDiv.trans (Nat.div_le_self N c)
              have hcDiv : c ≤ N / q := by
                apply (Nat.le_div_iff_mul_le hqpos).2
                simpa [Nat.mul_comm] using hqc
              exact ⟨Finset.mem_Ioc.mpr ⟨hTq, hqN⟩,
                Finset.mem_Icc.mpr ⟨hc1, hcDiv⟩⟩
            · rintro ⟨q, c⟩ hz
              rfl
            · rintro ⟨c, q⟩ hw
              rfl
            · rintro ⟨q, c⟩ hz
              rfl
      _ = ∑ c ∈ Finset.Ico 1 R,
          ∑ q ∈ Finset.Ioc T (N / c), (((μ c : ℤ) : ℂ)) :=
            (Finset.sum_sigma' (Finset.Ico 1 R)
              (fun c => Finset.Ioc T (N / c))
              (fun c _ => (((μ c : ℤ) : ℂ)))).symm
  have hupperIncidence :
      (∑ q ∈ Finset.Ioc T N, mertensSummatory (N / q)) =
        canonicalFrontierIncidence R n := by
    calc
      (∑ q ∈ Finset.Ioc T N, mertensSummatory (N / q)) =
        ∑ q ∈ Finset.Ioc T N,
          ∑ c ∈ Finset.Icc 1 (N / q), (((μ c : ℤ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact mertensSummatory_eq_sum_Icc (N / q)
      _ = ∑ c ∈ Finset.Ico 1 R,
          ∑ q ∈ Finset.Ioc T (N / c), (((μ c : ℤ) : ℂ)) := hswap
      _ = canonicalFrontierIncidence R n := by
        unfold canonicalFrontierIncidence
        apply Finset.sum_congr rfl
        intro c hc
        simp [T, N, X, Nat.div_div_eq_div_mul]
  rw [hupperIncidence] at hbundleUpper
  exact hbundleUpper.symm

end RHLean.Analysis

end
