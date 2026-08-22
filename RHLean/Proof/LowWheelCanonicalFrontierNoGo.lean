import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Proof.LowWheelCanonicalPrimeSplit
import RHLean.Proof.LowWheelSurvivorFloorExpansion

/-!
# Canonical frontier incidence: exact closure and no-go

The canonical one-prime frontier admits a pointwise lower-scale description.
For `X = R^2 - 1`, define the incidence field

`B_R(n) = 1 - sum_{q <= R/n} M(floor(X/(n*q)))`.

On the top half `R/2 < n <= R`, the reciprocal bundle has only `q = 1`, so

`B_R(n) = 1 - M(floor(X/n))`.

Thus every positive energy of this coordinate contains a local Mertens energy
verbatim.  The remaining signed self-reference is also exact but supplies no
new recurrence: the generic triangular identity

`sum_{n <= R} mu(n) sum_{q <= R/n} F(n*q) = F(1)`

is just `mu * 1 = delta` after regrouping by `m = n*q`.  Substituting the
pointwise bundle into the corrected lower-half/top-half bootstrap therefore
collapses algebraically to `M(X) = M(X)`.

No estimate, PNT input, asymptotic, or RH hypothesis appears here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Pointwise canonical frontier incidence in its exact Mertens-bundle form. -/
def canonicalFrontierIncidence (R n : ℕ) : ℂ :=
  1 - ∑ q ∈ Finset.Icc 1 (R / n),
    mertensSummatory (squareRootEndpoint R / (n * q))

/-- The pointwise incidence is exactly the finite lower-scale Mertens bundle. -/
theorem canonicalIncidence_eq_one_sub_mertensBundle
    (R n : ℕ) :
    canonicalFrontierIncidence R n =
      1 - ∑ q ∈ Finset.Icc 1 (R / n),
        mertensSummatory (squareRootEndpoint R / (n * q)) := by
  rfl

/-- On the upper half of the root range the bundle has only the `q = 1` term. -/
theorem canonicalIncidence_eq_one_sub_mertens_of_half_lt
    {R n : ℕ} (hn : 1 ≤ n) (hnR : n ≤ R) (hhalf : R / 2 < n) :
    canonicalFrontierIncidence R n =
      1 - mertensSummatory (squareRootEndpoint R / n) := by
  have hnpos : 0 < n := by omega
  have hRlt : R < n * 2 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hhalf
  have hlt2 : R / n < 2 := by
    apply (Nat.div_lt_iff_lt_mul hnpos).2
    simpa [Nat.mul_comm] using hRlt
  have hge1 : 1 ≤ R / n := (Nat.one_le_div_iff hnpos).2 hnR
  have hdiv : R / n = 1 := by omega
  simp [canonicalFrontierIncidence, hdiv]

/-- Positive top-half energy of the incidence field. -/
def canonicalFrontierTopEnergy (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (R / 2) R,
    (n : ℝ) * ‖canonicalFrontierIncidence R n‖ ^ 2

/-- The top-half positive energy literally contains the local Mertens values
`M(floor((R^2-1)/n))`; no positive norm has removed them. -/
theorem canonicalFrontierTopEnergy_eq_localMertensEnergy
    (R : ℕ) :
    canonicalFrontierTopEnergy R =
      ∑ n ∈ Finset.Ioc (R / 2) R,
        (n : ℝ) * ‖1 - mertensSummatory (squareRootEndpoint R / n)‖ ^ 2 := by
  classical
  unfold canonicalFrontierTopEnergy
  apply Finset.sum_congr rfl
  intro n hnI
  rcases Finset.mem_Ioc.mp hnI with ⟨hhalf, hnR⟩
  have hn : 1 ≤ n := by
    by_cases hR0 : R = 0
    · subst R
      simp at hhalf
    · have : 0 < n := by omega
      omega
  rw [canonicalIncidence_eq_one_sub_mertens_of_half_lt hn hnR hhalf]

/-- Generic triangular Möbius collapse.  Regrouping by `m = n*q` gives
coefficient `sum_{n | m} mu(n)`, hence only `m = 1` survives. -/
theorem mobius_hyperbola_double_sum_eq_head
    (F : ℕ → ℂ) {R : ℕ} (hR : 1 ≤ R) :
    (∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n), F (n * q)) =
      F 1 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n), F (n * q)) =
      ∑ n ∈ Finset.Icc 1 R,
        ∑ q ∈ Finset.Icc 1 (R / n),
          (((μ n : ℤ) : ℂ)) * F (n * q) := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [Finset.mul_sum]
    _ = ∑ m ∈ Finset.Icc 1 R,
        ∑ p ∈ m.divisorsAntidiagonal,
          (((μ p.1 : ℤ) : ℂ)) * F (p.1 * p.2) := by
            symm
            exact RHLean.Analysis.sum_Icc_divisorsAntidiagonal_eq_sum_div
              (fun a b => (((μ a : ℤ) : ℂ)) * F (a * b)) R
    _ = ∑ m ∈ Finset.Icc 1 R,
        (if m = 1 then F 1 else 0) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Nat.sum_divisorsAntidiagonal]
          calc
            (∑ d ∈ m.divisors,
                (((μ d : ℤ) : ℂ)) * F (d * (m / d))) =
              ∑ d ∈ m.divisors,
                (((μ d : ℤ) : ℂ)) * F m := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  have hdData := Nat.mem_divisors.mp hd
                  rw [Nat.mul_div_cancel' hdData.1]
            _ = (∑ d ∈ m.divisors, (((μ d : ℤ) : ℂ))) * F m := by
                  rw [Finset.sum_mul]
            _ = (if m = 1 then (1 : ℂ) else 0) * F m := by
                  rw [RHLean.Analysis.sum_divisors_moebius_eq_ite]
            _ = if m = 1 then F 1 else 0 := by
                  by_cases hm1 : m = 1
                  · subst m
                    simp
                  · simp [hm1]
    _ = F 1 := by
      have h1mem : (1 : ℕ) ∈ Finset.Icc 1 R :=
        Finset.mem_Icc.mpr ⟨le_rfl, hR⟩
      simp [h1mem]

/-- Corrected lower-half/top-half bootstrap expression. -/
def frontierBootstrapRHS (R : ℕ) : ℂ :=
  mertensSummatory (R / 2) -
    ∑ n ∈ Finset.Icc 1 (R / 2),
      (((μ n : ℤ) : ℂ)) * canonicalFrontierIncidence R n +
    ∑ n ∈ Finset.Ioc (R / 2) R,
      (((μ n : ℤ) : ℂ)) *
        mertensSummatory (squareRootEndpoint R / n)

/-- The corrected split bootstrap is exactly the full triangular Möbius bundle.
This is the algebraic step that makes the no-go transparent. -/
theorem frontierBootstrapRHS_eq_fullHyperbola
    (R : ℕ) (hR : 2 ≤ R) :
    frontierBootstrapRHS R =
      ∑ n ∈ Finset.Icc 1 R,
        (((μ n : ℤ) : ℂ)) *
          ∑ q ∈ Finset.Icc 1 (R / n),
            mertensSummatory (squareRootEndpoint R / (n * q)) := by
  classical
  let H := R / 2
  have hHle : H ≤ R := by
    dsimp [H]
    exact Nat.div_le_self R 2
  have hset : Finset.Icc 1 R = Finset.Icc 1 H ∪ Finset.Ioc H R := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 H) (Finset.Ioc H R) := by
    rw [Finset.disjoint_left]
    intro n hnlo hnhi
    simp only [Finset.mem_Icc] at hnlo
    simp only [Finset.mem_Ioc] at hnhi
    omega
  have hM : mertensSummatory H =
      ∑ n ∈ Finset.Icc 1 H, (((μ n : ℤ) : ℂ)) :=
    RHLean.Analysis.mertensSummatory_eq_sum_Icc H
  have htop :
      (∑ n ∈ Finset.Ioc H R,
          (((μ n : ℤ) : ℂ)) *
            ∑ q ∈ Finset.Icc 1 (R / n),
              mertensSummatory (squareRootEndpoint R / (n * q))) =
        ∑ n ∈ Finset.Ioc H R,
          (((μ n : ℤ) : ℂ)) *
            mertensSummatory (squareRootEndpoint R / n) := by
    apply Finset.sum_congr rfl
    intro n hnI
    rcases Finset.mem_Ioc.mp hnI with ⟨hHn, hnR⟩
    have hnpos : 0 < n := by omega
    have hRlt : R < n * 2 := by
      dsimp [H] at hHn
      exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hHn
    have hlt2 : R / n < 2 := by
      apply (Nat.div_lt_iff_lt_mul hnpos).2
      simpa [Nat.mul_comm] using hRlt
    have hge1 : 1 ≤ R / n := (Nat.one_le_div_iff hnpos).2 hnR
    have hdiv : R / n = 1 := by omega
    simp [hdiv]
  unfold frontierBootstrapRHS canonicalFrontierIncidence
  dsimp [H] at hM ⊢
  rw [hM]
  rw [hset, Finset.sum_union hdisj]
  rw [htop]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Corrected finite self-consistency relation. -/
theorem frontier_bootstrap_self_consistency
    (R : ℕ) (hR : 2 ≤ R) :
    mertensSummatory (squareRootEndpoint R) = frontierBootstrapRHS R := by
  rw [frontierBootstrapRHS_eq_fullHyperbola R hR]
  symm
  simpa using mobius_hyperbola_double_sum_eq_head
    (F := fun m => mertensSummatory (squareRootEndpoint R / m))
    (R := R) (by omega)

/-- **Definitive one-prime-frontier no-go.**  After the incidence bundle is
substituted, the bootstrap is exactly `mu * 1 = delta`; it collapses to the
identity `M(X) = M(X)` and imposes no additional finite-volume constraint. -/
theorem frontier_bootstrap_collapses_to_identity
    (R : ℕ) (hR : 2 ≤ R) :
    frontierBootstrapRHS R = mertensSummatory (squareRootEndpoint R) := by
  exact (frontier_bootstrap_self_consistency R hR).symm

end RHLean.Proof
