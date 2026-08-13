import Mathlib
import RHLean.Arithmetic.PrimeAveragedFrontierIdentity
import RHLean.Analysis.MertensEnergyRHForward

/-!
# Prime-averaged Boolean-cube frontier energy implies RH

The arithmetic cube layer already proves an exact identity for every `X`:

`pi(X) * M(X) = sum_{ell <= X, ell prime} F_ell(X)`,

where `F_ell(X)` is the signed Möbius mass on the first-failure boundary for the
fresh prime coordinate `ell`.

This module turns that simultaneous multi-prime identity into a quantitative RH
strand.  A mean-square estimate for the whole family of prime-coordinate
frontiers controls `M(X)` directly by finite Cauchy--Schwarz.  The prime-count
factor cancels on both sides; no lower asymptotic for `pi(X)` is needed, only the
fact that the prime set is nonempty for `X >= 2`.

This is deliberately distinct from the closed single-prime dyadic Li route.  It
uses the complete family of fresh-prime Boolean-cube frontiers simultaneously.
No frontier-energy estimate is asserted unconditionally here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Complex Möbius mass of the first-failure Boolean-cube frontier at one fresh
prime coordinate. -/
def primeProductFrontierMobiusMass (X ell : ℕ) : ℂ :=
  ∑ t ∈ primeProductFirstFailureBoundary (primesUpTo X) X ell,
    (((μ (primeFaceProduct t) : ℤ) : ℂ))

/-- Total mean-square mass over all fresh-prime frontier coordinates. -/
def primeAveragedFrontierEnergy (X : ℕ) : ℝ :=
  ∑ ell ∈ primesUpTo X, ‖primeProductFrontierMobiusMass X ell‖ ^ 2

/-- The prime-averaged frontier identity in the repository's standard complex
Mertens coordinate. -/
theorem card_mul_mertensSummatory_eq_sum_primeProductFrontierMobiusMass
    (X : ℕ) :
    (((primesUpTo X).card : ℂ)) * mertensSummatory X =
      ∑ ell ∈ primesUpTo X, primeProductFrontierMobiusMass X ell := by
  have h := card_nsmul_moebiusPrefix_eq_sum_primeFrontiers X
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  simpa [primeProductFrontierMobiusMass, mertensSummatory, nsmul_eq_mul] using hc

private theorem norm_finset_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hnorm := norm_sum_le s f
  have hsum0 : 0 ≤ ∑ i ∈ s, ‖f i‖ :=
    Finset.sum_nonneg fun _i _hi => norm_nonneg _
  have hsq :
      ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsum0).2 hnorm
  have hcauchy :=
    Finset.sum_mul_sq_le_sq_mul_sq s
      (fun _i => (1 : ℝ)) (fun i => ‖f i‖)
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := hsq
    _ ≤ (∑ i ∈ s, (1 : ℝ) ^ 2) *
        (∑ i ∈ s, ‖f i‖ ^ 2) := by
      simpa using hcauchy
    _ = (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by simp

/-- Critical mean-square target for the complete family of prime-coordinate
first-failure frontiers.  The normalization by the number of prime coordinates
is exactly what finite Cauchy--Schwarz requires to recover critical Mertens
energy. -/
def PrimeAveragedFrontierEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ, 2 ≤ X →
        primeAveragedFrontierEnergy X ≤
          C * ((primesUpTo X).card : ℝ) *
            Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε)

/-- The simultaneous multi-prime frontier-energy estimate implies the protected
Mertens-energy criterion.  The prime-count factor cancels algebraically, so no
quantitative prime-number theorem is consumed by this reduction. -/
theorem mertensEnergyBounded_of_primeAveragedFrontierEnergy
    (hF : PrimeAveragedFrontierEnergyBoundedStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hCb⟩ := hF ε hε
  let D : ℝ := C + 1
  have hD0 : 0 ≤ D := by dsimp [D]; linarith
  refine ⟨D, hD0, ?_⟩
  intro X
  by_cases hX : 2 ≤ X
  · let S : Finset ℕ := primesUpTo X
    let P : ℝ := (S.card : ℝ)
    let E : ℝ := primeAveragedFrontierEnergy X
    let Q : ℝ := Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε)
    have h2mem : 2 ∈ S := by
      dsimp [S]
      exact mem_primesUpTo.mpr ⟨Nat.prime_two, hX⟩
    have hScard : 0 < S.card := Finset.card_pos.mpr ⟨2, h2mem⟩
    have hP : 0 < P := by dsimp [P]; exact_mod_cast hScard
    have hQ0 : 0 ≤ Q := by
      dsimp [Q]
      exact Real.rpow_nonneg (by positivity) _
    have hfamily :=
      norm_finset_sum_sq_le_card_mul_sum_norm_sq S
        (fun ell => primeProductFrontierMobiusMass X ell)
    have hid :=
      card_mul_mertensSummatory_eq_sum_primeProductFrontierMobiusMass X
    have hcauchy :
        ‖((S.card : ℂ)) * mertensSummatory X‖ ^ 2 ≤ P * E := by
      rw [hid]
      simpa [S, P, E, primeAveragedFrontierEnergy] using hfamily
    have hleft :
        ‖((S.card : ℂ)) * mertensSummatory X‖ ^ 2 =
          P * (P * ‖mertensSummatory X‖ ^ 2) := by
      rw [norm_mul, Complex.norm_natCast]
      dsimp [P]
      ring
    rw [hleft] at hcauchy
    have hcancel1 : P * ‖mertensSummatory X‖ ^ 2 ≤ E :=
      (mul_le_mul_iff_right₀ hP).mp hcauchy
    have henergy0 := hCb X hX
    have henergy : E ≤ C * P * Q := by
      simpa [S, P, E, Q] using henergy0
    have hcombined :
        P * ‖mertensSummatory X‖ ^ 2 ≤ P * (C * Q) := by
      calc
        P * ‖mertensSummatory X‖ ^ 2 ≤ E := hcancel1
        _ ≤ C * P * Q := henergy
        _ = P * (C * Q) := by ring
    have hmain : ‖mertensSummatory X‖ ^ 2 ≤ C * Q :=
      (mul_le_mul_iff_right₀ hP).mp hcombined
    have hCD : C ≤ D := by dsimp [D]; linarith
    have hraise : C * Q ≤ D * Q :=
      mul_le_mul_of_nonneg_right hCD hQ0
    simpa [D, Q] using hmain.trans hraise
  · have hsmall : X = 0 ∨ X = 1 := by omega
    rcases hsmall with rfl | rfl
    · simpa [mertensSummatory] using hD0
    · have hpow :
          (1 : ℝ) ≤ Real.rpow (2 : ℝ) (1 + ε) :=
        Real.one_le_rpow (by norm_num) (by linarith)
      have hD1 : (1 : ℝ) ≤ D := by dsimp [D]; linarith
      have hone :
          (1 : ℝ) ≤ D * Real.rpow (2 : ℝ) (1 + ε) := by
        calc
          (1 : ℝ) ≤ D := hD1
          _ ≤ D * Real.rpow (2 : ℝ) (1 + ε) := by
            simpa using mul_le_mul_of_nonneg_left hpow hD0
      simpa [mertensSummatory, Finset.sum_range_succ] using hone

/-- Independent RH strand: a critical mean-square estimate for the complete
family of multi-prime Boolean-cube first-failure frontiers implies the Riemann
hypothesis through the already-kernel-checked Mertens-energy continuation. -/
theorem riemannHypothesis_of_primeAveragedFrontierEnergy
    (hF : PrimeAveragedFrontierEnergyBoundedStatement) :
    RiemannHypothesisStatement := by
  change RiemannHypothesis
  exact riemannHypothesis_of_mertensEnergy
    (mertensEnergyBounded_of_primeAveragedFrontierEnergy hF)

end RHLean.Analysis
