import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery
import RHLean.Analysis.MertensEnergyRHForward
import RHLean.Analysis.SquarePrefixMertensBridge

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-!
# Recovered square-root wheel as the exact Mertens criterion

The arithmetic layer proves that a square-root-covered prime wheel recovers the
joint signed quantity `raw - 2 * smooth` exactly as the Möbius prefix.  This
module packages the canonical minimal square-root wheel and shows that a
critical energy estimate for that single signed quantity is exactly the existing
Mertens-energy criterion, hence exactly the square-prefix criterion already used
by the square-block route.

No quantitative estimate is asserted here.  The open theorem is isolated as the
boundedness statement below.
-/

/-- The canonical minimal square-root wheel prefix at physical cutoff `X`.
Only prime coordinates through `sqrt X` are used, and the smooth-core correction
is retained inside the signed object. -/
def sqrtWheelRecoveredPrefix (X : ℕ) : ℤ :=
  primeWheelRawPositivePrefix (primesUpTo (Nat.sqrt X)) X -
    2 * primeWheelSmoothPositivePrefix (primesUpTo (Nat.sqrt X)) X X

/-- The canonical prime set through `sqrt X` has exactly the coverage required
by the pointwise prime-wheel recovery theorem. -/
theorem primesUpTo_sqrtCoverage (X : ℕ) :
    PrimeWheelSqrtCoverage (primesUpTo (Nat.sqrt X)) X := by
  intro p hp hple
  exact mem_primesUpTo.mpr ⟨hp, hple⟩

/-- Exact arithmetic recovery for the canonical minimal square-root wheel. -/
theorem sqrtWheelRecoveredPrefix_eq_moebiusPositivePrefix (X : ℕ) :
    sqrtWheelRecoveredPrefix X = moebiusPositivePrefix X := by
  unfold sqrtWheelRecoveredPrefix
  exact primeWheelRaw_sub_two_smooth_eq_moebiusPositivePrefix
    (primesUpTo (Nat.sqrt X)) X X
    (by
      intro p hp
      exact prime_of_mem_primesUpTo hp)
    (primesUpTo_sqrtCoverage X) le_rfl

/-- The canonical recovered wheel is exactly the repository's standard integer
Möbius prefix. -/
theorem sqrtWheelRecoveredPrefix_eq_moebiusPrefix (X : ℕ) :
    sqrtWheelRecoveredPrefix X =
      ∑ n ∈ Finset.range (X + 1), μ n := by
  rw [sqrtWheelRecoveredPrefix_eq_moebiusPositivePrefix,
    moebiusPositivePrefix_eq_moebiusPrefix]

/-- After the harmless integer-to-complex cast, the recovered wheel prefix is
literally the analytic Mertens summatory function used downstream. -/
theorem sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory (X : ℕ) :
    ((sqrtWheelRecoveredPrefix X : ℤ) : ℂ) = mertensSummatory X := by
  rw [sqrtWheelRecoveredPrefix_eq_moebiusPrefix]
  simp [mertensSummatory]

/-- The exact quantitative target for the canonical square-root wheel.  This is
the squared form of the desired `X^(1/2+ε)` cancellation, expressed without
splitting raw and smooth mass. -/
def SqrtWheelRecoveredEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ,
        ‖((sqrtWheelRecoveredPrefix X : ℤ) : ℂ)‖ ^ 2 ≤
          C * Real.rpow ((X + 1 : ℕ) : ℝ) (1 + ε)

/-- The recovered square-root wheel estimate is exactly the protected global
Mertens-energy criterion.  Thus proving the former loses no cancellation and
requires no additional analytic transfer theorem. -/
theorem sqrtWheelRecoveredEnergyBounded_iff_mertensEnergyBounded :
    SqrtWheelRecoveredEnergyBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro X
    have hx := hbound X
    rw [sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory X] at hx
    exact hx
  · intro h ε hε
    rcases h ε hε with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro X
    rw [sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory X]
    exact hbound X

/-- The same target is therefore exactly equivalent to the repository's
square-prefix energy criterion.  This is the formal square-block compatibility
statement for the recovered prime-wheel quantity. -/
theorem sqrtWheelRecoveredEnergyBounded_iff_squarePrefixEnergyBounded :
    SqrtWheelRecoveredEnergyBoundedStatement ↔
      SquarePrefixEnergyBoundedStatement := by
  exact sqrtWheelRecoveredEnergyBounded_iff_mertensEnergyBounded.trans
    mertensEnergyBounded_iff_squarePrefixEnergyBounded

/-- The existing Mertens continuation and completed-zeta reflection route turns
a proof of the recovered square-root wheel bound directly into RH. -/
theorem riemannHypothesis_of_sqrtWheelRecoveredEnergy
    (h : SqrtWheelRecoveredEnergyBoundedStatement) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  exact sqrtWheelRecoveredEnergyBounded_iff_mertensEnergyBounded.mp h

/-! ## Terminal square-clock state

At this point the recovered wheel is treated as one indivisible analytic state.
No subsequent theorem in this section splits its raw, smooth, deletion, sign, or
endpoint constituents before taking the terminal energy bound.
-/

/-- The final recombined wheel state at square scale `R`, evaluated at the
complete endpoint `R^2 - 1`.  All signed prime-wheel corrections remain inside
this one object. -/
def recombinedWheelState (R : ℕ) : ℂ :=
  ((sqrtWheelRecoveredPrefix (R ^ 2 - 1) : ℤ) : ℂ)

/-- Exact identification of the frozen recombined state with Mertens at the
same complete-square endpoint. -/
theorem recombinedWheelState_eq_mertensSummatory (R : ℕ) :
    recombinedWheelState R = mertensSummatory (R ^ 2 - 1) := by
  unfold recombinedWheelState
  exact sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory (R ^ 2 - 1)

/-- At positive square scale the frozen recombined state is exactly the
repository's square-prefix Mertens value. -/
theorem recombinedWheelState_eq_squarePrefixMertens
    {R : ℕ} (hR : 1 ≤ R) :
    recombinedWheelState R = squarePrefixMertens (R - 1) := by
  rw [recombinedWheelState_eq_mertensSummatory]
  unfold squarePrefixMertens squarePrefixEndpoint
  have hpred : R - 1 + 1 = R := by omega
  rw [hpred]

/-- **Terminal analytic premise.**  Every cancellation mechanism remains inside
`recombinedWheelState`; no component is bounded separately. -/
def RecombinedWheelStateEnergyBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℕ, 2 ≤ R →
        ‖recombinedWheelState R‖ ^ 2 ≤
          C * Real.rpow ((R : ℝ) ^ 2) (1 + ε)

private theorem terminal_rpow_square_one_add_half
    (x ε : ℝ) (hx : 0 ≤ x) :
    Real.rpow (x ^ 2) (1 + ε / 2) =
      Real.rpow x (2 + ε) := by
  have htwo : Real.rpow x (2 : ℝ) = x ^ (2 : ℕ) :=
    Real.rpow_natCast x 2
  calc
    Real.rpow (x ^ 2) (1 + ε / 2) =
        Real.rpow (Real.rpow x (2 : ℝ)) (1 + ε / 2) :=
      congrArg (fun t : ℝ => Real.rpow t (1 + ε / 2)) htwo.symm
    _ = Real.rpow x ((2 : ℝ) * (1 + ε / 2)) :=
      (Real.rpow_mul hx (2 : ℝ) (1 + ε / 2)).symm
    _ = Real.rpow x (2 + ε) := by ring_nf

/-- A bound on the single frozen state gives the existing RH-scale square-prefix
Mertens energy criterion.  The only exponent change is the harmless
reparameterization `ε ↦ ε / 2`. -/
theorem squarePrefixEnergyBounded_of_recombinedWheelStateEnergy
    (h : RecombinedWheelStateEnergyBound) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  rcases h (ε / 2) (by linarith) with ⟨C, hC, hbound⟩
  refine ⟨C, le_of_lt hC, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simpa [squarePrefixMertens, squarePrefixEndpoint] using (le_of_lt hC)
  · have hR : 2 ≤ n + 1 := by omega
    have hs := hbound (n + 1) hR
    have hstate :
        recombinedWheelState (n + 1) = squarePrefixMertens n := by
      simpa using
        (recombinedWheelState_eq_squarePrefixMertens
          (R := n + 1) (by omega : 1 ≤ n + 1))
    rw [hstate] at hs
    rw [terminal_rpow_square_one_add_half
      ((n + 1 : ℕ) : ℝ) ε (by positivity)] at hs
    exact hs

/-- The established square-prefix sampling theorem and Mertens continuation
route send an RH-scale square-prefix energy bound to the Riemann hypothesis. -/
theorem riemannHypothesis_of_squarePrefixEnergyBound
    (h : SquarePrefixEnergyBoundedStatement) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  exact mertensEnergyBounded_of_squarePrefixEnergyBounded h

/-- **Terminal chain.**  The one recombined-state bound implies the RH-scale
square-prefix Mertens bound and therefore the Riemann hypothesis. -/
theorem riemannHypothesis_of_recombinedWheelStateEnergy
    (h : RecombinedWheelStateEnergyBound) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_squarePrefixEnergyBound
    (squarePrefixEnergyBounded_of_recombinedWheelStateEnergy h)

end RHLean.Analysis
