import Mathlib
import RHLean.Analysis.PhysicalCenteredDistinguishedPrimeOperator
import RHLean.Analysis.PrimeWheelRecoveredMertensCriterion
import RHLean.Analysis.SquareRootTransportRealization

/-!
# Exact square-root wheel to physical signed reconstruction

This module begins the missing exact bridge between the canonical minimal
square-root prime wheel and the physical distinguished-prime transition data.
The goal is signal-level arithmetic reconstruction before any norm or analytic
estimate is introduced.

The first layer proves that every cofactor weight used by the physical
`(R,q)` fibre is literally the corrected square-root prime-wheel value on that
cofactor.  The equality is then propagated through the physical cell and
adjacent-transition fibre sums.

No estimate, stochastic assumption, new axiom, or RH input is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- At the exact complete-square endpoint, the canonical minimal square-root
wheel is literally the repository's square-prefix Mertens value. -/
theorem sqrtWheelRecoveredPrefix_cast_eq_squarePrefixMertens
    (n : ℕ) :
    ((sqrtWheelRecoveredPrefix (squarePrefixEndpoint n) : ℤ) : ℂ) =
      squarePrefixMertens n := by
  simpa [squarePrefixMertens] using
    sqrtWheelRecoveredPrefix_cast_eq_mertensSummatory
      (squarePrefixEndpoint n)

/-- Read one physical lower-cofactor weight directly from the corrected minimal
square-root prime wheel at the same physical cutoff. -/
def sqrtWheelCofactorWeight (R c : ℕ) : ℂ :=
  ((correctedPrimeWheelSite
      (primesUpTo (Nat.sqrt (squareRootEndpoint R)))
      (squareRootEndpoint R) c : ℤ) : ℂ)

/-- Every cofactor in the actual physical domain `1 <= c < R` is recovered
exactly as its canonical Möbius weight by the minimal square-root wheel. -/
theorem sqrtWheelCofactorWeight_eq_canonical
    {R c : ℕ}
    (hc : c ∈ Finset.Ico 1 R) :
    sqrtWheelCofactorWeight R c = canonicalMoebiusWeight c := by
  have hcData := Finset.mem_Ico.mp hc
  have hcPos : 0 < c := by omega
  have hR2 : 2 ≤ R := by omega
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hcX : c ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hmu :
      correctedPrimeWheelSite
          (primesUpTo (Nat.sqrt (squareRootEndpoint R)))
          (squareRootEndpoint R) c =
        μ c := by
    exact correctedPrimeWheelSite_eq_moebius
      (primesUpTo (Nat.sqrt (squareRootEndpoint R)))
      (by
        intro p hp
        exact prime_of_mem_primesUpTo hp)
      (primesUpTo_sqrtCoverage (squareRootEndpoint R))
      hcPos hcX
  simp [sqrtWheelCofactorWeight, canonicalMoebiusWeight, hmu]

/-- The physical cell fibre written with the actual corrected square-root wheel
instead of an already-named Möbius weight. -/
def sqrtWheelPhysicalCellFibreMass
    (R q k : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    if c * q ≤ squareRootEndpoint R ∧
        ∃ i : Fin 3, c * q = threeSlotValue k i then
      sqrtWheelCofactorWeight R c
    else
      0

/-- The wheel-explicit cell fibre is coefficient-for-coefficient the existing
physical signed cofactor fibre. -/
theorem sqrtWheelPhysicalCellFibreMass_eq_physical
    (R q k : ℕ) :
    sqrtWheelPhysicalCellFibreMass R q k =
      physicalDistinguishedPrimeCellFibreMass R q k := by
  classical
  unfold sqrtWheelPhysicalCellFibreMass
    physicalDistinguishedPrimeCellFibreMass
  apply Finset.sum_congr rfl
  intro c hc
  rw [sqrtWheelCofactorWeight_eq_canonical hc]

/-- The wheel-explicit signed mass on one adjacent six-site physical transition. -/
def sqrtWheelPhysicalLocalTransitionFibreMass
    (R q k : ℕ) : ℂ :=
  sqrtWheelPhysicalCellFibreMass R q k +
    sqrtWheelPhysicalCellFibreMass R q (k + 1)

/-- The local adjacent-transition mass is therefore exactly the physical one. -/
theorem sqrtWheelPhysicalLocalTransitionFibreMass_eq_physical
    (R q k : ℕ) :
    sqrtWheelPhysicalLocalTransitionFibreMass R q k =
      physicalDistinguishedPrimeLocalTransitionFibreMass R q k := by
  simp [sqrtWheelPhysicalLocalTransitionFibreMass,
    physicalDistinguishedPrimeLocalTransitionFibreMass,
    sqrtWheelPhysicalCellFibreMass_eq_physical]

/-- One fixed-prime transition class, with the actual physical signed state
labels but wheel-explicit cofactor weights. -/
def sqrtWheelPhysicalTransitionMass
    (R q : ℕ) (s t : SignedPrimeHitState) : ℂ :=
  ∑ k ∈ Finset.range (physicalDistinguishedPrimeCarrierLength R),
    if physicalDistinguishedPrimeState R q k = s ∧
        physicalDistinguishedPrimeState R q (k + 1) = t then
      sqrtWheelPhysicalLocalTransitionFibreMass R q k
    else
      0

/-- Every wheel-explicit transition coefficient is exactly the corresponding
physical signed transition coefficient. -/
theorem sqrtWheelPhysicalTransitionMass_eq_physical
    (R q : ℕ) (s t : SignedPrimeHitState) :
    sqrtWheelPhysicalTransitionMass R q s t =
      physicalDistinguishedPrimeTransitionMass R q s t := by
  classical
  unfold sqrtWheelPhysicalTransitionMass
    physicalDistinguishedPrimeTransitionMass
  apply Finset.sum_congr rfl
  intro k hk
  rw [sqrtWheelPhysicalLocalTransitionFibreMass_eq_physical]

/-- Raw fixed-prime kernel instantiated directly from the minimal square-root
wheel and the actual physical signed-state field. -/
def sqrtWheelPhysicalRawKernel
    (R q : ℕ) : SignedPrimeHitState → SignedPrimeHitState → ℂ :=
  fun s t => sqrtWheelPhysicalTransitionMass R q s t

/-- The wheel-instantiated raw kernel is literally the repository's physical
raw kernel; primality and scale hypotheses are used only to match its API, not
to prove the arithmetic equality. -/
theorem sqrtWheelPhysicalRawKernel_eq_physical
    (R q : ℕ) (hq : q.Prime) (hRq : R < q) :
    sqrtWheelPhysicalRawKernel R q =
      physicalDistinguishedPrimeRawKernel R q hq hRq := by
  funext s t
  exact sqrtWheelPhysicalTransitionMass_eq_physical R q s t

end RHLean.Analysis
