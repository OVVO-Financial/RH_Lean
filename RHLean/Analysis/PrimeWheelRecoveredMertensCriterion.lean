import Mathlib
import RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery
import RHLean.Analysis.MertensEnergyRHForward
import RHLean.Analysis.SquarePrefixMertensBridge

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

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

/-! ## Exact wheel instantiation of the physical signed fibres -/

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

end RHLean.Analysis
