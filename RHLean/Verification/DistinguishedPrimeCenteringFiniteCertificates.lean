import Mathlib
import RHLean.Analysis.MertensEnergyCriterion
import RHLean.Analysis.PhysicalCenteredDistinguishedPrimeOperator

/-!
# Finite certificates for centered distinguished-prime contraction

This verification module tests the centering and scalar-contraction architecture
against the actual three-slot Mobius cells.

For one prime `q`, a cell is called Mertens-visible active when `q` divides one
of the three physical values `4*k+1`, `4*k+2`, `4*k+3` and the Mobius value of
that hit is nonzero.  The active state records the physical slot together with
the sign of that Mobius value.  All other cells are placed in the inactive
state.  For `q > 6`, adjacent active states are arithmetically impossible by the
existing distinguished-prime support theorem.

From the finite square-root carrier we form exact transition counts and the
empirical row-normalized rational kernel.  We then center only the six active
destination coefficients, exactly as in
`PhysicalCenteredDistinguishedPrimeOperator`, and test the squared form of the
scalar criterion from `MertensEnergyCriterion`:

`alpha + beta * gamma < 1`.

Because all quantities are nonnegative, the test can be performed over exact
rationals without introducing numerical square roots:

`beta^2 * gamma^2 < (1 - alpha)^2` together with `alpha < 1`.

This is a finite diagnostic certificate, not a claim that row normalization is
the final canonical physical operator normalization.  Its purpose is to test
whether the newly certified sparse centering mechanism survives contact with
the real Mobius sign data before the remaining normalization bridge is chosen.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Verification

open RHLean.Analysis RHLean.Arithmetic RHLean.Proof

/-- Number of adjacent-cell transitions whose destination three-slot cell is
fully contained below `R^2 - 1`. -/
def distinguishedPrimeTransportTransitionCount (R : ℕ) : ℕ :=
  (squareRootEndpoint R - 3) / 4

/-- Bool encoding of a nonzero Mobius sign.  `true` means `+1`; `false` means
`-1`.  This helper is only called after nonvanishing has been checked. -/
def visibleMoebiusSignBit (n : ℕ) : Bool :=
  decide (μ n = 1)

/-- Mertens-visible signed fixed-prime state of one physical three-slot cell.
A `q`-hit whose Mobius value is zero is deliberately assigned to the inactive
sector, matching the separation of the zero-containing defect in the physical
degree-one architecture. -/
def empiricalDistinguishedPrimeState (q k : ℕ) : SignedPrimeHitState :=
  let n0 := threeSlotValue k 0
  let n1 := threeSlotValue k 1
  let n2 := threeSlotValue k 2
  if q ∣ n0 ∧ μ n0 ≠ 0 then
    some ((0 : Fin 3), visibleMoebiusSignBit n0)
  else if q ∣ n1 ∧ μ n1 ≠ 0 then
    some ((1 : Fin 3), visibleMoebiusSignBit n1)
  else if q ∣ n2 ∧ μ n2 ≠ 0 then
    some ((2 : Fin 3), visibleMoebiusSignBit n2)
  else
    none

/-- Exact count of one empirical fixed-prime state transition on the square-root
carrier. -/
def empiricalDistinguishedPrimeTransitionCount
    (R q : ℕ) (s t : SignedPrimeHitState) : ℕ :=
  ((Finset.range (distinguishedPrimeTransportTransitionCount R)).filter fun k =>
    empiricalDistinguishedPrimeState q k = s ∧
      empiricalDistinguishedPrimeState q (k + 1) = t).card

/-- Exact source-row population. -/
def empiricalDistinguishedPrimeSourceCount
    (R q : ℕ) (s : SignedPrimeHitState) : ℕ :=
  ∑ t : SignedPrimeHitState,
    empiricalDistinguishedPrimeTransitionCount R q s t

/-- Row-normalized empirical kernel.  An unobserved source row is assigned zero,
so the definition is total. -/
def empiricalDistinguishedPrimeRowKernel
    (R q : ℕ) (s t : SignedPrimeHitState) : ℚ :=
  let row := empiricalDistinguishedPrimeSourceCount R q s
  if row = 0 then 0
  else
    (empiricalDistinguishedPrimeTransitionCount R q s t : ℚ) / (row : ℚ)

/-- Inactive scalar coefficient of the empirical row-normalized kernel. -/
def empiricalDistinguishedPrimeAlpha (R q : ℕ) : ℚ :=
  empiricalDistinguishedPrimeRowKernel R q none none

/-- Mean of the six inactive-source to active-destination coefficients. -/
def empiricalDistinguishedPrimeActiveMean (R q : ℕ) : ℚ :=
  (∑ t : PrimeActiveLabel,
    empiricalDistinguishedPrimeRowKernel R q none (some t)) / 6

/-- Centered inactive-source to active-destination coefficient. -/
def empiricalDistinguishedPrimeCenteredB
    (R q : ℕ) (t : PrimeActiveLabel) : ℚ :=
  empiricalDistinguishedPrimeRowKernel R q none (some t) -
    empiricalDistinguishedPrimeActiveMean R q

/-- Exact squared Euclidean norm of the six centered active-destination
coefficients. -/
def empiricalDistinguishedPrimeBetaSq (R q : ℕ) : ℚ :=
  ∑ t : PrimeActiveLabel,
    empiricalDistinguishedPrimeCenteredB R q t ^ 2

/-- Exact squared Euclidean norm of the six active-source to inactive-destination
coefficients. -/
def empiricalDistinguishedPrimeGammaSq (R q : ℕ) : ℚ :=
  ∑ s : PrimeActiveLabel,
    empiricalDistinguishedPrimeRowKernel R q (some s) none ^ 2

/-- Exact rational squared form of the strict scalar contraction gate.

When `alpha`, `beta`, and `gamma` are nonnegative, this is equivalent to
`alpha + beta * gamma < 1`, with `beta^2` and `gamma^2` given by the two exact
squared norms above. -/
def EmpiricalDistinguishedPrimeScalarGate (R q : ℕ) : Prop :=
  0 ≤ empiricalDistinguishedPrimeAlpha R q ∧
    empiricalDistinguishedPrimeAlpha R q < 1 ∧
    empiricalDistinguishedPrimeBetaSq R q *
        empiricalDistinguishedPrimeGammaSq R q <
      (1 - empiricalDistinguishedPrimeAlpha R q) ^ 2

instance empiricalDistinguishedPrimeScalarGateDecidable (R q : ℕ) :
    Decidable (EmpiricalDistinguishedPrimeScalarGate R q) := by
  unfold EmpiricalDistinguishedPrimeScalarGate
  infer_instance

/-- The empirical kernel has the same active-to-active forced-zero support on a
checked finite carrier. -/
def EmpiricalDistinguishedPrimeSupportGate (R q : ℕ) : Prop :=
  ∀ s t : PrimeActiveLabel,
    empiricalDistinguishedPrimeTransitionCount R q (some s) (some t) = 0

instance empiricalDistinguishedPrimeSupportGateDecidable (R q : ℕ) :
    Decidable (EmpiricalDistinguishedPrimeSupportGate R q) := by
  unfold EmpiricalDistinguishedPrimeSupportGate
  infer_instance

/-- Combined exact finite diagnostic. -/
def EmpiricalDistinguishedPrimeValidation (R q : ℕ) : Prop :=
  R < q ∧ q.Prime ∧
    EmpiricalDistinguishedPrimeSupportGate R q ∧
    EmpiricalDistinguishedPrimeScalarGate R q

instance empiricalDistinguishedPrimeValidationDecidable (R q : ℕ) :
    Decidable (EmpiricalDistinguishedPrimeValidation R q) := by
  unfold EmpiricalDistinguishedPrimeValidation
  infer_instance

/-- Exhaustive transport-prime scan at `R = 50`: every prime
`50 < q ≤ 50^2 - 1` passes both the exact support test and the centered squared
scalar contraction gate. -/
theorem empiricalDistinguishedPrimeValidation_R50 :
    ∀ q ∈ Finset.Ioc 50 (squareRootEndpoint 50),
      q.Prime → EmpiricalDistinguishedPrimeValidation 50 q := by
  native_decide

/-- Near-cutoff sample at `R = 100`. -/
theorem empiricalDistinguishedPrimeValidation_R100_q101 :
    EmpiricalDistinguishedPrimeValidation 100 101 := by
  native_decide

/-- Sparse high-fibre sample at `R = 100`, close to half of the square endpoint.
This is a severe finite-data test because only a tiny number of visible hits are
available. -/
theorem empiricalDistinguishedPrimeValidation_R100_q5003 :
    EmpiricalDistinguishedPrimeValidation 100 5003 := by
  native_decide

/-- Larger-cutoff near-boundary prime sample. -/
theorem empiricalDistinguishedPrimeValidation_R200_q20011 :
    EmpiricalDistinguishedPrimeValidation 200 20011 := by
  native_decide

end RHLean.Verification
