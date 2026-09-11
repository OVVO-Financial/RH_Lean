import RHLean.Proof.TwoWheelQ2GoCompatibility

/-!
# Exceptional scalar daughters and the prime-insertion coboundary

The chronological high column already is an exact prime coboundary. Its
potential is the frozen cube at the original cutoff, so completing the prime
chronology leaves the full Mertens value as the terminal potential.

For the exceptional owners `3,5,7` the predecessor cubes are finite, with
products `2,6,30`. They vanish identically after those cutoffs. Consequently,
at `X >= 1470` every scalar Go daughter in this owner set is zero and its
signed recovered daughter is entirely negative high transport. In particular,
the scalar `FF-FT-TF+TT` Gram has only its `TT` term left there.

These statements concern the scalar Go/high-column dictionary. They do not
identify the complete physical incidence packet with a scalar daughter, and
they do not assert an energy estimate or a failure of possible cancellation
inside the high-transport Gram.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- The high-prime column in the exact recovered q-square daughter identity. -/
def q2DaughterHighTransport (q X : ℕ) : ℤ :=
  ∑ p ∈ frozenPrimeUniverseHighPrimeSet (q - 1) (X / (q * q)),
    frozenPrimeUniverseMass (primesUpTo (p - 1)) ((X / (q * q)) / p)

/-- A finite prime-insertion coboundary, including its terminal potential.
The cutoff is `X/q²` on both potentials; it has not decreased further. -/
theorem q2DaughterHighTransport_eq_go_sub_mertens
    {q X : ℕ} (hcut : q - 1 ≤ X / (q * q)) :
    q2DaughterHighTransport q X =
      squareRootLowPrimeGoWallSquareResidual q X -
        mertensSummatoryInt (X / (q * q)) := by
  have h := mertensDaughter_eq_goDaughter_sub_highOwnerColumn
    (q := q) (X := X) hcut
  change mertensSummatoryInt (X / (q * q)) =
    squareRootLowPrimeGoWallSquareResidual q X - q2DaughterHighTransport q X at h
  linarith

/-- Completing the predecessor cube kills the frozen scalar daughter. -/
theorem q2GoDaughter_eq_zero_of_predecessorCube_complete
    {q X : ℕ} (hq : 2 < q)
    (hfit : primeFaceProduct (primesUpTo (q - 1)) ≤ X / (q * q)) :
    squareRootLowPrimeGoWallSquareResidual q X = 0 := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff]
  apply frozenPrimeUniverseMass_eq_zero_of_complete_old_cube
  · refine ⟨2, mem_primesUpTo_of_prime_le Nat.prime_two ?_⟩
    omega
  · intro p hp
    exact prime_of_mem_primesUpTo hp
  · exact hfit

/-- Beyond predecessor-cube completion the entire scalar daughter is carried
by high transport; the prime telescope retains the Mertens terminal value. -/
theorem q2DaughterHighTransport_eq_neg_mertens_of_predecessorCube_complete
    {q X : ℕ} (hq : 2 < q)
    (hfit : primeFaceProduct (primesUpTo (q - 1)) ≤ X / (q * q))
    (hcut : q - 1 ≤ X / (q * q)) :
    q2DaughterHighTransport q X =
      -mertensSummatoryInt (X / (q * q)) := by
  rw [q2DaughterHighTransport_eq_go_sub_mertens hcut,
    q2GoDaughter_eq_zero_of_predecessorCube_complete hq hfit, zero_sub]

/-- The owner-five predecessor cube fits precisely from daughter cutoff six. -/
theorem q2GoDaughter_five_eq_zero {X : ℕ} (hX : 150 ≤ X) :
    squareRootLowPrimeGoWallSquareResidual 5 X = 0 := by
  apply q2GoDaughter_eq_zero_of_predecessorCube_complete (by norm_num)
  have hprod : primeFaceProduct (primesUpTo (5 - 1)) = 6 := by native_decide
  rw [hprod]
  omega

/-- The owner-seven predecessor cube fits from daughter cutoff thirty. -/
theorem q2GoDaughter_seven_eq_zero {X : ℕ} (hX : 1470 ≤ X) :
    squareRootLowPrimeGoWallSquareResidual 7 X = 0 := by
  apply q2GoDaughter_eq_zero_of_predecessorCube_complete (by norm_num)
  have hprod : primeFaceProduct (primesUpTo (7 - 1)) = 30 := by native_decide
  rw [hprod]
  omega

/-- All three exceptional scalar frozen daughters vanish beyond one explicit
cutoff. This does not assert that their physical incidence operators vanish. -/
theorem exceptionalGoDaughter_eq_zero
    {q X : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) (hX : 1470 ≤ X) :
    squareRootLowPrimeGoWallSquareResidual q X = 0 := by
  rcases hq with rfl | rfl | rfl
  · exact squareRootLowPrimeGoWallSquareResidual_three_eq_zero (by omega)
  · exact q2GoDaughter_five_eq_zero (by omega)
  · exact q2GoDaughter_seven_eq_zero hX

/-- Exact signed exceptional high columns, with no norm taken. -/
theorem exceptionalHighTransport_eq_neg_mertens
    {q X : ℕ} (hq : q = 3 ∨ q = 5 ∨ q = 7) (hX : 1470 ≤ X) :
    q2DaughterHighTransport q X =
      -mertensSummatoryInt (X / (q * q)) := by
  have hcut : q - 1 ≤ X / (q * q) := by
    rcases hq with rfl | rfl | rfl <;> omega
  rw [q2DaughterHighTransport_eq_go_sub_mertens hcut,
    exceptionalGoDaughter_eq_zero hq hX, zero_sub]

/-- Each entry of the *scalar daughter* signed Gram has only its high/high
piece left after the exceptional predecessor cubes complete. This is not a
replacement for the still-unidentified physical packet Gram. -/
theorem exceptionalScalarDaughterGram_eq_highTransportGram
    {q r X : ℕ}
    (hq : q = 3 ∨ q = 5 ∨ q = 7)
    (hr : r = 3 ∨ r = 5 ∨ r = 7) (hX : 1470 ≤ X) :
    (squareRootLowPrimeGoWallSquareResidual q X - q2DaughterHighTransport q X) *
        (squareRootLowPrimeGoWallSquareResidual r X - q2DaughterHighTransport r X) =
      q2DaughterHighTransport q X * q2DaughterHighTransport r X := by
  rw [exceptionalGoDaughter_eq_zero hq hX, exceptionalGoDaughter_eq_zero hr hX]
  ring

end RHLean.Proof
