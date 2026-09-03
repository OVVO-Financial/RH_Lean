import Mathlib
import RHLean.Analysis.NativePNTSignedLocalSurplus
import RHLean.Analysis.OptimalLogBase

/-!
# Sequential Viole cross energy on the resolved Euler carrier

The adjacent Viole seed exposed in `OptimalLogBase` has two exact descriptions:

* `D(M,L) = E(L)-E(M)` and `X(M,L) = E(M)D(M,L)`;
* the shared old-fibre drift is a Mobius logarithmic reciprocal transform.

This file connects those descriptions to the already-compiled signed Euler
machinery.  The key observation is that when the same wheel cutoff `y` resolves
both endpoints (`M,L < 2*y^2`), the signed Selberg remainder disappears from
the endpoint difference.  The whole discrepancy is then one explicit Euler
forcing:

`D = shared reciprocal drift - resolved-wheel drift - (L-M)`.

There is an even more direct block form at every subdoubling endpoint.  The
new-fibre mass is exactly the existing protected square-block Mobius
correlation, so

`D = -(protected block correlation + (L-M))`.

Thus the endpoint update is literally `E(L) = E(M) - P`, where `P` is the
protected block pull, and the complete energy change is

`P^2 - 2 E(M) P`.

For Viole cutoffs the common choice `y=r` resolves both endpoints from `r>=4`;
the protected-block form already holds from the subdoubling onset `r>=3`.
No absolute remainder, probability, independence, or auxiliary covariance
envelope enters.

The shared reciprocal drift is also expanded atom-by-atom.  On those sequential
atoms adjoining one fresh prime has exactly the same Mobius cancellation law as
`NativePNTSignedLocalSurplus`, with an exact positive absolute surplus.  The
protected block itself already has the repository's reciprocal fresh-prime law,
physical-defect ledger, and Abel return.  These are now two exact views of the
same one-step energy update.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-! ## Sequential reciprocal atoms -/

/-- One signed reciprocal Mobius atom for the endpoint difference `L-M`.
The carrier is the old prefix `m*k <= M`; only the endpoint response changes. -/
def nativePNTSequentialMobiusSignedAtom
    (M L m k : Nat) : Real :=
  (μ : ArithmeticFunction Real) m * Real.log (k : Real) *
    (nativePNTError (L / (m * k)) - nativePNTError (M / (m * k)))

/-- The #555 shared reciprocal drift is literally the sum of the sequential
signed atoms on the old reciprocal carrier. -/
theorem nativePNTSequentialSharedMobiusReciprocalMass_eq_sum_atoms
    (M L : Nat) :
    nativePNTSequentialSharedMobiusReciprocalMass M L =
      ∑ m ∈ Finset.Icc 1 M,
        ∑ k ∈ Finset.Icc 1 (M / m),
          nativePNTSequentialMobiusSignedAtom M L m k := by
  unfold nativePNTSequentialSharedMobiusReciprocalMass
    nativePNTMobiusLogReciprocalMass nativePNTMobiusLogReciprocalFiber
    nativePNTSequentialMobiusSignedAtom
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- **Fresh-prime law on the sequential endpoint-difference atom.**
The two atoms `(m,p*k)` and `(m*p,k)` have the same endpoint difference, so
Mobius sign reversal removes the duplicated `log k` contribution and leaves
exactly `log p`. -/
theorem nativePNTSequentialMobiusSignedAtom_pair_adjoin_prime
    (M L m p k : Nat) (hk : 1 <= k)
    (hp : p.Prime) (hcop : Nat.Coprime m p) :
    nativePNTSequentialMobiusSignedAtom M L m (p * k) +
        nativePNTSequentialMobiusSignedAtom M L (m * p) k =
      ((μ m : Int) : Real) * Real.log (p : Real) *
        (nativePNTError (L / ((m * p) * k)) -
          nativePNTError (M / ((m * p) * k))) := by
  unfold nativePNTSequentialMobiusSignedAtom
  change
    ((μ m : Int) : Real) * Real.log ((p * k : Nat) : Real) *
          (nativePNTError (L / (m * (p * k))) -
            nativePNTError (M / (m * (p * k)))) +
        ((μ (m * p) : Int) : Real) * Real.log (k : Real) *
          (nativePNTError (L / ((m * p) * k)) -
            nativePNTError (M / ((m * p) * k))) =
      ((μ m : Int) : Real) * Real.log (p : Real) *
        (nativePNTError (L / ((m * p) * k)) -
          nativePNTError (M / ((m * p) * k)))
  rw [nativeMobius_adjoin_prime m p hp hcop]
  push_cast
  have hmul : m * (p * k) = (m * p) * k := by ring
  rw [hmul]
  have hp0 : (p : Real) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hk0 : (k : Real) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 by omega)
  rw [Real.log_mul hp0 hk0]
  ring

/-- **Exact local surplus on the sequential carrier.**
Fresh-prime pairing removes exactly twice the duplicated `log k` mass, now
weighted by the endpoint-difference response. -/
theorem nativePNTSequentialMobiusSignedAtom_pair_abs_surplus_eq
    (M L m p k : Nat) (hk : 1 <= k)
    (hp : p.Prime) (hcop : Nat.Coprime m p) :
    |nativePNTSequentialMobiusSignedAtom M L m (p * k)| +
        |nativePNTSequentialMobiusSignedAtom M L (m * p) k| -
        |nativePNTSequentialMobiusSignedAtom M L m (p * k) +
          nativePNTSequentialMobiusSignedAtom M L (m * p) k| =
      2 * |((μ m : Int) : Real)| * Real.log (k : Real) *
        |nativePNTError (L / ((m * p) * k)) -
          nativePNTError (M / ((m * p) * k))| := by
  rw [nativePNTSequentialMobiusSignedAtom_pair_adjoin_prime
    M L m p k hk hp hcop]
  unfold nativePNTSequentialMobiusSignedAtom
  change
    |((μ m : Int) : Real) * Real.log ((p * k : Nat) : Real) *
        (nativePNTError (L / (m * (p * k))) -
          nativePNTError (M / (m * (p * k))))| +
      |((μ (m * p) : Int) : Real) * Real.log (k : Real) *
        (nativePNTError (L / ((m * p) * k)) -
          nativePNTError (M / ((m * p) * k)))| -
      |((μ m : Int) : Real) * Real.log (p : Real) *
        (nativePNTError (L / ((m * p) * k)) -
          nativePNTError (M / ((m * p) * k)))| =
    2 * |((μ m : Int) : Real)| * Real.log (k : Real) *
      |nativePNTError (L / ((m * p) * k)) -
        nativePNTError (M / ((m * p) * k))|
  rw [nativeMobius_adjoin_prime m p hp hcop]
  push_cast
  have hmul : m * (p * k) = (m * p) * k := by ring
  rw [hmul]
  have hp0 : (p : Real) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hk0 : (k : Real) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 by omega)
  have hpLog0 : 0 <= Real.log (p : Real) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hkLog0 : 0 <= Real.log (k : Real) :=
    Real.log_nonneg (by exact_mod_cast hk)
  rw [Real.log_mul hp0 hk0]
  simp only [abs_mul, abs_neg, abs_of_nonneg hpLog0,
    abs_of_nonneg hkLog0, abs_of_nonneg (add_nonneg hpLog0 hkLog0)]
  ring

/-! ## The exact resolved-wheel forcing -/

/-- Change in the signed mass already resolved by the same Euler wheel cutoff. -/
def nativePNTSequentialResolvedWheelDrift
    (y M L : Nat) : Real :=
  nativePNTWheelResolvedSignedMass y L - nativePNTWheelResolvedSignedMass y M

/-- The single Euler forcing which remains after the signed Selberg remainder
is cancelled between two endpoints resolved by the same square-root wheel. -/
def nativePNTSequentialEulerForcing
    (y M L : Nat) : Real :=
  nativePNTSequentialSharedMobiusReciprocalMass M L -
    nativePNTSequentialResolvedWheelDrift y M L -
    ((L - M : Nat) : Real)

/-- The Euler forcing is explicitly the fresh-prime sequential atom mass minus
the resolved-wheel drift and physical block length. -/
theorem nativePNTSequentialEulerForcing_eq_atomSum_sub_wheel_sub_length
    (y M L : Nat) :
    nativePNTSequentialEulerForcing y M L =
      (∑ m ∈ Finset.Icc 1 M,
        ∑ k ∈ Finset.Icc 1 (M / m),
          nativePNTSequentialMobiusSignedAtom M L m k) -
      nativePNTSequentialResolvedWheelDrift y M L -
      ((L - M : Nat) : Real) := by
  unfold nativePNTSequentialEulerForcing
  rw [nativePNTSequentialSharedMobiusReciprocalMass_eq_sum_atoms]

/-- **Resolved-wheel closure of the #555 seed.**
If the same wheel cutoff resolves both endpoints, the signed Selberg remainder
cancels exactly.  The complete new discrepancy is the one Euler forcing above. -/
theorem nativePNTSequentialSquareBlockDiscrepancy_eq_eulerForcing
    (y M L : Nat)
    (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M)
    (hMscale : M < 2 * y ^ 2) (hLscale : L < 2 * y ^ 2) :
    nativePNTSequentialSquareBlockDiscrepancy M L =
      nativePNTSequentialEulerForcing y M L := by
  have hrec :=
    nativePNTSignedSelberg_recurrence_difference_subdoubling M L hM hML hsub
  rw [nativePNTSequentialSharedFiberDrift_eq_mobiusReciprocalMass] at hrec
  have hWM :=
    nativePNTError_mul_log_add_squareRootWheel_eq_remainder y M hMscale
  have hWL :=
    nativePNTError_mul_log_add_squareRootWheel_eq_remainder y L hLscale
  have hD :=
    nativePNTSequentialSquareBlockDiscrepancy_eq_lambdaMass_sub_length
      M L hM hML
  unfold nativePNTSequentialEulerForcing nativePNTSequentialResolvedWheelDrift
  linarith

/-- Consequently the #555 cross energy is literally old endpoint error times
the resolved Euler forcing. -/
theorem nativePNTSequentialSquareBlockCrossEnergy_eq_error_mul_eulerForcing
    (y M L : Nat)
    (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M)
    (hMscale : M < 2 * y ^ 2) (hLscale : L < 2 * y ^ 2) :
    nativePNTSequentialSquareBlockCrossEnergy M L =
      nativePNTError M * nativePNTSequentialEulerForcing y M L := by
  unfold nativePNTSequentialSquareBlockCrossEnergy
  rw [nativePNTSequentialSquareBlockDiscrepancy_eq_eulerForcing
    y M L hM hML hsub hMscale hLscale]

/-- **Energy change on one all-Euler forcing.**
The diagonal and cross covariance are no longer separate arithmetic objects:
`E(L)^2-E(M)^2 = 2 E(M) F + F^2`, with `F` entirely on the resolved Euler
carrier. -/
theorem nativePNTError_sq_sub_sq_eq_two_mul_error_mul_eulerForcing_add_sq
    (y M L : Nat)
    (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M)
    (hMscale : M < 2 * y ^ 2) (hLscale : L < 2 * y ^ 2) :
    nativePNTError L ^ 2 - nativePNTError M ^ 2 =
      2 * nativePNTError M * nativePNTSequentialEulerForcing y M L +
        nativePNTSequentialEulerForcing y M L ^ 2 := by
  have henergy :=
    nativePNTError_sq_sub_sq_eq_two_mul_crossEnergy_add_discrepancy_sq M L
  rw [nativePNTSequentialSquareBlockCrossEnergy_eq_error_mul_eulerForcing
      y M L hM hML hsub hMscale hLscale,
    nativePNTSequentialSquareBlockDiscrepancy_eq_eulerForcing
      y M L hM hML hsub hMscale hLscale] at henergy
  nlinarith

/-- Non-circular seed consumer stated only in the Euler forcing. -/
theorem nativePNTSequentialEulerForcing_seed_contraction
    (y M L : Nat) (alpha alpha' : Real)
    (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M)
    (hMscale : M < 2 * y ^ 2) (hLscale : L < 2 * y ^ 2)
    (halpha : 0 <= alpha) (halpha' : 0 <= alpha')
    (hold : |nativePNTError M| <= alpha * (M : Real))
    (hforcing :
      2 * nativePNTError M * nativePNTSequentialEulerForcing y M L +
          nativePNTSequentialEulerForcing y M L ^ 2 <=
        (alpha' * (L : Real)) ^ 2 - (alpha * (M : Real)) ^ 2) :
    |nativePNTError L| <= alpha' * (L : Real) := by
  apply nativePNTSequentialCrossEnergy_seed_contraction
    M L alpha alpha' halpha halpha' hold
  rw [nativePNTSequentialSquareBlockCrossEnergy_eq_error_mul_eulerForcing
      y M L hM hML hsub hMscale hLscale,
    nativePNTSequentialSquareBlockDiscrepancy_eq_eulerForcing
      y M L hM hML hsub hMscale hLscale]
  nlinarith

/-! ## Direct bridge to the protected square-block correlation -/

/-- The signed amount by which the new physical block pulls the inherited
endpoint error.  It is the already-defined protected Mobius correlation plus
the deterministic physical block length. -/
def nativePNTSequentialProtectedBlockPull (M L : Nat) : Real :=
  nativePNTSignedSquareBlockMobiusCorrelation L M L +
    ((L - M : Nat) : Real)

/-- **The missing connection.**  At a subdoubling endpoint the entire new
PNT-error discrepancy is the negative of the protected block pull.  This uses
the exact #555 new-fibre identity and the existing interval Fubini theorem, so
no same-wheel scale assumption is needed. -/
theorem nativePNTSequentialSquareBlockDiscrepancy_eq_neg_protectedBlockPull
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTSequentialSquareBlockDiscrepancy M L =
      -nativePNTSequentialProtectedBlockPull M L := by
  have hD :=
    nativePNTSequentialSquareBlockDiscrepancy_eq_lambdaMass_sub_length
      M L hM hML
  have hnew := nativePNTSequentialNewFiberMass_endpoint_of_subdoubling M L hsub
  unfold nativePNTSequentialNewFiberMass at hnew
  rw [nativeLambdaSquareBlockWeighted_eq_mobiusCorrelation L M L] at hnew
  unfold nativePNTSequentialProtectedBlockPull
  linarith

/-- The endpoint itself is therefore updated by subtracting the protected block
pull from the inherited error. -/
theorem nativePNTError_eq_old_sub_protectedBlockPull
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTError L =
      nativePNTError M - nativePNTSequentialProtectedBlockPull M L := by
  have hD :=
    nativePNTSequentialSquareBlockDiscrepancy_eq_neg_protectedBlockPull
      M L hM hML hsub
  unfold nativePNTSequentialSquareBlockDiscrepancy at hD
  linarith

/-- The #555 cross energy is exactly the negative old-error/protected-pull
interaction. -/
theorem nativePNTSequentialSquareBlockCrossEnergy_eq_neg_error_mul_protectedBlockPull
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTSequentialSquareBlockCrossEnergy M L =
      -nativePNTError M * nativePNTSequentialProtectedBlockPull M L := by
  unfold nativePNTSequentialSquareBlockCrossEnergy
  rw [nativePNTSequentialSquareBlockDiscrepancy_eq_neg_protectedBlockPull
    M L hM hML hsub]
  ring

/-- **Protected-correlation energy identity.**  The complete one-step energy
change is `P^2 - 2 E(M) P` for the single protected block pull `P`.  Thus the
positive diagonal and signed cross covariance are literally the square and
linear parts of one already-formalized Euler object. -/
theorem nativePNTError_sq_sub_sq_eq_protectedBlockPull_sq_sub_two_mul_error
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTError L ^ 2 - nativePNTError M ^ 2 =
      nativePNTSequentialProtectedBlockPull M L ^ 2 -
        2 * nativePNTError M * nativePNTSequentialProtectedBlockPull M L := by
  have henergy :=
    nativePNTError_sq_sub_sq_eq_two_mul_crossEnergy_add_discrepancy_sq M L
  rw [nativePNTSequentialSquareBlockCrossEnergy_eq_neg_error_mul_protectedBlockPull
      M L hM hML hsub,
    nativePNTSequentialSquareBlockDiscrepancy_eq_neg_protectedBlockPull
      M L hM hML hsub] at henergy
  nlinarith

/-- The same-wheel Euler forcing and the protected block pull are the same
quantity with opposite sign.  This identifies the sequential reciprocal/wheel
view and the existing protected block/Abel view exactly. -/
theorem nativePNTSequentialEulerForcing_eq_neg_protectedBlockPull
    (y M L : Nat)
    (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M)
    (hMscale : M < 2 * y ^ 2) (hLscale : L < 2 * y ^ 2) :
    nativePNTSequentialEulerForcing y M L =
      -nativePNTSequentialProtectedBlockPull M L := by
  have hEuler :=
    nativePNTSequentialSquareBlockDiscrepancy_eq_eulerForcing
      y M L hM hML hsub hMscale hLscale
  have hProtected :=
    nativePNTSequentialSquareBlockDiscrepancy_eq_neg_protectedBlockPull
      M L hM hML hsub
  linarith

/-- Non-circular endpoint seed consumer stated directly on the protected block
pull.  This is the exact socket to be paid by the existing fresh-prime physical
defect / survivor / Abel machinery. -/
theorem nativePNTSequentialProtectedBlockPull_seed_contraction
    (M L : Nat) (alpha alpha' : Real)
    (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M)
    (halpha : 0 <= alpha) (halpha' : 0 <= alpha')
    (hold : |nativePNTError M| <= alpha * (M : Real))
    (hpull :
      nativePNTSequentialProtectedBlockPull M L ^ 2 -
          2 * nativePNTError M * nativePNTSequentialProtectedBlockPull M L <=
        (alpha' * (L : Real)) ^ 2 - (alpha * (M : Real)) ^ 2) :
    |nativePNTError L| <= alpha' * (L : Real) := by
  apply nativePNTSequentialCrossEnergy_seed_contraction
    M L alpha alpha' halpha halpha' hold
  rw [nativePNTSequentialSquareBlockCrossEnergy_eq_neg_error_mul_protectedBlockPull
      M L hM hML hsub,
    nativePNTSequentialSquareBlockDiscrepancy_eq_neg_protectedBlockPull
      M L hM hML hsub]
  nlinarith

/-! ## Literal Viole specialization -/

/-- The old Viole endpoint lies below twice the square of the same wheel cutoff
from `r>=2`. -/
theorem violeClockCutoff_lt_two_mul_sq
    (r : Nat) (hr : 2 <= r) :
    violeClockCutoff r < 2 * r ^ 2 := by
  have hrpos : 0 < r := by omega
  have hrr : r < r * r := by
    simpa using Nat.mul_lt_mul_of_pos_right (by omega : 1 < r) hrpos
  unfold violeClockCutoff
  calc
    r ^ 2 + r < r ^ 2 + r ^ 2 := by
      simpa [pow_two] using Nat.add_lt_add_left hrr (r ^ 2)
    _ = 2 * r ^ 2 := by ring

/-- From `r>=4`, the next Viole endpoint is also below `2*r^2`; hence one and
the same wheel cutoff `r` resolves both sides of the adjacent step. -/
theorem violeClockCutoff_succ_lt_two_mul_sq
    (r : Nat) (hr : 4 <= r) :
    violeClockCutoff (r + 1) < 2 * r ^ 2 := by
  have hsmall : 3 * r + 2 < 4 * r := by omega
  have hfour : 4 * r <= r * r := by
    exact Nat.mul_le_mul_right r hr
  have htail : 3 * r + 2 < r * r := hsmall.trans_le hfour
  unfold violeClockCutoff
  calc
    (r + 1) ^ 2 + (r + 1) = r ^ 2 + (3 * r + 2) := by ring
    _ < r ^ 2 + r ^ 2 := by
      simpa [pow_two] using Nat.add_lt_add_left htail (r ^ 2)
    _ = 2 * r ^ 2 := by ring

/-- The one Euler forcing for the literal Viole adjacent-square step. -/
def violeClockSequentialEulerForcing (r : Nat) : Real :=
  nativePNTSequentialEulerForcing r
    (violeClockCutoff r) (violeClockCutoff (r + 1))

/-- Protected block pull for the literal Viole adjacent-square step. -/
def violeClockProtectedBlockPull (r : Nat) : Real :=
  nativePNTSequentialProtectedBlockPull
    (violeClockCutoff r) (violeClockCutoff (r + 1))

/-- **Viole protected-block closure.**  From the exact subdoubling onset, the
new discrepancy is simply the negative protected block pull. -/
theorem violeClockSequentialSquareBlockDiscrepancy_eq_neg_protectedBlockPull
    (r : Nat) (hr : 3 <= r) :
    nativePNTSequentialSquareBlockDiscrepancy
        (violeClockCutoff r) (violeClockCutoff (r + 1)) =
      -violeClockProtectedBlockPull r := by
  unfold violeClockProtectedBlockPull
  apply nativePNTSequentialSquareBlockDiscrepancy_eq_neg_protectedBlockPull
  · unfold violeClockCutoff
    nlinarith
  · exact violeClockCutoff_le_succ r
  · exact violeClockCutoff_succ_lt_two_mul r hr

/-- The actual Viole cross-covariance increment is the negative interaction of
the inherited endpoint error with the protected block pull. -/
theorem violeClockSequentialCrossEnergy_eq_neg_error_mul_protectedBlockPull
    (r : Nat) (hr : 3 <= r) :
    violeClockSequentialCrossEnergy r =
      -nativePNTError (violeClockCutoff r) * violeClockProtectedBlockPull r := by
  unfold violeClockSequentialCrossEnergy violeClockProtectedBlockPull
  apply nativePNTSequentialSquareBlockCrossEnergy_eq_neg_error_mul_protectedBlockPull
  · unfold violeClockCutoff
    nlinarith
  · exact violeClockCutoff_le_succ r
  · exact violeClockCutoff_succ_lt_two_mul r hr

/-- The full Viole endpoint energy change is the residual-reduction quadratic
of the existing protected block correlation. -/
theorem violeClockError_energyChange_eq_protectedBlockPull
    (r : Nat) (hr : 3 <= r) :
    nativePNTError (violeClockCutoff (r + 1)) ^ 2 -
        nativePNTError (violeClockCutoff r) ^ 2 =
      violeClockProtectedBlockPull r ^ 2 -
        2 * nativePNTError (violeClockCutoff r) *
          violeClockProtectedBlockPull r := by
  unfold violeClockProtectedBlockPull
  apply nativePNTError_sq_sub_sq_eq_protectedBlockPull_sq_sub_two_mul_error
  · unfold violeClockCutoff
    nlinarith
  · exact violeClockCutoff_le_succ r
  · exact violeClockCutoff_succ_lt_two_mul r hr

/-- **Viole closure.** From `r>=4`, the complete adjacent-square discrepancy is
exactly the shared sequential Mobius drift minus the same-wheel resolved drift
and physical block length. -/
theorem violeClockSequentialSquareBlockDiscrepancy_eq_eulerForcing
    (r : Nat) (hr : 4 <= r) :
    nativePNTSequentialSquareBlockDiscrepancy
        (violeClockCutoff r) (violeClockCutoff (r + 1)) =
      violeClockSequentialEulerForcing r := by
  unfold violeClockSequentialEulerForcing
  apply nativePNTSequentialSquareBlockDiscrepancy_eq_eulerForcing
  · unfold violeClockCutoff
    nlinarith
  · exact violeClockCutoff_le_succ r
  · exact violeClockCutoff_succ_lt_two_mul r (by omega)
  · exact violeClockCutoff_lt_two_mul_sq r (by omega)
  · exact violeClockCutoff_succ_lt_two_mul_sq r hr

/-- The actual Viole cross covariance increment is inherited endpoint error
multiplied by that one Euler forcing. -/
theorem violeClockSequentialCrossEnergy_eq_error_mul_eulerForcing
    (r : Nat) (hr : 4 <= r) :
    violeClockSequentialCrossEnergy r =
      nativePNTError (violeClockCutoff r) *
        violeClockSequentialEulerForcing r := by
  unfold violeClockSequentialCrossEnergy
  have hM : 1 <= violeClockCutoff r := by
    unfold violeClockCutoff
    nlinarith
  rw [nativePNTSequentialSquareBlockCrossEnergy_eq_error_mul_eulerForcing
    r (violeClockCutoff r) (violeClockCutoff (r + 1))
    hM (violeClockCutoff_le_succ r)
    (violeClockCutoff_succ_lt_two_mul r (by omega))
    (violeClockCutoff_lt_two_mul_sq r (by omega))
    (violeClockCutoff_succ_lt_two_mul_sq r hr)]
  rfl

/-- The full Viole endpoint energy change is now a quadratic in a single
prime-by-prime Euler forcing. -/
theorem violeClockError_energyChange_eq_eulerForcing
    (r : Nat) (hr : 4 <= r) :
    nativePNTError (violeClockCutoff (r + 1)) ^ 2 -
        nativePNTError (violeClockCutoff r) ^ 2 =
      2 * nativePNTError (violeClockCutoff r) *
          violeClockSequentialEulerForcing r +
        violeClockSequentialEulerForcing r ^ 2 := by
  have hM : 1 <= violeClockCutoff r := by
    unfold violeClockCutoff
    nlinarith
  simpa [violeClockSequentialEulerForcing] using
    (nativePNTError_sq_sub_sq_eq_two_mul_error_mul_eulerForcing_add_sq
      r (violeClockCutoff r) (violeClockCutoff (r + 1))
      hM (violeClockCutoff_le_succ r)
      (violeClockCutoff_succ_lt_two_mul r (by omega))
      (violeClockCutoff_lt_two_mul_sq r (by omega))
      (violeClockCutoff_succ_lt_two_mul_sq r hr))

end RHLean.Analysis
