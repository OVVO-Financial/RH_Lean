import Mathlib
import RHLean.Analysis.AlpogeMobiusLogLift
import RHLean.Proof.FinitePartialMoments

/-!
# Alpoge / NNS upper and lower partial moments of the true Mobius source

The original two-wall finite-C source has BOTH Mobius signs. We must not
replace its complete signed population with a nonnegative ASK count or
discard either side. The source below keeps the historical twist at R,
the physical cutoff R^2-1, and an arbitrary real colour weight P(n).

This file proves the UPM1/LPM1 decomposition and the exact cross-payment
identity. These are unconditional arithmetic / NNS identities, *not*
new cancellation estimates. The same signed difference may be expressed
by the full native mu*Lambda convolution in AlpogeMobiusLogLift.

The physical nonnegative Alpoge four-colour projector can be inserted as
P once its native character values have been identified; this module does
not silently assume such an identification.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- A site of the original signed Mobius population, with an optional
real four-colour weight. The two-wall sign switches exactly at n=R. -/
def alpogeMobiusPartialAtom (R : ℕ) (P : ℕ → ℝ) (n : ℕ) : ℝ :=
  alpogeMobiusTwoWall R n * (P n * (μ : ArithmeticFunction ℝ) n)

/-- The n=1 seed has been kept separately since log(1)=0 in the
native mu*Lambda logarithmic lifting theorem. -/
def alpogeMobiusPartialSource (R : ℕ) (P : ℕ → ℝ) : ℝ :=
  P 1 +
    ∑ n ∈ Finset.Icc 2 (R ^ 2 - 1), alpogeMobiusPartialAtom R P n

/-- UPM1 (positive sign) of the actual two-wall Mobius source.
The initial n=1 seed is separately and explicitly included. -/
def alpogeMobiusPartialUPM (R : ℕ) (P : ℕ → ℝ) : ℝ :=
  P 1 +
    upperPartialMass (Finset.Icc 2 (R ^ 2 - 1))
      (alpogeMobiusPartialAtom R P)

/-- LPM1 (negative sign) of the same source. -/
def alpogeMobiusPartialLPM (R : ℕ) (P : ℕ → ℝ) : ℝ :=
  lowerPartialMass (Finset.Icc 2 (R ^ 2 - 1))
    (alpogeMobiusPartialAtom R P)

/-- The full, nonnegative absolute site population. For any P>=0, it
is the colour-weighted squarefree census (including the n=1 seed).
The source/cross identities do not need P>=0. -/
def alpogeMobiusPartialTotal (R : ℕ) (P : ℕ → ℝ) : ℝ :=
  P 1 +
    finiteAbsoluteMass (Finset.Icc 2 (R ^ 2 - 1))
      (alpogeMobiusPartialAtom R P)

/-- No sign loss: the original source is literally UPM1 minus LPM1. -/
theorem alpogeMobiusPartialUPM_sub_LPM (R : ℕ) (P : ℕ → ℝ) :
    alpogeMobiusPartialUPM R P -
      alpogeMobiusPartialLPM R P =
        alpogeMobiusPartialSource R P := by
  have h :=
    upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum
      (Finset.Icc 2 (R ^ 2 - 1)) (alpogeMobiusPartialAtom R P)
  unfold alpogeMobiusPartialUPM alpogeMobiusPartialLPM
    alpogeMobiusPartialSource
  unfold finiteSignedSum at h
  linarith

/-- No missing signed population: UPM1 plus LPM1 equals the entire
absolute squarefree census. -/
theorem alpogeMobiusPartialUPM_add_LPM (R : ℕ) (P : ℕ → ℝ) :
    alpogeMobiusPartialUPM R P +
      alpogeMobiusPartialLPM R P =
        alpogeMobiusPartialTotal R P := by
  have h :=
    upperPartialMass_add_lowerPartialMass_eq_finiteAbsoluteMass
      (Finset.Icc 2 (R ^ 2 - 1)) (alpogeMobiusPartialAtom R P)
  unfold alpogeMobiusPartialUPM alpogeMobiusPartialLPM
    alpogeMobiusPartialTotal
  linarith

/-- The exact degree-two cross-payment ledger; the only possible gain
is in the full UPM*LPM cross term, NOT by separately bounding UPM and
LPM before they have been recombined. -/
theorem alpogeMobiusPartial_cross_square (R : ℕ) (P : ℕ → ℝ) :
    (alpogeMobiusPartialSource R P) ^ 2 =
      (alpogeMobiusPartialTotal R P) ^ 2 -
      4 * alpogeMobiusPartialUPM R P *
        alpogeMobiusPartialLPM R P := by
  have hd := alpogeMobiusPartialUPM_sub_LPM R P
  have ht := alpogeMobiusPartialUPM_add_LPM R P
  calc
    (alpogeMobiusPartialSource R P) ^ 2 =
        (alpogeMobiusPartialUPM R P -
          alpogeMobiusPartialLPM R P) ^ 2 := by rw [hd]
    _ = (alpogeMobiusPartialUPM R P +
          alpogeMobiusPartialLPM R P) ^ 2 -
        4 * alpogeMobiusPartialUPM R P *
          alpogeMobiusPartialLPM R P := by ring
    _ = (alpogeMobiusPartialTotal R P) ^ 2 -
        4 * alpogeMobiusPartialUPM R P *
          alpogeMobiusPartialLPM R P := by rw [ht]

/-- The principal colour P=1 is precisely the native signed finite-C
two-wall Mobius source, not an alternative target. -/
theorem alpogeMobiusPartial_principal_eq_twoWall (R : ℕ) :
    alpogeMobiusPartialSource R (fun _ => 1) =
      alpogeMobiusTwoWallSource R := by
  unfold alpogeMobiusPartialSource alpogeMobiusTwoWallSource
  simp [alpogeMobiusPartialAtom]

/-- Hence the actual principal UPM-LPM imbalance is exactly the
complete Alpoge-to-native-mu*Lambda signed source. -/
theorem alpogeMobiusPartial_principal_eq_lambda (R : ℕ) :
    alpogeMobiusPartialUPM R (fun _ => 1) -
      alpogeMobiusPartialLPM R (fun _ => 1) =
        alpogeMobiusTwoWallLambdaSource R := by
  rw [alpogeMobiusPartialUPM_sub_LPM,
    alpogeMobiusPartial_principal_eq_twoWall,
    alpogeMobiusTwoWall_eq_lambdaSource]

end RHLean.Analysis
