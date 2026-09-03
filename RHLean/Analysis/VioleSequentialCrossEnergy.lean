import Mathlib
import RHLean.Analysis.VioleClockSignedHistoryBudget
import RHLean.Analysis.NativePNTSignedWheelRemainder
import RHLean.Analysis.BlockCovarianceDecomposition

/-!
# Sequential cross energy for adjacent Viole square blocks

The direct-cutoff budget of `VioleClockSignedHistoryBudget` is a propagation
consumer. At its first subdoubling endpoint the budget reduces to the desired
new-slope endpoint estimate itself, so the arithmetic seed must be expressed
before that consumer.

This file isolates the exact sequential seed geometry.

For adjacent cutoffs `M <= L`, write

`D(M,L) = E(L) - E(M)`

and define the sequential cross energy

`X(M,L) = E(M) * D(M,L)`.

Then

`E(L)^2 - E(M)^2 = 2 X(M,L) + D(M,L)^2`.

Thus the only way a new block can reduce endpoint energy is through its signed
interaction with the inherited endpoint state. The same increment is also
literally one step of the generic signed-block cross covariance already present
in `BlockCovarianceDecomposition`.

The second half of the file differences the exact signed Selberg recurrences at
`M` and `L`. The difference splits into

* shared old fibres `d <= M`, whose reciprocal quotient has moved; and
* genuinely new fibres `M < d <= L`.

The shared drift is then rewritten exactly as the existing Möbius logarithmic
reciprocal mass. No absolute value, independence assumption, or new analytic
estimate is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Signed PNT-error discrepancy created between two physical cutoffs. -/
def nativePNTSequentialSquareBlockDiscrepancy (M L : Nat) : Real :=
  nativePNTError L - nativePNTError M

/-- Sequential old/new cross energy: inherited endpoint error times the signed
error discrepancy created by the next block. -/
def nativePNTSequentialSquareBlockCrossEnergy (M L : Nat) : Real :=
  nativePNTError M * nativePNTSequentialSquareBlockDiscrepancy M L

/-- The discrepancy is exactly the von-Mangoldt block discrepancy. -/
theorem nativePNTSequentialSquareBlockDiscrepancy_eq_lambdaMass_sub_length
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    nativePNTSequentialSquareBlockDiscrepancy M L =
      nativePNTLambdaSquareBlockMass M L - ((L - M : Nat) : Real) := by
  unfold nativePNTSequentialSquareBlockDiscrepancy
  exact nativePNTError_sub_eq_lambdaSquareBlockMass_sub_length M L hM hML

/-- Exact two-block energy identity. The diagonal `D^2` and the cross term
`2 E(M) D` are the complete change in endpoint energy. -/
theorem nativePNTError_sq_sub_sq_eq_two_mul_crossEnergy_add_discrepancy_sq
    (M L : Nat) :
    nativePNTError L ^ 2 - nativePNTError M ^ 2 =
      2 * nativePNTSequentialSquareBlockCrossEnergy M L +
        nativePNTSequentialSquareBlockDiscrepancy M L ^ 2 := by
  unfold nativePNTSequentialSquareBlockCrossEnergy
    nativePNTSequentialSquareBlockDiscrepancy
  ring

/-- A cross-energy budget is an exact non-circular seed consumer. If the old
endpoint lies below slope `alpha` and the signed old/new interaction plus the
new-block diagonal fits inside the target energy decrement, then the new
endpoint lies below slope `alpha'`. -/
theorem nativePNTSequentialCrossEnergy_seed_contraction
    (M L : Nat) (alpha alpha' : Real)
    (halpha : 0 <= alpha) (halpha' : 0 <= alpha')
    (hold : |nativePNTError M| <= alpha * (M : Real))
    (hcross :
      2 * nativePNTSequentialSquareBlockCrossEnergy M L +
          nativePNTSequentialSquareBlockDiscrepancy M L ^ 2 <=
        (alpha' * (L : Real)) ^ 2 - (alpha * (M : Real)) ^ 2) :
    |nativePNTError L| <= alpha' * (L : Real) := by
  have hMtarget0 : 0 <= alpha * (M : Real) :=
    mul_nonneg halpha (Nat.cast_nonneg M)
  have hLtarget0 : 0 <= alpha' * (L : Real) :=
    mul_nonneg halpha' (Nat.cast_nonneg L)
  have hMsq :
      nativePNTError M ^ 2 <= (alpha * (M : Real)) ^ 2 := by
    have habsSq :
        |nativePNTError M| ^ 2 <= (alpha * (M : Real)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hMtarget0).2 hold
    simpa [sq_abs] using habsSq
  have henergy :=
    nativePNTError_sq_sub_sq_eq_two_mul_crossEnergy_add_discrepancy_sq M L
  have hLsq :
      nativePNTError L ^ 2 <= (alpha' * (L : Real)) ^ 2 := by
    nlinarith
  have habsLsq :
      |nativePNTError L| ^ 2 <= (alpha' * (L : Real)) ^ 2 := by
    simpa [sq_abs] using hLsq
  exact (sq_le_sq₀ (abs_nonneg _) hLtarget0).1 habsLsq

/-! ## Viole-clock realization as literal block covariance -/

/-- Signed PNT-error increment of one Viole clock block. -/
def violeClockErrorIncrement (r : Nat) : Real :=
  nativePNTError (violeClockCutoff (r + 1)) -
    nativePNTError (violeClockCutoff r)

/-- The Viole block increments telescope exactly to the endpoint PNT error.
The base cutoff is zero and `E(0)=0`. -/
theorem signedBlockPrefix_violeClockErrorIncrement (R : Nat) :
    signedBlockPrefix violeClockErrorIncrement R =
      nativePNTError (violeClockCutoff R) := by
  induction R with
  | zero =>
      simp [signedBlockPrefix, violeClockCutoff, nativePNTError, nativePsi]
  | succ R ih =>
      rw [signedBlockPrefix_succ, ih]
      unfold violeClockErrorIncrement
      ring

/-- Sequential cross energy at Viole block `r`. -/
def violeClockSequentialCrossEnergy (r : Nat) : Real :=
  nativePNTSequentialSquareBlockCrossEnergy
    (violeClockCutoff r) (violeClockCutoff (r + 1))

/-- The Viole sequential cross energy is literally the one-step increment of
the generic signed-block cross covariance. Thus `X_r` is not merely analogous
to cross-block covariance: it is exactly that existing object on the block
sequence of PNT-error increments. -/
theorem violeClockSequentialCrossEnergy_eq_crossCovariance_increment
    (r : Nat) :
    violeClockSequentialCrossEnergy r =
      signedBlockCrossCovariance violeClockErrorIncrement (r + 1) -
        signedBlockCrossCovariance violeClockErrorIncrement r := by
  rw [signedBlockCrossCovariance_succ,
    signedBlockPrefix_violeClockErrorIncrement]
  unfold violeClockSequentialCrossEnergy
    nativePNTSequentialSquareBlockCrossEnergy
    nativePNTSequentialSquareBlockDiscrepancy
    violeClockErrorIncrement
  ring

/-! ## Exact difference of the signed Selberg recurrences -/

/-- Shared old-fibre drift when the endpoint moves from `M` to `L`. Every
physical divisor is still in the old prefix; only its reciprocal quotient
changes. -/
def nativePNTSequentialSharedFiberDrift (M L : Nat) : Real :=
  ∑ d ∈ Finset.Icc 1 M,
    Λ d * (nativePNTError (L / d) - nativePNTError (M / d))

/-- Genuinely new divisor fibres born in `(M,L]`. -/
def nativePNTSequentialNewFiberMass (M L : Nat) : Real :=
  ∑ d ∈ Finset.Ioc M L,
    Λ d * nativePNTError (L / d)

/-- The full signed reciprocal error-mass increment splits exactly into shared
old-fibre drift plus the genuinely new fibres. -/
theorem nativePNTLambdaSignedErrorMass_sub_eq_shared_add_new
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    (∑ d ∈ Finset.Icc 1 L, Λ d * nativePNTError (L / d)) -
        (∑ d ∈ Finset.Icc 1 M, Λ d * nativePNTError (M / d)) =
      nativePNTSequentialSharedFiberDrift M L +
        nativePNTSequentialNewFiberMass M L := by
  have hset :
      Finset.Icc 1 L = Finset.Icc 1 M ∪ Finset.Ioc M L := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdis : Disjoint (Finset.Icc 1 M) (Finset.Ioc M L) := by
    rw [Finset.disjoint_left]
    intro d hdM hdBlock
    rw [Finset.mem_Icc] at hdM
    rw [Finset.mem_Ioc] at hdBlock
    omega
  have hsplit :
      (∑ d ∈ Finset.Icc 1 L, Λ d * nativePNTError (L / d)) =
        (∑ d ∈ Finset.Icc 1 M, Λ d * nativePNTError (L / d)) +
          ∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (L / d) := by
    rw [hset, Finset.sum_union hdis]
  rw [hsplit]
  unfold nativePNTSequentialSharedFiberDrift nativePNTSequentialNewFiberMass
  rw [← Finset.sum_sub_distrib]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro d _hd
    ring
  · rfl

/-- Exact recurrence difference: endpoint motion equals shared reciprocal-fibre
motion plus the genuinely new fibres, with the signed Selberg remainder kept
exactly. -/
theorem nativePNTSignedSelberg_recurrence_difference_eq_shared_add_new
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    nativePNTError L * Real.log (L : Real) -
        nativePNTError M * Real.log (M : Real) +
        nativePNTSequentialSharedFiberDrift M L +
        nativePNTSequentialNewFiberMass M L =
      nativePNTSignedSelbergRemainder L - nativePNTSignedSelbergRemainder M := by
  have hLrec := nativePNTError_mul_log_add_mobiusSigned_eq_remainder L
  have hMrec := nativePNTError_mul_log_add_mobiusSigned_eq_remainder M
  rw [← nativeLambdaSignedErrorMass_eq_mobiusReciprocal] at hLrec hMrec
  have hsplit :=
    nativePNTLambdaSignedErrorMass_sub_eq_shared_add_new M L hM hML
  linarith

/-- At a subdoubling seed endpoint every genuinely new divisor has quotient
one, so the new-fibre contribution is exactly the negative von-Mangoldt block
mass. -/
theorem nativePNTSequentialNewFiberMass_endpoint_of_subdoubling
    (M L : Nat) (hsub : L < 2 * M) :
    nativePNTSequentialNewFiberMass M L =
      -nativePNTLambdaSquareBlockMass M L := by
  unfold nativePNTSequentialNewFiberMass nativePNTLambdaSquareBlockMass
  calc
    (∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (L / d)) =
        ∑ d ∈ Finset.Ioc M L, -(Λ d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdI := Finset.mem_Ioc.mp hd
      have hlo : 1 * d <= L := by simpa using hdI.2
      have hhi : L < (1 + 1) * d := by
        have htwo : 2 * M < 2 * d := by omega
        omega
      have hdiv : L / d = 1 := Nat.div_eq_of_lt_le hlo hhi
      rw [hdiv]
      simp [nativePNTError, nativePsi]
    _ = -(∑ d ∈ Finset.Ioc M L, Λ d) := by
      rw [Finset.sum_neg_distrib]

/-- Subdoubling recurrence difference after replacing the new fibres by their
exact block mass. -/
theorem nativePNTSignedSelberg_recurrence_difference_subdoubling
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTError L * Real.log (L : Real) -
        nativePNTError M * Real.log (M : Real) +
        nativePNTSequentialSharedFiberDrift M L -
        nativePNTLambdaSquareBlockMass M L =
      nativePNTSignedSelbergRemainder L - nativePNTSignedSelbergRemainder M := by
  have h := nativePNTSignedSelberg_recurrence_difference_eq_shared_add_new
    M L hM hML
  rw [nativePNTSequentialNewFiberMass_endpoint_of_subdoubling M L hsub] at h
  linarith

/-- The subdoubling recurrence can be rewritten directly in the sequential
block discrepancy `D = E(L)-E(M)`. This is the exact seed equation before any
inequality is taken. -/
theorem nativePNTSequentialDiscrepancy_mul_log_sub_one_eq
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTSequentialSquareBlockDiscrepancy M L *
          (Real.log (L : Real) - 1) +
        nativePNTError M *
          (Real.log (L : Real) - Real.log (M : Real)) +
        nativePNTSequentialSharedFiberDrift M L - ((L - M : Nat) : Real) =
      nativePNTSignedSelbergRemainder L - nativePNTSignedSelbergRemainder M := by
  have hrec :=
    nativePNTSignedSelberg_recurrence_difference_subdoubling M L hM hML hsub
  have hD :=
    nativePNTSequentialSquareBlockDiscrepancy_eq_lambdaMass_sub_length
      M L hM hML
  unfold nativePNTSequentialSquareBlockDiscrepancy at hD ⊢
  rw [Nat.cast_sub hML] at hD ⊢
  nlinarith

/-! ## Exact bridge to the existing reciprocal Möbius coordinate -/

/-- The shared-fibre drift written directly in the repository's generic Möbius
logarithmic reciprocal coordinate. -/
def nativePNTSequentialSharedMobiusReciprocalMass (M L : Nat) : Real :=
  nativePNTMobiusLogReciprocalMass M
    (fun d => nativePNTError (L / d) - nativePNTError (M / d))

/-- Exact Fubini bridge: the sequential shared-fibre drift is literally an
existing prime-by-prime Möbius reciprocal mass. -/
theorem nativePNTSequentialSharedFiberDrift_eq_mobiusReciprocalMass
    (M L : Nat) :
    nativePNTSequentialSharedFiberDrift M L =
      nativePNTSequentialSharedMobiusReciprocalMass M L := by
  unfold nativePNTSequentialSharedFiberDrift
    nativePNTSequentialSharedMobiusReciprocalMass
  simpa using
    (nativeLambdaWeighted_eq_mobiusLogReciprocalMass M
      (fun d => nativePNTError (L / d) - nativePNTError (M / d)))

/-- The same split can be written entirely in already-existing Möbius
coordinates: the change of the full signed reciprocal error mass equals the
shared reciprocal drift plus the new-block Möbius correlation. -/
theorem nativePNTMobiusReciprocalSignedErrorMass_sub_eq_shared_add_blockCorrelation
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    nativePNTMobiusReciprocalSignedErrorMass L -
        nativePNTMobiusReciprocalSignedErrorMass M =
      nativePNTSequentialSharedMobiusReciprocalMass M L +
        nativePNTSignedSquareBlockMobiusCorrelation L M L := by
  have hsplit :=
    nativePNTLambdaSignedErrorMass_sub_eq_shared_add_new M L hM hML
  rw [nativeLambdaSignedErrorMass_eq_mobiusReciprocal,
    nativeLambdaSignedErrorMass_eq_mobiusReciprocal] at hsplit
  rw [nativePNTSequentialSharedFiberDrift_eq_mobiusReciprocalMass] at hsplit
  have hblock := nativeLambdaSquareBlockWeighted_eq_mobiusCorrelation L M L
  unfold nativePNTSequentialNewFiberMass at hsplit
  rw [hblock] at hsplit
  exact hsplit

/-- Consequently the shared sequential reciprocal drift is exactly the change
of the full prime-by-prime reciprocal mass after removing the new-block
correlation. This is the exact carrier identity to use before asking for any
centered covariance estimate. -/
theorem nativePNTSequentialSharedMobiusReciprocalMass_eq_full_sub_old_sub_block
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) :
    nativePNTSequentialSharedMobiusReciprocalMass M L =
      nativePNTMobiusReciprocalSignedErrorMass L -
        nativePNTMobiusReciprocalSignedErrorMass M -
          nativePNTSignedSquareBlockMobiusCorrelation L M L := by
  have h :=
    nativePNTMobiusReciprocalSignedErrorMass_sub_eq_shared_add_blockCorrelation
      M L hM hML
  linarith

/-- Multiplying the exact seed equation by the inherited endpoint error exposes
`X(M,L)` directly against the existing reciprocal Möbius mass. This is an
identity, not an estimate. -/
theorem nativePNTSequentialCrossEnergy_mul_log_sub_one_eq_mobiusReciprocal
    (M L : Nat) (hM : 1 <= M) (hML : M <= L) (hsub : L < 2 * M) :
    nativePNTSequentialSquareBlockCrossEnergy M L *
          (Real.log (L : Real) - 1) +
        nativePNTError M ^ 2 *
          (Real.log (L : Real) - Real.log (M : Real)) +
        nativePNTError M *
          nativePNTSequentialSharedMobiusReciprocalMass M L -
        nativePNTError M * ((L - M : Nat) : Real) =
      nativePNTError M *
        (nativePNTSignedSelbergRemainder L - nativePNTSignedSelbergRemainder M) := by
  have hseed :=
    nativePNTSequentialDiscrepancy_mul_log_sub_one_eq M L hM hML hsub
  rw [nativePNTSequentialSharedFiberDrift_eq_mobiusReciprocalMass] at hseed
  unfold nativePNTSequentialSquareBlockCrossEnergy
  nlinarith

end RHLean.Analysis
