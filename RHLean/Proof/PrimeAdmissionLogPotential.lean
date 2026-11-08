import Mathlib

/-!
# Exact logarithmic bookkeeping for prime admission

For a fixed positive historical denominator `W`, a centered signed state `F`
changes to `F - m` when the next admitted prime contributes the daughter sum
`m`.  The logarithmic amplification changes by the logarithm of

`1 + (m^2 - 2 * F * m) / (W + F^2)`.

The mixed term is retained with its exact sign.  The logarithm arguments are
proved positive, and the one-step identity is telescoped over any finite chain
of such updates.  These are identities, not an estimate on the accumulated
signed contribution and not a proof of a zero limiting growth exponent.

The arithmetic consumer supplies the actual prime-admission states and their
recurrence; this module does not assume any cancellation bound.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- The logarithm of one plus the normalized centered square. -/
def primeAdmissionLogPotential (W F : ℝ) : ℝ :=
  Real.log (1 + F ^ 2 / W)

/-- The exact logarithmic increment, including the signed mixed term. -/
def primeAdmissionLogIncrement (W F m : ℝ) : ℝ :=
  Real.log (1 + (m ^ 2 - 2 * F * m) / (W + F ^ 2))

/-- Adding a square to a positive historical denominator stays positive. -/
theorem primeAdmissionEnergy_pos (W F : ℝ) (hW : 0 < W) :
    0 < W + F ^ 2 :=
  add_pos_of_pos_of_nonneg hW (sq_nonneg F)

/-- The potential always takes the logarithm of a positive number. -/
theorem primeAdmissionLogPotential_argument_pos (W F : ℝ) (hW : 0 < W) :
    0 < 1 + F ^ 2 / W := by
  have hsq : 0 ≤ F ^ 2 / W := div_nonneg (sq_nonneg F) hW.le
  linarith

/-- The normalized centered-square logarithm is nonnegative. -/
theorem primeAdmissionLogPotential_nonneg (W F : ℝ) (hW : 0 < W) :
    0 ≤ primeAdmissionLogPotential W F := by
  unfold primeAdmissionLogPotential
  apply Real.log_nonneg
  have hsq : 0 ≤ F ^ 2 / W := div_nonneg (sq_nonneg F) hW.le
  linarith

/-- The increment argument is exactly a ratio of two positive energies. -/
theorem primeAdmissionLogIncrement_argument_eq_div (W F m : ℝ)
    (hW : 0 < W) :
    1 + (m ^ 2 - 2 * F * m) / (W + F ^ 2) =
      (W + (F - m) ^ 2) / (W + F ^ 2) := by
  have hden : W + F ^ 2 ≠ 0 := ne_of_gt (primeAdmissionEnergy_pos W F hW)
  field_simp [hden] <;> ring

/-- Even a negative signed increment has a strictly positive logarithm
argument; no absolute values or sign assumptions on `F` or `m` are needed. -/
theorem primeAdmissionLogIncrement_argument_pos (W F m : ℝ)
    (hW : 0 < W) :
    0 < 1 + (m ^ 2 - 2 * F * m) / (W + F ^ 2) := by
  rw [primeAdmissionLogIncrement_argument_eq_div W F m hW]
  exact div_pos (primeAdmissionEnergy_pos W (F - m) hW)
    (primeAdmissionEnergy_pos W F hW)

/-- Separating the fixed normalization from the logarithmic potential. -/
theorem primeAdmissionLogPotential_eq_log_sub (W F : ℝ) (hW : 0 < W) :
    primeAdmissionLogPotential W F = Real.log (W + F ^ 2) - Real.log W := by
  have harg : 1 + F ^ 2 / W = (W + F ^ 2) / W := by
    field_simp [ne_of_gt hW] <;> ring
  unfold primeAdmissionLogPotential
  rw [harg, Real.log_div (ne_of_gt (primeAdmissionEnergy_pos W F hW))
    (ne_of_gt hW)]

/-- Exact one-prime logarithmic update.  In particular the mixed term
`-2 * F * m` cannot be discarded when telescoping. -/
theorem primeAdmissionLogPotential_step (W F m : ℝ) (hW : 0 < W) :
    primeAdmissionLogPotential W (F - m) =
      primeAdmissionLogPotential W F + primeAdmissionLogIncrement W F m := by
  rw [primeAdmissionLogPotential_eq_log_sub W (F - m) hW,
    primeAdmissionLogPotential_eq_log_sub W F hW]
  unfold primeAdmissionLogIncrement
  rw [primeAdmissionLogIncrement_argument_eq_div W F m hW,
    Real.log_div (ne_of_gt (primeAdmissionEnergy_pos W (F - m) hW))
      (ne_of_gt (primeAdmissionEnergy_pos W F hW))]
  ring

/-- Difference form of the same exact update, for interval telescopes. -/
theorem primeAdmissionLogIncrement_eq_sub (W F m : ℝ) (hW : 0 < W) :
    primeAdmissionLogIncrement W F m =
      primeAdmissionLogPotential W (F - m) - primeAdmissionLogPotential W F := by
  linarith [primeAdmissionLogPotential_step W F m hW]

/-- A zero daughter contribution gives a zero logarithmic increment. -/
@[simp] theorem primeAdmissionLogIncrement_zero (W F : ℝ) :
    primeAdmissionLogIncrement W F 0 = 0 := by
  simp [primeAdmissionLogIncrement]

/-- Finite telescoping of an actual subtraction recurrence.  Only the updates
in `range N` are required; no estimate on their signed sum is assumed. -/
theorem primeAdmissionLogPotential_telescope (W : ℝ) (F m : ℕ → ℝ)
    (N : ℕ) (hW : 0 < W)
    (hstep : ∀ j < N, F (j + 1) = F j - m j) :
    primeAdmissionLogPotential W (F N) =
      primeAdmissionLogPotential W (F 0) +
        ∑ j ∈ Finset.range N, primeAdmissionLogIncrement W (F j) (m j) := by
  revert hstep
  induction N with
  | zero =>
      intro _
      simp
  | succ N ih =>
      intro hstep
      have hprev := ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self N)))
      calc
        primeAdmissionLogPotential W (F (N + 1)) =
            primeAdmissionLogPotential W (F N) +
              primeAdmissionLogIncrement W (F N) (m N) := by
          rw [hstep N (Nat.lt_succ_self N)]
          exact primeAdmissionLogPotential_step W (F N) (m N) hW
        _ = (primeAdmissionLogPotential W (F 0) +
              ∑ j ∈ Finset.range N, primeAdmissionLogIncrement W (F j) (m j)) +
                primeAdmissionLogIncrement W (F N) (m N) := by
          rw [hprev]
        _ = primeAdmissionLogPotential W (F 0) +
              ∑ j ∈ Finset.range (N + 1),
                primeAdmissionLogIncrement W (F j) (m j) := by
          rw [Finset.sum_range_succ]
          ring

/-- Expanded form of the finite telescope, showing every signed mixed term. -/
theorem primeAdmissionLogPotential_telescope_expanded (W : ℝ) (F m : ℕ → ℝ)
    (N : ℕ) (hW : 0 < W)
    (hstep : ∀ j < N, F (j + 1) = F j - m j) :
    Real.log (1 + (F N) ^ 2 / W) =
      Real.log (1 + (F 0) ^ 2 / W) +
        ∑ j ∈ Finset.range N,
          Real.log (1 + ((m j) ^ 2 - 2 * F j * m j) / (W + (F j) ^ 2)) := by
  simpa only [primeAdmissionLogPotential, primeAdmissionLogIncrement] using
    primeAdmissionLogPotential_telescope W F m N hW hstep

end RHLean.Proof
