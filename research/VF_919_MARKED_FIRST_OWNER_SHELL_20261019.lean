import «research.VF_919_SEVEN_EIGHTHS_DYADIC_SHELL_COVARIANCE_20261019»

/-!
# Exact first-marked-prime allocation of the complete square-shell source

A finite arbitrary marked prime set P is allowed. Each physical integer
n belongs either to the P-sifted part or to the UNIQUE least marked
divisor p in P. A site never gets multiplied by the number of its
marked prime factors. All squareful Mobius-zero sites remain zero.

This first-owner partition is a more parsimonious source-preserving
alternative to inclusion-exclusion truncated at omega_P(n)<=3.
It does not require the restriction P0^4>=4H^2, and does not discard
the unmarked sector.

The dyadic marked energy expands EXACTLY as
 E = sifted^2 + sifted-marked cross + same-prime + distinct-prime.
The unmarked and cross sectors cannot be omitted when seeking a
genuine 7/8 bound. No analytic estimate is assumed or proved.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Literal marked divisors, retaining each prime label once. -/
def vf919MarkedDivisors (P : Finset ℕ) (n : ℕ) : Finset ℕ :=
  P.filter (fun p => p ∣ n)

/-- Deterministic owner chosen only when at least one marked divisor is
present. The value on the empty support is never used as a prime. -/
def vf919FirstMarkedDivisor (P : Finset ℕ) (n : ℕ) : ℕ :=
  if h : (vf919MarkedDivisors P n).Nonempty then
    (vf919MarkedDivisors P n).min' h
  else 0

theorem vf919FirstMarkedDivisor_mem (P : Finset ℕ) (n : ℕ)
    (h : (vf919MarkedDivisors P n).Nonempty) :
    vf919FirstMarkedDivisor P n ∈ vf919MarkedDivisors P n := by
  unfold vf919FirstMarkedDivisor
  rw [dif_pos h]
  exact Finset.min'_mem _ h

theorem vf919FirstMarkedDivisor_mem_band (P : Finset ℕ) (n : ℕ)
    (h : (vf919MarkedDivisors P n).Nonempty) :
    vf919FirstMarkedDivisor P n ∈ P :=
  (Finset.mem_filter.mp (vf919FirstMarkedDivisor_mem P n h)).1

theorem vf919FirstMarkedDivisor_dvd (P : Finset ℕ) (n : ℕ)
    (h : (vf919MarkedDivisors P n).Nonempty) :
    vf919FirstMarkedDivisor P n ∣ n :=
  (Finset.mem_filter.mp (vf919FirstMarkedDivisor_mem P n h)).2

/-- Complete unmarked component, including its *actual* Mobius sign. -/
def vf919SiftedPhysicalSite (P : Finset ℕ) (n : ℕ) : ℝ :=
  if (vf919MarkedDivisors P n).Nonempty then 0 else realMoebiusStep n

/-- First-marked-prime component: exactly ONE label receives each
marked integer, rather than omega_P(n) copies of it. -/
def vf919FirstMarkedPhysicalSite (P : Finset ℕ) (p n : ℕ) : ℝ :=
  if (vf919MarkedDivisors P n).Nonempty ∧
      p = vf919FirstMarkedDivisor P n then realMoebiusStep n else 0

/-- Each genuine integer appears precisely once in the marked
population; no weights 1/omega and no truncated inclusion-exclusion. -/
theorem vf919MarkedPrioritySite_partition (P : Finset ℕ) (n : ℕ) :
    realMoebiusStep n =
      vf919SiftedPhysicalSite P n +
        ∑ p ∈ P, vf919FirstMarkedPhysicalSite P p n := by
  classical
  by_cases h : (vf919MarkedDivisors P n).Nonempty
  · have hp : vf919FirstMarkedDivisor P n ∈ P :=
      vf919FirstMarkedDivisor_mem_band P n h
    simp [vf919SiftedPhysicalSite, vf919FirstMarkedPhysicalSite, h, hp]
  · simp [vf919SiftedPhysicalSite, vf919FirstMarkedPhysicalSite, h]

/-- The native square shell is the exact (half-open) physical sum. -/
theorem vf919SquareShellSum_eq_physicalIco (R : ℕ) :
    vf919SquareShellSum R =
      ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2), realMoebiusStep n := by
  have hle : R ^ 2 ≤ (R + 1) ^ 2 := by
    have hsq : (R + 1) ^ 2 = R ^ 2 + (2 * R + 1) := by ring
    omega
  unfold vf919SquareShellSum realMertensLength
  exact (Finset.sum_Ico_eq_sub _ hle).symm

def vf919SiftedSquareShell (P : Finset ℕ) (R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
    vf919SiftedPhysicalSite P n

def vf919FirstMarkedSquareShell (P : Finset ℕ) (p R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
    vf919FirstMarkedPhysicalSite P p n

/-- Source-preserving exact shell decomposition for ANY marked band.
Sifted sites, including those without marked prime factors, remain. -/
theorem vf919SquareShell_eq_sifted_add_firstMarked
    (P : Finset ℕ) (R : ℕ) :
    vf919SquareShellSum R =
      vf919SiftedSquareShell P R +
        ∑ p ∈ P, vf919FirstMarkedSquareShell P p R := by
  rw [vf919SquareShellSum_eq_physicalIco]
  calc
    (∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2), realMoebiusStep n) =
      ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        (vf919SiftedPhysicalSite P n +
          ∑ p ∈ P, vf919FirstMarkedPhysicalSite P p n) := by
          apply Finset.sum_congr rfl
          intro n _
          exact vf919MarkedPrioritySite_partition P n
    _ = vf919SiftedSquareShell P R +
          ∑ p ∈ P, vf919FirstMarkedSquareShell P p R := by
      unfold vf919SiftedSquareShell vf919FirstMarkedSquareShell
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm

/-- The same-owner square contribution in the marked source. -/
def vf919MarkedSameOwnerEnergy (P : Finset ℕ) (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    ∑ p ∈ P, vf919FirstMarkedSquareShell P p R ^ 2

/-- The exact non-diagonal remainder in the marked first-owner square.
It is NOT known to be nonpositive. -/
def vf919MarkedDistinctOwnerEnergy (P : Finset ℕ) (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    ((∑ p ∈ P, vf919FirstMarkedSquareShell P p R) ^ 2 -
      ∑ p ∈ P, vf919FirstMarkedSquareShell P p R ^ 2)

/-- The exact (possibly positive) sifted/marked cross energy. -/
def vf919MarkedSiftedCrossEnergy (P : Finset ℕ) (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    (vf919SiftedSquareShell P R ^ 2 +
      2 * vf919SiftedSquareShell P R *
        ∑ p ∈ P, vf919FirstMarkedSquareShell P p R)

/-- Full signed dyadic shell energy: the sifted sector, its mixed
interactions, same marked owner, and distinct marked owners must ALL be
paid. This identity retains every original Mobius atom exactly. -/
theorem vf919DyadicSquareShell_fullMarkedEnergy
    (P : Finset ℕ) (H : ℕ) :
    vf919DyadicSquareShellEnergy H =
      vf919MarkedSiftedCrossEnergy P H +
        vf919MarkedSameOwnerEnergy P H +
          vf919MarkedDistinctOwnerEnergy P H := by
  unfold vf919DyadicSquareShellEnergy
    vf919MarkedSiftedCrossEnergy
    vf919MarkedSameOwnerEnergy
    vf919MarkedDistinctOwnerEnergy
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R _
  rw [vf919SquareShell_eq_sifted_add_firstMarked]
  ring

#print axioms vf919FirstMarkedDivisor_mem
#print axioms vf919FirstMarkedDivisor_mem_band
#print axioms vf919FirstMarkedDivisor_dvd
#print axioms vf919MarkedPrioritySite_partition
#print axioms vf919SquareShellSum_eq_physicalIco
#print axioms vf919SquareShell_eq_sifted_add_firstMarked
#print axioms vf919DyadicSquareShell_fullMarkedEnergy

end RHLean.Analysis
