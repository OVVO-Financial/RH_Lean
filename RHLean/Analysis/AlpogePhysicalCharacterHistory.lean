import Mathlib
import RHLean.Analysis.AlpogeNativeSharpASKBalance

/-!
# Complete physical character histories: discrete Abel without losing a prime power

An unconditional reduction for the actual Frobenius/inertia character source.
For arbitrary complex coefficients c(n) and ell, let

  H_c(N) = N * (ell + sum_(1<=n<=N) c(n)/n) - sum_(1<=n<=N) c(n).

At every successor, the endpoint c(N+1) cancels EXACTLY:
  H_c(N+1)-H_c(N) = ell + sum_(1<=n<=N) c(n)/n.

Therefore H_c(M)-H_c(N) is the complete signed history of all its
earlier reciprocal-prefix values. A norm cannot be moved through the
summation without losing that signed history.

Specializing to c(n)=Lambda(n)*primVal(inertia,frob,psi,n) identifies
the NONPRINCIPAL Alpoge GPsi with this exact native history.
The principal Gz requires the separate real/log/Euler centering already
proved in AlpogeGzErdosReciprocalHistory. This file does not assume a
character saving, supply a conductor witness, or claim RH.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Reciprocal history of an arbitrary complex physical arithmetic coefficient. -/
def alpogePhysicalCharacterRecip (c : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, c n / (n : ℂ)

/-- Complete, not separately-triangled, character Chebyshev prefix. -/
def alpogePhysicalCharacterPsi (c : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, c n

/-- The full signed character observable, including the counterterm ell. -/
def alpogePhysicalCharacterHistory (c : ℕ → ℂ) (ell : ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) * (alpogePhysicalCharacterRecip c N + ell) -
    alpogePhysicalCharacterPsi c N

theorem alpogePhysicalCharacterRecip_succ
    (c : ℕ → ℂ) (N : ℕ) :
    alpogePhysicalCharacterRecip c (N + 1) =
      alpogePhysicalCharacterRecip c N + c (N + 1) / (↑(N + 1) : ℂ) := by
  unfold alpogePhysicalCharacterRecip
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

theorem alpogePhysicalCharacterPsi_succ
    (c : ℕ → ℂ) (N : ℕ) :
    alpogePhysicalCharacterPsi c (N + 1) =
      alpogePhysicalCharacterPsi c N + c (N + 1) := by
  unfold alpogePhysicalCharacterPsi
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- The ENTIRE new prime-power term cancels before an inequality is taken. -/
theorem alpogePhysicalCharacterHistory_succ_sub
    (c : ℕ → ℂ) (ell : ℂ) (N : ℕ) :
    alpogePhysicalCharacterHistory c ell (N + 1) -
      alpogePhysicalCharacterHistory c ell N =
        alpogePhysicalCharacterRecip c N + ell := by
  unfold alpogePhysicalCharacterHistory
  rw [alpogePhysicalCharacterRecip_succ,
      alpogePhysicalCharacterPsi_succ]
  have hN : (↑(N + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero N)
  push_cast
  field_simp [hN]
  ring

/-- No character-energy estimate is presumed: this is an equality of
the complete historical sum with its terminal value. -/
theorem alpogePhysicalCharacterHistory_difference_eq_history
    (c : ℕ → ℂ) (ell : ℂ) (N M : ℕ) (hNM : N ≤ M) :
    alpogePhysicalCharacterHistory c ell M -
      alpogePhysicalCharacterHistory c ell N =
        ∑ j ∈ Finset.Ico N M,
          (alpogePhysicalCharacterRecip c j + ell) := by
  induction M, hNM using Nat.le_induction with
  | base =>
      simp
  | succ M hNM ih =>
      rw [Finset.sum_Ico_succ_top hNM]
      have hs := alpogePhysicalCharacterHistory_succ_sub c ell M
      calc
        alpogePhysicalCharacterHistory c ell (M + 1) -
          alpogePhysicalCharacterHistory c ell N =
            (alpogePhysicalCharacterHistory c ell M -
              alpogePhysicalCharacterHistory c ell N) +
                (alpogePhysicalCharacterRecip c M + ell) := by
                  linear_combination hs
        _ = _ := by rw [ih]

theorem alpogePhysicalCharacterHistory_eq_sum
    (c : ℕ → ℂ) (ell : ℂ) (N : ℕ) :
    alpogePhysicalCharacterHistory c ell N =
      ∑ j ∈ Finset.range N,
        (alpogePhysicalCharacterRecip c j + ell) := by
  have h := alpogePhysicalCharacterHistory_difference_eq_history
    c ell 0 N (Nat.zero_le N)
  simpa [alpogePhysicalCharacterHistory,
    alpogePhysicalCharacterRecip, alpogePhysicalCharacterPsi,
    Finset.Ico_zero_eq_range] using h

/-- The only unconditional bound introduced here is the correctly
charged total variation of the COMPLETE centered reciprocal history.
Crucially this is NOT asserted to have square-root size. -/
theorem alpogePhysicalCharacterHistory_norm_le_totalVariation
    (c : ℕ → ℂ) (ell : ℂ) (N : ℕ) :
    ‖alpogePhysicalCharacterHistory c ell N‖ ≤
      ∑ j ∈ Finset.range N,
        ‖alpogePhysicalCharacterRecip c j + ell‖ := by
  rw [alpogePhysicalCharacterHistory_eq_sum]
  exact norm_sum_le _ _

/-- Original sharp prime-power kernel, exactly as a centered history. -/
theorem alpogePhysicalCharacterWeighted_eq_history
    (c : ℕ → ℂ) (ell : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      c n * ((N : ℂ) / (n : ℂ) - 1)) +
      (N : ℂ) * ell =
        alpogePhysicalCharacterHistory c ell N := by
  unfold alpogePhysicalCharacterHistory
    alpogePhysicalCharacterRecip alpogePhysicalCharacterPsi
  calc
    _ = (∑ n ∈ Finset.Icc 1 N,
      ((N : ℂ) * (c n / (n : ℂ)) - c n)) +
        (N : ℂ) * ell := by
          congr 1
          apply Finset.sum_congr rfl
          intro n _hn
          ring
    _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
          ring

/-- The physical coefficient includes ALL Lambda prime powers and their
actual Frobenius/inertia multiplicative mean, without a toy host. -/
def alpogePhysicalFrobCharacterCoefficient
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ψ : AddChar G ℂ) (n : ℕ) : ℂ :=
  ((Λ n : ℝ) : ℂ) *
    alpogeNativeFrobInertiaPrimeValue inertia frob ψ n

/-- EXACT complete-source identification for every nonprincipal
Frobenius/inertia character at an integer endpoint. No GRH bound is
smuggled into ell and no ramified term is removed. -/
theorem alpogeNativeFrobGPsi_nat_eq_physicalHistory
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ) (ψ : AddChar G ℂ) (N : ℕ)
    (hψ : ψ ≠ 0) :
    alpogeNativeFrobInertiaGPsi inertia frob ell ψ (N : ℝ) =
      alpogePhysicalCharacterHistory
        (alpogePhysicalFrobCharacterCoefficient inertia frob ψ)
        (ell ψ) N := by
  rw [alpogeNativeFrobInertiaGPsi_nonprincipal
    inertia frob ell ψ (N : ℝ) hψ]
  unfold alpogeNativeFrobInertiaPrimeSum
  rw [Nat.floor_natCast]
  have hsum :
      (∑ n ∈ Finset.Icc 1 N,
        ((Λ n : ℝ) : ℂ) *
          alpogeNativeFrobInertiaPrimeValue inertia frob ψ n *
          (((N : ℝ) / (n : ℝ) - 1 : ℝ) : ℂ)) =
      ∑ n ∈ Finset.Icc 1 N,
        alpogePhysicalFrobCharacterCoefficient inertia frob ψ n *
          ((N : ℂ) / (n : ℂ) - 1) := by
    apply Finset.sum_congr rfl
    intro n _hn
    unfold alpogePhysicalFrobCharacterCoefficient
    push_cast
    ring
  rw [hsum]
  exact alpogePhysicalCharacterWeighted_eq_history
    (alpogePhysicalFrobCharacterCoefficient inertia frob ψ)
    (ell ψ) N

/-- A fully unconditional statement for all three *actual* distinguished
nonprincipal characters, if instantiated with the published psiA/psiB.
Any square-root estimate on them must now be a theorem about the
complete reciprocal histories, not an unproved character norm. -/
theorem alpogeNativeFrobGPsi_nat_norm_eq_history_norm
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (inertia : ℕ → AddSubgroup G) (frob : ℕ → G)
    (ell : AddChar G ℂ → ℂ) (ψ : AddChar G ℂ) (N : ℕ)
    (hψ : ψ ≠ 0) :
    ‖alpogeNativeFrobInertiaGPsi inertia frob ell ψ (N : ℝ)‖ =
      ‖∑ j ∈ Finset.range N,
        (alpogePhysicalCharacterRecip
          (alpogePhysicalFrobCharacterCoefficient inertia frob ψ) j +
          ell ψ)‖ := by
  rw [alpogeNativeFrobGPsi_nat_eq_physicalHistory
    inertia frob ell ψ N hψ,
      alpogePhysicalCharacterHistory_eq_sum]

end RHLean.Analysis
