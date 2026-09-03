import Mathlib
import RHLean.Analysis.DynamicVioleBaseline
import RHLean.Analysis.NativePNTSquarePrefixMobiusError

/-!
# Möbius correlation form of the signed Viole square-block response

`DynamicVioleBaseline` isolates the exact signed divisor-block response

`B(N;M,L) = sum_{M<d<=L} w_N(d) * e(floor(N/d))`

inside the normalized first Selberg recurrence.  This module pushes that block
through the already-compiled identity `Lambda = mu * log` without taking an
absolute value.

The result is an exact uncentered correlation

`sum_m mu(m) * Response(N,M,L,m)`.

For fixed total divisor `d`, the error value is frozen while the Möbius-log
fibre is paired.  Thus adjoining a fresh prime acts by the same Euler factor as
elsewhere in the repository.  The only local defect is the explicit difference
between the parent and child cofactor responses.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Response seen from one Möbius cofactor after restricting the total divisor
to the physical square block `(M,L]`.  The error is attached to the total
divisor `d`, so it is unchanged by any internal divisor-fibre pairing. -/
def nativePNTSignedSquareBlockCofactorResponse
    (N M L m : Nat) : Real :=
  ∑ d ∈ (Finset.Ioc M L).filter (fun d => m ∣ d),
    Real.log ((d / m : Nat) : Real) * nativePNTError (N / d)

/-- Uncentered Möbius-parity correlation of the complete square-block response. -/
def nativePNTSignedSquareBlockMobiusCorrelation
    (N M L : Nat) : Real :=
  ∑ m ∈ Finset.Icc 1 L,
    (μ : ArithmeticFunction Real) m *
      nativePNTSignedSquareBlockCofactorResponse N M L m

/-- Exact interval Fubini identity.  The `Lambda`-weighted square block is
literally the Möbius-parity correlation above.  No triangle inequality,
probabilistic centering, or asymptotic estimate is used. -/
theorem nativeLambdaSquareBlockWeighted_eq_mobiusCorrelation
    (N M L : Nat) :
    (∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (N / d)) =
      nativePNTSignedSquareBlockMobiusCorrelation N M L := by
  classical
  have hmem : ∀ (d m : Nat),
      d ∈ Finset.Ioc M L ∧ m ∈ d.divisors ↔
        d ∈ (Finset.Ioc M L).filter (fun x => m ∣ x) ∧
          m ∈ Finset.Icc 1 L := by
    intro d m
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc,
      Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdM, hdL⟩, hmd, hd0⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hd0 (Nat.eq_zero_of_zero_dvd hmd)
      have hmdle : m ≤ d := Nat.le_of_dvd (by omega) hmd
      exact ⟨⟨⟨hdM, hdL⟩, hmd⟩,
        Nat.one_le_iff_ne_zero.mpr hm0, hmdle.trans hdL⟩
    · rintro ⟨⟨⟨hdM, hdL⟩, hmd⟩, _hm1, _hmL⟩
      exact ⟨⟨hdM, hdL⟩, hmd, Nat.ne_of_gt (by omega : 0 < d)⟩
  calc
    (∑ d ∈ Finset.Ioc M L, Λ d * nativePNTError (N / d)) =
        ∑ d ∈ Finset.Ioc M L,
          ∑ m ∈ d.divisors,
            ((μ : ArithmeticFunction Real) m *
              Real.log ((d / m : Nat) : Real)) *
                nativePNTError (N / d) := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [← nativeMobiusLogDivisorFiber_eq_vonMangoldt d,
        nativeMobiusLogDivisorFiber, Finset.sum_mul]
    _ = ∑ m ∈ Finset.Icc 1 L,
          ∑ d ∈ (Finset.Ioc M L).filter (fun x => m ∣ x),
            ((μ : ArithmeticFunction Real) m *
              Real.log ((d / m : Nat) : Real)) *
                nativePNTError (N / d) :=
      Finset.sum_comm' hmem
    _ = ∑ m ∈ Finset.Icc 1 L,
          (μ : ArithmeticFunction Real) m *
            (∑ d ∈ (Finset.Ioc M L).filter (fun x => m ∣ x),
              Real.log ((d / m : Nat) : Real) *
                nativePNTError (N / d)) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ = nativePNTSignedSquareBlockMobiusCorrelation N M L := by
      rfl

/-- On a genuine later endpoint, the normalized floor-weight square-block
response is exactly the Möbius correlation divided by that endpoint. -/
theorem nativePNTNormalizedFloorSquareBlockResponse_eq_mobiusCorrelation_div
    (N M L : Nat) (hL : 1 ≤ L) (hLN : L ≤ N) :
    nativePNTNormalizedFloorSquareBlockResponse N M L =
      nativePNTSignedSquareBlockMobiusCorrelation N M L / (N : Real) := by
  have hN : 1 ≤ N := hL.trans hLN
  have hNR0 : (N : Real) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  unfold nativePNTNormalizedFloorSquareBlockResponse
  calc
    (∑ d ∈ Finset.Ioc M L,
        nativePNTNormalizedFloorWeight N d *
          nativePNTNormalizedError (N / d)) =
      ∑ d ∈ Finset.Ioc M L,
        (Λ d * nativePNTError (N / d)) / (N : Real) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdI := Finset.mem_Ioc.mp hd
        have hdpos : 0 < d := by omega
        have hdN : d ≤ N := hdI.2.trans hLN
        have hq1 : 1 ≤ N / d :=
          (Nat.one_le_div_iff hdpos).2 hdN
        have hqR0 : (((N / d : Nat) : Real)) ≠ 0 := by
          exact_mod_cast (show N / d ≠ 0 by omega)
        unfold nativePNTNormalizedFloorWeight nativePNTNormalizedError
        field_simp [hNR0, hqR0]
        ring
    _ = (∑ d ∈ Finset.Ioc M L,
          Λ d * nativePNTError (N / d)) / (N : Real) := by
      rw [Finset.sum_div]
    _ = nativePNTSignedSquareBlockMobiusCorrelation N M L / (N : Real) := by
      rw [nativeLambdaSquareBlockWeighted_eq_mobiusCorrelation]

/-! ## Centered covariance coordinate -/

/-- Number of Möbius cofactor coordinates in the square-block correlation. -/
def nativePNTSignedSquareBlockCofactorCard (L : Nat) : Nat :=
  (Finset.Icc 1 L).card

/-- Total Möbius parity on the cofactor carrier. -/
def nativePNTSignedSquareBlockParitySum (L : Nat) : Real :=
  ∑ m ∈ Finset.Icc 1 L, (μ : ArithmeticFunction Real) m

/-- Total unweighted cofactor response on the same carrier. -/
def nativePNTSignedSquareBlockResponseSum
    (N M L : Nat) : Real :=
  ∑ m ∈ Finset.Icc 1 L,
    nativePNTSignedSquareBlockCofactorResponse N M L m

/-- Uniform mean of the Möbius parity field. -/
def nativePNTSignedSquareBlockParityMean (L : Nat) : Real :=
  nativePNTSignedSquareBlockParitySum L /
    (nativePNTSignedSquareBlockCofactorCard L : Real)

/-- Uniform mean of the signed response field. -/
def nativePNTSignedSquareBlockResponseMean
    (N M L : Nat) : Real :=
  nativePNTSignedSquareBlockResponseSum N M L /
    (nativePNTSignedSquareBlockCofactorCard L : Real)

/-- Uniform centered covariance of Möbius parity with the square-block response. -/
def nativePNTSignedSquareBlockCovariance
    (N M L : Nat) : Real :=
  ((nativePNTSignedSquareBlockCofactorCard L : Real) *
        nativePNTSignedSquareBlockMobiusCorrelation N M L -
      nativePNTSignedSquareBlockParitySum L *
        nativePNTSignedSquareBlockResponseSum N M L) /
    (nativePNTSignedSquareBlockCofactorCard L : Real) ^ 2

/-- Exact mean-plus-covariance decomposition of the uncentered correlation. -/
theorem nativePNTSignedSquareBlockMobiusCorrelation_eq_card_mul_mean_add_covariance
    (N M L : Nat) (hL : 1 ≤ L) :
    nativePNTSignedSquareBlockMobiusCorrelation N M L =
      (nativePNTSignedSquareBlockCofactorCard L : Real) *
        (nativePNTSignedSquareBlockParityMean L *
            nativePNTSignedSquareBlockResponseMean N M L +
          nativePNTSignedSquareBlockCovariance N M L) := by
  have hcardNat : 0 < nativePNTSignedSquareBlockCofactorCard L := by
    unfold nativePNTSignedSquareBlockCofactorCard
    apply Finset.card_pos.mpr
    exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩⟩
  have hcard0 : (nativePNTSignedSquareBlockCofactorCard L : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardNat)
  unfold nativePNTSignedSquareBlockParityMean
    nativePNTSignedSquareBlockResponseMean
    nativePNTSignedSquareBlockCovariance
  field_simp [hcard0]
  ring

/-- Consequently the literal normalized square-block response is exactly its
mean-plus-covariance coordinate divided by the later endpoint. -/
theorem nativePNTNormalizedFloorSquareBlockResponse_eq_mean_add_covariance
    (N M L : Nat) (hL : 1 ≤ L) (hLN : L ≤ N) :
    nativePNTNormalizedFloorSquareBlockResponse N M L =
      ((nativePNTSignedSquareBlockCofactorCard L : Real) *
        (nativePNTSignedSquareBlockParityMean L *
            nativePNTSignedSquareBlockResponseMean N M L +
          nativePNTSignedSquareBlockCovariance N M L)) / (N : Real) := by
  rw [nativePNTNormalizedFloorSquareBlockResponse_eq_mobiusCorrelation_div
      N M L hL hLN,
    nativePNTSignedSquareBlockMobiusCorrelation_eq_card_mul_mean_add_covariance
      N M L hL]

/-! ## Prime-by-prime Euler law and explicit physical defect -/

/-- Reciprocal uncentered correlation coordinate for one cofactor. -/
def nativePNTSignedSquareBlockCorrelationReciprocalSummand
    (N M L m : Nat) : Real :=
  (((μ m : Int) : Real) *
      nativePNTSignedSquareBlockCofactorResponse N M L m) / (m : Real)

/-- The only local defect when a fresh prime is adjoined to the reciprocal
correlation coordinate: the child sees a different cofactor response. -/
def nativePNTSignedSquareBlockFreshPrimePhysicalDefect
    (N M L m p : Nat) : Real :=
  (((μ m : Int) : Real) *
      (nativePNTSignedSquareBlockCofactorResponse N M L m -
        nativePNTSignedSquareBlockCofactorResponse N M L (m * p))) /
    ((m * p : Nat) : Real)

/-- **Exact Euler law for one fresh prime.**  The parent/child reciprocal
correlation pair contracts by `1 - 1/p`; every failure of the response to be
invariant under the prime addition is retained in the explicit signed physical
defect above. -/
theorem nativePNTSignedSquareBlockCorrelationReciprocalSummand_add_mul_freshPrime
    (N M L : Nat) {m p : Nat}
    (hm : 0 < m) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L (m * p) =
      (1 - 1 / (p : Real)) *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand N M L m +
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect N M L m p := by
  have hm0 : (m : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hp0 : (p : Real) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  unfold nativePNTSignedSquareBlockCorrelationReciprocalSummand
    nativePNTSignedSquareBlockFreshPrimePhysicalDefect
  rw [nativeMobius_adjoin_prime m p hp hcop]
  push_cast
  field_simp [hm0, hp0]
  ring

end RHLean.Analysis
