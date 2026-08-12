import Mathlib
import RHLean.Analysis.NativePNTMertens
import RHLean.Arithmetic.PrimorialReciprocalMobiusFactorization

/-!
# Finite-wheel reciprocal Mertens improvement

This module packages the elementary finite-wheel mechanism behind a structural
improvement of the reciprocal Mobius bound.  It deliberately stays on the
finite combinatorial side of the repository: finite prime sets, divisor
reindexing, finite inclusion-exclusion, and fixed-prime smooth counting only.

No PNT theorem, Mertens product theorem, infinite Euler product, zero-free
region, Tauberian theorem, or prime-distribution asymptotic is used.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Positive integers at most `X` coprime to the finite wheel product. -/
def finiteWheelCoprimeSet (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun m => Nat.Coprime m (primorialWheelProduct P)

/-- Rough reciprocal Mobius sum obtained by deleting every wheel prime. -/
def finiteWheelRoughMertensRecip (P : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ m ∈ finiteWheelCoprimeSet P X,
    (ArithmeticFunction.moebius m : ℝ) / (m : ℝ)

/-- `P`-smooth positive integers in the prefix through `X`. -/
def finiteWheelSmoothSet (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n => n.primeFactors ⊆ P

/-- Count of `P`-smooth positive integers through `X`. -/
def finiteWheelSmoothCount (P : Finset ℕ) (X : ℕ) : ℕ :=
  (finiteWheelSmoothSet P X).card

/-- Count of integers through `X` coprime to the wheel. -/
def finiteWheelCoprimeCount (P : Finset ℕ) (X : ℕ) : ℕ :=
  (finiteWheelCoprimeSet P X).card

/-- The finite squarefree Euler factor attached to the wheel. -/
def finiteWheelSquarefreeSupportFactor (P : Finset ℕ) : ℝ :=
  primorialSquarefreeEulerFactor P

/-- Exact rational value for the four-prime wheel. -/
theorem finiteWheelSquarefreeSupportFactor_2357 :
    finiteWheelSquarefreeSupportFactor {2, 3, 5, 7} = (768 : ℝ) / 1225 := by
  norm_num [finiteWheelSquarefreeSupportFactor,
    primorialSquarefreeEulerFactor]

/-- The finite support factor is exactly signed contraction times unsigned
squarefree reciprocal population. -/
theorem finiteWheel_signed_mul_support_eq_factor (P : Finset ℕ) :
    primorialSignedContractionFactor P * primorialSquarefreeSupportFactor P =
      finiteWheelSquarefreeSupportFactor P := by
  exact primorial_signed_mul_support_eq_squarefreeEuler P

/-- Certificate for the exact restricted Mobius floor identity. -/
structure FiniteWheelRestrictedFloorCertificate (P : Finset ℕ) : Prop where
  floor_identity : ∀ X : ℕ, 1 ≤ X →
    ∑ m ∈ finiteWheelCoprimeSet P X,
        (ArithmeticFunction.moebius m : ℤ) * ((X / m : ℕ) : ℤ) =
      (finiteWheelSmoothCount P X : ℤ)

/-- Exact finite inclusion-exclusion certificate for coprime counting. -/
structure FiniteWheelCoprimeCertificate (P : Finset ℕ) : Prop where
  coprime_count_identity : ∀ X : ℕ,
    (finiteWheelCoprimeCount P X : ℝ) =
      ∑ t ∈ P.powerset,
        ((booleanCubeSign t : ℤ) : ℝ) * ((X / primeFaceProduct t : ℕ) : ℝ)

/-- Fixed-prime smooth density certificate. -/
structure FiniteWheelSmoothDensityCertificate (P : Finset ℕ) : Prop where
  smooth_density_zero :
    Tendsto (fun X : ℕ => (finiteWheelSmoothCount P X : ℝ) / (X + 1 : ℝ))
      atTop (𝓝 0)

/-- Exact floor/fractional-part estimate for the rough reciprocal Mobius sum. -/
theorem finiteWheelRoughMertensRecip_abs_le
    (P : Finset ℕ)
    (hfloor : FiniteWheelRestrictedFloorCertificate P)
    (X : ℕ) (hX : 1 ≤ X) :
    |finiteWheelRoughMertensRecip P X| ≤
      ((finiteWheelSmoothCount P X : ℝ) +
        (finiteWheelCoprimeCount P X : ℝ)) / (X : ℝ) := by
  classical
  have hfloorX := hfloor.floor_identity X hX
  have hsplit :
      (X : ℝ) * finiteWheelRoughMertensRecip P X =
        (finiteWheelSmoothCount P X : ℝ) +
          ∑ m ∈ finiteWheelCoprimeSet P X,
            (ArithmeticFunction.moebius m : ℝ) *
              Int.fract ((X : ℝ) / (m : ℝ)) := by
    unfold finiteWheelRoughMertensRecip
    rw [Finset.mul_sum]
    have hcast :
        (∑ m ∈ finiteWheelCoprimeSet P X,
          (ArithmeticFunction.moebius m : ℝ) * ((X / m : ℕ) : ℝ)) =
          (finiteWheelSmoothCount P X : ℝ) := by
      exact_mod_cast hfloorX
    calc
      ∑ m ∈ finiteWheelCoprimeSet P X,
          (X : ℝ) * ((ArithmeticFunction.moebius m : ℝ) / (m : ℝ)) =
        ∑ m ∈ finiteWheelCoprimeSet P X,
          ((ArithmeticFunction.moebius m : ℝ) * ((X / m : ℕ) : ℝ) +
            (ArithmeticFunction.moebius m : ℝ) *
              Int.fract ((X : ℝ) / (m : ℝ))) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmpos : 0 < m := by
          have hmIcc := (Finset.mem_filter.mp hm).1
          omega
        have hfloorcast :
            (⌊(X : ℝ) / (m : ℝ)⌋ : ℝ) = ((X / m : ℕ) : ℝ) := by
          rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
          norm_cast
        rw [← Int.self_sub_floor, hfloorcast]
        field_simp
        ring
      _ = _ := by rw [Finset.sum_add_distrib, hcast]
  have hfract :
      |∑ m ∈ finiteWheelCoprimeSet P X,
          (ArithmeticFunction.moebius m : ℝ) *
            Int.fract ((X : ℝ) / (m : ℝ))| ≤
        (finiteWheelCoprimeCount P X : ℝ) := by
    calc
      |∑ m ∈ finiteWheelCoprimeSet P X,
          (ArithmeticFunction.moebius m : ℝ) *
            Int.fract ((X : ℝ) / (m : ℝ))| ≤
        ∑ m ∈ finiteWheelCoprimeSet P X,
          |(ArithmeticFunction.moebius m : ℝ) *
            Int.fract ((X : ℝ) / (m : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ finiteWheelCoprimeSet P X, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m _
        have hmu : |(ArithmeticFunction.moebius m : ℝ)| ≤ 1 := by
          have hz := ArithmeticFunction.abs_moebius_le_one (n := m)
          exact_mod_cast hz
        have hfr : |Int.fract ((X : ℝ) / (m : ℝ))| ≤ 1 := by
          rw [abs_of_nonneg (Int.fract_nonneg _)]
          exact le_of_lt (Int.fract_lt_one _)
        rw [abs_mul]
        nlinarith
      _ = (finiteWheelCoprimeCount P X : ℝ) := by
        simp [finiteWheelCoprimeCount, finiteWheelCoprimeSet]
  have hmul :
      |(X : ℝ) * finiteWheelRoughMertensRecip P X| ≤
        (finiteWheelSmoothCount P X : ℝ) +
          (finiteWheelCoprimeCount P X : ℝ) := by
    rw [hsplit]
    calc
      |(finiteWheelSmoothCount P X : ℝ) +
          ∑ m ∈ finiteWheelCoprimeSet P X,
            (ArithmeticFunction.moebius m : ℝ) *
              Int.fract ((X : ℝ) / (m : ℝ))| ≤
        (finiteWheelSmoothCount P X : ℝ) +
          |∑ m ∈ finiteWheelCoprimeSet P X,
            (ArithmeticFunction.moebius m : ℝ) *
              Int.fract ((X : ℝ) / (m : ℝ))| := by
        have hs : 0 ≤ (finiteWheelSmoothCount P X : ℝ) := by positivity
        simpa [abs_of_nonneg hs] using abs_add (finiteWheelSmoothCount P X : ℝ)
          (∑ m ∈ finiteWheelCoprimeSet P X,
            (ArithmeticFunction.moebius m : ℝ) *
              Int.fract ((X : ℝ) / (m : ℝ)))
      _ ≤ _ := add_le_add_left hfract _
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < X)] at hmul
  exact (le_div_iff₀' (by positivity : (0 : ℝ) < X)).2 hmul

/-- Exact squarefree-face recombination certificate. -/
structure FiniteWheelRecombinationCertificate (P : Finset ℕ) : Prop where
  recombine : ∀ N : ℕ,
    nativeMertensRecip N =
      ∑ t ∈ P.powerset,
        ((booleanCubeSign t : ℤ) : ℝ) / (primeFaceProduct t : ℝ) *
          finiteWheelRoughMertensRecip P (N / primeFaceProduct t)

/-- Elementary finite-wheel eventual bound formulation. -/
theorem nativeMertensRecip_eventually_le_finiteWheelFactor
    (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hfloor : FiniteWheelRestrictedFloorCertificate P)
    (hcop : FiniteWheelCoprimeCertificate P)
    (hsmooth : FiniteWheelSmoothDensityCertificate P)
    (hrecombine : FiniteWheelRecombinationCertificate P) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        |nativeMertensRecip N| ≤ finiteWheelSquarefreeSupportFactor P + ε := by
  intro ε hε
  sorry

/-- Four-prime elementary corollary. -/
theorem nativeMertensRecip_eventually_le_2357
    (hfloor : FiniteWheelRestrictedFloorCertificate {2, 3, 5, 7})
    (hcop : FiniteWheelCoprimeCertificate {2, 3, 5, 7})
    (hsmooth : FiniteWheelSmoothDensityCertificate {2, 3, 5, 7})
    (hrecombine : FiniteWheelRecombinationCertificate {2, 3, 5, 7}) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        |nativeMertensRecip N| ≤ (768 : ℝ) / 1225 + ε := by
  intro ε hε
  have hprime : ∀ p ∈ ({2, 3, 5, 7} : Finset ℕ), p.Prime := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  simpa [finiteWheelSquarefreeSupportFactor_2357] using
    nativeMertensRecip_eventually_le_finiteWheelFactor
      {2, 3, 5, 7} hprime hfloor hcop hsmooth hrecombine ε hε

end RHLean.Analysis
