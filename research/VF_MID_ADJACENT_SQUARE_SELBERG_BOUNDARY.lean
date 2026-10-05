import Mathlib
import «research.VF_MID_SQUARE_THETA_NATIVE_DESCENT»

/-!
# Adjacent-square Selberg frontier collapse

At the exact square-root wheel cutoff `R` and endpoint `(R+1)^2`,
the partial wheel is already exact on every open square-block site.
Consequently the unresolved second-Selberg frontier collapses to the
single endpoint square when `R+1` is prime, and is empty otherwise.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The partial `R`-wheel is already exact on every open site of the
adjacent square block `(R^2,(R+1)^2)`. -/
theorem vfMidOpenSquare_partialPrimeWheel_exact
    {R n : ℕ} (hR : 3 ≤ R)
    (hn : n ∈ vfMidSquareWheelSites R) :
    partialPrimeWheelSite R ((R + 1) ^ 2) n = μ n := by
  have hnI := Finset.mem_Ioo.mp hn
  have hscale : (R + 1) ^ 2 < 2 * R ^ 2 :=
    vfMidSquare_succ_sq_lt_two_mul_sq R hR
  by_contra hne
  have herr :
      μ n - partialPrimeWheelSite R ((R + 1) ^ 2) n ≠ 0 := by
    intro hzero
    have heq :
        μ n = partialPrimeWheelSite R ((R + 1) ^ 2) n :=
      sub_eq_zero.mp hzero
    exact hne heq.symm
  rcases
      partialPrimeWheel_nonzero_error_factorization_of_two_mul_sq
        R ((R + 1) ^ 2) hscale (by omega : 0 < n) hnI.2.le herr with
    ⟨q, r, _hqPrime, _hrPrime, hRq, hRr, _hresolved, hnqr⟩
  have hqLower : R + 1 ≤ q := by omega
  have hrLower : R + 1 ≤ r := by omega
  have hprod :
      (R + 1) ^ 2 ≤ q * r := by
    simpa [pow_two] using Nat.mul_le_mul hqLower hrLower
  rw [hnqr] at hnI
  omega

/-- The physical open square block and the unresolved adjacent-square
second-Selberg frontier are disjoint.  Every VF seat in the block is therefore
on the resolved side of the wheel split. -/
theorem vfMidSquareWheelSites_disjoint_adjacentSecondSelbergFrontier
    (R : ℕ) (hR : 3 ≤ R) :
    Disjoint (vfMidSquareWheelSites R)
      (nativePNTSignedSecondSelbergWheelFrontierSites
        R ((R + 1) ^ 2)) := by
  rw [Finset.disjoint_left]
  intro n hnBlock hnFront
  have hnI := Finset.mem_Ioo.mp hnBlock
  have hnData :=
    mem_nativePNTSignedSecondSelbergWheelFrontierSites.mp hnFront
  have hscale : (R + 1) ^ 2 < 2 * R ^ 2 :=
    vfMidSquare_succ_sq_lt_two_mul_sq R hR
  rcases
      partialPrimeWheel_nonzero_error_factorization_of_two_mul_sq
        R ((R + 1) ^ 2) hscale (by omega : 0 < n)
        (Finset.mem_Icc.mp hnData.1).2 hnData.2 with
    ⟨q, r, _hqPrime, _hrPrime, hRq, hRr, _hresolved, hnqr⟩
  have hqLower : R + 1 ≤ q := by omega
  have hrLower : R + 1 ≤ r := by omega
  have hprod :
      (R + 1) ^ 2 ≤ q * r := by
    simpa [pow_two] using Nat.mul_le_mul hqLower hrLower
  rw [hnqr] at hnI
  omega

/-- Exact adjacent-square frontier membership.  There is no mixed two-prime
face at this scale; the only possible unresolved site is the endpoint square,
and it occurs exactly when `R+1` itself is prime. -/
theorem vfMidAdjacentSquareSecondSelbergFrontierSite_iff
    {R n : ℕ} (hR : 3 ≤ R) :
    n ∈ nativePNTSignedSecondSelbergWheelFrontierSites
        R ((R + 1) ^ 2) ↔
      n = (R + 1) ^ 2 ∧ (R + 1).Prime := by
  constructor
  · intro hn
    have hscale : (R + 1) ^ 2 < 2 * R ^ 2 :=
      vfMidSquare_succ_sq_lt_two_mul_sq R hR
    rcases
        nativePNTSignedSecondSelbergWheelFrontierSite_classification
          hscale hn with hsq | hmix
    · rcases hsq with
        ⟨q, hqPrime, hRq, hnq, _herr, _hkernel⟩
      have hnData :=
        mem_nativePNTSignedSecondSelbergWheelFrontierSites.mp hn
      have hnle : n ≤ (R + 1) ^ 2 :=
        (Finset.mem_Icc.mp hnData.1).2
      have hqLower : R + 1 ≤ q := by omega
      have hqUpper : q ≤ R + 1 := by
        by_contra hnot
        have hlt : R + 1 < q := by omega
        have hpow :
            (R + 1) ^ 2 < q ^ 2 :=
          Nat.pow_lt_pow_left hlt (by omega)
        rw [hnq] at hnle
        omega
      have hqEq : q = R + 1 := by omega
      subst q
      exact ⟨by simpa using hnq, hqPrime⟩
    · rcases hmix with
        ⟨q, r, _hqPrime, _hrPrime, hqr, hRq, hRr,
          hnqr, _herr, _hkernel⟩
      have hnData :=
        mem_nativePNTSignedSecondSelbergWheelFrontierSites.mp hn
      have hnle : n ≤ (R + 1) ^ 2 :=
        (Finset.mem_Icc.mp hnData.1).2
      rw [hnqr] at hnle
      rcases lt_or_gt_of_ne hqr with hqrLt | hrqLt
      · have hqLower : R + 1 ≤ q := by omega
        have hrLower : R + 2 ≤ r := by omega
        have hprod :
            (R + 1) * (R + 2) ≤ q * r :=
          Nat.mul_le_mul hqLower hrLower
        have hstrict :
            (R + 1) ^ 2 < (R + 1) * (R + 2) := by
          have hpos : 0 < R + 1 := by omega
          rw [pow_two]
          exact Nat.mul_lt_mul_of_pos_left
            (by omega : R + 1 < R + 2) hpos
        omega
      · have hrLower : R + 1 ≤ r := by omega
        have hqLower : R + 2 ≤ q := by omega
        have hprod :
            (R + 2) * (R + 1) ≤ q * r :=
          Nat.mul_le_mul hqLower hrLower
        have hstrict :
            (R + 1) ^ 2 < (R + 2) * (R + 1) := by
          have hpos : 0 < R + 1 := by omega
          rw [pow_two]
          exact Nat.mul_lt_mul_of_pos_right
            (by omega : R + 1 < R + 2) hpos
        omega
  · rintro ⟨rfl, hPrime⟩
    apply mem_nativePNTSignedSecondSelbergWheelFrontierSites.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨by positivity, le_rfl⟩
    · have ha :
          primeWheelResolvedPart R ((R + 1) ^ 2) = 1 := by
        have ha0 :
            primeWheelResolvedPart R ((R + 1) ^ 2) ≠ 0 :=
          primeWheelResolvedPart_ne_zero R ((R + 1) ^ 2)
        by_contra hane
        obtain ⟨p, hpPrime, hpDvd⟩ :=
          Nat.exists_prime_and_dvd hane
        have hpPF :
            p ∈ (primeWheelResolvedPart R ((R + 1) ^ 2)).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hpPrime, hpDvd, ha0⟩
        have hpLe : p ≤ R :=
          primeWheelResolvedPart_primeFactor_le hpPF
        have hab :=
          primeWheelResolvedPart_mul_unresolvedPart
            R (n := (R + 1) ^ 2) (by positivity)
        have hpDvdSq : p ∣ (R + 1) ^ 2 := by
          rw [← hab]
          exact dvd_mul_of_dvd_left hpDvd _
        have hpDvdBase : p ∣ R + 1 :=
          hpPrime.dvd_of_dvd_pow hpDvdSq
        have hpEq : p = R + 1 :=
          (Nat.prime_dvd_prime_iff_eq hpPrime hPrime).mp hpDvdBase
        omega
      have hb :
          primeWheelUnresolvedPart R ((R + 1) ^ 2) =
            (R + 1) ^ 2 := by
        have hab :=
          primeWheelResolvedPart_mul_unresolvedPart
            R (n := (R + 1) ^ 2) (by positivity)
        rw [ha] at hab
        simpa using hab
      have hb1 : (R + 1) ^ 2 ≠ 1 := by
        nlinarith
      have hnsq : ¬ Squarefree ((R + 1) ^ 2) := by
        rw [Nat.squarefree_iff_prime_squarefree]
        push_neg
        exact ⟨R + 1, hPrime, by simp [pow_two]⟩
      have hmu0 :
          μ ((R + 1) ^ 2) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
      have herr :=
        partialPrimeWheel_error_eq
          R ((R + 1) ^ 2)
          (n := (R + 1) ^ 2)
          (by positivity) le_rfl
      rw [hb, if_neg hb1, ha, hb, hmu0] at herr
      norm_num at herr
      intro hzero
      rw [hmu0] at hzero
      omega

/-- Finset form of the exact adjacent-square frontier collapse. -/
theorem vfMidAdjacentSquareSecondSelbergFrontierSites_eq
    (R : ℕ) (hR : 3 ≤ R) :
    nativePNTSignedSecondSelbergWheelFrontierSites
        R ((R + 1) ^ 2) =
      if (R + 1).Prime then {(R + 1) ^ 2} else ∅ := by
  ext n
  rw [vfMidAdjacentSquareSecondSelbergFrontierSite_iff hR]
  by_cases hp : (R + 1).Prime <;> simp [hp]

/-- Closed form of the adjacent-square signed second-Selberg boundary charge. -/
theorem vfMidAdjacentSquareSecondSelbergFrontierCharge_eq
    (R : ℕ) (hR : 3 ≤ R) :
    nativePNTSignedSecondSelbergWheelFrontierCharge
        R ((R + 1) ^ 2) =
      if (R + 1).Prime then
        -(Real.log ((R + 1 : ℕ) : ℝ)) ^ 2
      else 0 := by
  unfold nativePNTSignedSecondSelbergWheelFrontierCharge
  rw [vfMidAdjacentSquareSecondSelbergFrontierSites_eq R hR]
  by_cases hp : (R + 1).Prime
  · simp [hp, nativePNTSignedSecondSelbergKernel_prime_sq]
  · simp [hp]

/-- The square-root-wheel Fubini residual vanishes identically at the adjacent
square endpoint.  This is the exact specialization of the repository's
cofactor-first reciprocal Fubini split: every unresolved divisor has quotient
one, hence logarithmic fibre weight zero. -/
theorem vfMidAdjacentSquareWheelFubiniResidual_eq_zero
    (R : ℕ) (hR : 3 ≤ R) :
    nativePNTWheelResidualSignedMass R ((R + 1) ^ 2) = 0 := by
  exact nativePNTWheelResidualSignedMass_eq_zero_of_lt_two_mul_sq
    R ((R + 1) ^ 2)
      (vfMidSquare_succ_sq_lt_two_mul_sq R hR)

/-- Consequently the exact first signed Selberg recurrence at the adjacent
square endpoint contains only the resolved partial-wheel mass. -/
theorem vfMidAdjacentSquareWheelFubini_eq_resolved
    (R : ℕ) (hR : 3 ≤ R) :
    nativePNTError ((R + 1) ^ 2) *
          Real.log (((R + 1) ^ 2 : ℕ) : ℝ) +
        nativePNTWheelResolvedSignedMass R ((R + 1) ^ 2) =
      nativePNTSignedSelbergRemainder ((R + 1) ^ 2) := by
  exact nativePNTError_mul_log_add_squareRootWheel_eq_remainder
    R ((R + 1) ^ 2)
      (vfMidSquare_succ_sq_lt_two_mul_sq R hR)

/-- **Adjacent-square sequential Fubini closure.**

After the square-root wheel residual has vanished, the complete physical
PNT-error increment is the repository's resolved Euler forcing.  This is the
literal one-block cofactor/quotient Fubini map; no unresolved boundary term is
discarded. -/
theorem vfMidAdjacentSquareSequentialDiscrepancy_eq_resolvedEulerForcing
    (R : ℕ) (hR : 3 ≤ R) :
    nativePNTSequentialSquareBlockDiscrepancy
        (R ^ 2) ((R + 1) ^ 2) =
      nativePNTSequentialEulerForcing
        R (R ^ 2) ((R + 1) ^ 2) := by
  exact nativePNTSequentialSquareBlockDiscrepancy_eq_eulerForcing
    R (R ^ 2) ((R + 1) ^ 2)
    (by nlinarith : 1 ≤ R ^ 2)
    (by nlinarith : R ^ 2 ≤ (R + 1) ^ 2)
    (vfMidSquare_succ_sq_lt_two_mul_sq R hR)
    (by nlinarith : R ^ 2 < 2 * R ^ 2)
    (vfMidSquare_succ_sq_lt_two_mul_sq R hR)

/-- The corresponding adjacent-square PNT energy change remains entirely on
that resolved Euler forcing. -/
theorem vfMidAdjacentSquarePNTErrorEnergy_eq_resolvedEulerForcing
    (R : ℕ) (hR : 3 ≤ R) :
    nativePNTError ((R + 1) ^ 2) ^ 2 -
        nativePNTError (R ^ 2) ^ 2 =
      2 * nativePNTError (R ^ 2) *
          nativePNTSequentialEulerForcing
            R (R ^ 2) ((R + 1) ^ 2) +
        nativePNTSequentialEulerForcing
          R (R ^ 2) ((R + 1) ^ 2) ^ 2 := by
  exact nativePNTError_sq_sub_sq_eq_two_mul_error_mul_eulerForcing_add_sq
    R (R ^ 2) ((R + 1) ^ 2)
    (by nlinarith : 1 ≤ R ^ 2)
    (by nlinarith : R ^ 2 ≤ (R + 1) ^ 2)
    (vfMidSquare_succ_sq_lt_two_mul_sq R hR)
    (by nlinarith : R ^ 2 < 2 * R ^ 2)
    (vfMidSquare_succ_sq_lt_two_mul_sq R hR)

/-- The resolved interior of the second-Selberg product carrier after removing
the exact adjacent-square wheel frontier. -/
def vfMidAdjacentSquareSecondSelbergResolvedSites (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ((R + 1) ^ 2)).sdiff
    nativePNTSignedSecondSelbergWheelFrontierSites R ((R + 1) ^ 2)

/-- Signed second-Selberg error mass on the resolved interior. -/
def vfMidAdjacentSquareSecondSelbergResolvedErrorMass (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidAdjacentSquareSecondSelbergResolvedSites R,
    nativePNTSignedSecondSelbergKernel n *
      nativePNTError (((R + 1) ^ 2) / n)

/-- **Exact second-Selberg boundary split.**

The full signed second-Selberg product carrier is the resolved interior plus
the literal wheel frontier.  No sign or absolute-value estimate occurs here. -/
theorem vfMidAdjacentSquareSecondSelbergKernelErrorMass_eq_resolved_add_frontier
    (R : ℕ) :
    nativePNTSignedSecondSelbergKernelErrorMass ((R + 1) ^ 2) =
      vfMidAdjacentSquareSecondSelbergResolvedErrorMass R +
        nativePNTSignedSecondSelbergWheelFrontierErrorMass
          R ((R + 1) ^ 2) := by
  have hsub :
      nativePNTSignedSecondSelbergWheelFrontierSites R ((R + 1) ^ 2) ⊆
        Finset.Icc 1 ((R + 1) ^ 2) := by
    intro n hn
    exact
      (mem_nativePNTSignedSecondSelbergWheelFrontierSites.mp hn).1
  have hs := Finset.sum_sdiff hsub
    (f := fun n =>
      nativePNTSignedSecondSelbergKernel n *
        nativePNTError (((R + 1) ^ 2) / n))
  unfold nativePNTSignedSecondSelbergKernelErrorMass
    vfMidAdjacentSquareSecondSelbergResolvedErrorMass
    vfMidAdjacentSquareSecondSelbergResolvedSites
    nativePNTSignedSecondSelbergWheelFrontierErrorMass
  exact hs.symm

/-- Boundary-error form after the reciprocal quotient has collapsed to one. -/
theorem vfMidAdjacentSquareSecondSelbergFrontierErrorMass_eq
    (R : ℕ) (hR : 3 ≤ R) :
    nativePNTSignedSecondSelbergWheelFrontierErrorMass
        R ((R + 1) ^ 2) =
      if (R + 1).Prime then
        (Real.log ((R + 1 : ℕ) : ℝ)) ^ 2
      else 0 := by
  have hscale : (R + 1) ^ 2 < 2 * R ^ 2 :=
    vfMidSquare_succ_sq_lt_two_mul_sq R hR
  rw [nativePNTSignedSecondSelbergWheelFrontierErrorMass_eq_neg_charge hscale,
    vfMidAdjacentSquareSecondSelbergFrontierCharge_eq R hR]
  by_cases hp : (R + 1).Prime <;> simp [hp]

end RHLean.Analysis
