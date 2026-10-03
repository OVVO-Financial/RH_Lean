import Mathlib
import «research.VF_MID_FLOOR_LI_DISCRETE_BACKLOG»
import «research.PRIME_FLIP_PNT_TELESCOPE»
import «research.PRIME_DENSITY_PNT_LOG_BOUND»
import RHLean.Analysis.PrimeSievePNTResidualEnvelope

/-!
# Floor-Li signed population balance in the Mobius/Abel carrier

The primitive integer mismatch is the first difference of

  E(n) = pi(n) - floor(Li_2(n)).

Its signed mass on an interval telescopes exactly to E(B)-E(A).

When the primitive mismatch takes values in {-1,0,1}, that signed mass is
literally

  #( +1 mismatches ) - #( -1 mismatches ).

Write

  r(n) = Li_2(n) - floor(Li_2(n)).

Then 0 <= r(n) < 1 and exactly

  E(n) = Delta(n) + r(n),

where Delta(n) = pi(n)-Li_2(n) is the repository prime discrepancy.
Consequently every interval satisfies

  signedMismatch(A,B)
    = [Delta(B)-Delta(A)] + [r(B)-r(A)],

with |r(B)-r(A)| < 1.

The existing prime-flip Abel identity then gives the exact carrier formula

  signedMismatch(A,B)
    = primeFlipPNTError(A,B)
      + primeSieveMoebiusDiscrepancySum(A,B)
      - primeSieveAbelBoundary(A,B)
      + endpointRounding(A,B).

Thus the discrete {-1,0,1} balance differs by strictly less than one count
from the already-compiled prime-flip/Mobius/Abel carrier.  We do NOT identify
the mismatch atom with the Mobius function; Mobius enters through the exact
Abel atomization already present in the repository.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Primitive integer mismatch -/

def vfMidFloorLiIntegerPotential (n : ℕ) : ℤ :=
  ⌊vfMidLogarithmicIntegralFromTwo (n : ℝ)⌋

def vfMidPrimeFloorLiIntegerBacklog (n : ℕ) : ℤ :=
  (Nat.primeCounting n : ℤ) - vfMidFloorLiIntegerPotential n

def vfMidFloorLiPrimitiveMismatch (n : ℕ) : ℤ :=
  vfMidPrimeFloorLiIntegerBacklog (n + 1) -
    vfMidPrimeFloorLiIntegerBacklog n

def vfMidFloorLiSignedMismatchMass (A B : ℕ) : ℤ :=
  ∑ n ∈ Finset.Ico A B, vfMidFloorLiPrimitiveMismatch n

theorem vfMidFloorLiSignedMismatchMass_eq_backlog_increment
    {A B : ℕ} (hAB : A ≤ B) :
    vfMidFloorLiSignedMismatchMass A B =
      vfMidPrimeFloorLiIntegerBacklog B -
        vfMidPrimeFloorLiIntegerBacklog A := by
  unfold vfMidFloorLiSignedMismatchMass vfMidFloorLiPrimitiveMismatch
  exact Finset.sum_Ico_sub vfMidPrimeFloorLiIntegerBacklog hAB

theorem vfMidPrimeFloorLiIntegerBacklog_sq (R : ℕ) :
    vfMidPrimeFloorLiIntegerBacklog (R ^ 2) =
      vfMidPrimeFloorLiBacklog R := by
  unfold vfMidPrimeFloorLiIntegerBacklog vfMidPrimeFloorLiBacklog
    vfMidFloorLiIntegerPotential vfMidFloorLiSquarePotential
  norm_num [Nat.cast_pow]

theorem vfMidFloorLiSignedMismatchMass_sq_eq_neg_dyadicPrimeDefect
    {A B : ℕ} (hAB : A ≤ B) :
    vfMidFloorLiSignedMismatchMass (A ^ 2) (B ^ 2) =
      -vfMidFloorLiDyadicPrimeDefect A B := by
  have hsq : A ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hAB 2
  rw [vfMidFloorLiSignedMismatchMass_eq_backlog_increment hsq,
    vfMidPrimeFloorLiIntegerBacklog_sq,
    vfMidPrimeFloorLiIntegerBacklog_sq]
  have hdef :=
    vfMidFloorLiDyadicPrimeDefect_eq_neg_backlog_increment A B hAB
  omega

/-! ## Literal +1 / -1 populations -/

def VFMidFloorLiPrimitiveTernaryOn (A B : ℕ) : Prop :=
  ∀ n ∈ Finset.Ico A B,
    vfMidFloorLiPrimitiveMismatch n = -1 ∨
      vfMidFloorLiPrimitiveMismatch n = 0 ∨
        vfMidFloorLiPrimitiveMismatch n = 1

def vfMidFloorLiPositiveMismatchPopulation (A B : ℕ) : ℤ :=
  ∑ n ∈ Finset.Ico A B,
    if vfMidFloorLiPrimitiveMismatch n = 1 then 1 else 0

def vfMidFloorLiNegativeMismatchPopulation (A B : ℕ) : ℤ :=
  ∑ n ∈ Finset.Ico A B,
    if vfMidFloorLiPrimitiveMismatch n = -1 then 1 else 0

def vfMidFloorLiSignedPopulationBalance (A B : ℕ) : ℤ :=
  vfMidFloorLiPositiveMismatchPopulation A B -
    vfMidFloorLiNegativeMismatchPopulation A B

/-! ## Ternary support is automatic above 4 -/

theorem vfMidFloorLiOneStepMass_nonneg_lt_one
    {n : ℕ} (hn : 4 ≤ n) :
    0 ≤ vfMidLogarithmicIntegralFromTwo ((n + 1 : ℕ) : ℝ) -
          vfMidLogarithmicIntegralFromTwo (n : ℝ) ∧
      vfMidLogarithmicIntegralFromTwo ((n + 1 : ℕ) : ℝ) -
          vfMidLogarithmicIntegralFromTwo (n : ℝ) < 1 := by
  have hnon0 :=
    densityTightLiWeight_nonneg (q := n + 1) (by omega : 3 ≤ n + 1)
  have hnon :
      0 ≤ vfMidLogarithmicIntegralFromTwo ((n + 1 : ℕ) : ℝ) -
        vfMidLogarithmicIntegralFromTwo (n : ℝ) := by
    simpa [densityTightLiWeight, vfMidLogarithmicIntegralFromTwo,
      logarithmicIntegralFromTwo] using hnon0
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 2 ≤ n by omega)
  have hstep0 :=
    abs_logarithmicIntegralFromTwo_sub_le
      (a := (n : ℝ)) (b := ((n + 1 : ℕ) : ℝ))
      hn2 (by exact_mod_cast (show n ≤ n + 1 by omega))
  have hstep :
      |vfMidLogarithmicIntegralFromTwo ((n + 1 : ℕ) : ℝ) -
        vfMidLogarithmicIntegralFromTwo (n : ℝ)| ≤
          1 / Real.log (n : ℝ) := by
    have hone :
        (((n + 1 : ℕ) : ℝ) - (n : ℝ)) = 1 := by
      push_cast
      ring
    simpa [vfMidLogarithmicIntegralFromTwo,
      logarithmicIntegralFromTwo, hone] using hstep0
  have hlog4eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have h2 := Real.log_two_gt_d9
    rw [hlog4eq]
    nlinarith
  have h4n : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (1 : ℝ) < Real.log (n : ℝ) := by
    have hmono :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4n
    exact hlog4.trans_le hmono
  have hinv : 1 / Real.log (n : ℝ) < 1 := by
    have hlogpos : 0 < Real.log (n : ℝ) := by linarith
    exact (div_lt_one hlogpos).2 hlogn
  constructor
  · exact hnon
  · exact lt_of_le_of_lt (le_abs_self _) (hstep.trans_lt hinv)

theorem vfMidFloorLiIntegerPotential_step_zero_or_one
    {n : ℕ} (hn : 4 ≤ n) :
    vfMidFloorLiIntegerPotential (n + 1) -
        vfMidFloorLiIntegerPotential n = 0 ∨
      vfMidFloorLiIntegerPotential (n + 1) -
        vfMidFloorLiIntegerPotential n = 1 := by
  let a : ℝ := vfMidLogarithmicIntegralFromTwo (n : ℝ)
  let b : ℝ := vfMidLogarithmicIntegralFromTwo ((n + 1 : ℕ) : ℝ)
  have hmass := vfMidFloorLiOneStepMass_nonneg_lt_one hn
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [hmass.1]
  have hba : b < a + 1 := by
    dsimp [a, b]
    linarith [hmass.2]
  have hfloor : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_mono hab
  have hafloor : a < ((⌊a⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one a
  have hbupper : b < ((⌊a⌋ : ℤ) : ℝ) + 2 := by
    linarith
  have hnot : ¬ (⌊a⌋ + 2 ≤ ⌊b⌋) := by
    intro hbad
    have hcast :
        (((⌊a⌋ + 2 : ℤ) : ℝ)) ≤ ((⌊b⌋ : ℤ) : ℝ) := by
      exact_mod_cast hbad
    have hble : ((⌊b⌋ : ℤ) : ℝ) ≤ b := Int.floor_le b
    push_cast at hcast
    linarith
  have hupper : ⌊b⌋ ≤ ⌊a⌋ + 1 := by omega
  change ⌊b⌋ - ⌊a⌋ = 0 ∨ ⌊b⌋ - ⌊a⌋ = 1
  omega

theorem vfMidPrimeCountingInteger_step_zero_or_one
    (n : ℕ) :
    (Nat.primeCounting (n + 1) : ℤ) -
        (Nat.primeCounting n : ℤ) = 0 ∨
      (Nat.primeCounting (n + 1) : ℤ) -
        (Nat.primeCounting n : ℤ) = 1 := by
  have hlo :
      Nat.primeCounting n ≤ Nat.primeCounting (n + 1) :=
    Nat.monotone_primeCounting (by omega)
  have hup0 := vfMid_primeCounting_add_le n 1
  have hup :
      Nat.primeCounting (n + 1) ≤ Nat.primeCounting n + 1 := by
    simpa using hup0
  omega

theorem vfMidFloorLiPrimitiveMismatch_ternary
    {n : ℕ} (hn : 4 ≤ n) :
    vfMidFloorLiPrimitiveMismatch n = -1 ∨
      vfMidFloorLiPrimitiveMismatch n = 0 ∨
        vfMidFloorLiPrimitiveMismatch n = 1 := by
  have hp := vfMidPrimeCountingInteger_step_zero_or_one n
  have hf := vfMidFloorLiIntegerPotential_step_zero_or_one hn
  unfold vfMidFloorLiPrimitiveMismatch
    vfMidPrimeFloorLiIntegerBacklog
  rcases hp with hp | hp <;> rcases hf with hf | hf <;> omega

theorem vfMidFloorLiPrimitiveTernaryOn_of_four_le
    {A B : ℕ} (hA : 4 ≤ A) :
    VFMidFloorLiPrimitiveTernaryOn A B := by
  intro n hn
  have hnA := (Finset.mem_Ico.mp hn).1
  exact vfMidFloorLiPrimitiveMismatch_ternary (hA.trans hnA)

theorem vfMidFloorLiSignedPopulationBalance_eq_mismatchMass
    {A B : ℕ}
    (htern : VFMidFloorLiPrimitiveTernaryOn A B) :
    vfMidFloorLiSignedPopulationBalance A B =
      vfMidFloorLiSignedMismatchMass A B := by
  unfold vfMidFloorLiSignedPopulationBalance
    vfMidFloorLiPositiveMismatchPopulation
    vfMidFloorLiNegativeMismatchPopulation
    vfMidFloorLiSignedMismatchMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rcases htern n hn with hm | hz | hp
  · simp [hm]
  · simp [hz]
  · simp [hp]

theorem vfMidFloorLiSignedPopulationBalance_eq_backlog_increment
    {A B : ℕ} (hAB : A ≤ B)
    (htern : VFMidFloorLiPrimitiveTernaryOn A B) :
    vfMidFloorLiSignedPopulationBalance A B =
      vfMidPrimeFloorLiIntegerBacklog B -
        vfMidPrimeFloorLiIntegerBacklog A := by
  rw [vfMidFloorLiSignedPopulationBalance_eq_mismatchMass htern,
    vfMidFloorLiSignedMismatchMass_eq_backlog_increment hAB]

/-! ## Exact transfer to the classical prime-minus-Li discrepancy -/

def vfMidFloorLiEndpointRounding (n : ℕ) : ℝ :=
  vfMidLogarithmicIntegralFromTwo (n : ℝ) -
    liFloorPrimeCountProxy (n : ℝ)

theorem vfMidFloorLiEndpointRounding_nonneg_lt_one (n : ℕ) :
    0 ≤ vfMidFloorLiEndpointRounding n ∧
      vfMidFloorLiEndpointRounding n < 1 := by
  unfold vfMidFloorLiEndpointRounding
  constructor
  · exact sub_nonneg.mpr (liFloorPrimeCountProxy_le_li (n : ℝ))
  · have h := li_lt_liFloorPrimeCountProxy_add_one (n : ℝ)
    linarith

theorem abs_vfMidFloorLiEndpointRounding_sub_lt_one
    (A B : ℕ) :
    |vfMidFloorLiEndpointRounding B -
        vfMidFloorLiEndpointRounding A| < 1 := by
  rcases vfMidFloorLiEndpointRounding_nonneg_lt_one A with ⟨hA0, hA1⟩
  rcases vfMidFloorLiEndpointRounding_nonneg_lt_one B with ⟨hB0, hB1⟩
  rw [abs_lt]
  constructor <;> linarith

def vfMidPrimeLiIntegerDiscrepancyReal (n : ℕ) : ℝ :=
  (primeSievePrimeDiscrepancy n).re

theorem vfMidPrimeLiIntegerDiscrepancyReal_eq (n : ℕ) :
    vfMidPrimeLiIntegerDiscrepancyReal n =
      (Nat.primeCounting n : ℝ) -
        vfMidLogarithmicIntegralFromTwo (n : ℝ) := by
  unfold vfMidPrimeLiIntegerDiscrepancyReal primeSievePrimeDiscrepancy
  rw [primeSievePrefixPrimeCount_eq_primeCounting]
  simp [vfMidLogarithmicIntegralFromTwo, logarithmicIntegralFromTwo]

/-- The classical prime discrepancy is a genuinely real-valued complex
coordinate, so its real presentation can be cast back without loss. -/
theorem primeSievePrimeDiscrepancy_eq_vfMidPrimeLiIntegerDiscrepancyReal
    (n : ℕ) :
    primeSievePrimeDiscrepancy n =
      (vfMidPrimeLiIntegerDiscrepancyReal n : ℂ) := by
  unfold vfMidPrimeLiIntegerDiscrepancyReal primeSievePrimeDiscrepancy
  rw [primeSievePrefixPrimeCount_eq_primeCounting]
  simp

theorem vfMidPrimeFloorLiIntegerBacklog_cast_eq_primeLi_add_rounding
    (n : ℕ) :
    ((vfMidPrimeFloorLiIntegerBacklog n : ℤ) : ℝ) =
      vfMidPrimeLiIntegerDiscrepancyReal n +
        vfMidFloorLiEndpointRounding n := by
  rw [vfMidPrimeLiIntegerDiscrepancyReal_eq]
  unfold vfMidPrimeFloorLiIntegerBacklog
    vfMidFloorLiIntegerPotential
    vfMidFloorLiEndpointRounding
    liFloorPrimeCountProxy
  push_cast
  ring

theorem abs_vfMidPrimeFloorLiIntegerBacklog_sub_primeLi_lt_one
    (n : ℕ) :
    |((vfMidPrimeFloorLiIntegerBacklog n : ℤ) : ℝ) -
        vfMidPrimeLiIntegerDiscrepancyReal n| < 1 := by
  rw [vfMidPrimeFloorLiIntegerBacklog_cast_eq_primeLi_add_rounding]
  have h := vfMidFloorLiEndpointRounding_nonneg_lt_one n
  rw [add_sub_cancel_left, abs_of_nonneg h.1]
  exact h.2

/-! ## Exact Mobius/Abel carrier for the discrete signed population -/

def vfMidFloorLiMoebiusAbelCarrier (A B : ℕ) : ℂ :=
  primeFlipPNTError A B +
    primeSieveMoebiusDiscrepancySum A B -
      primeSieveAbelBoundary A B

theorem vfMidFloorLiMoebiusAbelCarrier_eq_primeLi_increment
    {A B : ℕ} (hAB : A ≤ B) :
    vfMidFloorLiMoebiusAbelCarrier A B =
      primeSievePrimeDiscrepancy B -
        primeSievePrimeDiscrepancy A := by
  unfold vfMidFloorLiMoebiusAbelCarrier
  rw [primeFlipPNTError_eq_endpoint_sub_moebiusDiscrepancy_add_boundary hAB]
  ring

theorem vfMidFloorLiSignedMismatchMass_cast_eq_moebiusAbel_add_rounding
    {A B : ℕ} (hAB : A ≤ B) :
    ((vfMidFloorLiSignedMismatchMass A B : ℤ) : ℂ) =
      vfMidFloorLiMoebiusAbelCarrier A B +
        ((vfMidFloorLiEndpointRounding B -
          vfMidFloorLiEndpointRounding A : ℝ) : ℂ) := by
  rw [vfMidFloorLiSignedMismatchMass_eq_backlog_increment hAB]
  have hB :=
    vfMidPrimeFloorLiIntegerBacklog_cast_eq_primeLi_add_rounding B
  have hA :=
    vfMidPrimeFloorLiIntegerBacklog_cast_eq_primeLi_add_rounding A
  have hcarrier :=
    vfMidFloorLiMoebiusAbelCarrier_eq_primeLi_increment hAB
  have hBcomplex0 := congrArg (fun x : ℝ => (x : ℂ)) hB
  have hAcomplex0 := congrArg (fun x : ℝ => (x : ℂ)) hA
  have hBcomplex :
      (((vfMidPrimeFloorLiIntegerBacklog B : ℤ) : ℂ)) =
        (vfMidPrimeLiIntegerDiscrepancyReal B : ℂ) +
          (vfMidFloorLiEndpointRounding B : ℂ) := by
    simpa using hBcomplex0
  have hAcomplex :
      (((vfMidPrimeFloorLiIntegerBacklog A : ℤ) : ℂ)) =
        (vfMidPrimeLiIntegerDiscrepancyReal A : ℂ) +
          (vfMidFloorLiEndpointRounding A : ℂ) := by
    simpa using hAcomplex0
  rw [← primeSievePrimeDiscrepancy_eq_vfMidPrimeLiIntegerDiscrepancyReal B]
    at hBcomplex
  rw [← primeSievePrimeDiscrepancy_eq_vfMidPrimeLiIntegerDiscrepancyReal A]
    at hAcomplex
  push_cast at hBcomplex hAcomplex ⊢
  rw [hcarrier]
  linear_combination hBcomplex - hAcomplex

theorem norm_vfMidFloorLiSignedMismatchMass_sub_moebiusAbel_lt_one
    {A B : ℕ} (hAB : A ≤ B) :
    ‖((vfMidFloorLiSignedMismatchMass A B : ℤ) : ℂ) -
        vfMidFloorLiMoebiusAbelCarrier A B‖ < 1 := by
  rw [vfMidFloorLiSignedMismatchMass_cast_eq_moebiusAbel_add_rounding hAB]
  have hround :=
    abs_vfMidFloorLiEndpointRounding_sub_lt_one A B
  have heq :
      vfMidFloorLiMoebiusAbelCarrier A B +
          ((vfMidFloorLiEndpointRounding B -
            vfMidFloorLiEndpointRounding A : ℝ) : ℂ) -
          vfMidFloorLiMoebiusAbelCarrier A B =
        ((vfMidFloorLiEndpointRounding B -
          vfMidFloorLiEndpointRounding A : ℝ) : ℂ) := by
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact hround

theorem norm_vfMidFloorLiSignedPopulationBalance_sub_moebiusAbel_lt_one
    {A B : ℕ} (hAB : A ≤ B)
    (htern : VFMidFloorLiPrimitiveTernaryOn A B) :
    ‖((vfMidFloorLiSignedPopulationBalance A B : ℤ) : ℂ) -
        vfMidFloorLiMoebiusAbelCarrier A B‖ < 1 := by
  rw [vfMidFloorLiSignedPopulationBalance_eq_mismatchMass htern]
  exact norm_vfMidFloorLiSignedMismatchMass_sub_moebiusAbel_lt_one hAB

theorem norm_vfMidFloorLiDyadicPrimeDefect_add_moebiusAbel_lt_one
    {A B : ℕ} (hAB : A ≤ B) :
    ‖((vfMidFloorLiDyadicPrimeDefect A B : ℤ) : ℂ) +
        vfMidFloorLiMoebiusAbelCarrier (A ^ 2) (B ^ 2)‖ < 1 := by
  have hsq : A ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hAB 2
  have hmain :=
    norm_vfMidFloorLiSignedMismatchMass_sub_moebiusAbel_lt_one hsq
  rw [vfMidFloorLiSignedMismatchMass_sq_eq_neg_dyadicPrimeDefect hAB] at hmain
  push_cast at hmain
  have hsign :
      -(((vfMidFloorLiDyadicPrimeDefect A B : ℤ) : ℂ)) -
          vfMidFloorLiMoebiusAbelCarrier (A ^ 2) (B ^ 2) =
        -((((vfMidFloorLiDyadicPrimeDefect A B : ℤ) : ℂ) +
          vfMidFloorLiMoebiusAbelCarrier (A ^ 2) (B ^ 2))) := by
    ring
  rw [hsign, norm_neg] at hmain
  exact hmain

end RHLean.Analysis
