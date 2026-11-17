import Mathlib
import «research.SURVIVOR_PRIME_COMPOSITE_ACCOUNTING_20261117»
import RHLean.Analysis.NativePNTTransfer
import RHLean.Analysis.SquareBlockSurvivorBridge
import RHLean.Analysis.MertensEnergyRHForward

/-!
# The complete survivor scale and its necessarily large prime component

The translated local survivor criterion contains the one-point window `H=1`.
Conversely, its every-positive-loss pointwise squared bound controls every
translated window `1 <= H <= N`, with the explicit factor `2^(2+epsilon)`.

The exact prime-count accounting identifies what the composite fibre must
cancel. The already-proved native prime number theorem, with no external
analytic hypothesis, shows that the prime fibre by itself cannot even satisfy
a uniform cubic squared bound. This is an obstruction to estimating the two
fibres separately, not an obstruction to their complete signed sum.

The final conditional consumer targets Mathlib's `RiemannHypothesis` directly;
it uses the existing native Mertens-energy implication and introduces no
`ClassicalMertensRHCriterion` parameter. The complete survivor estimate remains
an explicit open premise.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology

namespace RHLean.Proof

open RHLean.Analysis

/-- The pointwise squared form of the complete signed survivor target. -/
def SurvivorPointwiseSquaredBoundStatement (Λ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℕ, 1 ≤ t →
        ‖survivorZeroMode Λ t‖ ^ 2 ≤
          C * Real.rpow (t : ℝ) (2 + ε)

/-- The one-point translated window is part of the survivor criterion. -/
theorem survivorPointwiseSquared_of_powerSaving
    {Λ : ℝ} (hlocal : SurvivorZeroModePowerSavingStatement Λ) :
    SurvivorPointwiseSquaredBoundStatement Λ := by
  intro ε hε
  rcases hlocal ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht
  have h := hbound t 1 (by simp) ht
  simpa [localSequenceEnergy] using! h

/-- Pointwise control gives all allowed translated windows, with a fixed
factor `2^(2+epsilon)` because every sampled index is at most `2*N`. -/
theorem survivorPowerSaving_of_pointwiseSquared
    {Λ : ℝ} (hpoint : SurvivorPointwiseSquaredBoundStatement Λ) :
    SurvivorZeroModePowerSavingStatement Λ := by
  intro ε hε
  rcases hpoint ε hε with ⟨C, hC, hbound⟩
  let K := Real.rpow 2 (2 + ε)
  refine ⟨C * K, mul_nonneg hC (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro N H hH hHN
  have hN : 1 ≤ N := hH.trans hHN
  unfold localSequenceEnergy
  calc
    (∑ h ∈ Finset.range H, ‖survivorZeroMode Λ (N + h)‖ ^ 2) ≤
        ∑ _h ∈ Finset.range H,
          (C * K) * Real.rpow (N : ℝ) (2 + ε) := by
      apply Finset.sum_le_sum
      intro h hh
      have hhlt : h < H := Finset.mem_range.mp hh
      have hindex : 1 ≤ N + h := le_add_right hN
      have hboundIndex := hbound (N + h) hindex
      have hindexNat : N + h ≤ 2 * N := by omega
      have hindexR : ((N + h : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        exact_mod_cast hindexNat
      have hexp : 0 ≤ 2 + ε := by linarith
      have hp := Real.rpow_le_rpow (by positivity) hindexR hexp
      have hmul :
          Real.rpow (2 * (N : ℝ)) (2 + ε) =
            Real.rpow 2 (2 + ε) * Real.rpow (N : ℝ) (2 + ε) :=
        Real.mul_rpow (by norm_num) (by positivity)
      calc
        ‖survivorZeroMode Λ (N + h)‖ ^ 2 ≤
            C * Real.rpow ((N + h : ℕ) : ℝ) (2 + ε) := hboundIndex
        _ ≤ C * Real.rpow (2 * (N : ℝ)) (2 + ε) :=
          mul_le_mul_of_nonneg_left hp hC
        _ = (C * K) * Real.rpow (N : ℝ) (2 + ε) := by
          rw [hmul]
          simp only [K, mul_assoc]
    _ = (H : ℝ) * ((C * K) * Real.rpow (N : ℝ) (2 + ε)) := by simp
    _ = (C * K) * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε) := by ring

/-- Exact equivalence, including `H=1`; an almost-every-stage conclusion is
not the statement of either side. -/
theorem survivorPowerSaving_iff_pointwiseSquared (Λ : ℝ) :
    SurvivorZeroModePowerSavingStatement Λ ↔
      SurvivorPointwiseSquaredBoundStatement Λ :=
  ⟨survivorPointwiseSquared_of_powerSaving,
    survivorPowerSaving_of_pointwiseSquared⟩

/-- The composite fibre minus the exact prime-count main contribution is
literally the complete signed survivor. -/
theorem survivorComposite_primeCount_residual_eq_survivor
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {t : ℕ} (ht : 1 ≤ t)
    (hkX : survivorPrimeCutoff Λ t ≤ squarePrefixEndpoint t) :
    survivorCompositeZeroMode Λ t -
        ((primeCountUpTo (squarePrefixEndpoint t) -
          primeCountUpTo (survivorPrimeCutoff Λ t) : ℕ) : ℂ) =
      survivorZeroMode Λ t := by
  rw [survivorCompositeZeroMode_eq_survivor_add_primeCount_sub hΛ ht hkX]
  ring

/-- The open complete-source criterion requires the composite fibre to cancel
the exact prime count at the same pointwise squared scale. -/
theorem survivorComposite_residual_sq_le_of_powerSaving
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hsurvivor : SurvivorZeroModePowerSavingStatement Λ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ t : ℕ, 1 ≤ t → 2 * Λ ≤ (t : ℝ) →
          ‖survivorCompositeZeroMode Λ t -
            ((primeCountUpTo (squarePrefixEndpoint t) -
              primeCountUpTo (survivorPrimeCutoff Λ t) : ℕ) : ℂ)‖ ^ 2 ≤
            C * Real.rpow (t : ℝ) (2 + ε) := by
  intro ε hε
  rcases survivorPointwiseSquared_of_powerSaving hsurvivor ε hε with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht hstage
  have hk : survivorPrimeCutoff Λ t ≤ t :=
    survivorPrimeCutoff_le_stage hΛ ht hstage
  have htX : t ≤ squarePrefixEndpoint t := by
    have hendpoint := squarePrefixEndpoint_add_one t
    nlinarith
  rw [survivorComposite_primeCount_residual_eq_survivor hΛ ht (hk.trans htX)]
  exact hbound t ht

private theorem survivor_primeCountUpTo_eq_primeCounting (n : ℕ) :
    primeCountUpTo n = Nat.primeCounting n := by
  classical
  change ((Finset.Icc 2 n).filter Nat.Prime).card = Nat.primeCounting n
  rw [← Nat.primesLE_eq_filter_Icc_two, Nat.primesLE_card_eq_primeCounting]

private theorem survivor_primeCountUpTo_le (n : ℕ) :
    primeCountUpTo n ≤ n := by
  classical
  calc
    primeCountUpTo n ≤ (Finset.Icc 2 n).card := Finset.card_filter_le _ _
    _ ≤ n := by rw [Nat.card_Icc]; omega

/-- A weak polynomial consequence of the already-proved native PNT. The
fourth-root stage below makes the final obstruction use only integer powers. -/
theorem survivor_primeCounting_eighth_eventually_ge_seventh :
    ∀ᶠ n : ℕ in atTop, n ^ 7 ≤ Nat.primeCounting (n ^ 8) := by
  have hpnt : ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) <
        (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ) :=
    (tendsto_order.1 nativePrimeNumberTheorem).1 (1 / 2) (by norm_num)
  rcases eventually_atTop.1 hpnt with ⟨N0, hN0⟩
  have hloglim : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have h :=
      (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_one] using
      h.comp tendsto_natCast_atTop_atTop
  have hlogsmall : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) / (n : ℝ) < (1 / 16 : ℝ) :=
    (tendsto_order.1 hloglim).2 (1 / 16) (by norm_num)
  filter_upwards [eventually_ge_atTop N0, eventually_ge_atTop 1, hlogsmall]
    with n hn0 hn1 hlog
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hn7pos : 0 < n ^ 7 := pow_pos (by omega : 0 < n) 7
  have hn8 : n ≤ n ^ 8 := by
    calc
      n = n * 1 := by omega
      _ ≤ n * n ^ 7 := Nat.mul_le_mul_left n (by omega)
      _ = n ^ 8 := by ring
  have hpntn := hN0 (n ^ 8) (hn0.trans hn8)
  have hlogn : Real.log (n : ℝ) < (1 / 16 : ℝ) * (n : ℝ) :=
    (div_lt_iff₀ hnpos).1 hlog
  have hlog8 : Real.log (((n ^ 8 : ℕ) : ℝ)) ≤ (n : ℝ) / 2 := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    linarith
  have hpntMul : (1 / 2 : ℝ) * (n : ℝ) ^ 8 <
      (Nat.primeCounting (n ^ 8) : ℝ) * Real.log (((n ^ 8 : ℕ) : ℝ)) := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < ((n ^ 8 : ℕ) : ℝ))).1 hpntn
    simpa only [Nat.cast_pow] using h
  have hmul := mul_le_mul_of_nonneg_left hlog8
    (Nat.cast_nonneg (Nat.primeCounting (n ^ 8)) :
      (0 : ℝ) ≤ (Nat.primeCounting (n ^ 8) : ℝ))
  have hpow : (n : ℝ) ^ 8 < (Nat.primeCounting (n ^ 8) : ℝ) * (n : ℝ) := by
    linarith
  have hseven : (n : ℝ) ^ 7 < (Nat.primeCounting (n ^ 8) : ℝ) := by
    have hscaled : (n : ℝ) ^ 7 * (n : ℝ) <
        (Nat.primeCounting (n ^ 8) : ℝ) * (n : ℝ) := by
      calc
        (n : ℝ) ^ 7 * (n : ℝ) = (n : ℝ) ^ 8 := by ring
        _ < (Nat.primeCounting (n ^ 8) : ℝ) * (n : ℝ) := hpow
    exact lt_of_mul_lt_mul_right hscaled hnpos.le
  exact_mod_cast hseven.le

/-- Along fourth-power stages the pure-prime component has a polynomial lower
bound. This theorem uses native PNT, not prime-phase equidistribution. -/
theorem survivorPrimeZeroMode_fourth_stage_lower
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 7 - (n : ℝ) ^ 4 ≤ ‖survivorPrimeZeroMode Λ (n ^ 4)‖ := by
  have hstage : ∀ᶠ n : ℕ in atTop, 2 * Λ ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * Λ)
  filter_upwards [survivor_primeCounting_eighth_eventually_ge_seventh,
    eventually_ge_atTop 1, hstage] with n hpi hn1 hstageN
  have hnpos : 0 < n := by omega
  have hn3pos : 0 < n ^ 3 := pow_pos hnpos 3
  have hn4 : n ≤ n ^ 4 := by
    calc
      n = n * 1 := by omega
      _ ≤ n * n ^ 3 := Nat.mul_le_mul_left n (by omega)
      _ = n ^ 4 := by ring
  have ht : 1 ≤ n ^ 4 := hn1.trans hn4
  have hstageT : 2 * Λ ≤ ((n ^ 4 : ℕ) : ℝ) := by
    exact hstageN.trans (by exact_mod_cast hn4)
  have hk : survivorPrimeCutoff Λ (n ^ 4) ≤ n ^ 4 :=
    survivorPrimeCutoff_le_stage hΛ ht hstageT
  have hX : n ^ 8 ≤ squarePrefixEndpoint (n ^ 4) := by
    have hendpoint := squarePrefixEndpoint_add_one (n ^ 4)
    have hpow : (n ^ 4) ^ 2 = n ^ 8 := by ring
    nlinarith
  have htX : n ^ 4 ≤ squarePrefixEndpoint (n ^ 4) := by
    have hendpoint := squarePrefixEndpoint_add_one (n ^ 4)
    nlinarith
  have hnorm : ‖survivorPrimeZeroMode Λ (n ^ 4)‖ =
      ((primeCountUpTo (squarePrefixEndpoint (n ^ 4)) -
        primeCountUpTo (survivorPrimeCutoff Λ (n ^ 4)) : ℕ) : ℝ) := by
    rw [survivorPrimeZeroMode_eq_neg_primeCount_sub hΛ ht (hk.trans htX),
      norm_neg, Complex.norm_natCast]
  have hpiX : n ^ 7 ≤ primeCountUpTo (squarePrefixEndpoint (n ^ 4)) := by
    rw [survivor_primeCountUpTo_eq_primeCounting]
    exact hpi.trans (Nat.monotone_primeCounting hX)
  have hpiK : primeCountUpTo (survivorPrimeCutoff Λ (n ^ 4)) ≤ n ^ 4 :=
    (survivor_primeCountUpTo_le _).trans hk
  have hsum : n ^ 7 ≤
      (primeCountUpTo (squarePrefixEndpoint (n ^ 4)) -
        primeCountUpTo (survivorPrimeCutoff Λ (n ^ 4))) + n ^ 4 := by omega
  have hsumR : (n : ℝ) ^ 7 ≤
      ((primeCountUpTo (squarePrefixEndpoint (n ^ 4)) -
        primeCountUpTo (survivorPrimeCutoff Λ (n ^ 4)) : ℕ) : ℝ) +
        (n : ℝ) ^ 4 := by exact_mod_cast hsum
  rw [hnorm]
  linarith

/-- The actual prime fibre cannot satisfy even the fixed cubic squared bound.
The complete signed survivor can only be small through its composite return. -/
theorem survivorPrimeZeroMode_not_cubic_squared_bound
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℕ, 1 ≤ t →
        ‖survivorPrimeZeroMode Λ t‖ ^ 2 ≤ C * (t : ℝ) ^ 3 := by
  rintro ⟨C, _hC, hbound⟩
  rcases eventually_atTop.1 (survivorPrimeZeroMode_fourth_stage_lower hΛ) with
    ⟨N0, hN0⟩
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max (N0 : ℝ) (max 2 (4 * C + 2)))
  have hn0R : (N0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : N0 ≤ n := by exact_mod_cast hn0R.le
  have hn2 : (2 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
  have hnC : 4 * C + 2 < (n : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have ht : 1 ≤ n ^ 4 := by
    have htpos : 0 < n ^ 4 := pow_pos (by omega : 0 < n) 4
    omega
  have hlower := hN0 n hn0
  have hn3 : (2 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have hpow : (2 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by gcongr
    norm_num at hpow
    linarith
  have hfour : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  have hseven : 2 * (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 7 := by
    have h := mul_le_mul_of_nonneg_right hn3 hfour
    nlinarith only [h]
  have hhalf : (n : ℝ) ^ 7 / 2 ≤ ‖survivorPrimeZeroMode Λ (n ^ 4)‖ := by
    linarith
  have hsquare : ((n : ℝ) ^ 7 / 2) ^ 2 ≤
      ‖survivorPrimeZeroMode Λ (n ^ 4)‖ ^ 2 := by
    have hhalf0 : (0 : ℝ) ≤ (n : ℝ) ^ 7 / 2 := by positivity
    exact pow_le_pow_left₀ hhalf0 hhalf 2
  have hupper := hbound (n ^ 4) ht
  have hpoly : (n : ℝ) ^ 14 ≤ 4 * C * (n : ℝ) ^ 12 := by
    simp only [Nat.cast_pow] at hupper
    nlinarith [hsquare]
  have hcancel : (n : ℝ) ^ 2 ≤ 4 * C := by
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 12)).mp
    nlinarith only [hpoly]
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- In particular, the pure-prime fibre does not satisfy the survivor's
every-positive-loss translated local energy scale. -/
theorem survivorPrimeZeroMode_not_uniformLocalRHScale
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ¬ (∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ N H : ℕ, 1 ≤ H → H ≤ N →
          localSequenceEnergy (survivorPrimeZeroMode Λ) N H ≤
            C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) := by
  intro hlocal
  rcases hlocal 1 (by norm_num) with ⟨C, hC, hbound⟩
  apply survivorPrimeZeroMode_not_cubic_squared_bound hΛ
  refine ⟨C, hC, ?_⟩
  intro t ht
  have h := hbound t 1 (by simp) ht
  rw [show (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num] at h
  simpa [localSequenceEnergy, Real.rpow_natCast] using h

/-- The complete survivor premise reaches Mathlib RH through the existing
native Mertens-energy consumer, with no extra classical-criterion interface. -/
theorem survivorPowerSaving_implies_mathlibRH
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hsurvivor : SurvivorZeroModePowerSavingStatement Λ) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  apply squarePrefix_uniformLocalBounded_iff_mertensEnergyBounded.1
  exact squareBlockSurvivorPowerSaving_implies_squarePrefixUniformLocal hΛ hsurvivor

end RHLean.Proof
