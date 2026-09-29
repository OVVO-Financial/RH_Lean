import Mathlib
import RHLean.Analysis.SquareRootMatchedTransport
import RHLean.Analysis.SquareRootTransportRealization
import RHLean.Analysis.PrimeSieveLipschitzExcursion
import RHLean.Analysis.CanonicalLowOccupancy

/-!
# Discretization of the hybrid Li model

At square-root cutoff `R`, write `X = R^2 - 1` and `L = logarithmicIntegralFromTwo`.
The hybrid Li model keeps the complete actual `R`-smooth sector and gives the
post-root primes Li frequencies with the forced negative fresh-prime
orientation:

    F_R      = S_R - sum_{c<R} mu(c) [L(floor(X/c)) - L(R)],
    F_R^cont = S_R - sum_{c<R} mu(c) [L(X/c)        - L(R)],

where `S_R = squareRootSmoothMass (R-1)`.  The two transport sums are the
existing `squareRootTransportDiscretePNTMain` and
`squareRootTransportSmoothMain`.

This file proves the following exact statements.

* `liHybridModel_sub_continuous`: `F_R - F_R^cont = -Q_R`, where `Q_R` is the
  existing floor correction.
* `norm_liHybridModel_sub_continuous_le`: `|F_R - F_R^cont| <= (R-1)/log R`.
* `squareRootTransportDiscretePNTMain_eq_oddPaired`: the exact owner-two pairing
  of the Li tail onto odd cofactors.
* `norm_liHybridGridModel_sub_liHybridModel_le`: replacing each paired Li
  interval mass by the integer rank-grid count `floor(L(t) - L(R))` moves the
  model by at most the number of odd cofactors, hence by at most `R/2`.
* `liHybridModel_eq_mertens_add_primeCountDiscrepancy`:
  `F_R = M(X) + sum_{c<R} mu(c) Delta(floor(X/c)) - M(R-1) Delta(R)`, where
  `Delta(y) = pi(y) - L(y)`.

These control only the *internal* discretization of the Li model.  They do not
bound `F_R`, and they do not bound the displacement of actual primes from Li
frequencies.  By the last identity, a root-scale bound for `F_R` carries the
same Möbius-weighted prime-count discrepancy as the existing
`squareRootTransportPNTError`; no quantitative estimate is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-! ## The three model coordinates -/

/-- Hybrid Li model at integer reciprocal cutoffs: actual smooth sector minus
the Li-frequency post-root tail. -/
def liHybridModel (R : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) - squareRootTransportDiscretePNTMain R

/-- Hybrid Li model with the reciprocal cutoffs `X/c` left unfloored. -/
def liHybridContinuousModel (R : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) - squareRootTransportSmoothMain R

/-- Exact floor-removal identity: the two hybrid models differ by minus the
existing aggregate floor correction. -/
theorem liHybridModel_sub_continuous (R : ℕ) :
    liHybridModel R - liHybridContinuousModel R =
      -squareRootTransportFloorCorrection R := by
  unfold liHybridModel liHybridContinuousModel
  rw [squareRootTransportDiscretePNTMain_eq_smooth_add_floor]
  ring

/-! ## Floor rounding costs at most `(R-1)/log R` -/

/-- Every positive cofactor below the root sends the endpoint above the root:
`R <= floor((R^2-1)/c)`. -/
theorem le_squareRootEndpoint_div {R c : ℕ} (hc1 : 1 ≤ c) (hcR : c < R) :
    R ≤ squareRootEndpoint R / c := by
  have hcpos : 0 < c := by omega
  apply (Nat.le_div_iff_mul_le hcpos).2
  unfold squareRootEndpoint
  have hc : c ≤ R - 1 := by omega
  calc R * c ≤ R * (R - 1) := Nat.mul_le_mul_left R hc
    _ = R ^ 2 - R := by
        rw [Nat.mul_sub, Nat.mul_one, pow_two]
    _ ≤ R ^ 2 - 1 := by omega

/-- One cofactor's floor-rounding weight is at most `1/log R`. -/
theorem norm_squareRootTransportRoundingWeight_le {R c : ℕ}
    (hR : 2 ≤ R) (hc1 : 1 ≤ c) (hcR : c < R) :
    ‖squareRootTransportRoundingWeight R c‖ ≤ 1 / Real.log R := by
  obtain ⟨X, hX⟩ : ∃ X, squareRootEndpoint R = X := ⟨_, rfl⟩
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
  have hRa : R ≤ X / c := hX ▸ le_squareRootEndpoint_div hc1 hcR
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hRa' : (R : ℝ) ≤ ((X / c : ℕ) : ℝ) := by exact_mod_cast hRa
  have ha2 : (2 : ℝ) ≤ ((X / c : ℕ) : ℝ) := hR2.trans hRa'
  have hab : ((X / c : ℕ) : ℝ) ≤ (X : ℝ) / (c : ℝ) := Nat.cast_div_le
  have hlen : (X : ℝ) / (c : ℝ) - ((X / c : ℕ) : ℝ) ≤ 1 := by
    have hlt : X < X / c * c + c := Nat.lt_div_mul_add (by omega)
    have hlt' : (X : ℝ) < ((X / c : ℕ) : ℝ) * c + c := by exact_mod_cast hlt
    have hexp : (1 + ((X / c : ℕ) : ℝ)) * c = ((X / c : ℕ) : ℝ) * c + c := by
      ring
    rw [sub_le_iff_le_add, div_le_iff₀ hcpos, hexp]
    exact hlt'.le
  have hlip := abs_logarithmicIntegralFromTwo_sub_le ha2 hab
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog : Real.log R ≤ Real.log ((X / c : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hRa'
  have hweight :
      squareRootTransportRoundingWeight R c =
        ((logarithmicIntegralFromTwo ((X / c : ℕ) : ℝ) -
            logarithmicIntegralFromTwo ((X : ℝ) / (c : ℝ)) : ℝ) : ℂ) := by
    unfold squareRootTransportRoundingWeight squareRootTransportLiDiscWeight
      squareRootTransportLiSmoothWeight
    rw [hX]
    push_cast
    ring
  rw [hweight, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  calc |logarithmicIntegralFromTwo ((X : ℝ) / (c : ℝ)) -
          logarithmicIntegralFromTwo ((X / c : ℕ) : ℝ)|
      ≤ ((X : ℝ) / (c : ℝ) - ((X / c : ℕ) : ℝ)) /
          Real.log ((X / c : ℕ) : ℝ) := hlip
    _ ≤ 1 / Real.log ((X / c : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right hlen
        exact le_of_lt (lt_of_lt_of_le hlogR hlog)
    _ ≤ 1 / Real.log R := one_div_le_one_div_of_le hlogR hlog

/-- **Floor-rounding bound.**  The aggregate floor correction is at most
`(R-1)/log R`.  Only the model geometry is used. -/
theorem norm_squareRootTransportFloorCorrection_le {R : ℕ} (hR : 2 ≤ R) :
    ‖squareRootTransportFloorCorrection R‖ ≤ ((R : ℝ) - 1) / Real.log R := by
  unfold squareRootTransportFloorCorrection
  calc ‖∑ c ∈ Finset.Ico 1 R,
          canonicalMoebiusWeight c * squareRootTransportRoundingWeight R c‖
      ≤ ∑ c ∈ Finset.Ico 1 R,
          ‖canonicalMoebiusWeight c * squareRootTransportRoundingWeight R c‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _c ∈ Finset.Ico 1 R, 1 / Real.log R := by
        apply Finset.sum_le_sum
        intro c hc
        rcases Finset.mem_Ico.mp hc with ⟨hc1, hcR⟩
        rw [norm_mul]
        calc ‖canonicalMoebiusWeight c‖ *
              ‖squareRootTransportRoundingWeight R c‖
            ≤ 1 * (1 / Real.log R) :=
              mul_le_mul (norm_canonicalMoebiusWeight_le_one c)
                (norm_squareRootTransportRoundingWeight_le hR hc1 hcR)
                (norm_nonneg _) zero_le_one
          _ = 1 / Real.log R := one_mul _
    _ = ((R : ℝ) - 1) / Real.log R := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        rw [Nat.cast_sub (by omega : 1 ≤ R)]
        ring

/-- The floored and continuous hybrid Li models differ by at most
`(R-1)/log R`. -/
theorem norm_liHybridModel_sub_continuous_le {R : ℕ} (hR : 2 ≤ R) :
    ‖liHybridModel R - liHybridContinuousModel R‖ ≤
      ((R : ℝ) - 1) / Real.log R := by
  rw [liHybridModel_sub_continuous, norm_neg]
  exact norm_squareRootTransportFloorCorrection_le hR

/-! ## Exact owner-two pairing of the Li tail -/

/-- Lower endpoint of the surviving interval of an odd cofactor after pairing
with its even mate `2c`.  If `2c` is not a cofactor below `R`, the whole
post-root interval survives. -/
def liPairedLower (R c : ℕ) : ℕ :=
  if 2 * c < R then squareRootEndpoint R / (2 * c) else R

/-- Li mass of the surviving interval of one odd cofactor. -/
def liPairedIntervalMass (R c : ℕ) : ℝ :=
  logarithmicIntegralFromTwo ((squareRootEndpoint R / c : ℕ) : ℝ) -
    logarithmicIntegralFromTwo ((liPairedLower R c : ℕ) : ℝ)

theorem moebius_two_mul_of_odd {d : ℕ} (hd : Odd d) :
    μ (2 * d) = -μ d := by
  have hcop : Nat.Coprime 2 d := (Nat.coprime_two_left).2 hd
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

theorem moebius_two_mul_of_even {d : ℕ} (hd : Even d) :
    μ (2 * d) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  obtain ⟨k, rfl⟩ := hd
  have h4 : 2 * 2 ∣ 2 * (k + k) := ⟨k, by ring⟩
  have hunit := hsq 2 h4
  exact absurd (Nat.isUnit_iff.mp hunit) (by norm_num)

theorem canonicalMoebiusWeight_two_mul_of_odd {d : ℕ} (hd : Odd d) :
    canonicalMoebiusWeight (2 * d) = -canonicalMoebiusWeight d := by
  unfold canonicalMoebiusWeight
  rw [moebius_two_mul_of_odd hd]
  push_cast
  ring

theorem canonicalMoebiusWeight_two_mul_of_even {d : ℕ} (hd : Even d) :
    canonicalMoebiusWeight (2 * d) = 0 := by
  unfold canonicalMoebiusWeight
  rw [moebius_two_mul_of_even hd]
  simp

/-- Even cofactors below `R` are exactly the doubles of cofactors `d` with
`2d < R`. -/
theorem sum_Ico_even_eq_sum_double {R : ℕ} (f : ℕ → ℂ) :
    (∑ c ∈ Finset.Ico 1 R, if Even c then f c else 0) =
      ∑ d ∈ Finset.Ico 1 R, if 2 * d < R then f (2 * d) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun c => c / 2) (fun d => 2 * d)
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_Ico, Nat.even_iff] at hc ⊢
    omega
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Ico, Nat.even_iff] at hd ⊢
    omega
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_Ico, Nat.even_iff] at hc
    omega
  · intro d _hd
    omega
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_Ico, Nat.even_iff] at hc
    congr 1
    omega

/-- **Exact owner-two pairing.**  The Li tail is carried entirely by odd
cofactors, each on its surviving interval `(liPairedLower R c, X/c]`.  Even
squarefree cofactors are cancelled by the fresh-prime sign reversal
`mu(2c) = -mu(c)`; cofactors divisible by four have `mu = 0`. -/
theorem squareRootTransportDiscretePNTMain_eq_oddPaired (R : ℕ) :
    squareRootTransportDiscretePNTMain R =
      ∑ c ∈ Finset.Ico 1 R,
        if Odd c then
          canonicalMoebiusWeight c * (liPairedIntervalMass R c : ℂ)
        else 0 := by
  set w : ℕ → ℂ := fun c => squareRootTransportLiDiscWeight R c with hw
  have hsplit :
      squareRootTransportDiscretePNTMain R =
        (∑ c ∈ Finset.Ico 1 R,
            if Odd c then canonicalMoebiusWeight c * w c else 0) +
          ∑ c ∈ Finset.Ico 1 R,
            if Even c then canonicalMoebiusWeight c * w c else 0 := by
    unfold squareRootTransportDiscretePNTMain
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _hc
    rcases Nat.even_or_odd c with he | ho
    · have hno : ¬ Odd c := Nat.not_odd_iff_even.mpr he
      simp [hno, he, hw]
    · have hne : ¬ Even c := Nat.not_even_iff_odd.mpr ho
      simp [ho, hne, hw]
  have heven :
      (∑ c ∈ Finset.Ico 1 R,
          if Even c then canonicalMoebiusWeight c * w c else 0) =
        ∑ d ∈ Finset.Ico 1 R,
          if Odd d then
            (if 2 * d < R then -(canonicalMoebiusWeight d * w (2 * d)) else 0)
          else 0 := by
    rw [sum_Ico_even_eq_sum_double
      (fun c => canonicalMoebiusWeight c * w c)]
    apply Finset.sum_congr rfl
    intro d _hd
    rcases Nat.even_or_odd d with he | ho
    · have hno : ¬ Odd d := Nat.not_odd_iff_even.mpr he
      simp [hno, canonicalMoebiusWeight_two_mul_of_even he]
    · by_cases h2 : 2 * d < R
      · simp [ho, h2, canonicalMoebiusWeight_two_mul_of_odd ho]
      · simp [ho, h2]
  rw [hsplit, heven, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases ho : Odd c
  · simp only [ho, if_true]
    unfold liPairedIntervalMass liPairedLower
    by_cases h2 : 2 * c < R
    · simp only [h2, if_true, hw]
      unfold squareRootTransportLiDiscWeight
      push_cast
      ring
    · simp only [h2, if_false, hw]
      unfold squareRootTransportLiDiscWeight
      push_cast
      ring
  · simp [ho]

/-! ## Rank-grid quantization costs at most `R/2` after pairing -/

/-- Phase-zero integer Li rank grid: the number of grid labels in `(R, t]`. -/
def liRankGridCount (R t : ℕ) : ℤ :=
  ⌊logarithmicIntegralFromTwo (t : ℝ) - logarithmicIntegralFromTwo (R : ℝ)⌋

/-- Rank-grid count of the surviving interval of one odd cofactor. -/
def liPairedGridMass (R c : ℕ) : ℤ :=
  liRankGridCount R (squareRootEndpoint R / c) -
    liRankGridCount R (liPairedLower R c)

/-- Hybrid model with the paired Li interval masses replaced by rank-grid
counts.  The actual smooth sector is unchanged. -/
def liHybridGridModel (R : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) -
    ∑ c ∈ Finset.Ico 1 R,
      if Odd c then
        canonicalMoebiusWeight c * ((liPairedGridMass R c : ℤ) : ℂ)
      else 0

/-- Grid count minus Li mass on one interval is a difference of fractional
parts. -/
theorem abs_liPairedGridMass_sub_intervalMass_lt (R c : ℕ) :
    |((liPairedGridMass R c : ℤ) : ℝ) - liPairedIntervalMass R c| < 1 := by
  unfold liPairedGridMass liPairedIntervalMass liRankGridCount
  set u := logarithmicIntegralFromTwo ((squareRootEndpoint R / c : ℕ) : ℝ) -
    logarithmicIntegralFromTwo (R : ℝ)
  set v := logarithmicIntegralFromTwo ((liPairedLower R c : ℕ) : ℝ) -
    logarithmicIntegralFromTwo (R : ℝ)
  have hmass :
      logarithmicIntegralFromTwo ((squareRootEndpoint R / c : ℕ) : ℝ) -
          logarithmicIntegralFromTwo ((liPairedLower R c : ℕ) : ℝ) = u - v := by
    simp only [u, v]
    ring
  rw [hmass]
  have hu1 := Int.floor_le u
  have hu2 := Int.lt_floor_add_one u
  have hv1 := Int.floor_le v
  have hv2 := Int.lt_floor_add_one v
  push_cast
  rw [abs_lt]
  constructor <;> linarith

/-- The number of odd cofactors below `R` is at most `R/2`. -/
theorem card_odd_Ico_le (R : ℕ) :
    ((Finset.Ico 1 R).filter Odd).card ≤ R / 2 := by
  calc ((Finset.Ico 1 R).filter Odd).card
      ≤ ((Finset.range (R / 2)).image (fun k => 2 * k + 1)).card := by
        apply Finset.card_le_card
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_Ico, Nat.odd_iff] at hc
        simp only [Finset.mem_image, Finset.mem_range]
        exact ⟨c / 2, by omega, by omega⟩
    _ ≤ (Finset.range (R / 2)).card := Finset.card_image_le
    _ = R / 2 := Finset.card_range _

/-- **Rank-grid quantization bound.**  After exact owner-two pairing, replacing
Li frequencies by the integer rank grid moves the hybrid model by at most the
number of odd cofactors below `R`. -/
theorem norm_liHybridGridModel_sub_liHybridModel_le_card (R : ℕ) :
    ‖liHybridGridModel R - liHybridModel R‖ ≤
      (((Finset.Ico 1 R).filter Odd).card : ℝ) := by
  unfold liHybridGridModel liHybridModel
  rw [squareRootTransportDiscretePNTMain_eq_oddPaired]
  have hdiff :
      squareRootSmoothMass (R - 1) -
          (∑ c ∈ Finset.Ico 1 R,
            if Odd c then
              canonicalMoebiusWeight c * ((liPairedGridMass R c : ℤ) : ℂ)
            else 0) -
        (squareRootSmoothMass (R - 1) -
          ∑ c ∈ Finset.Ico 1 R,
            if Odd c then
              canonicalMoebiusWeight c * (liPairedIntervalMass R c : ℂ)
            else 0) =
        -∑ c ∈ (Finset.Ico 1 R).filter Odd,
          canonicalMoebiusWeight c *
            ((((liPairedGridMass R c : ℤ) : ℝ) -
              liPairedIntervalMass R c : ℝ) : ℂ) := by
    rw [Finset.sum_filter]
    have hpt : ∀ c ∈ Finset.Ico 1 R,
        ((if Odd c then
            canonicalMoebiusWeight c * ((liPairedGridMass R c : ℤ) : ℂ)
          else 0) -
          (if Odd c then
            canonicalMoebiusWeight c * (liPairedIntervalMass R c : ℂ)
          else 0)) =
        (if Odd c then
          canonicalMoebiusWeight c *
            ((((liPairedGridMass R c : ℤ) : ℝ) -
              liPairedIntervalMass R c : ℝ) : ℂ)
        else 0) := by
      intro c _hc
      by_cases ho : Odd c
      · simp only [ho, if_true]
        push_cast
        ring
      · simp [ho]
    rw [← Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
    ring
  rw [hdiff, norm_neg]
  calc ‖∑ c ∈ (Finset.Ico 1 R).filter Odd,
          canonicalMoebiusWeight c *
            ((((liPairedGridMass R c : ℤ) : ℝ) -
              liPairedIntervalMass R c : ℝ) : ℂ)‖
      ≤ ∑ c ∈ (Finset.Ico 1 R).filter Odd,
          ‖canonicalMoebiusWeight c *
            ((((liPairedGridMass R c : ℤ) : ℝ) -
              liPairedIntervalMass R c : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ (Finset.Ico 1 R).filter Odd, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro c _hc
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ‖canonicalMoebiusWeight c‖ *
              |((liPairedGridMass R c : ℤ) : ℝ) - liPairedIntervalMass R c|
            ≤ 1 * 1 :=
              mul_le_mul (norm_canonicalMoebiusWeight_le_one c)
                (abs_liPairedGridMass_sub_intervalMass_lt R c).le
                (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = (((Finset.Ico 1 R).filter Odd).card : ℝ) := by simp

/-- The rank-grid and floored hybrid Li models differ by at most `R/2`. -/
theorem norm_liHybridGridModel_sub_liHybridModel_le (R : ℕ) :
    ‖liHybridGridModel R - liHybridModel R‖ ≤ ((R / 2 : ℕ) : ℝ) :=
  (norm_liHybridGridModel_sub_liHybridModel_le_card R).trans
    (by exact_mod_cast card_odd_Ico_le R)

/-- The rank-grid and continuous hybrid Li models differ by at most
`R/2 + (R-1)/log R`. -/
theorem norm_liHybridGridModel_sub_continuous_le {R : ℕ} (hR : 2 ≤ R) :
    ‖liHybridGridModel R - liHybridContinuousModel R‖ ≤
      ((R / 2 : ℕ) : ℝ) + ((R : ℝ) - 1) / Real.log R := by
  have h :
      liHybridGridModel R - liHybridContinuousModel R =
        (liHybridGridModel R - liHybridModel R) +
          (liHybridModel R - liHybridContinuousModel R) := by ring
  rw [h]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_liHybridGridModel_sub_liHybridModel_le R)
      (norm_liHybridModel_sub_continuous_le hR))

/-! ## The hybrid model in prime-count discrepancy coordinates -/

/-- Exact return to the top Mertens value: the hybrid model is `M(X)` plus the
existing Möbius-weighted prime-count discrepancy of the transport. -/
theorem liHybridModel_eq_mertens_add_pntError (R : ℕ) (hR : 1 ≤ R) :
    liHybridModel R =
      mertensSummatory (squareRootEndpoint R) +
        squareRootTransportPNTError R := by
  have hend : squarePrefixEndpoint (R - 1) = squareRootEndpoint R := by
    unfold squarePrefixEndpoint squareRootEndpoint
    rw [Nat.sub_add_cancel hR]
  have hM : mertensSummatory (squareRootEndpoint R) =
      squareRootSmoothMass (R - 1) - squareRootTransportCofactorFirst R := by
    rw [← hend, ← squarePrefixMertens,
      squarePrefixMertens_eq_squareRootSmooth_sub_transport,
      squareRootTransportMass_pred_eq_cofactorFirst R hR]
  unfold liHybridModel
  rw [hM, squareRootTransportCofactorFirst_eq_discretePNT_add_error]
  ring

/-- Classical prime-count discrepancy `Delta(y) = pi(y) - L(y)` at an integer
point, with the repository's Li normalization. -/
def primeCountLiDiscrepancy (y : ℕ) : ℂ :=
  (∑ q ∈ Finset.range (y + 1), if q.Prime then (1 : ℂ) else 0) -
    ((logarithmicIntegralFromTwo (y : ℝ) : ℝ) : ℂ)

/-- One cofactor's raw-minus-Li weight is a difference of two discrepancies. -/
theorem squareRootTransportRaw_sub_liDisc_eq_discrepancy
    {R c : ℕ} (hc1 : 1 ≤ c) (hcR : c < R) :
    squareRootTransportRawWeight R c - squareRootTransportLiDiscWeight R c =
      primeCountLiDiscrepancy (squareRootEndpoint R / c) -
        primeCountLiDiscrepancy R := by
  have hRa : R ≤ squareRootEndpoint R / c := le_squareRootEndpoint_div hc1 hcR
  rw [squareRootTransportRawWeight_eq_primeCountDifference hc1]
  have hsplit :
      (∑ q ∈ Finset.range (squareRootEndpoint R / c + 1),
          if q.Prime then (1 : ℂ) else 0) =
        (∑ q ∈ Finset.range (R + 1), if q.Prime then (1 : ℂ) else 0) +
          ∑ q ∈ Finset.Ioc R (squareRootEndpoint R / c),
            if q.Prime then (1 : ℂ) else 0 := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _
      (Nat.zero_le (R + 1)) (by omega : R + 1 ≤ squareRootEndpoint R / c + 1)]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  unfold primeCountLiDiscrepancy squareRootTransportLiDiscWeight
  rw [hsplit]
  push_cast
  ring

/-- `M(R-1)` as a sum over the positive cofactors below `R`. -/
theorem mertensSummatory_pred_eq_sum_Ico {R : ℕ} (hR : 1 ≤ R) :
    mertensSummatory (R - 1) =
      ∑ c ∈ Finset.Ico 1 R, canonicalMoebiusWeight c := by
  unfold mertensSummatory canonicalMoebiusWeight
  rw [Nat.sub_add_cancel hR, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < R)]
  simp

/-- **Identity (12).**  The hybrid Li model is the top Mertens value plus the
Möbius-weighted prime-count discrepancy at the reciprocal cutoffs, minus the
root boundary term `M(R-1) Delta(R)`. -/
theorem liHybridModel_eq_mertens_add_primeCountDiscrepancy
    (R : ℕ) (hR : 1 ≤ R) :
    liHybridModel R =
      mertensSummatory (squareRootEndpoint R) +
        (∑ c ∈ Finset.Ico 1 R,
          canonicalMoebiusWeight c *
            primeCountLiDiscrepancy (squareRootEndpoint R / c)) -
        mertensSummatory (R - 1) * primeCountLiDiscrepancy R := by
  rw [liHybridModel_eq_mertens_add_pntError R hR,
    mertensSummatory_pred_eq_sum_Ico hR, Finset.sum_mul]
  unfold squareRootTransportPNTError
  have hpt : ∀ c ∈ Finset.Ico 1 R,
      canonicalMoebiusWeight c *
          (squareRootTransportRawWeight R c -
            squareRootTransportLiDiscWeight R c) =
        canonicalMoebiusWeight c *
            primeCountLiDiscrepancy (squareRootEndpoint R / c) -
          canonicalMoebiusWeight c * primeCountLiDiscrepancy R := by
    intro c hc
    rcases Finset.mem_Ico.mp hc with ⟨hc1, hcR⟩
    rw [squareRootTransportRaw_sub_liDisc_eq_discrepancy hc1 hcR]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
  ring

end RHLean.Proof
