import RHLean.Proof.PostRootCovariancePrimeWheel210Scratch
import RHLean.Analysis.RoughWheelFiniteCounting
import RHLean.Arithmetic.PrimorialReciprocalMobiusFactorization

/-!
# Quantitative finite wheels and the cost of their child bands

Every bound uses the exact signed wheel identity before estimating individual
bands.  The resulting constants improve at 6, 30 and 210.  Their iteration is
also audited: density contracts by `1-1/p`, but the additional child intervals
cost `1+1/p`, so separate-band counting has factor `1-1/p^2`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The finite carrier used by the interval count has exactly Euler's
reduced-residue cardinality; this connects the density calculation to that
literal carrier. -/
theorem roughWheelResidues_card_eq_totient (W : ℕ) :
    (roughWheelResidues W).card = Nat.totient W := by
  unfold roughWheelResidues Nat.totient
  congr 1
  apply Finset.filter_congr
  intro n _hn
  exact Nat.coprime_comm

/-- Fresh-prime residue contraction on the same finite counting carrier. -/
theorem roughWheelResidueDensity_mul_freshPrime
    {W p : ℕ} (hW : 0 < W) (hp : Nat.Prime p) (hcop : Nat.Coprime W p) :
    ((roughWheelResidues (W * p)).card : ℝ) / ((W * p : ℕ) : ℝ) =
      ((roughWheelResidues W).card : ℝ) / W * (1 - 1 / (p : ℝ)) := by
  rw [roughWheelResidues_card_eq_totient, Nat.totient_mul hcop,
    Nat.totient_prime hp, roughWheelResidues_card_eq_totient]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  have hWR : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hWR, hpR]
  <;> ring

/-- The covariance prefix and the wheel-one prefix have identical endpoints. -/
theorem realMertensLength_succ_eq_roughMertens_one (B : ℕ) :
    realMertensLength (B + 1) = (roughMertens 1 B : ℝ) := by
  simp [realMertensLength, realMoebiusStep, roughMertens, roughMoebius]

/-- Finite `6`-wheel bound, including all incomplete-period and floor costs. -/
theorem abs_realMertensLength_succ_le_sixWheel (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (2 / 9 : ℝ) * B + 9 := by
  have h0 := abs_roughInterval_le_density (W := 6)
    (a := B / 2) (b := B) (by norm_num) (by omega)
  rw [roughWheelResidues_card_six] at h0
  norm_num at h0
  obtain ⟨h0lo, h0hi⟩ := abs_le.mp h0
  have h1 := abs_roughInterval_le_density (W := 6)
    (a := B / 6) (b := B / 3) (by norm_num) (by omega)
  rw [roughWheelResidues_card_six] at h1
  norm_num at h1
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  have hwidthNat : 3 * (B + B / 3) ≤
      2 * B + 3 * (B / 2 + B / 6) + 6 := by omega
  have hwidth : (3 : ℝ) * ((B : ℝ) + ((B / 3 : ℕ) : ℝ)) ≤
      2 * (B : ℝ) + 3 * (((B / 2 : ℕ) : ℝ) + ((B / 6 : ℕ) : ℝ)) + 6 := by
    exact_mod_cast hwidthNat
  rw [realMertensLength_succ_eq_roughMertens_one,
    roughMertens_one_eq_sixWheel_twoBands]
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

/-- The same finite bound on the exact post-root Bessel remainder. -/
theorem postRootCovarianceRemainder_le_sixWheelSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((2 / 9 : ℝ) * W + 9) ^ 2 / 2 := by
  exact postRootCovarianceRemainder_le_of_mertensMajorant
    (abs_realMertensLength_succ_le_sixWheel W)

/-- Finite `30`-wheel bound, including all incomplete-period and floor costs. -/
theorem abs_realMertensLength_succ_le_thirtyWheel (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (16 / 75 : ℝ) * B + 66 := by
  have h0 := abs_roughInterval_le_density (W := 30)
    (a := B / 2) (b := B) (by norm_num) (by omega)
  rw [roughWheelResidues_card_thirty] at h0
  norm_num at h0
  obtain ⟨h0lo, h0hi⟩ := abs_le.mp h0
  have h1 := abs_roughInterval_le_density (W := 30)
    (a := B / 10) (b := B / 5) (by norm_num) (by omega)
  rw [roughWheelResidues_card_thirty] at h1
  norm_num at h1
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  have h2 := abs_roughInterval_le_density (W := 30)
    (a := B / 6) (b := B / 3) (by norm_num) (by omega)
  rw [roughWheelResidues_card_thirty] at h2
  norm_num at h2
  obtain ⟨h2lo, h2hi⟩ := abs_le.mp h2
  have h3 := abs_roughInterval_le_density (W := 30)
    (a := B / 30) (b := B / 15) (by norm_num) (by omega)
  rw [roughWheelResidues_card_thirty] at h3
  norm_num at h3
  obtain ⟨h3lo, h3hi⟩ := abs_le.mp h3
  have hwidthNat : 5 * (B + B / 5 + B / 3 + B / 15) ≤
      4 * B + 5 * (B / 2 + B / 10 + B / 6 + B / 30) + 20 := by omega
  have hwidth : (5 : ℝ) * ((B : ℝ) + ((B / 5 : ℕ) : ℝ) + ((B / 3 : ℕ) : ℝ) + ((B / 15 : ℕ) : ℝ)) ≤
      4 * (B : ℝ) + 5 * (((B / 2 : ℕ) : ℝ) + ((B / 10 : ℕ) : ℝ) + ((B / 6 : ℕ) : ℝ) + ((B / 30 : ℕ) : ℝ)) + 20 := by
    exact_mod_cast hwidthNat
  rw [realMertensLength_succ_eq_roughMertens_one,
    roughMertens_one_eq_thirtyWheel_fourBands]
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

/-- The same finite bound on the exact post-root Bessel remainder. -/
theorem postRootCovarianceRemainder_le_thirtyWheelSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((16 / 75 : ℝ) * W + 66) ^ 2 / 2 := by
  exact postRootCovarianceRemainder_le_of_mertensMajorant
    (abs_realMertensLength_succ_le_thirtyWheel W)

/-- Finite `210`-wheel bound, including all incomplete-period and floor costs. -/
theorem abs_realMertensLength_succ_le_twoTenWheel (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (256 / 1225 : ℝ) * B + 770 := by
  have h0 := abs_roughInterval_le_density (W := 210)
    (a := B / 2) (b := B) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h0
  norm_num at h0
  obtain ⟨h0lo, h0hi⟩ := abs_le.mp h0
  have h1 := abs_roughInterval_le_density (W := 210)
    (a := B / 14) (b := B / 7) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h1
  norm_num at h1
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  have h2 := abs_roughInterval_le_density (W := 210)
    (a := B / 10) (b := B / 5) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h2
  norm_num at h2
  obtain ⟨h2lo, h2hi⟩ := abs_le.mp h2
  have h3 := abs_roughInterval_le_density (W := 210)
    (a := B / 70) (b := B / 35) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h3
  norm_num at h3
  obtain ⟨h3lo, h3hi⟩ := abs_le.mp h3
  have h4 := abs_roughInterval_le_density (W := 210)
    (a := B / 6) (b := B / 3) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h4
  norm_num at h4
  obtain ⟨h4lo, h4hi⟩ := abs_le.mp h4
  have h5 := abs_roughInterval_le_density (W := 210)
    (a := B / 42) (b := B / 21) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h5
  norm_num at h5
  obtain ⟨h5lo, h5hi⟩ := abs_le.mp h5
  have h6 := abs_roughInterval_le_density (W := 210)
    (a := B / 30) (b := B / 15) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h6
  norm_num at h6
  obtain ⟨h6lo, h6hi⟩ := abs_le.mp h6
  have h7 := abs_roughInterval_le_density (W := 210)
    (a := B / 210) (b := B / 105) (by norm_num) (by omega)
  rw [roughWheelResidues_card_twoTen] at h7
  norm_num at h7
  obtain ⟨h7lo, h7hi⟩ := abs_le.mp h7
  have hwidthNat : 35 * (B + B / 7 + B / 5 + B / 35 + B / 3 + B / 21 + B / 15 + B / 105) ≤
      32 * B + 35 * (B / 2 + B / 14 + B / 10 + B / 70 + B / 6 + B / 42 + B / 30 + B / 210) + 280 := by omega
  have hwidth : (35 : ℝ) * ((B : ℝ) + ((B / 7 : ℕ) : ℝ) + ((B / 5 : ℕ) : ℝ) + ((B / 35 : ℕ) : ℝ) + ((B / 3 : ℕ) : ℝ) + ((B / 21 : ℕ) : ℝ) + ((B / 15 : ℕ) : ℝ) + ((B / 105 : ℕ) : ℝ)) ≤
      32 * (B : ℝ) + 35 * (((B / 2 : ℕ) : ℝ) + ((B / 14 : ℕ) : ℝ) + ((B / 10 : ℕ) : ℝ) + ((B / 70 : ℕ) : ℝ) + ((B / 6 : ℕ) : ℝ) + ((B / 42 : ℕ) : ℝ) + ((B / 30 : ℕ) : ℝ) + ((B / 210 : ℕ) : ℝ)) + 280 := by
    exact_mod_cast hwidthNat
  rw [realMertensLength_succ_eq_roughMertens_one,
    roughMertens_one_eq_twoTenWheel_eightBands]
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

/-- The same finite bound on the exact post-root Bessel remainder. -/
theorem postRootCovarianceRemainder_le_twoTenWheelSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((256 / 1225 : ℝ) * W + 770) ^ 2 / 2 := by
  exact postRootCovarianceRemainder_le_of_mertensMajorant
    (abs_realMertensLength_succ_le_twoTenWheel W)

/-- Leading coefficient for separately counted bands after the initial
2-wheel, with `P` containing the subsequent odd primes. -/
def primeWheelBandSupportCoefficient (P : Finset ℕ) : ℝ :=
  (1 / 4) * primorialSquarefreeEulerFactor P

/-- The existing exact finite-cube factorization accounts for both the
thinner residue population and the extra child-band lengths. -/
theorem primeWheelBandSupportCoefficient_eq_density_mul_bandLength (P : Finset ℕ) :
    primeWheelBandSupportCoefficient P =
      ((1 / 2) * primorialSignedContractionFactor P) *
        ((1 / 2) * primorialSquarefreeSupportFactor P) := by
  rw [primeWheelBandSupportCoefficient,
    ← primorial_signed_mul_support_eq_squarefreeEuler]
  ring

/-- A new prime contracts this particular unsigned majorant by `1-1/p^2`. -/
theorem primeWheelBandSupportCoefficient_insert
    (P : Finset ℕ) (p : ℕ) (hp : p ∉ P) :
    primeWheelBandSupportCoefficient (insert p P) =
      primeWheelBandSupportCoefficient P * (1 - 1 / (p : ℝ) ^ 2) := by
  classical
  simp only [primeWheelBandSupportCoefficient, primorialSquarefreeEulerFactor,
    Finset.prod_insert hp]
  ring

/-- The leading coefficients of the three actual interval estimates above. -/
theorem primeWheelBandSupportCoefficient_6_30_210 :
    primeWheelBandSupportCoefficient {3} = (2 / 9 : ℝ) ∧
      primeWheelBandSupportCoefficient {3, 5} = (16 / 75 : ℝ) ∧
      primeWheelBandSupportCoefficient {3, 5, 7} = (256 / 1225 : ℝ) := by
  norm_num [primeWheelBandSupportCoefficient, primorialSquarefreeEulerFactor]

private theorem squareReciprocalProduct_Icc (N : ℕ) :
    (∏ n ∈ Finset.Icc 3 (N + 2), (1 - 1 / (n : ℝ) ^ 2)) =
      2 * ((N : ℝ) + 3) / (3 * ((N : ℝ) + 2)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [show N + 1 + 2 = (N + 2) + 1 by omega,
        Finset.prod_Icc_succ_top (by omega), ih]
      push_cast
      have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
      have h3 : (N : ℝ) + 3 ≠ 0 := by positivity
      field_simp [h2, h3]
      <;> ring

/-- An elementary uniform positive floor for separate-band counting.
Even allowing *all* integers at least three as factors leaves at least `1/6`.
Thus this majorant cannot be made arbitrarily small by feeding it more primes.
This is a statement about this unsigned estimate, not a lower bound on `|M|`. -/
theorem primeWheelBandSupportCoefficient_ge_one_sixth
    (P : Finset ℕ) (hP : ∀ p ∈ P, 3 ≤ p) :
    (1 / 6 : ℝ) ≤ primeWheelBandSupportCoefficient P := by
  classical
  let N := P.sup id
  let T := Finset.Icc 3 (N + 2)
  have hsub : P ⊆ T := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨hP p hp,
      (Finset.le_sup (f := id) hp).trans (by omega)⟩
  have hfilter : T.filter (fun p => p ∈ P) = P := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hprod : (∏ p ∈ T, (1 - 1 / (p : ℝ) ^ 2)) ≤
      ∏ p ∈ T.filter (fun p => p ∈ P), (1 - 1 / (p : ℝ) ^ 2) := by
    rw [Finset.prod_filter]
    apply Finset.prod_le_prod
    · intro p hp
      have hpR : (3 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
      apply sub_nonneg.mpr
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)).mpr
      nlinarith
    · intro p _hp
      split_ifs
      · rfl
      · have hnonneg : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 := by positivity
        linarith
  rw [hfilter] at hprod
  have hexact := squareReciprocalProduct_Icc N
  change (∏ p ∈ T, (1 - 1 / (p : ℝ) ^ 2)) = _ at hexact
  have hfloor : (2 / 3 : ℝ) ≤ 2 * ((N : ℝ) + 3) / (3 * ((N : ℝ) + 2)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  rw [hexact] at hprod
  unfold primeWheelBandSupportCoefficient primorialSquarefreeEulerFactor
  linarith

/-! ## A further signed gain at 2310

The separate-band floor above does not apply after opposite bands are
recombined.  At the next prime, the negative `11` band overlaps the positive
`15` band.  Their common physical interval cancels exactly.
-/

set_option maxRecDepth 10000 in
private theorem roughWheelResidues_card_2310 : (roughWheelResidues 2310).card = 480 := by
  decide

/-- Exact refinement by `11`, with the common `(B/22,B/15]` interval removed
from the opposite `11` and `15` bands before any absolute value is taken. -/
theorem roughMertens_one_eq_2310Wheel_overlapCancelled (B : ℕ) :
    roughMertens 1 B =
      roughInterval 2310 (B / 2) (B)
      - roughInterval 2310 (B / 15) (B / 11)
      - roughInterval 2310 (B / 14) (B / 7)
      + roughInterval 2310 (B / 154) (B / 77)
      - roughInterval 2310 (B / 10) (B / 5)
      + roughInterval 2310 (B / 110) (B / 55)
      + roughInterval 2310 (B / 70) (B / 35)
      - roughInterval 2310 (B / 770) (B / 385)
      - roughInterval 2310 (B / 6) (B / 3)
      + roughInterval 2310 (B / 66) (B / 33)
      + roughInterval 2310 (B / 42) (B / 21)
      - roughInterval 2310 (B / 462) (B / 231)
      + roughInterval 2310 (B / 30) (B / 22)
      - roughInterval 2310 (B / 330) (B / 165)
      - roughInterval 2310 (B / 210) (B / 105)
      + roughInterval 2310 (B / 2310) (B / 1155) := by
  have hs6 : Squarefree 6 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).2
      ⟨Nat.prime_two.squarefree, (show Nat.Prime 3 by norm_num).squarefree⟩
  have hs30 : Squarefree 30 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 5 6)).2
      ⟨(show Nat.Prime 5 by norm_num).squarefree, hs6⟩
  have hs210 : Squarefree 210 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 7 30)).2
      ⟨(show Nat.Prime 7 by norm_num).squarefree, hs30⟩
  have hs2310 : Squarefree 2310 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 11 210)).2
      ⟨(show Nat.Prime 11 by norm_num).squarefree, hs210⟩
  have hr0 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 2) (B)
  norm_num at hr0
  have h0 : roughInterval 210 (B / 2) (B) =
      roughInterval 2310 (B / 2) (B) -
        roughInterval 2310 (B / 22) (B / 11) := by
    simpa [Nat.div_div_eq_div_mul] using hr0
  have hr1 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 14) (B / 7)
  norm_num at hr1
  have h1 : roughInterval 210 (B / 14) (B / 7) =
      roughInterval 2310 (B / 14) (B / 7) -
        roughInterval 2310 (B / 154) (B / 77) := by
    simpa [Nat.div_div_eq_div_mul] using hr1
  have hr2 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 10) (B / 5)
  norm_num at hr2
  have h2 : roughInterval 210 (B / 10) (B / 5) =
      roughInterval 2310 (B / 10) (B / 5) -
        roughInterval 2310 (B / 110) (B / 55) := by
    simpa [Nat.div_div_eq_div_mul] using hr2
  have hr3 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 70) (B / 35)
  norm_num at hr3
  have h3 : roughInterval 210 (B / 70) (B / 35) =
      roughInterval 2310 (B / 70) (B / 35) -
        roughInterval 2310 (B / 770) (B / 385) := by
    simpa [Nat.div_div_eq_div_mul] using hr3
  have hr4 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 6) (B / 3)
  norm_num at hr4
  have h4 : roughInterval 210 (B / 6) (B / 3) =
      roughInterval 2310 (B / 6) (B / 3) -
        roughInterval 2310 (B / 66) (B / 33) := by
    simpa [Nat.div_div_eq_div_mul] using hr4
  have hr5 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 42) (B / 21)
  norm_num at hr5
  have h5 : roughInterval 210 (B / 42) (B / 21) =
      roughInterval 2310 (B / 42) (B / 21) -
        roughInterval 2310 (B / 462) (B / 231) := by
    simpa [Nat.div_div_eq_div_mul] using hr5
  have hr6 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 30) (B / 15)
  norm_num at hr6
  have h6 : roughInterval 210 (B / 30) (B / 15) =
      roughInterval 2310 (B / 30) (B / 15) -
        roughInterval 2310 (B / 330) (B / 165) := by
    simpa [Nat.div_div_eq_div_mul] using hr6
  have hr7 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 210) (B / 105)
  norm_num at hr7
  have h7 : roughInterval 210 (B / 210) (B / 105) =
      roughInterval 2310 (B / 210) (B / 105) -
        roughInterval 2310 (B / 2310) (B / 1155) := by
    simpa [Nat.div_div_eq_div_mul] using hr7
  rw [roughMertens_one_eq_twoTenWheel_eightBands, h0, h1, h2, h3, h4, h5, h6, h7]
  unfold roughInterval
  ring

/-- Counting only after the opposite-band overlap has cancelled improves
on the separate-band 2310 coefficient, from `6144/29645` to `17648/88935`. -/
theorem abs_realMertensLength_succ_le_2310Wheel (B : ℕ) :
    |realMertensLength (B + 1)| ≤ (17648 / 88935 : ℝ) * B + 15364 := by
  have h0 := abs_roughInterval_le_density (W := 2310)
    (a := B / 2) (b := B) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h0
  norm_num at h0
  obtain ⟨h0lo, h0hi⟩ := abs_le.mp h0
  have h1 := abs_roughInterval_le_density (W := 2310)
    (a := B / 15) (b := B / 11) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h1
  norm_num at h1
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp h1
  have h2 := abs_roughInterval_le_density (W := 2310)
    (a := B / 14) (b := B / 7) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h2
  norm_num at h2
  obtain ⟨h2lo, h2hi⟩ := abs_le.mp h2
  have h3 := abs_roughInterval_le_density (W := 2310)
    (a := B / 154) (b := B / 77) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h3
  norm_num at h3
  obtain ⟨h3lo, h3hi⟩ := abs_le.mp h3
  have h4 := abs_roughInterval_le_density (W := 2310)
    (a := B / 10) (b := B / 5) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h4
  norm_num at h4
  obtain ⟨h4lo, h4hi⟩ := abs_le.mp h4
  have h5 := abs_roughInterval_le_density (W := 2310)
    (a := B / 110) (b := B / 55) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h5
  norm_num at h5
  obtain ⟨h5lo, h5hi⟩ := abs_le.mp h5
  have h6 := abs_roughInterval_le_density (W := 2310)
    (a := B / 70) (b := B / 35) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h6
  norm_num at h6
  obtain ⟨h6lo, h6hi⟩ := abs_le.mp h6
  have h7 := abs_roughInterval_le_density (W := 2310)
    (a := B / 770) (b := B / 385) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h7
  norm_num at h7
  obtain ⟨h7lo, h7hi⟩ := abs_le.mp h7
  have h8 := abs_roughInterval_le_density (W := 2310)
    (a := B / 6) (b := B / 3) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h8
  norm_num at h8
  obtain ⟨h8lo, h8hi⟩ := abs_le.mp h8
  have h9 := abs_roughInterval_le_density (W := 2310)
    (a := B / 66) (b := B / 33) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h9
  norm_num at h9
  obtain ⟨h9lo, h9hi⟩ := abs_le.mp h9
  have h10 := abs_roughInterval_le_density (W := 2310)
    (a := B / 42) (b := B / 21) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h10
  norm_num at h10
  obtain ⟨h10lo, h10hi⟩ := abs_le.mp h10
  have h11 := abs_roughInterval_le_density (W := 2310)
    (a := B / 462) (b := B / 231) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h11
  norm_num at h11
  obtain ⟨h11lo, h11hi⟩ := abs_le.mp h11
  have h12 := abs_roughInterval_le_density (W := 2310)
    (a := B / 30) (b := B / 22) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h12
  norm_num at h12
  obtain ⟨h12lo, h12hi⟩ := abs_le.mp h12
  have h13 := abs_roughInterval_le_density (W := 2310)
    (a := B / 330) (b := B / 165) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h13
  norm_num at h13
  obtain ⟨h13lo, h13hi⟩ := abs_le.mp h13
  have h14 := abs_roughInterval_le_density (W := 2310)
    (a := B / 210) (b := B / 105) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h14
  norm_num at h14
  obtain ⟨h14lo, h14hi⟩ := abs_le.mp h14
  have h15 := abs_roughInterval_le_density (W := 2310)
    (a := B / 2310) (b := B / 1155) (by norm_num) (by omega)
  rw [roughWheelResidues_card_2310] at h15
  norm_num at h15
  obtain ⟨h15lo, h15hi⟩ := abs_le.mp h15
  have hwidthNat : 1155 * (B + B / 11 + B / 7 + B / 77 + B / 5 + B / 55 + B / 35 + B / 385 + B / 3 + B / 33 + B / 21 + B / 231 + B / 22 + B / 165 + B / 105 + B / 1155) ≤
      1103 * B + 1155 * (B / 2 + B / 15 + B / 14 + B / 154 + B / 10 + B / 110 + B / 70 + B / 770 + B / 6 + B / 66 + B / 42 + B / 462 + B / 30 + B / 330 + B / 210 + B / 2310) + 18480 := by omega
  have hwidth : (1155 : ℝ) * ((B : ℝ) +
        ((B / 11 : ℕ) : ℝ) +
        ((B / 7 : ℕ) : ℝ) +
        ((B / 77 : ℕ) : ℝ) +
        ((B / 5 : ℕ) : ℝ) +
        ((B / 55 : ℕ) : ℝ) +
        ((B / 35 : ℕ) : ℝ) +
        ((B / 385 : ℕ) : ℝ) +
        ((B / 3 : ℕ) : ℝ) +
        ((B / 33 : ℕ) : ℝ) +
        ((B / 21 : ℕ) : ℝ) +
        ((B / 231 : ℕ) : ℝ) +
        ((B / 22 : ℕ) : ℝ) +
        ((B / 165 : ℕ) : ℝ) +
        ((B / 105 : ℕ) : ℝ) +
        ((B / 1155 : ℕ) : ℝ)) ≤
      1103 * (B : ℝ) + 1155 * (((B / 2 : ℕ) : ℝ) +
        ((B / 15 : ℕ) : ℝ) +
        ((B / 14 : ℕ) : ℝ) +
        ((B / 154 : ℕ) : ℝ) +
        ((B / 10 : ℕ) : ℝ) +
        ((B / 110 : ℕ) : ℝ) +
        ((B / 70 : ℕ) : ℝ) +
        ((B / 770 : ℕ) : ℝ) +
        ((B / 6 : ℕ) : ℝ) +
        ((B / 66 : ℕ) : ℝ) +
        ((B / 42 : ℕ) : ℝ) +
        ((B / 462 : ℕ) : ℝ) +
        ((B / 30 : ℕ) : ℝ) +
        ((B / 330 : ℕ) : ℝ) +
        ((B / 210 : ℕ) : ℝ) +
        ((B / 2310 : ℕ) : ℝ)) + 18480 := by
    exact_mod_cast hwidthNat
  rw [realMertensLength_succ_eq_roughMertens_one,
    roughMertens_one_eq_2310Wheel_overlapCancelled]
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

/-- The extra signed overlap gain transfers to the exact Bessel remainder. -/
theorem postRootCovarianceRemainder_le_2310WheelSquare (W : ℕ) :
    postRootCovarianceRemainder W ≤
      ((17648 / 88935 : ℝ) * W + 15364) ^ 2 / 2 := by
  exact postRootCovarianceRemainder_le_of_mertensMajorant
    (abs_realMertensLength_succ_le_2310Wheel W)

end RHLean.Proof
