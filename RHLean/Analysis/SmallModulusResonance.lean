import RHLean.Analysis.ReducedQuadraticGauss
import RHLean.Analysis.PrimeWheelLocalSpectrum

namespace RHLean.QuadraticPrimePhase

/-- Every unit modulo `6` has square `1`. -/
theorem unit_sq_eq_one_mod_six :
    ∀ u : (ZMod 6)ˣ, (u : ZMod 6) ^ 2 = 1 := by
  native_decide

/-- Every unit modulo `24` has square `1`. -/
theorem unit_sq_eq_one_mod_twenty_four :
    ∀ u : (ZMod 24)ˣ, (u : ZMod 24) ^ 2 = 1 := by
  native_decide

/-- If a unit squares to one modulo `2 * r`, its quadratic phase is the
single additive-character value with numerator `a`. -/
theorem quadraticUnitPhase_eq_additiveCharacter_of_sq_eq_one
    {a : ℤ} {r : ℕ} [NeZero (2 * r)]
    (u : (ZMod (2 * r))ˣ)
    (hu : (u : ZMod (2 * r)) ^ 2 = 1) :
    quadraticUnitPhase a r u =
      additiveCharacter (2 * (r : ℤ)) a := by
  unfold quadraticUnitPhase quadraticPhase
  apply additiveCharacter_eq_of_sub_dvd
  have hz :
      ((a * (u.val.val : ℤ) ^ 2 - a : ℤ) : ZMod (2 * r)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, hu]
    ring
  have hdvd :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (a * (u.val.val : ℤ) ^ 2 - a) (2 * r)).mp hz
  simpa using hdvd

/-- When all units modulo `2 * r` square to one, the reduced sum is the
totient times one coherent additive-character phase. -/
theorem reducedQuadraticGauss_eq_totient_mul_phase_of_unit_sq
    (a : ℤ) (r : ℕ) (hr : 0 < r)
    (hsq : ∀ u : (ZMod (2 * r))ˣ,
      (u : ZMod (2 * r)) ^ 2 = 1) :
    reducedQuadraticGauss a r hr =
      (Nat.totient (2 * r) : ℂ) *
        additiveCharacter (2 * (r : ℤ)) a := by
  classical
  letI : NeZero (2 * r) :=
    ⟨Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hr)⟩
  have hphase : ∀ u : (ZMod (2 * r))ˣ,
      quadraticUnitPhase a r u =
        additiveCharacter (2 * (r : ℤ)) a :=
    fun u => quadraticUnitPhase_eq_additiveCharacter_of_sq_eq_one u (hsq u)
  simp [reducedQuadraticGauss, hphase, ZMod.card_units_eq_totient]

/-- Under the same square-one hypothesis, normalization removes the exact
unit count and leaves the coherent phase. -/
theorem normalizedReducedQuadraticGauss_eq_phase_of_unit_sq
    (a : ℤ) (r : ℕ) (hr : 0 < r)
    (hsq : ∀ u : (ZMod (2 * r))ˣ,
      (u : ZMod (2 * r)) ^ 2 = 1) :
    normalizedReducedQuadraticGauss a r hr =
      additiveCharacter (2 * (r : ℤ)) a := by
  rw [normalizedReducedQuadraticGauss,
    reducedQuadraticGauss_eq_totient_mul_phase_of_unit_sq a r hr hsq]
  have htotNat : Nat.totient (2 * r) ≠ 0 :=
    (Nat.totient_pos.mpr (Nat.mul_pos (by norm_num) hr)).ne'
  have htot : (Nat.totient (2 * r) : ℂ) ≠ 0 := by
    exact_mod_cast htotNat
  field_simp [htot]

/-- Exact coherent normalized phase for modulus `6`. -/
theorem normalizedReducedQuadraticGauss_mod_six
    (a : ℤ) :
    normalizedReducedQuadraticGauss a 3 (by norm_num) =
      additiveCharacter 6 a := by
  simpa using
    normalizedReducedQuadraticGauss_eq_phase_of_unit_sq
      a 3 (by norm_num) unit_sq_eq_one_mod_six

/-- Exact coherent normalized phase for modulus `24`. -/
theorem normalizedReducedQuadraticGauss_mod_twenty_four
    (a : ℤ) :
    normalizedReducedQuadraticGauss a 12 (by norm_num) =
      additiveCharacter 24 a := by
  simpa using
    normalizedReducedQuadraticGauss_eq_phase_of_unit_sq
      a 12 (by norm_num) unit_sq_eq_one_mod_twenty_four

/-- The corrected normalized factor at `(a, r) = (1, 3)` is exactly `e(1/6)`. -/
theorem normalizedReducedQuadraticGauss_one_three :
    normalizedReducedQuadraticGauss 1 3 (by norm_num) =
      additiveCharacter 6 1 := by
  exact normalizedReducedQuadraticGauss_mod_six 1

/-- Every integer additive-character value lies on the complex unit circle. -/
theorem norm_additiveCharacter
    (modulus numerator : ℤ) :
    ‖additiveCharacter modulus numerator‖ = 1 := by
  simp [additiveCharacter, Complex.norm_exp]

/-- The prime-3 quadratic factor has exact norm one; it is not the rational
cell-mask energy `1/9`. -/
theorem norm_normalizedReducedQuadraticGauss_one_three :
    ‖normalizedReducedQuadraticGauss 1 3 (by norm_num)‖ = 1 := by
  rw [normalizedReducedQuadraticGauss_one_three]
  exact norm_additiveCharacter 6 1

end RHLean.QuadraticPrimePhase

open scoped BigOperators
open AddChar

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-! ## Physical three-slot cancellation of the prime-three resonance -/

/-- Inverse of the physical step `4` modulo `9`. -/
def physicalPrimeThreeInverseStep : ZMod 9 := 7

/-- Local frequency seen after transporting the four-cell clock to the
prime-`3` square torus. -/
def physicalPrimeThreeTransportedFrequency (r : ZMod 9) : ZMod 9 :=
  physicalPrimeThreeInverseStep * r

/-- Phase contributed by physical slot `j` at a transported prime-`3`
frequency. -/
def physicalPrimeThreeSlotPhase (j : ℕ) (r : ZMod 9) : ℂ :=
  ZMod.stdAddChar
    (((j : ℕ) : ZMod 9) * physicalPrimeThreeTransportedFrequency r)

private theorem stdAddChar_threeCycle_sum_eq_zero
    (x : ZMod 9) (hx0 : x ≠ 0) (hx3 : 3 • x = 0) :
    ZMod.stdAddChar x +
        ZMod.stdAddChar (2 • x) +
        ZMod.stdAddChar (3 • x) = 0 := by
  let z : ℂ := ZMod.stdAddChar x
  have hz1 : z ≠ 1 := by
    intro hz
    apply hx0
    exact ZMod.injective_stdAddChar (by simpa [z] using hz)
  have hz3 : z ^ 3 = 1 := by
    calc
      z ^ 3 = ZMod.stdAddChar (3 • x) := by
        symm
        exact AddChar.map_nsmul_eq_pow
          (ZMod.stdAddChar : AddChar (ZMod 9) ℂ) 3 x
      _ = ZMod.stdAddChar 0 := by rw [hx3]
      _ = 1 := AddChar.map_zero_eq_one _
  have hfactor : (z - 1) * (z ^ 2 + z + 1) = 0 := by
    calc
      (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 := by ring
      _ = 0 := by rw [hz3]; ring
  have hsum : z ^ 2 + z + 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hz1)
  calc
    ZMod.stdAddChar x +
        ZMod.stdAddChar (2 • x) +
        ZMod.stdAddChar (3 • x) =
      z + z ^ 2 + z ^ 3 := by
        rw [AddChar.map_nsmul_eq_pow
          (ZMod.stdAddChar : AddChar (ZMod 9) ℂ) 2 x]
        rw [AddChar.map_nsmul_eq_pow
          (ZMod.stdAddChar : AddChar (ZMod 9) ℂ) 3 x]
        rfl
    _ = 0 := by
      rw [hz3]
      linarith

private theorem physicalPrimeThreeTransportedFrequency_data
    (r : ZMod 9) (hr0 : r ≠ 0) (hr3 : 3 ∣ r.val) :
    physicalPrimeThreeTransportedFrequency r ≠ 0 ∧
      3 • physicalPrimeThreeTransportedFrequency r = 0 := by
  have hrval0 : r.val ≠ 0 := by
    intro hval
    apply hr0
    rw [← ZMod.natCast_zmod_val r, hval]
    simp
  have hrlt : r.val < 9 := r.isLt
  rcases hr3 with ⟨q, hq⟩
  have hcases : r.val = 3 ∨ r.val = 6 := by omega
  rcases hcases with h3 | h6
  · have hr : r = (3 : ZMod 9) := by
      rw [← ZMod.natCast_zmod_val r, h3]
    subst r
    constructor <;>
      norm_num [physicalPrimeThreeTransportedFrequency,
        physicalPrimeThreeInverseStep, nsmul_eq_mul]
  · have hr : r = (6 : ZMod 9) := by
      rw [← ZMod.natCast_zmod_val r, h6]
    subst r
    constructor <;>
      norm_num [physicalPrimeThreeTransportedFrequency,
        physicalPrimeThreeInverseStep, nsmul_eq_mul]

/-- **Exact cancellation of the dangerous prime-`3` slot phases.**  Every
nonzero conductor-`3` frequency disappears after summing the three physical
slot shifts, before taking an absolute value or norm. -/
theorem physicalPrimeThreeSlotPhase_sum_eq_zero
    (r : ZMod 9) (hr0 : r ≠ 0) (hr3 : 3 ∣ r.val) :
    physicalPrimeThreeSlotPhase 1 r +
        physicalPrimeThreeSlotPhase 2 r +
        physicalPrimeThreeSlotPhase 3 r = 0 := by
  let x := physicalPrimeThreeTransportedFrequency r
  have hx := physicalPrimeThreeTransportedFrequency_data r hr0 hr3
  have hcycle := stdAddChar_threeCycle_sum_eq_zero x hx.1 hx.2
  simpa [physicalPrimeThreeSlotPhase, x, nsmul_eq_mul] using hcycle

/-- The actual common local prime-`3` raw Fourier coefficient transported from
the cell clock. -/
def physicalPrimeThreeLocalRawMode (r : ZMod 9) : ℂ :=
  localPrimeCombNaturalSpectrum 3 (by norm_num)
    (physicalPrimeThreeTransportedFrequency r)

/-- One physical slot packet of the local raw prime-`3` mode. -/
def physicalPrimeThreeLocalRawSlotMode
    (j : ℕ) (r : ZMod 9) : ℂ :=
  physicalPrimeThreeSlotPhase j r * physicalPrimeThreeLocalRawMode r

/-- At a nonzero conductor-`3` frequency, the transported local raw coefficient
is the explicit coherent value `1-2*3 = -5`. -/
theorem physicalPrimeThreeLocalRawMode_eq_neg_five
    (r : ZMod 9) (hr0 : r ≠ 0) (hr3 : 3 ∣ r.val) :
    physicalPrimeThreeLocalRawMode r = (-5 : ℂ) := by
  have hx := physicalPrimeThreeTransportedFrequency_data r hr0 hr3
  unfold physicalPrimeThreeLocalRawMode
  rw [localPrimeCombNaturalSpectrum_eq_explicit]
  rw [if_neg hx.1]
  have hxdiv : 3 ∣ (physicalPrimeThreeTransportedFrequency r).val := by
    have hrval0 : r.val ≠ 0 := by
      intro hval
      apply hr0
      rw [← ZMod.natCast_zmod_val r, hval]
      simp
    have hrlt : r.val < 9 := r.isLt
    rcases hr3 with ⟨q, hq⟩
    have hcases : r.val = 3 ∨ r.val = 6 := by omega
    rcases hcases with h3 | h6
    · have hr : r = (3 : ZMod 9) := by
        rw [← ZMod.natCast_zmod_val r, h3]
      subst r
      norm_num [physicalPrimeThreeTransportedFrequency,
        physicalPrimeThreeInverseStep]
    · have hr : r = (6 : ZMod 9) := by
        rw [← ZMod.natCast_zmod_val r, h6]
      subst r
      norm_num [physicalPrimeThreeTransportedFrequency,
        physicalPrimeThreeInverseStep]
  rw [if_pos hxdiv]
  norm_num

/-- **Local raw resonance cancellation.**  Although each prime-`3` conductor
packet carries the coherent coefficient `-5`, the sum of its three physical
slot packets is exactly zero. -/
theorem physicalPrimeThreeLocalRawSlotMode_sum_eq_zero
    (r : ZMod 9) (hr0 : r ≠ 0) (hr3 : 3 ∣ r.val) :
    physicalPrimeThreeLocalRawSlotMode 1 r +
        physicalPrimeThreeLocalRawSlotMode 2 r +
        physicalPrimeThreeLocalRawSlotMode 3 r = 0 := by
  unfold physicalPrimeThreeLocalRawSlotMode
  rw [physicalPrimeThreeLocalRawMode_eq_neg_five r hr0 hr3]
  have hphase := physicalPrimeThreeSlotPhase_sum_eq_zero r hr0 hr3
  calc
    physicalPrimeThreeSlotPhase 1 r * (-5 : ℂ) +
        physicalPrimeThreeSlotPhase 2 r * (-5 : ℂ) +
        physicalPrimeThreeSlotPhase 3 r * (-5 : ℂ) =
      (physicalPrimeThreeSlotPhase 1 r +
          physicalPrimeThreeSlotPhase 2 r +
          physicalPrimeThreeSlotPhase 3 r) * (-5 : ℂ) := by ring
    _ = 0 := by rw [hphase]; ring

end RHLean.Analysis
