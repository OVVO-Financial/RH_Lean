import Mathlib
import RHLean.Analysis.PrimeWheelLocalSpectrum

/-!
# Prime-three physical resonance cancellation

The local `3^2` square-sensitive comb has a dangerous nonzero conductor-`3`
frequency: its local Fourier coefficient has no small-modulus decay.  The
physical three-slot geometry nevertheless supplies an exact cancellation before
any norm is taken.

The affine map `k ↦ 4k+j` on `ZMod 9` has inverse multiplier `7`.  Thus a
frequency `r` on the cell clock contributes the slot phase

`e_9(j * 7r)`.

When `r` is a nonzero multiple of `3`, the element `7r` has additive order
`3`, so the three physical slot phases sum to zero.  Consequently any common
local coefficient on that conductor, in particular the actual local
square-sensitive prime-`3` coefficient, cancels exactly across the three slots.

This is an arithmetic cancellation statement, not an estimate.  It does not yet
assert that the global smooth-core correction factors through the same local
packet; that is the next lifting step.
-/

open scoped BigOperators
open AddChar

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

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
