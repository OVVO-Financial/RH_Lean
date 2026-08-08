import Mathlib
import RHLean.Proof.FareyModesAndTransportWindows
import RHLean.Proof.SurvivorResidueCollisionReindex

/-!
# Survivor pair effective modulus

This module formalizes the elementary arithmetic reduction behind the
nonprimitive survivor resonance diagnostic.

For a reduced Farey numerator/denominator pair `(a,r)` and a nonnegative height
gap `Delta`, define the pair-effective quadratic modulus

```text
q_eff = 2r / gcd(a Delta, 2r)
```

and the rough denominator

```text
s(r) = r / gcd(r,12).
```

The central theorem proves exactly

```text
q_eff | 24  <->  s(r) | Delta
```

when `gcd(a,r)=1` and `r>0`.  It is then instantiated on the actual survivor
source-pair height gap.  No density estimate or cancellation estimate is made.
-/

noncomputable section

namespace RHLean.Proof

/-- Absolute gap between the signed doubled heights of two actual survivor
source coordinates. -/
def survivorPairHeightGap (c q c' q' : ℕ) : ℕ :=
  Int.natAbs
    (survivorHeightDifference c q - survivorHeightDifference c' q')

/-- Effective quadratic modulus after pair differencing. -/
def survivorPairEffectiveModulus (a r Δ : ℕ) : ℕ :=
  (2 * r) / Nat.gcd (a * Δ) (2 * r)

/-- Farey denominator with the complete `2,3` small-modulus part removed. -/
def survivorFareyRoughDenominator (r : ℕ) : ℕ :=
  r / Nat.gcd r 12

/-- General reduced-denominator divisibility identity. -/
private theorem div_gcd_dvd_iff_dvd_mul
    {m n d : ℕ} (hm : 0 < m) :
    m / Nat.gcd m n ∣ d ↔ m ∣ d * n := by
  have hgpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm
  have hgm : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
  have hgn : Nat.gcd m n ∣ n := Nat.gcd_dvd_right m n
  have hcop :
      Nat.Coprime (m / Nat.gcd m n) (n / Nat.gcd m n) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  constructor
  · intro h
    have hprod := Nat.mul_dvd_mul h hgn
    simpa [Nat.div_mul_cancel hgm] using hprod
  · intro h
    have hmul :
        Nat.gcd m n * (m / Nat.gcd m n) ∣
          Nat.gcd m n * (d * (n / Nat.gcd m n)) := by
      simpa [Nat.mul_div_cancel' hgm, Nat.mul_div_cancel' hgn,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    have hred :
        m / Nat.gcd m n ∣ d * (n / Nat.gcd m n) :=
      (Nat.mul_dvd_mul_iff_left hgpos).mp hmul
    exact hcop.dvd_of_dvd_mul_right hred

/-- The pair-effective modulus divides `24` exactly when the rough denominator
divides the pair height gap.  In particular, the numerator disappears from the
exceptional-set criterion for reduced Farey modes. -/
theorem survivorPairEffectiveModulus_dvd_24_iff_roughDenominator_dvd
    (a r Δ : ℕ) (hr : 0 < r) (hcop : Nat.Coprime a r) :
    survivorPairEffectiveModulus a r Δ ∣ 24 ↔
      survivorFareyRoughDenominator r ∣ Δ := by
  have h2r : 0 < 2 * r := Nat.mul_pos (by norm_num) hr
  have heff :
      survivorPairEffectiveModulus a r Δ ∣ 24 ↔
        2 * r ∣ 24 * (a * Δ) := by
    simpa [survivorPairEffectiveModulus, Nat.gcd_comm] using
      (div_gcd_dvd_iff_dvd_mul
        (m := 2 * r) (n := a * Δ) (d := 24) h2r)
  have htwo :
      2 * r ∣ 24 * (a * Δ) ↔ r ∣ 12 * (a * Δ) := by
    rw [show 24 * (a * Δ) = 2 * (12 * (a * Δ)) by ring]
    exact Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)
  have hcancelA :
      r ∣ 12 * (a * Δ) ↔ r ∣ 12 * Δ := by
    constructor
    · intro h
      have h' : r ∣ (12 * Δ) * a := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
      exact hcop.symm.dvd_of_dvd_mul_right h'
    · intro h
      have h' : r ∣ (12 * Δ) * a := dvd_mul_of_dvd_left h a
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h'
  have hrough :
      survivorFareyRoughDenominator r ∣ Δ ↔ r ∣ Δ * 12 := by
    simpa [survivorFareyRoughDenominator] using
      (div_gcd_dvd_iff_dvd_mul (m := r) (n := 12) (d := Δ) hr)
  calc
    survivorPairEffectiveModulus a r Δ ∣ 24 ↔
        2 * r ∣ 24 * (a * Δ) := heff
    _ ↔ r ∣ 12 * (a * Δ) := htwo
    _ ↔ r ∣ 12 * Δ := hcancelA
    _ ↔ r ∣ Δ * 12 := by simp [Nat.mul_comm]
    _ ↔ survivorFareyRoughDenominator r ∣ Δ := hrough.symm

/-- Actual survivor source-pair specialization of the effective-modulus
criterion. -/
theorem survivorPairEffectiveModulus_dvd_24_iff_roughDenominator_dvd_heightGap
    (a r c q c' q' : ℕ) (hr : 0 < r) (hcop : Nat.Coprime a r) :
    survivorPairEffectiveModulus a r (survivorPairHeightGap c q c' q') ∣ 24 ↔
      survivorFareyRoughDenominator r ∣ survivorPairHeightGap c q c' q' := by
  exact survivorPairEffectiveModulus_dvd_24_iff_roughDenominator_dvd
    a r (survivorPairHeightGap c q c' q') hr hcop

/-- Every retained Farey pair automatically satisfies the hypotheses of the
actual source-pair effective-modulus criterion. -/
theorem survivorPairEffectiveModulus_dvd_24_iff_of_fareyModePair
    {R : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareyModePairs R)
    (c q c' q' : ℕ) :
    survivorPairEffectiveModulus p.1 p.2 (survivorPairHeightGap c q c' q') ∣ 24 ↔
      survivorFareyRoughDenominator p.2 ∣ survivorPairHeightGap c q c' q' := by
  have hmem := mem_fareyModePairs.mp hp
  exact survivorPairEffectiveModulus_dvd_24_iff_roughDenominator_dvd_heightGap
    p.1 p.2 c q c' q' (by omega) hmem.2.1

end RHLean.Proof
