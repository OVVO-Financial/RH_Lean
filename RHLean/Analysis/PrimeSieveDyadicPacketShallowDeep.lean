import Mathlib
import RHLean.Analysis.PrimeSieveDyadicSignedPackets

/-!
# Recursive midpoint packets and the shallow/deep analytic split

PR #323 exposed the signed sibling packet

`B(a,m,b) = (b-m)(D(m)-D(a)) - (m-a)(D(b)-D(m))`

for the clipped prime discrepancy `D = pi - Li`, but deliberately stopped before
building the recursive midpoint tree.  This module performs that deterministic
step.

For an interval `[a,b]`, repeatedly split at

`m = a + floor ((b-a)/2)`.

The width-normalized sibling packet is the discrete Faber--Schauder coefficient
at that node.  The generic frame theorem below proves that the chord energy on an
interval of width at most `2^depth` is bounded by `2 * depth` times the complete
midpoint-packet energy through that depth.  The factor `depth` is the expected
Cauchy loss along one nested path; no arithmetic estimate enters the proof.

For the reciprocal prime-discrepancy blocks, the native dyadic label `j` is a
sufficient recursion depth because every occupied `j`-block has width at most
`2^j`.  A cutoff `J` then gives the exact partition

`packetEnergy = shallowEnergy(J) + deepEnergy(J)`.

Two analytic predicates are named at the end:

* `DyadicPacketShallowEnergyBlockBoundedStatement`;
* `DyadicPacketDeepTailBlockBoundedStatement`.

They are intentionally not proved here.  Together with the deterministic frame
and the existing #321 coherent/Mobius hypotheses, they reduce RH to the targeted
question of controlling the shallow signed modes and the recursively deep tail.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## Generic discrete midpoint frame -/

/-- Integer midpoint used by the recursive packet tree. -/
def dyadicPacketMidpoint (a b : ℕ) : ℕ :=
  a + (b - a) / 2

/-- Generic signed sibling packet for a complex-valued discrete function. -/
private def genericSignedSiblingPacket
    (f : ℕ → ℂ) (a m b : ℕ) : ℂ :=
  (((b - m : ℕ) : ℂ) * (f m - f a)) -
    (((m - a : ℕ) : ℂ) * (f b - f m))

/-- Width-normalized generic sibling packet. -/
private def genericSignedSiblingResidual
    (f : ℕ → ℂ) (a m b : ℕ) : ℂ :=
  (((b - a : ℕ) : ℂ)⁻¹) * genericSignedSiblingPacket f a m b

/-- Chord energy on the half-open integer interval `[a,b)`.  The left endpoint
contributes zero; using `Ico` makes midpoint splitting exact. -/
private def genericChordEnergy (f : ℕ → ℂ) (a b : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico a b, ‖genericSignedSiblingResidual f a d b‖ ^ 2

/-- Complete recursive midpoint-packet energy through a prescribed number of
levels.  Nodes of width at most one do not split. -/
private def genericMidpointPacketTreeEnergy
    (f : ℕ → ℂ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        ((b - a : ℕ) : ℝ) *
            ‖genericSignedSiblingResidual f a m b‖ ^ 2 +
          genericMidpointPacketTreeEnergy f depth a m +
          genericMidpointPacketTreeEnergy f depth m b
      else 0

private theorem dyadicPacketMidpoint_facts
    {a b : ℕ} (h : a + 1 < b) :
    a < dyadicPacketMidpoint a b ∧
      dyadicPacketMidpoint a b < b := by
  unfold dyadicPacketMidpoint
  omega

private theorem dyadicPacketMidpoint_child_widths
    {a b depth : ℕ}
    (hsplit : a + 1 < b)
    (hwidth : b - a ≤ 2 ^ (depth + 1)) :
    dyadicPacketMidpoint a b - a ≤ 2 ^ depth ∧
      b - dyadicPacketMidpoint a b ≤ 2 ^ depth := by
  have hp : 2 ^ (depth + 1) = 2 * 2 ^ depth := by
    rw [pow_succ]
    ring
  rw [hp] at hwidth
  unfold dyadicPacketMidpoint
  omega

private theorem genericSignedSiblingResidual_eq_zero_left
    (f : ℕ → ℂ) (a b : ℕ) :
    genericSignedSiblingResidual f a a b = 0 := by
  simp [genericSignedSiblingResidual, genericSignedSiblingPacket]

private theorem genericSignedSiblingResidual_eq_zero_of_width_le_one
    {f : ℕ → ℂ} {a b d : ℕ}
    (hwidth : b - a ≤ 1) (hd : d ∈ Finset.Ico a b) :
    genericSignedSiblingResidual f a d b = 0 := by
  have hdI := Finset.mem_Ico.mp hd
  have hda : d = a := by omega
  subst d
  exact genericSignedSiblingResidual_eq_zero_left f a b

private theorem genericChordEnergy_eq_zero_of_width_le_one
    (f : ℕ → ℂ) {a b : ℕ} (hwidth : b - a ≤ 1) :
    genericChordEnergy f a b = 0 := by
  unfold genericChordEnergy
  apply Finset.sum_eq_zero
  intro d hd
  rw [genericSignedSiblingResidual_eq_zero_of_width_le_one hwidth hd]
  simp

private theorem sum_Ico_split
    (g : ℕ → ℝ) {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b) :
    (∑ d ∈ Finset.Ico a b, g d) =
      (∑ d ∈ Finset.Ico a m, g d) +
        ∑ d ∈ Finset.Ico m b, g d := by
  have hdis : Disjoint (Finset.Ico a m) (Finset.Ico m b) := by
    rw [Finset.disjoint_left]
    intro d hdl hdr
    simp only [Finset.mem_Ico] at hdl hdr
    omega
  have hunion : Finset.Ico a m ∪ Finset.Ico m b = Finset.Ico a b := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  rw [← hunion, Finset.sum_union hdis]

private theorem genericResidual_left_decomposition
    {f : ℕ → ℂ} {a d m b : ℕ}
    (had : a ≤ d) (hdm : d ≤ m) (hmb : m < b) (ham : a < m) :
    genericSignedSiblingResidual f a d b =
      genericSignedSiblingResidual f a d m +
        ((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) *
          genericSignedSiblingResidual f a m b) := by
  have ham0 : ((((m - a : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m - a))
  have hab0 : ((((b - a : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < b - a))
  unfold genericSignedSiblingResidual genericSignedSiblingPacket
  push_cast
  field_simp [ham0, hab0]
  ring

private theorem genericResidual_right_decomposition
    {f : ℕ → ℂ} {a m d b : ℕ}
    (ham : a < m) (hmd : m ≤ d) (hdb : d ≤ b) (hmb : m < b) :
    genericSignedSiblingResidual f a d b =
      genericSignedSiblingResidual f m d b +
        ((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) *
          genericSignedSiblingResidual f a m b) := by
  have hmb0 : ((((b - m : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < b - m))
  have hab0 : ((((b - a : ℕ) : ℂ))) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < b - a))
  unfold genericSignedSiblingResidual genericSignedSiblingPacket
  push_cast
  field_simp [hmb0, hab0]
  ring

private theorem natCast_ratio_norm_le_one
    {p q : ℕ} (hpq : p ≤ q) (hq : 0 < q) :
    ‖((p : ℂ) * ((q : ℂ)⁻¹))‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  simpa [div_eq_mul_inv] using (div_le_one hqR).2 hpqR

private theorem left_tent_energy_le
    (c : ℂ) {a m : ℕ} (ham : a < m) :
    (∑ d ∈ Finset.Ico a m,
      ‖((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) ≤
      ((m - a : ℕ) : ℝ) * ‖c‖ ^ 2 := by
  calc
    (∑ d ∈ Finset.Ico a m,
        ‖((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) ≤
      ∑ _d ∈ Finset.Ico a m, ‖c‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        have hdI := Finset.mem_Ico.mp hd
        have hratio := natCast_ratio_norm_le_one
          (p := d - a) (q := m - a) (by omega) (by omega)
        rw [norm_mul]
        have hr0 : 0 ≤ ‖((d - a : ℂ) * ((m - a : ℂ)⁻¹))‖ := norm_nonneg _
        have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
        nlinarith
    _ = ((m - a : ℕ) : ℝ) * ‖c‖ ^ 2 := by
      simp [Nat.card_Ico, nsmul_eq_mul]

private theorem right_tent_energy_le
    (c : ℂ) {m b : ℕ} (hmb : m < b) :
    (∑ d ∈ Finset.Ico m b,
      ‖((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) ≤
      ((b - m : ℕ) : ℝ) * ‖c‖ ^ 2 := by
  calc
    (∑ d ∈ Finset.Ico m b,
        ‖((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) ≤
      ∑ _d ∈ Finset.Ico m b, ‖c‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        have hdI := Finset.mem_Ico.mp hd
        have hratio := natCast_ratio_norm_le_one
          (p := b - d) (q := b - m) (by omega) (by omega)
        rw [norm_mul]
        have hr0 : 0 ≤ ‖((b - d : ℂ) * ((b - m : ℂ)⁻¹))‖ := norm_nonneg _
        have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
        nlinarith
    _ = ((b - m : ℕ) : ℝ) * ‖c‖ ^ 2 := by
      simp [Nat.card_Ico, nsmul_eq_mul]

private theorem norm_add_sq_le_two (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have htri := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

private theorem weighted_norm_add_sq
    (q : ℕ) (hq : 1 ≤ q) (u v : ℂ) :
    (q : ℝ) * ‖u + v‖ ^ 2 ≤
      ((q + 1 : ℕ) : ℝ) * ‖u‖ ^ 2 +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) * ‖v‖ ^ 2 := by
  have htri := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  push_cast
  nlinarith [sq_nonneg (‖u‖ - (q : ℝ) * ‖v‖)]

private theorem genericChordEnergy_split_crude
    (f : ℕ → ℂ) {a m b : ℕ} (ham : a < m) (hmb : m < b) :
    genericChordEnergy f a b ≤
      2 * (genericChordEnergy f a m + genericChordEnergy f m b) +
        2 * ((b - a : ℕ) : ℝ) *
          ‖genericSignedSiblingResidual f a m b‖ ^ 2 := by
  let c := genericSignedSiblingResidual f a m b
  have hsplit := sum_Ico_split
    (g := fun d => ‖genericSignedSiblingResidual f a d b‖ ^ 2)
    ham.le hmb.le
  unfold genericChordEnergy
  rw [hsplit]
  have hleft :
      (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
        2 * (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
        2 * ((m - a : ℕ) : ℝ) * ‖c‖ ^ 2 := by
    calc
      (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
        ∑ d ∈ Finset.Ico a m,
          (2 * ‖genericSignedSiblingResidual f a d m‖ ^ 2 +
            2 * ‖((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
              apply Finset.sum_le_sum
              intro d hd
              have hdI := Finset.mem_Ico.mp hd
              rw [genericResidual_left_decomposition hdI.1.le hdI.2.le hmb ham]
              exact norm_add_sq_le_two _ _
      _ = 2 * (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
          2 * (∑ d ∈ Finset.Ico a m,
            ‖((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
          2 * ((m - a : ℕ) : ℝ) * ‖c‖ ^ 2 := by
              gcongr
              exact left_tent_energy_le c ham
  have hright :
      (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
        2 * (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
        2 * ((b - m : ℕ) : ℝ) * ‖c‖ ^ 2 := by
    calc
      (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
        ∑ d ∈ Finset.Ico m b,
          (2 * ‖genericSignedSiblingResidual f m d b‖ ^ 2 +
            2 * ‖((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
              apply Finset.sum_le_sum
              intro d hd
              have hdI := Finset.mem_Ico.mp hd
              rw [genericResidual_right_decomposition ham hdI.1.le hdI.2.le hmb]
              exact norm_add_sq_le_two _ _
      _ = 2 * (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
          2 * (∑ d ∈ Finset.Ico m b,
            ‖((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
          2 * ((b - m : ℕ) : ℝ) * ‖c‖ ^ 2 := by
              gcongr
              exact right_tent_energy_le c hmb
  have hwidth :
      ((m - a : ℕ) : ℝ) + ((b - m : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) := by
    push_cast
    have : b - a = (m - a) + (b - m) := by omega
    exact_mod_cast this.symm
  dsimp [c] at hleft hright ⊢
  linarith

private theorem genericChordEnergy_split_weighted
    (f : ℕ → ℂ) (q : ℕ) (hq : 1 ≤ q)
    {a m b : ℕ} (ham : a < m) (hmb : m < b) :
    (q : ℝ) * genericChordEnergy f a b ≤
      ((q + 1 : ℕ) : ℝ) *
          (genericChordEnergy f a m + genericChordEnergy f m b) +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) * ((b - a : ℕ) : ℝ) *
          ‖genericSignedSiblingResidual f a m b‖ ^ 2 := by
  let c := genericSignedSiblingResidual f a m b
  have hsplit := sum_Ico_split
    (g := fun d => ‖genericSignedSiblingResidual f a d b‖ ^ 2)
    ham.le hmb.le
  unfold genericChordEnergy
  rw [hsplit, mul_add]
  have hleft :
      (q : ℝ) * (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
        ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico a m,
          ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
          ((m - a : ℕ) : ℝ) * ‖c‖ ^ 2 := by
    rw [Finset.mul_sum]
    calc
      (∑ d ∈ Finset.Ico a m,
          (q : ℝ) * ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
        ∑ d ∈ Finset.Ico a m,
          (((q + 1 : ℕ) : ℝ) *
              ‖genericSignedSiblingResidual f a d m‖ ^ 2 +
            (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
              ‖((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
                apply Finset.sum_le_sum
                intro d hd
                have hdI := Finset.mem_Ico.mp hd
                rw [genericResidual_left_decomposition hdI.1.le hdI.2.le hmb ham]
                exact weighted_norm_add_sq q hq _ _
      _ = ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico a m,
            ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
          (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
            (∑ d ∈ Finset.Ico a m,
              ‖((((d - a : ℕ) : ℂ) * (((m - a : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                congr 1
                rw [← Finset.mul_sum, ← Finset.mul_sum]
                ring
      _ ≤ ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico a m,
            ‖genericSignedSiblingResidual f a d m‖ ^ 2) +
          (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
            ((m - a : ℕ) : ℝ) * ‖c‖ ^ 2 := by
                gcongr
                exact left_tent_energy_le c ham
  have hright :
      (q : ℝ) * (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
        ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico m b,
          ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
        (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
          ((b - m : ℕ) : ℝ) * ‖c‖ ^ 2 := by
    rw [Finset.mul_sum]
    calc
      (∑ d ∈ Finset.Ico m b,
          (q : ℝ) * ‖genericSignedSiblingResidual f a d b‖ ^ 2) ≤
        ∑ d ∈ Finset.Ico m b,
          (((q + 1 : ℕ) : ℝ) *
              ‖genericSignedSiblingResidual f m d b‖ ^ 2 +
            (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
              ‖((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
                apply Finset.sum_le_sum
                intro d hd
                have hdI := Finset.mem_Ico.mp hd
                rw [genericResidual_right_decomposition ham hdI.1.le hdI.2.le hmb]
                exact weighted_norm_add_sq q hq _ _
      _ = ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico m b,
            ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
          (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
            (∑ d ∈ Finset.Ico m b,
              ‖((((b - d : ℕ) : ℂ) * (((b - m : ℕ) : ℂ)⁻¹)) * c)‖ ^ 2) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                congr 1
                rw [← Finset.mul_sum, ← Finset.mul_sum]
                ring
      _ ≤ ((q + 1 : ℕ) : ℝ) * (∑ d ∈ Finset.Ico m b,
            ‖genericSignedSiblingResidual f m d b‖ ^ 2) +
          (q : ℝ) * ((q + 1 : ℕ) : ℝ) *
            ((b - m : ℕ) : ℝ) * ‖c‖ ^ 2 := by
                gcongr
                exact right_tent_energy_le c hmb
  have hwidth :
      ((m - a : ℕ) : ℝ) + ((b - m : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) := by
    push_cast
    have : b - a = (m - a) + (b - m) := by omega
    exact_mod_cast this.symm
  dsimp [c] at hleft hright ⊢
  linarith

private theorem genericMidpointPacketTreeEnergy_nonneg
    (f : ℕ → ℂ) (depth a b : ℕ) :
    0 ≤ genericMidpointPacketTreeEnergy f depth a b := by
  induction depth generalizing a b with
  | zero => simp [genericMidpointPacketTreeEnergy]
  | succ depth ih =>
      simp only [genericMidpointPacketTreeEnergy]
      split
      · positivity
      · simp

private theorem genericMidpointPacketTreeEnergy_mono_succ
    (f : ℕ → ℂ) (depth a b : ℕ) :
    genericMidpointPacketTreeEnergy f depth a b ≤
      genericMidpointPacketTreeEnergy f (depth + 1) a b := by
  induction depth generalizing a b with
  | zero =>
      simpa [genericMidpointPacketTreeEnergy] using
        genericMidpointPacketTreeEnergy_nonneg f 1 a b
  | succ depth ih =>
      simp only [genericMidpointPacketTreeEnergy]
      by_cases hsplit : a + 1 < b
      · simp [hsplit]
        gcongr
        · exact ih _ _
        · exact ih _ _
      · simp [hsplit]

private theorem genericMidpointPacketTreeEnergy_mono
    (f : ℕ → ℂ) {r s a b : ℕ} (hrs : r ≤ s) :
    genericMidpointPacketTreeEnergy f r a b ≤
      genericMidpointPacketTreeEnergy f s a b := by
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hrs ih =>
      exact ih.trans (genericMidpointPacketTreeEnergy_mono_succ f s a b)

/-- **Deterministic discrete Faber--Schauder frame.**  If the interval width fits
inside `2^depth`, its chord energy is controlled by twice the recursion depth
times the complete midpoint-packet energy. -/
private theorem genericChordEnergy_le_midpointPacketTreeEnergy
    (f : ℕ → ℂ) :
    ∀ (depth a b : ℕ), a ≤ b → b - a ≤ 2 ^ depth →
      genericChordEnergy f a b ≤
        (2 * depth : ℕ) * genericMidpointPacketTreeEnergy f depth a b := by
  intro depth
  induction depth with
  | zero =>
      intro a b hab hwidth
      have hw : b - a ≤ 1 := by simpa using hwidth
      rw [genericChordEnergy_eq_zero_of_width_le_one f hw]
      simp
  | succ depth ih =>
      intro a b hab hwidth
      by_cases hsplit : a + 1 < b
      · let m := dyadicPacketMidpoint a b
        have hm := dyadicPacketMidpoint_facts hsplit
        have hchildren := dyadicPacketMidpoint_child_widths hsplit hwidth
        have hleftIH := ih a m hm.1.le hchildren.1
        have hrightIH := ih m b hm.2.le hchildren.2
        have htree :
            genericMidpointPacketTreeEnergy f (depth + 1) a b =
              ((b - a : ℕ) : ℝ) *
                  ‖genericSignedSiblingResidual f a m b‖ ^ 2 +
                genericMidpointPacketTreeEnergy f depth a m +
                genericMidpointPacketTreeEnergy f depth m b := by
          simp [genericMidpointPacketTreeEnergy, hsplit, m]
        by_cases hdepth : depth = 0
        · subst depth
          have hleft0 : genericChordEnergy f a m = 0 := by
            have := hleftIH
            simp at this
            exact le_antisymm this (by
              unfold genericChordEnergy
              positivity)
          have hright0 : genericChordEnergy f m b = 0 := by
            have := hrightIH
            simp at this
            exact le_antisymm this (by
              unfold genericChordEnergy
              positivity)
          have hcrude := genericChordEnergy_split_crude f hm.1 hm.2
          rw [hleft0, hright0, htree]
          norm_num at hcrude ⊢
          linarith [genericMidpointPacketTreeEnergy_nonneg f 0 a m,
            genericMidpointPacketTreeEnergy_nonneg f 0 m b]
        · have hdpos : 1 ≤ depth := by omega
          have hweighted := genericChordEnergy_split_weighted
            f depth hdpos hm.1 hm.2
          have hdepthR : (0 : ℝ) < depth := by exact_mod_cast (by omega : 0 < depth)
          have hchild :
              genericChordEnergy f a m + genericChordEnergy f m b ≤
                (2 * depth : ℕ) *
                  (genericMidpointPacketTreeEnergy f depth a m +
                    genericMidpointPacketTreeEnergy f depth m b) := by
            push_cast at hleftIH hrightIH ⊢
            linarith
          have hfactor0 : (0 : ℝ) ≤ depth + 1 := by positivity
          have hscaled := mul_le_mul_of_nonneg_left hchild hfactor0
          push_cast at hweighted hscaled ⊢
          rw [htree]
          nlinarith
      · have hw : b - a ≤ 1 := by omega
        rw [genericChordEnergy_eq_zero_of_width_le_one f hw]
        exact mul_nonneg (by positivity)
          (genericMidpointPacketTreeEnergy_nonneg f (depth + 1) a b)

/-! ## Specialization to the signed prime-discrepancy packets -/

private def primeSieveClippedDiscrepancyFunction (y x : ℕ) : ℕ → ℂ :=
  fun d => primeSieveDyadicClippedDiscrepancy y x d

private theorem genericResidual_eq_primeSieveResidual
    (y x a m b : ℕ) :
    genericSignedSiblingResidual (primeSieveClippedDiscrepancyFunction y x) a m b =
      primeSieveSignedSiblingPacketResidual y x a m b := by
  rfl

/-- Recursive midpoint-packet energy of one occupied #322 dyadic block. -/
def primeSieveDyadicPacketTreeBlockEnergy
    (y x j depth : ℕ) : ℝ :=
  genericMidpointPacketTreeEnergy
    (primeSieveClippedDiscrepancyFunction y x) depth
    (primeSieveDyadicBlockLeft j)
    (primeSieveDyadicBlockRight y x j + 1)

/-- Full packet-tree energy: each occupied `j`-block is refined through depth
`j`, enough to reduce its width to unit intervals. -/
def primeSieveDyadicPacketTreeEnergy (y x : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    primeSieveDyadicPacketTreeBlockEnergy y x j j

/-- Shallow packet energy through the first `J` levels of each dyadic block. -/
def primeSieveDyadicPacketShallowEnergy (y x J : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    primeSieveDyadicPacketTreeBlockEnergy y x j (min J j)

/-- Deep packet tail beyond level `J`.  Monotonicity below shows this difference
is nonnegative, so it is an honest tail energy rather than a formal subtraction. -/
def primeSieveDyadicPacketDeepEnergy (y x J : ℕ) : ℝ :=
  primeSieveDyadicPacketTreeEnergy y x -
    primeSieveDyadicPacketShallowEnergy y x J

/-- Exact shallow/deep partition of the recursive packet energy. -/
theorem primeSieveDyadicPacket_shallow_add_deep
    (y x J : ℕ) :
    primeSieveDyadicPacketShallowEnergy y x J +
      primeSieveDyadicPacketDeepEnergy y x J =
        primeSieveDyadicPacketTreeEnergy y x := by
  unfold primeSieveDyadicPacketDeepEnergy
  ring

/-- Shallow energy is bounded by the full recursive packet energy. -/
theorem primeSieveDyadicPacketShallowEnergy_le_treeEnergy
    (y x J : ℕ) :
    primeSieveDyadicPacketShallowEnergy y x J ≤
      primeSieveDyadicPacketTreeEnergy y x := by
  unfold primeSieveDyadicPacketShallowEnergy primeSieveDyadicPacketTreeEnergy
  apply Finset.sum_le_sum
  intro j hj
  exact genericMidpointPacketTreeEnergy_mono
    (primeSieveClippedDiscrepancyFunction y x) (min_le_right J j)

/-- The deep tail is nonnegative. -/
theorem primeSieveDyadicPacketDeepEnergy_nonneg
    (y x J : ℕ) :
    0 ≤ primeSieveDyadicPacketDeepEnergy y x J := by
  unfold primeSieveDyadicPacketDeepEnergy
  exact sub_nonneg.mpr (primeSieveDyadicPacketShallowEnergy_le_treeEnergy y x J)

private theorem primeSieveDyadicBlock_width_le_two_pow
    (y x j : ℕ) :
    primeSieveDyadicBlockRight y x j + 1 -
        primeSieveDyadicBlockLeft j ≤ 2 ^ j := by
  unfold primeSieveDyadicBlockRight primeSieveDyadicBlockLeft
  have hright : min (x / (y + 1)) (2 ^ (j + 1) - 1) + 1 ≤ 2 ^ (j + 1) := by
    have hp : 0 < 2 ^ (j + 1) := by positivity
    omega
  rw [pow_succ] at hright ⊢
  omega

private theorem genericChordEnergy_eq_blockChordEnergy
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    genericChordEnergy (primeSieveClippedDiscrepancyFunction y x)
        (primeSieveDyadicBlockLeft j)
        (primeSieveDyadicBlockRight y x j + 1) =
      ∑ d ∈ primeSieveDyadicBlock y x j,
        ‖primeSieveDyadicChordResidual y x j d‖ ^ 2 := by
  have hset :
      Finset.Ico (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j + 1) =
        primeSieveDyadicBlock y x j := by
    rw [primeSieveDyadicBlock_eq_explicitIcc]
    ext d
    simp
    omega
  unfold genericChordEnergy
  rw [hset]
  apply Finset.sum_congr rfl
  intro d hd
  rw [genericResidual_eq_primeSieveResidual]
  rw [primeSieveDyadicRootPacketResidual_eq_chordResidual hj hd]

/-- Per-block deterministic frame inequality. -/
theorem primeSieveDyadicBlockChordEnergy_le_packetTree
    {y x j : ℕ} (hj : j ∈ primeSieveDyadicBlockIndices y x) :
    (∑ d ∈ primeSieveDyadicBlock y x j,
        ‖primeSieveDyadicChordResidual y x j d‖ ^ 2) ≤
      (2 * j : ℕ) * primeSieveDyadicPacketTreeBlockEnergy y x j j := by
  rw [← genericChordEnergy_eq_blockChordEnergy hj]
  unfold primeSieveDyadicPacketTreeBlockEnergy
  exact genericChordEnergy_le_midpointPacketTreeEnergy
    (primeSieveClippedDiscrepancyFunction y x) j
    (primeSieveDyadicBlockLeft j)
    (primeSieveDyadicBlockRight y x j + 1)
    (by
      have h := primeSieveDyadicBlockLeft_le_right_of_mem_indices hj
      omega)
    (primeSieveDyadicBlock_width_le_two_pow y x j)

/-- Weighted global frame inequality.  The only loss between #322 chord energy
and the recursive packet energy is the logarithmic dyadic depth. -/
theorem primeSieveDyadicChordEnergy_le_weightedPacketTree
    (y x : ℕ) :
    primeSieveDyadicChordEnergy y x ≤
      ∑ j ∈ primeSieveDyadicBlockIndices y x,
        (2 * j : ℕ) * primeSieveDyadicPacketTreeBlockEnergy y x j j := by
  unfold primeSieveDyadicChordEnergy
  apply Finset.sum_le_sum
  intro j hj
  exact primeSieveDyadicBlockChordEnergy_le_packetTree hj

/-! ## Analytic frontier -/

/-- Critical block-uniform shallow packet target.  The cutoff is quantified
uniformly so later finite-wheel/rough transport can choose the useful low-depth
window without changing the downstream statement. -/
def DyadicPacketShallowEnergyBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (J k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveDyadicPacketShallowEnergy
            (primorialPNTPrimeSieveCutoff k) x J ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- Critical block-uniform deep-tail target.  This is the genuinely recursive
analytic premise suggested by the finite packet diagnostics. -/
def DyadicPacketDeepTailBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (J k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveDyadicPacketDeepEnergy
            (primorialPNTPrimeSieveCutoff k) x J ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- Combined shallow and deep estimates control the unweighted recursive packet
energy at critical scale. -/
theorem dyadicPacketTreeEnergyBlockBounded_of_shallow_deep
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement)
    (hT : DyadicPacketDeepTailBlockBoundedStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (J k x : ℕ),
          2 ≤ k →
          primorialBlockLower k ≤ x →
          x ≤ primorialBlockUpper k →
          primeSieveDyadicPacketTreeEnergy
              (primorialPNTPrimeSieveCutoff k) x ≤
            C * Real.rpow ((x : ℝ) + 1) (1 + ε) := by
  intro ε hε
  obtain ⟨CS, hCS, hSb⟩ := hS ε hε
  obtain ⟨CT, hCT, hTb⟩ := hT ε hε
  refine ⟨CS + CT, add_nonneg hCS hCT, ?_⟩
  intro J k x hk hlow hup
  have hs := hSb J k x hk hlow hup
  have ht := hTb J k x hk hlow hup
  rw [← primeSieveDyadicPacket_shallow_add_deep
    (primorialPNTPrimeSieveCutoff k) x J]
  nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (x : ℝ) + 1) (1 + ε)]

/-- The remaining deterministic conversion needed by the terminal theorem: a
critical unweighted packet-tree estimate implies the #323 root-packet estimate.
The logarithmic depth loss is absorbed into the arbitrary epsilon allowance. -/
def DyadicPacketTreeToRootCriticalTransfer : Prop :=
  (∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (k x : ℕ),
          2 ≤ k →
          primorialBlockLower k ≤ x →
          x ≤ primorialBlockUpper k →
          primeSieveDyadicPacketTreeEnergy
              (primorialPNTPrimeSieveCutoff k) x ≤
            C * Real.rpow ((x : ℝ) + 1) (1 + ε)) →
    DyadicSignedRootPacketEnergyBlockBoundedStatement

/-- Terminal shallow/deep reduction.  The only open estimates named by this
module are the shallow and deep packet bounds; `hFrame` is the deterministic
logarithmic-depth absorption interface isolated above. -/
theorem riemannHypothesis_of_dyadicPacketShallowDeepAnalyticPackage
    (hC : DyadicCoherentChannelRHScale)
    (hS : DyadicPacketShallowEnergyBlockBoundedStatement)
    (hT : DyadicPacketDeepTailBlockBoundedStatement)
    (hFrame : DyadicPacketTreeToRootCriticalTransfer)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_dyadicSignedPacketAnalyticPackage hC
  · apply hFrame
    intro ε hε
    obtain ⟨C, hC0, hCb⟩ :=
      dyadicPacketTreeEnergyBlockBounded_of_shallow_deep hS hT ε hε
    refine ⟨C, hC0, ?_⟩
    intro k x hk hlow hup
    exact hCb 0 k x hk hlow hup
  · exact hD

end RHLean.Analysis
