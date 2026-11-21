import Mathlib

/-!
# A native integral-lattice C-to-R certificate

This is the exact *integer* realification (a,b) -> (a-b,a+b).
It proves parity image, finite Gram transport, determinant (wedge) cost,
integral divisibility both ways, and height at arbitrary multiplicity.
It does NOT prove Alpoge's original theta DIV/SlopeIneq/covolume input.
-/

noncomputable section
open Finset

namespace RHLean.Geometry

def integralCR (v : ℤ × ℤ) : ℤ × ℤ :=
  (v.1 - v.2, v.1 + v.2)

def integralDot (v w : ℤ × ℤ) : ℤ :=
  v.1 * w.1 + v.2 * w.2

def integralWedge (v w : ℤ × ℤ) : ℤ :=
  v.1 * w.2 - v.2 * w.1

def integralHeight (v : ℤ × ℤ) : ℤ :=
  |v.1| + |v.2|

theorem integralCR_add (v w : ℤ × ℤ) :
    integralCR (v + w) = integralCR v + integralCR w := by
  rcases v with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  apply Prod.ext <;> simp [integralCR] <;> ring

/-- Full image equals the parity sublattice. No arbitrary real targets. -/
theorem integralCR_range_iff (v : ℤ × ℤ) :
    (∃ w : ℤ × ℤ, integralCR w = v) ↔
      ∃ a : ℤ, v.1 + v.2 = 2 * a := by
  rcases v with ⟨u,w⟩
  constructor
  · rintro ⟨⟨a,b⟩,h⟩
    have h1 : a - b = u := congrArg Prod.fst h
    have h2 : a + b = w := congrArg Prod.snd h
    exact ⟨a, by omega⟩
  · rintro ⟨a,ha⟩
    refine ⟨(a,w-a), ?_⟩
    apply Prod.ext
    · change a - (w-a) = u
      omega
    · change a + (w-a) = w
      omega

theorem integralCR_injective : Function.Injective integralCR := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have h1 : a - b = c - d := congrArg Prod.fst h
  have h2 : a + b = c + d := congrArg Prod.snd h
  have ha : a = c := by omega
  have hb : b = d := by omega
  simp [ha, hb]

/-- Exact 2-dimensional determinant factor on every integer frame. -/
theorem integralCR_wedge (v w : ℤ × ℤ) :
    integralWedge (integralCR v) (integralCR w) =
      2 * integralWedge v w := by
  rcases v with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  simp only [integralWedge, integralCR]
  ring

/-- The normalized real Gram pairing is exactly the original one. -/
theorem integralCR_dot (v w : ℤ × ℤ) :
    integralDot (integralCR v) (integralCR w) =
      2 * integralDot v w := by
  rcases v with ⟨a,b⟩
  rcases w with ⟨c,d⟩
  simp only [integralDot, integralCR]
  ring

theorem integralCR_div_forward (d : ℤ) (v : ℤ × ℤ)
    (h1 : d ∣ v.1) (h2 : d ∣ v.2) :
    d ∣ (integralCR v).1 ∧ d ∣ (integralCR v).2 := by
  dsimp [integralCR]
  exact ⟨dvd_sub h1 h2, dvd_add h1 h2⟩

/-- The reverse integral transport costs exactly a factor 2.
This is essential at ramified/dyadic places. -/
theorem integralCR_div_reverse_two (d : ℤ) (v : ℤ × ℤ)
    (h1 : d ∣ (integralCR v).1)
    (h2 : d ∣ (integralCR v).2) :
    d ∣ 2 * v.1 ∧ d ∣ 2 * v.2 := by
  have hs : d ∣ (integralCR v).1 + (integralCR v).2 :=
    dvd_add h1 h2
  have ht : d ∣ (integralCR v).2 - (integralCR v).1 :=
    dvd_sub h2 h1
  have heq1 : (integralCR v).1 + (integralCR v).2 =
      2 * v.1 := by
    simp only [integralCR]
    ring
  have heq2 : (integralCR v).2 - (integralCR v).1 =
      2 * v.2 := by
    simp only [integralCR]
    ring
  rw [heq1] at hs
  rw [heq2] at ht
  exact ⟨hs, ht⟩

theorem integralCR_height_le (v : ℤ × ℤ) :
    integralHeight (integralCR v) ≤
      2 * integralHeight v := by
  have h1 : |v.1 - v.2| ≤ |v.1| + |v.2| := by
    simpa [sub_eq_add_neg] using (abs_add_le v.1 (-v.2))
  have h2 : |v.1 + v.2| ≤ |v.1| + |v.2| := abs_add_le _ _
  dsimp [integralHeight, integralCR]
  omega

/-- Arbitrary multiplicity frame; all rows preserved, no dropped signs. -/
def integralCRFrame {m : ℕ} (v : Fin m → ℤ × ℤ) :
    Fin m → ℤ × ℤ :=
  fun i => integralCR (v i)

theorem integralCRFrame_range_iff (m : ℕ)
    (v : Fin m → ℤ × ℤ) :
    (∃ w : Fin m → ℤ × ℤ, integralCRFrame w = v) ↔
      ∀ i : Fin m, ∃ a : ℤ, (v i).1 + (v i).2 = 2 * a := by
  constructor
  · rintro ⟨w,hw⟩ i
    have hi : integralCR (w i) = v i := congrFun hw i
    exact (integralCR_range_iff (v i)).mp ⟨w i,hi⟩
  · intro hv
    classical
    let h (i : Fin m) : ∃ w : ℤ × ℤ, integralCR w = v i :=
      (integralCR_range_iff (v i)).mpr (hv i)
    let w : Fin m → ℤ × ℤ := fun i => Classical.choose (h i)
    refine ⟨w, ?_⟩
    funext i
    exact Classical.choose_spec (h i)

theorem integralCRFrame_gram (m : ℕ)
    (v w : Fin m → ℤ × ℤ) :
    (∑ i : Fin m, integralDot (integralCR (v i)) (integralCR (w i))) =
      2 * ∑ i : Fin m, integralDot (v i) (w i) := by
  calc
    _ = ∑ i : Fin m, 2 * integralDot (v i) (w i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact integralCR_dot (v i) (w i)
    _ = _ := by rw [Finset.mul_sum]

theorem integralCRFrame_height (m : ℕ)
    (v : Fin m → ℤ × ℤ) :
    (∑ i : Fin m, integralHeight (integralCR (v i))) ≤
      2 * ∑ i : Fin m, integralHeight (v i) := by
  calc
    _ ≤ ∑ i : Fin m, 2 * integralHeight (v i) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact integralCR_height_le (v i)
    _ = _ := by rw [Finset.mul_sum]

/-- Intrinsic m-fold parity index has logarithmic scale m log 2.
The index statement itself follows from the proved parity-image
description; the full quotient-index formalization is separate. -/
theorem integralCRFrame_log_two (m : ℕ) :
    Real.log ((2 : ℝ) ^ m) = (m : ℝ) * Real.log 2 := by
  rw [Real.log_pow]

/-- One checked transport certificate. The source's integral divisor
evidence is a REAL obligation, not an assumed theta-lift theorem. -/
structure NativeIntegralLatticeCertificate (m : ℕ) where
  source : Fin m → ℤ × ℤ
  divisor : ℤ
  source_divisible : ∀ i : Fin m,
    divisor ∣ (source i).1 ∧ divisor ∣ (source i).2

theorem NativeIntegralLatticeCertificate.forward_divisibility
    {m : ℕ} (C : NativeIntegralLatticeCertificate m)
    (i : Fin m) :
    C.divisor ∣ (integralCR (C.source i)).1 ∧
      C.divisor ∣ (integralCR (C.source i)).2 :=
  integralCR_div_forward C.divisor (C.source i)
    (C.source_divisible i).1 (C.source_divisible i).2

theorem NativeIntegralLatticeCertificate.gram
    {m : ℕ} (C : NativeIntegralLatticeCertificate m) :
    (∑ i : Fin m,
      integralDot (integralCR (C.source i))
        (integralCR (C.source i))) =
      2 * ∑ i : Fin m,
        integralDot (C.source i) (C.source i) :=
  integralCRFrame_gram m C.source C.source

theorem NativeIntegralLatticeCertificate.height
    {m : ℕ} (C : NativeIntegralLatticeCertificate m) :
    (∑ i : Fin m, integralHeight (integralCR (C.source i))) ≤
      2 * ∑ i : Fin m, integralHeight (C.source i) :=
  integralCRFrame_height m C.source

/-! ## Arithmetic coordinate transport over actual number fields

The preceding integer certificate is not automatically a certificate for
an arbitrary number-field embedding. The integral basis is the necessary
restriction-of-scalars link. No unproved theta-lift or height theorem enters.
-/

open NumberField

/-- Exact commutation of the integral-basis coefficient map with the
same C-to-R transform, for the ring of integers of ANY number field K.
This is the actual arithmetic restriction-of-scalars map, not an
assumption that Re/Im of an algebraic integer are ordinary integers. -/
theorem integralCR_ringOfIntegers_basis
    (K : Type*) [Field K] [NumberField K]
    (a b : 𝓞 K) (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (((RingOfIntegers.basis K).repr (a - b)) i,
      ((RingOfIntegers.basis K).repr (a + b)) i) =
      integralCR
        (((RingOfIntegers.basis K).repr a) i,
          ((RingOfIntegers.basis K).repr b) i) := by
  apply Prod.ext
  · change ((RingOfIntegers.basis K).repr (a - b)) i =
        ((RingOfIntegers.basis K).repr a) i -
          ((RingOfIntegers.basis K).repr b) i
    simp
  · change ((RingOfIntegers.basis K).repr (a + b)) i =
        ((RingOfIntegers.basis K).repr a) i +
          ((RingOfIntegers.basis K).repr b) i
    simp

/-- Genuine m-slot number-field integral-basis frame.
Each coefficient is integral by construction; no imaginary-part
integrality assertion is needed. -/
def numberFieldIntegralFrame
    (K : Type*) [Field K] [NumberField K]
    {m : ℕ} (a b : Fin m → 𝓞 K)
    (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    Fin m → ℤ × ℤ :=
  fun j => (((RingOfIntegers.basis K).repr (a j)) i,
    ((RingOfIntegers.basis K).repr (b j)) i)

/-- The full m-frame commutes with restriction of scalars coefficientwise. -/
theorem numberFieldIntegralFrame_CR
    (K : Type*) [Field K] [NumberField K]
    {m : ℕ} (a b : Fin m → 𝓞 K)
    (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    numberFieldIntegralFrame K
      (fun j => a j - b j) (fun j => a j + b j) i =
        integralCRFrame (numberFieldIntegralFrame K a b i) := by
  funext j
  exact integralCR_ringOfIntegers_basis K (a j) (b j) i

/-- The exact logarithmic scale of the 2^(m*d) coefficient-index factor.
It has NOT been identified with Alpoge's normalized number-field covolume
until the source-specific rank and embedding metrics are verified. -/
theorem numberFieldIntegralFrame_log_two_cost (m d : ℕ) :
    Real.log ((2 : ℝ) ^ (m * d)) =
      (m : ℝ) * (d : ℝ) * Real.log 2 := by
  rw [Real.log_pow]
  push_cast
  ring

end RHLean.Geometry
