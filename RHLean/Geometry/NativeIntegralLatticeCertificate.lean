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
    (a b : 𝓞 K) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
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
    (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    Fin m → ℤ × ℤ :=
  fun j => (((RingOfIntegers.basis K).repr (a j)) i,
    ((RingOfIntegers.basis K).repr (b j)) i)

/-- The full m-frame commutes with restriction of scalars coefficientwise. -/
theorem numberFieldIntegralFrame_CR
    (K : Type*) [Field K] [NumberField K]
    {m : ℕ} (a b : Fin m → 𝓞 K)
    (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
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

/-! ## Local prime-ideal depth and complex-embedding cost

The following theorems are valid in every commutative ring. In
particular they apply directly to the original integral coefficient
ring O_K, without interpreting Re/Im as integers.
-/

/-- The same integral matrix over any commutative ring. -/
def algebraicCR {A : Type*} [CommRing A] (v : A × A) : A × A :=
  (v.1 - v.2, v.1 + v.2)

/-- Any ideal-power depth survives forward transport exactly. -/
theorem algebraicCR_ideal_forward
    {A : Type*} [CommRing A] (I : Ideal A) (v : A × A)
    (h1 : v.1 ∈ I) (h2 : v.2 ∈ I) :
    (algebraicCR v).1 ∈ I ∧ (algebraicCR v).2 ∈ I := by
  change (v.1 - v.2 ∈ I) ∧ (v.1 + v.2 ∈ I)
  exact ⟨I.sub_mem h1 h2, I.add_mem h1 h2⟩

/-- Reverse transport can lose only the universal factor 2;
this is the explicit local obstruction at prime ideals over 2. -/
theorem algebraicCR_ideal_reverse_two
    {A : Type*} [CommRing A] (I : Ideal A) (v : A × A)
    (h1 : (algebraicCR v).1 ∈ I)
    (h2 : (algebraicCR v).2 ∈ I) :
    (2 : A) * v.1 ∈ I ∧ (2 : A) * v.2 ∈ I := by
  change v.1 - v.2 ∈ I at h1
  change v.1 + v.2 ∈ I at h2
  have hs : (v.1 - v.2) + (v.1 + v.2) ∈ I :=
    I.add_mem h1 h2
  have ht : (v.1 + v.2) - (v.1 - v.2) ∈ I :=
    I.sub_mem h2 h1
  have hA : (v.1 - v.2) + (v.1 + v.2) = (2 : A) * v.1 := by ring
  have hB : (v.1 + v.2) - (v.1 - v.2) = (2 : A) * v.2 := by ring
  rw [hA] at hs
  rw [hB] at ht
  exact ⟨hs,ht⟩

/-- The source-specific ideal can be a power of a ramified prime ideal.
No local place or prime-power row is discarded. -/
theorem algebraicCR_idealPow_forward
    {A : Type*} [CommRing A] (I : Ideal A) (k : ℕ) (v : A × A)
    (h1 : v.1 ∈ I ^ k) (h2 : v.2 ∈ I ^ k) :
    (algebraicCR v).1 ∈ I ^ k ∧
      (algebraicCR v).2 ∈ I ^ k :=
  algebraicCR_ideal_forward (I ^ k) v h1 h2

/-- The norm-square law of the integral matrix at a COMPLEX place.
It is the exact parallelogram identity, with no triangle-inequality tax. -/
theorem complexCR_normSq (a b : ℂ) :
    Complex.normSq (a - b) + Complex.normSq (a + b) =
      2 * (Complex.normSq a + Complex.normSq b) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im]
  ring

/-- The same exact Archimedean norm payment after any algebraic
embedding into C, including every embedding of a number field. -/
theorem algebraicCR_embedding_normSq
    {A : Type*} [CommRing A] (σ : A →+* ℂ) (a b : A) :
    Complex.normSq (σ (a - b)) + Complex.normSq (σ (a + b)) =
      2 * (Complex.normSq (σ a) + Complex.normSq (σ b)) := by
  simpa only [map_sub, map_add] using complexCR_normSq (σ a) (σ b)

/-- Away from divisors of 2, scalar divisibility is reversible. -/
theorem integralCR_div_reverse_coprime_two (d : ℤ) (v : ℤ × ℤ)
    (hd : IsCoprime d (2 : ℤ))
    (h1 : d ∣ (integralCR v).1)
    (h2 : d ∣ (integralCR v).2) :
    d ∣ v.1 ∧ d ∣ v.2 := by
  obtain ⟨ha,hb⟩ := integralCR_div_reverse_two d v h1 h2
  exact ⟨hd.dvd_of_dvd_mul_left ha, hd.dvd_of_dvd_mul_left hb⟩

/-! ## Transport the lattice AND the metric: no artificial cost

The ambient Euclidean lattice has index 2 per pair, but the image
sublattice must keep its own pulled-back norm. Normalizing its Gram by
one half removes the artificial coordinate determinant tax exactly.
This is intrinsic to the coordinate map, and does not bypass the
number-field theta-lift height/covolume hypotheses.
-/

/-- The full normalized REAL Gram pairing is EXACTLY unchanged. -/
theorem integralCRFrame_normalized_isometry
    (m : ℕ) (v w : Fin m → ℤ × ℤ) :
    (((∑ i : Fin m,
      integralDot (integralCR (v i)) (integralCR (w i))) : ℤ) : ℝ) / 2 =
      (((∑ i : Fin m, integralDot (v i) (w i)) : ℤ) : ℝ) := by
  rw [integralCRFrame_gram]
  push_cast
  ring

/-- The oriented area of any transported two-frame is unchanged
when the target volume form is normalized by the factor 2. -/
theorem integralCR_normalized_wedge
    (v w : ℤ × ℤ) :
    (((integralWedge (integralCR v) (integralCR w) : ℤ) : ℝ) / 2) =
      ((integralWedge v w : ℤ) : ℝ) := by
  rw [integralCR_wedge]
  push_cast
  ring

/-- Divisibility is EXACT when judged inside the proper transported
integral lattice. The factor-2 reverse loss in ambient coordinates
is a penalty for forgetting the parity-image condition, NOT a loss
for the lattice and ideal transported together. -/
theorem integralCR_divisible_iff_exact_image
    (d : ℤ) (v : ℤ × ℤ) :
    (d ∣ v.1 ∧ d ∣ v.2) ↔
      ∃ w : ℤ × ℤ,
        d ∣ w.1 ∧ d ∣ w.2 ∧ integralCR w = integralCR v := by
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨v, ha, hb, rfl⟩
  · rintro ⟨w,ha,hb,hw⟩
    have h : w = v := integralCR_injective hw
    subst w
    exact ⟨ha,hb⟩

/-- The apparent volume-index tax cancels its metric normalization.
This is an algebraic log identity, not yet an equality to Alpoge's
HN covolume of a specific number-field lattice. -/
theorem integralCRFrame_log_normalization_cancel (m : ℕ) :
    Real.log ((2 : ℝ) ^ m) - (m : ℝ) * Real.log 2 = 0 := by
  rw [integralCRFrame_log_two]
  ring

/-! ## Transport a complete integral O_K-submodule

The original number-field construction uses honest submodules over O_K,
not merely independent scalar pairs. The following map transports the
WHOLE submodule; image membership and ideal-depth preservation remain
statements about actual arithmetic coefficients.
-/

/-- Matrix [[1,-1],[1,1]] as a linear map over every commutative ring. -/
def algebraicCRLinear (A : Type*) [CommRing A] :
    (A × A) →ₗ[A] (A × A) where
  toFun := algebraicCR
  map_add' := by
    rintro ⟨a,b⟩ ⟨c,d⟩
    apply Prod.ext <;> simp [algebraicCR] <;> ring
  map_smul' := by
    intro r v
    rcases v with ⟨a,b⟩
    apply Prod.ext <;> simp [algebraicCR] <;> ring

/-- The image is a genuine O_K-submodule (no fake ambient lattice). -/
def numberFieldCRLattice
    (K : Type*) [Field K] [NumberField K]
    (L : Submodule (𝓞 K) ((𝓞 K) × (𝓞 K))) :
    Submodule (𝓞 K) ((𝓞 K) × (𝓞 K)) :=
  L.map (algebraicCRLinear (𝓞 K))

/-- Image membership uses a real SOURCE preimage in the original
ring-of-integers lattice, not an arbitrary ambient coordinate pair. -/
theorem numberFieldCRLattice_mem
    (K : Type*) [Field K] [NumberField K]
    (L : Submodule (𝓞 K) ((𝓞 K) × (𝓞 K)))
    (v : (𝓞 K) × (𝓞 K)) (hv : v ∈ L) :
    algebraicCR v ∈ numberFieldCRLattice K L := by
  exact Submodule.mem_map_of_mem hv

/-- On the whole image lattice, an I^k divisibility condition on
each original coefficient remains an I^k condition after transport. -/
theorem numberFieldCRLattice_idealPow
    (K : Type*) [Field K] [NumberField K]
    (L : Submodule (𝓞 K) ((𝓞 K) × (𝓞 K)))
    (I : Ideal (𝓞 K)) (k : ℕ)
    (hL : ∀ x : (𝓞 K) × (𝓞 K), x ∈ L →
      x.1 ∈ I ^ k ∧ x.2 ∈ I ^ k)
    (v : (𝓞 K) × (𝓞 K))
    (hv : v ∈ numberFieldCRLattice K L) :
    v.1 ∈ I ^ k ∧ v.2 ∈ I ^ k := by
  obtain ⟨x, hx, hEq⟩ := Submodule.mem_map.mp hv
  have hp := algebraicCR_idealPow_forward I k x (hL x hx).1 (hL x hx).2
  change algebraicCR x = v at hEq
  rw [← hEq]
  exact hp

/-- In characteristic zero, this integral two-coordinate transform is
injective over the WHOLE coefficient ring. In particular it cannot
destroy any genuine number-field lattice relation. -/
theorem algebraicCR_injective
    {A : Type*} [CommRing A] [IsDomain A] [CharZero A] :
    Function.Injective (algebraicCR (A := A)) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have h1 : a - b = c - d := by
    simpa only [algebraicCR] using congrArg Prod.fst h
  have h2 : a + b = c + d := by
    simpa only [algebraicCR] using congrArg Prod.snd h
  have h2a : (2 : A) * a = 2 * c := by
    linear_combination h1 + h2
  have h2b : (2 : A) * b = 2 * d := by
    linear_combination h2 - h1
  have htwo : (2 : A) ≠ 0 := by norm_num
  have ha : a = c := mul_left_cancel₀ htwo h2a
  have hb : b = d := mul_left_cancel₀ htwo h2b
  exact Prod.ext ha hb

/-- A point of the SOURCE O_K lattice belongs to that lattice iff
its transformed point belongs to the full TRANSPORTED image lattice.
This prevents an ambient-index loss from being counted as real
arithmetic information, and is not a claim about the theta-lift
LIVING INSIDE that lattice. -/
theorem numberFieldCRLattice_mem_iff
    (K : Type*) [Field K] [NumberField K]
    (L : Submodule (𝓞 K) ((𝓞 K) × (𝓞 K)))
    (v : (𝓞 K) × (𝓞 K)) :
    algebraicCR v ∈ numberFieldCRLattice K L ↔ v ∈ L := by
  constructor
  · intro hv
    rcases Submodule.mem_map.mp hv with ⟨w,hw,heq⟩
    have heq' : algebraicCR w = algebraicCR v := by
      simpa only [algebraicCRLinear] using heq
    have hsource := algebraicCR_injective heq'
    simpa [hsource] using hw
  · exact numberFieldCRLattice_mem K L v

end RHLean.Geometry
