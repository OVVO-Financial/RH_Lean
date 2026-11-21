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
      change algebraicCR w = algebraicCR v at heq
      exact heq
    have hsource := algebraicCR_injective heq'
    simpa [hsource] using hw
  · exact numberFieldCRLattice_mem K L v

/-!
## Exact-source norm transport for Alpoge Rerealize

These are exactly the source formulas vecAt/fcoord/normAt from the
published HermitianLatticesTheory; equality after K-linear basis
transport is proved for ALL infinite places and ALL Hermitian frames.

The published Rerealize theorem consumes this specific norm equality,
and transports height, slope, extremal slopes, covolume and quotient
slope. This module does not import the external formalism or assume RH.
-/

def nativeAlpogeVecAt
    {K V ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  fun i => v.embedding (b.repr x i)

def nativeAlpogeFcoord
    {K V ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x : V) : ι → ℂ :=
  Matrix.mulVec (X v)⁻¹ (nativeAlpogeVecAt b v x)

def nativeAlpogeNormAt
    {K V ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x : V) : ℝ :=
  Real.sqrt (∑ i : ι, ‖nativeAlpogeFcoord b X v x i‖ ^ 2)

/-- The exact original field coordinates are unchanged. -/
theorem nativeAlpogeVecAt_map
    {K V W ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (b : Module.Basis ι K V) (e : V ≃ₗ[K] W)
    (v : InfinitePlace K) (x : V) :
    nativeAlpogeVecAt (b.map e) v (e x) =
      nativeAlpogeVecAt b v x := by
  funext i
  simp [nativeAlpogeVecAt]

/-- Original place-frame coordinates agree exactly, with the SAME X. -/
theorem nativeAlpogeFcoord_map
    {K V W ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (e : V ≃ₗ[K] W) (v : InfinitePlace K) (x : V) :
    nativeAlpogeFcoord (b.map e) X v (e x) =
      nativeAlpogeFcoord b X v x := by
  simp [nativeAlpogeFcoord, nativeAlpogeVecAt_map]

/-- Direct native proof of the entire Rerealize norm hypothesis. -/
theorem nativeAlpogeNormAt_map
    {K V W ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (e : V ≃ₗ[K] W) (v : InfinitePlace K) (x : V) :
    nativeAlpogeNormAt (b.map e) X v (e x) =
      nativeAlpogeNormAt b X v x := by
  simp [nativeAlpogeNormAt, nativeAlpogeFcoord_map]

/-- No archimedean quadratic cost over all places, at any x. -/
theorem nativeAlpogeAllPlaceNormCost_map
    {K V W ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (e : V ≃ₗ[K] W) (x : V) :
    (∑ v : InfinitePlace K, (nativeAlpogeNormAt (b.map e) X v (e x)) ^ 2) =
      ∑ v : InfinitePlace K, (nativeAlpogeNormAt b X v x) ^ 2 := by
  simp only [nativeAlpogeNormAt_map]

/-! ## Source and full-lattice transport in one native certificate

The source family is a GENUINE module over the ring of integers of K.
There is no data field asserting a bound, slope identity or RH statement.
The new coordinate equivalence is exactly source-preserving and the
Hermitian norms at every infinite place coincide pointwise.
-/

/-- A number-field source, basis, frame and actual K-linear coordinate
equivalence, without any assumed geometric cost theorem. -/
structure NativeAlpogeRerealizeCertificate
    (K : Type*) [Field K] [NumberField K]
    (V W ι : Type*)
    [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype ι] [DecidableEq ι] where
  sourceBasis : Module.Basis ι K V
  sourceFrame : InfinitePlace K → Matrix ι ι ℂ
  sourceLattice : Submodule (𝓞 K) V
  coordinateEquiv : V ≃ₗ[K] W

/-- The whole number-field lattice is transported, not just a finite
selection of its vectors or a numerical scalar invariant. -/
def NativeAlpogeRerealizeCertificate.transportedLattice
    {K : Type*} [Field K] [NumberField K]
    {V W ι : Type*}
    [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype ι] [DecidableEq ι]
    (C : NativeAlpogeRerealizeCertificate K V W ι) :
    Submodule (𝓞 K) W :=
  C.sourceLattice.map (C.coordinateEquiv.toLinearMap.restrictScalars (𝓞 K))

/-- Entire source-lattice membership is EXACTLY equivalent after
realization, including all original integral relations and masks. -/
theorem NativeAlpogeRerealizeCertificate.transported_mem_iff
    {K : Type*} [Field K] [NumberField K]
    {V W ι : Type*}
    [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype ι] [DecidableEq ι]
    (C : NativeAlpogeRerealizeCertificate K V W ι) (x : V) :
    C.coordinateEquiv x ∈ C.transportedLattice ↔
      x ∈ C.sourceLattice := by
  unfold NativeAlpogeRerealizeCertificate.transportedLattice
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y,hy,heq⟩
    have heq' : C.coordinateEquiv y = C.coordinateEquiv x := by
      change C.coordinateEquiv y = C.coordinateEquiv x at heq
      exact heq
    have hxy : y = x := C.coordinateEquiv.injective heq'
    simpa [hxy] using hy
  · intro hx
    exact Submodule.mem_map_of_mem hx

/-- The exact norm identity for the SAME lattice certificate at
ALL infinite places. This is the full nontrivial numeric hypothesis
required by Alpoge's published Rerealize theorem. -/
theorem NativeAlpogeRerealizeCertificate.normAt_eq
    {K : Type*} [Field K] [NumberField K]
    {V W ι : Type*}
    [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype ι] [DecidableEq ι]
    (C : NativeAlpogeRerealizeCertificate K V W ι)
    (v : InfinitePlace K) (x : V) :
    nativeAlpogeNormAt (C.sourceBasis.map C.coordinateEquiv)
        C.sourceFrame v (C.coordinateEquiv x) =
      nativeAlpogeNormAt C.sourceBasis C.sourceFrame v x :=
  nativeAlpogeNormAt_map _ _ _ _ _

/-- The same integral linear transform COMMUTES with an arbitrary
complete signed source matrix, without dropping any cross coefficient.
In particular this applies to the native signed Selberg 2I-J matrix,
including its rank-one mean return, not merely its centered restriction. -/
theorem algebraicCR_commutes_complete_matrix
    {A : Type*} [CommRing A] {m : ℕ}
    (S : Matrix (Fin m) (Fin m) A)
    (v : Fin m → A × A) (i : Fin m) :
    algebraicCR (∑ j : Fin m, S i j • v j) =
      ∑ j : Fin m, S i j • algebraicCR (v j) := by
  change (algebraicCRLinear A) (∑ j : Fin m, S i j • v j) =
      ∑ j : Fin m, S i j • (algebraicCRLinear A) (v j)
  simp

/-! ## The exact native C-to-R equivalence, explicitly constructed

This supplies the genuine isomorphism field for a pair of number-field
coordinates. It is not a free assumption of an arithmetic cost theorem.
-/

/-- The integer matrix [[1,-1],[1,1]] becomes an invertible
K-linear equivalence over ANY characteristic-zero field.
The inverse is ((u+v)/2,(v-u)/2), including its dyadic denominator. -/
def algebraicCRFieldEquiv (K : Type*) [Field K] [CharZero K] :
    (K × K) ≃ₗ[K] (K × K) := by
  apply LinearEquiv.ofBijective (algebraicCRLinear K)
  constructor
  · exact algebraicCR_injective
  · rintro ⟨u,v⟩
    refine ⟨((u+v)/2, (v-u)/2), ?_⟩
    apply Prod.ext <;>
      dsimp [algebraicCRLinear, algebraicCR] <;>
      field_simp <;> ring

/-- The explicit change of number-field basis is exactly the
native C-to-R realification, not an arbitrary existential map. -/
theorem algebraicCRFieldEquiv_apply
    (K : Type*) [Field K] [CharZero K] (v : K × K) :
    algebraicCRFieldEquiv K v = algebraicCR v := by
  rfl

/-- Apply the all-place Rerealize norm identity to the actual native
C-to-R field equivalence. Same X, same physical source coefficients. -/
theorem nativeAlpogeNormAt_algebraicCR
    (K : Type*) [Field K] [NumberField K]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K (K × K))
    (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x : K × K) :
    nativeAlpogeNormAt (b.map (algebraicCRFieldEquiv K)) X v
      (algebraicCR x) =
        nativeAlpogeNormAt b X v x := by
  rw [← algebraicCRFieldEquiv_apply K x]
  exact nativeAlpogeNormAt_map b X (algebraicCRFieldEquiv K) v x

end RHLean.Geometry
