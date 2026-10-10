import Mathlib

/-!
# Exact principal coefficient map with the original exclusions

All products of ArithmeticFunction below are Dirichlet convolutions.
The norm coefficient is constructed as mu * (chi *pointwise* mu), and its
prime-to-six restriction is constructed, not postulated.  The full restored
coefficient identity is proved for the actual Mathlib integer Mobius function.
Its identification with Mobius on Eisenstein ideals is a separate semantic
obligation; no ideal splitting theorem or OpenAI analytic theorem is imported.

The finite physical-weight consumer retains arbitrary complex weights.  The
periodic quotient kernel is deterministic: its mean zero is not a bound on
its signed pairing with the norm coefficients.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

@[simp] theorem vf919ArithmeticFunction_sub_apply
    (f g : ArithmeticFunction ℂ) (n : ℕ) : (f - g) n = f n - g n := rfl

def vf919ChiMinusThree (n : ℕ) : ℂ :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1

theorem vf919ChiMinusThree_mul (m n : ℕ) :
    vf919ChiMinusThree (m * n) = vf919ChiMinusThree m * vf919ChiMinusThree n := by
  have hm := Nat.mod_lt m (by decide : 0 < 3)
  have hn := Nat.mod_lt n (by decide : 0 < 3)
  interval_cases h₁ : m % 3 <;> interval_cases h₂ : n % 3 <;>
    norm_num [vf919ChiMinusThree, Nat.mul_mod, h₁, h₂]

def vf919PrimeToSixMask (n : ℕ) : ℂ :=
  if 2 ∣ n ∨ 3 ∣ n then 0 else 1

theorem vf919PrimeToSixMask_mul (m n : ℕ) :
    vf919PrimeToSixMask (m * n) =
      vf919PrimeToSixMask m * vf919PrimeToSixMask n := by
  by_cases h₂m : 2 ∣ m <;> by_cases h₃m : 3 ∣ m <;>
    by_cases h₂n : 2 ∣ n <;> by_cases h₃n : 3 ∣ n <;>
    simp [vf919PrimeToSixMask, Nat.prime_two.dvd_mul,
      (by decide : Nat.Prime 3).dvd_mul, h₂m, h₃m, h₂n, h₃n]

def vf919ArithmeticTwist (g : ℕ → ℂ) (f : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ := ⟨fun n => g n * f n, by simp⟩

theorem vf919ArithmeticTwist_mul (g : ℕ → ℂ)
    (hg : ∀ m n, g (m * n) = g m * g n)
    (f h : ArithmeticFunction ℂ) :
    vf919ArithmeticTwist g (f * h) =
      vf919ArithmeticTwist g f * vf919ArithmeticTwist g h := by
  ext n
  simp only [vf919ArithmeticTwist, ArithmeticFunction.coe_mk,
    ArithmeticFunction.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
  rw [← hprod, hg]
  ring

theorem vf919ArithmeticTwist_one (g : ℕ → ℂ) (hg : g 1 = 1) :
    vf919ArithmeticTwist g 1 = 1 := by
  ext n
  by_cases hn : n = 1 <;>
    simp [vf919ArithmeticTwist, ArithmeticFunction.one_apply, hn, hg]

def vf919RationalMobius : ArithmeticFunction ℂ := ArithmeticFunction.moebius
def vf919RationalZeta : ArithmeticFunction ℂ := ArithmeticFunction.zeta
def vf919QuadraticCharacter : ArithmeticFunction ℂ :=
  vf919ArithmeticTwist vf919ChiMinusThree vf919RationalZeta
def vf919QuadraticInverse : ArithmeticFunction ℂ :=
  vf919ArithmeticTwist vf919ChiMinusThree vf919RationalMobius
def vf919EisensteinNormCoefficients : ArithmeticFunction ℂ :=
  vf919RationalMobius * vf919QuadraticInverse
def vf919ExcludedNormCoefficients : ArithmeticFunction ℂ :=
  vf919ArithmeticTwist vf919PrimeToSixMask vf919EisensteinNormCoefficients

@[simp] theorem vf919QuadraticCharacter_apply (n : ℕ) :
    vf919QuadraticCharacter n = vf919ChiMinusThree n := by
  by_cases hn : n = 0
  · simp [hn, vf919ChiMinusThree]
  · simp [vf919QuadraticCharacter, vf919ArithmeticTwist,
      vf919RationalZeta, hn]

theorem vf919QuadraticCharacter_mul_inverse :
    vf919QuadraticCharacter * vf919QuadraticInverse = 1 := by
  rw [vf919QuadraticCharacter, vf919QuadraticInverse,
    ← vf919ArithmeticTwist_mul vf919ChiMinusThree vf919ChiMinusThree_mul]
  have hinv : vf919RationalZeta * vf919RationalMobius = 1 :=
    ArithmeticFunction.coe_zeta_mul_coe_moebius
  rw [hinv]
  exact vf919ArithmeticTwist_one _ (by norm_num [vf919ChiMinusThree])

/-- The actual rational Mobius coefficient is the character convolution of
the constructed norm coefficients.  This is not an assumed estimate. -/
theorem vf919QuadraticCharacter_mul_norm_eq_mobius :
    vf919QuadraticCharacter * vf919EisensteinNormCoefficients =
      vf919RationalMobius := by
  unfold vf919EisensteinNormCoefficients
  calc
    vf919QuadraticCharacter * (vf919RationalMobius * vf919QuadraticInverse) =
        vf919RationalMobius *
          (vf919QuadraticCharacter * vf919QuadraticInverse) := by ring
    _ = vf919RationalMobius := by rw [vf919QuadraticCharacter_mul_inverse]; simp

def vf919DirichletDelta (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = k ∧ k ≠ 0 then 1 else 0, by
    by_cases hk : k = 0 <;> simp [hk]⟩

theorem vf919DirichletDelta_mul_apply (k : ℕ) (hk : 0 < k)
    (f : ArithmeticFunction ℂ) (n : ℕ) :
    (vf919DirichletDelta k * f) n = if k ∣ n then f (n / k) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [ArithmeticFunction.mul_apply]
  by_cases hkn : k ∣ n
  · rw [if_pos hkn]
    rw [Finset.sum_eq_single (k, n / k)]
    · simp [vf919DirichletDelta, hk.ne']
    · intro x hx hne
      by_cases hxk : x.1 = k
      · have hp := (Nat.mem_divisorsAntidiagonal.mp hx).1
        have hsecond : x.2 = n / k := by
          rw [← hp, hxk, Nat.mul_div_cancel_left _ hk]
        have heq : x = (k, n / k) := Prod.ext hxk hsecond
        exact (hne heq).elim
      · simp [vf919DirichletDelta, hxk]
    · intro hnot
      exact (hnot (Nat.mem_divisorsAntidiagonal.mpr
        ⟨Nat.mul_div_cancel' hkn, hn⟩)).elim
  · rw [if_neg hkn]
    apply Finset.sum_eq_zero
    intro x hx
    have hxk : x.1 ≠ k := by
      intro h
      apply hkn
      exact ⟨x.2, by simpa [h] using (Nat.mem_divisorsAntidiagonal.mp hx).1.symm⟩
    simp [vf919DirichletDelta, hxk]

theorem vf919DirichletDelta_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    vf919DirichletDelta a * vf919DirichletDelta b =
      vf919DirichletDelta (a * b) := by
  ext n
  rw [vf919DirichletDelta_mul_apply a ha]
  by_cases hab : n = a * b
  · subst n
    simp [vf919DirichletDelta, Nat.mul_div_cancel_left _ ha, ha.ne', hb.ne']
  · have hdiv : a ∣ n → n / a ≠ b := by
      intro h hq
      apply hab
      rw [← Nat.mul_div_cancel' h, hq]
    by_cases h : a ∣ n
    · simp [vf919DirichletDelta, h, hdiv h, hab]
    · simp [vf919DirichletDelta, h, hab]

private theorem vf919MaskedZeta_eq_deletedFactors :
    vf919ArithmeticTwist vf919PrimeToSixMask vf919RationalZeta =
      (1 - vf919DirichletDelta 2) * (1 - vf919DirichletDelta 3) *
        vf919RationalZeta := by
  have hdelta := vf919DirichletDelta_mul 2 3 (by decide) (by decide)
  change vf919DirichletDelta 2 * vf919DirichletDelta 3 = vf919DirichletDelta 6 at hdelta
  have hfactor : (1 - vf919DirichletDelta 2) * (1 - vf919DirichletDelta 3) *
      vf919RationalZeta = vf919RationalZeta - vf919DirichletDelta 2 * vf919RationalZeta -
        vf919DirichletDelta 3 * vf919RationalZeta + vf919DirichletDelta 6 * vf919RationalZeta := by
    rw [← hdelta]
    ring
  rw [hfactor]
  ext n
  by_cases hn : n = 0
  · simp [hn]
  have h₂ : 2 ∣ n → n / 2 ≠ 0 := fun h => by
    intro hz
    have := Nat.mul_div_cancel' h
    simp [hz] at this
    exact hn this.symm
  have h₃ : 3 ∣ n → n / 3 ≠ 0 := fun h => by
    intro hz
    have := Nat.mul_div_cancel' h
    simp [hz] at this
    exact hn this.symm
  have h₆ : 6 ∣ n → n / 6 ≠ 0 := fun h => by
    intro hz
    have := Nat.mul_div_cancel' h
    simp [hz] at this
    exact hn this.symm
  have h₆iff : 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  simp only [vf919ArithmeticFunction_sub_apply, ArithmeticFunction.add_apply]
  rw [vf919DirichletDelta_mul_apply 2 (by decide),
    vf919DirichletDelta_mul_apply 3 (by decide),
    vf919DirichletDelta_mul_apply 6 (by decide)]
  by_cases h2 : 2 ∣ n <;> by_cases h3 : 3 ∣ n <;>
    simp_all [vf919ArithmeticTwist, vf919PrimeToSixMask, vf919RationalZeta]

private theorem vf919MaskedCharacter_eq_deletedFactor :
    vf919ArithmeticTwist vf919PrimeToSixMask vf919QuadraticCharacter =
      (1 + vf919DirichletDelta 2) * vf919QuadraticCharacter := by
  ext n
  rw [add_mul, one_mul, ArithmeticFunction.add_apply,
    vf919DirichletDelta_mul_apply 2 (by decide)]
  by_cases h2 : 2 ∣ n
  · have hchi : vf919ChiMinusThree n = -vf919ChiMinusThree (n / 2) := by
      calc
        vf919ChiMinusThree n =
            vf919ChiMinusThree 2 * vf919ChiMinusThree (n / 2) := by
          rw [← vf919ChiMinusThree_mul, Nat.mul_div_cancel' h2]
        _ = -vf919ChiMinusThree (n / 2) := by
          rw [show vf919ChiMinusThree 2 = -1 from by norm_num [vf919ChiMinusThree]]
          ring
    simp [vf919ArithmeticTwist, vf919PrimeToSixMask, h2, hchi]
  · by_cases h3 : 3 ∣ n
    · have hn3 : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
      simp [vf919ArithmeticTwist, vf919PrimeToSixMask, h2,
        vf919ChiMinusThree, hn3]
    · simp [vf919ArithmeticTwist, vf919PrimeToSixMask, h2, h3]

/-- Restoring the genuine excluded norm factors 3 and 4 recovers rational
Mobius after the character convolution.  All four signs are retained. -/
theorem vf919ExcludedNorm_restored_character_eq_mobius :
    vf919QuadraticCharacter *
        ((1 - vf919DirichletDelta 3) * (1 - vf919DirichletDelta 4)) *
        vf919ExcludedNormCoefficients = vf919RationalMobius := by
  let μ6 := vf919ArithmeticTwist vf919PrimeToSixMask vf919RationalMobius
  let ζ6 := vf919ArithmeticTwist vf919PrimeToSixMask vf919RationalZeta
  let χ6 := vf919ArithmeticTwist vf919PrimeToSixMask vf919QuadraticCharacter
  let i6 := vf919ArithmeticTwist vf919PrimeToSixMask vf919QuadraticInverse
  have hμζ : μ6 * ζ6 = 1 := by
    dsimp [μ6, ζ6]
    rw [← vf919ArithmeticTwist_mul _ vf919PrimeToSixMask_mul]
    have hi : vf919RationalMobius * vf919RationalZeta = 1 :=
      ArithmeticFunction.coe_moebius_mul_coe_zeta
    rw [hi]
    exact vf919ArithmeticTwist_one _ (by norm_num [vf919PrimeToSixMask])
  have hχi : χ6 * i6 = 1 := by
    dsimp [χ6, i6]
    rw [← vf919ArithmeticTwist_mul _ vf919PrimeToSixMask_mul,
      vf919QuadraticCharacter_mul_inverse]
    exact vf919ArithmeticTwist_one _ (by norm_num [vf919PrimeToSixMask])
  have ha : vf919ExcludedNormCoefficients = μ6 * i6 := by
    exact vf919ArithmeticTwist_mul _ vf919PrimeToSixMask_mul _ _
  have hrestore : (1 - vf919DirichletDelta 2) *
      (1 - vf919DirichletDelta 3) * μ6 = vf919RationalMobius := by
    calc
      (1 - vf919DirichletDelta 2) * (1 - vf919DirichletDelta 3) * μ6 =
          (1 - vf919DirichletDelta 2) * (1 - vf919DirichletDelta 3) * μ6 *
            (vf919RationalZeta * vf919RationalMobius) := by
              rw [show vf919RationalZeta * vf919RationalMobius = 1 from
                ArithmeticFunction.coe_zeta_mul_coe_moebius]; simp
      _ = (μ6 * ζ6) * vf919RationalMobius := by
        dsimp [ζ6]
        rw [vf919MaskedZeta_eq_deletedFactors]
        ring
      _ = vf919RationalMobius := by rw [hμζ]; simp
  have hfour : 1 - vf919DirichletDelta 4 =
      (1 - vf919DirichletDelta 2) * (1 + vf919DirichletDelta 2) := by
    have h := vf919DirichletDelta_mul 2 2 (by decide) (by decide)
    change vf919DirichletDelta 2 * vf919DirichletDelta 2 = vf919DirichletDelta 4 at h
    rw [← h]
    ring
  calc
    vf919QuadraticCharacter *
        ((1 - vf919DirichletDelta 3) * (1 - vf919DirichletDelta 4)) *
        vf919ExcludedNormCoefficients =
      (1 - vf919DirichletDelta 2) * (1 - vf919DirichletDelta 3) * μ6 * (χ6 * i6) := by
        rw [ha, hfour]
        dsimp [χ6]
        rw [vf919MaskedCharacter_eq_deletedFactor]
        ring
    _ = vf919RationalMobius := by rw [hχi, mul_one, hrestore]

/-- Literal finite transformation of a physical site weight. -/
def vf919PhysicalHeckeKernel (N : ℕ) (w : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, vf919ChiMinusThree d *
    (w (m * d) - w (3 * (m * d)) - w (4 * (m * d)) + w (12 * (m * d)))

theorem vf919PhysicalHeckeKernel_sub (N m : ℕ) (w v : ℕ → ℂ) :
    vf919PhysicalHeckeKernel N (fun n => w n - v n) m =
      vf919PhysicalHeckeKernel N w m - vf919PhysicalHeckeKernel N v m := by
  unfold vf919PhysicalHeckeKernel
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  ring

def vf919SmoothPhysicalWeight (R X n : ℕ) : ℂ :=
  by classical exact if n ≤ X ∧ (∀ p : ℕ, p.Prime → p ∣ n → p ≤ R) then 1 else 0
def vf919HighTransportPhysicalWeight (R X n : ℕ) : ℂ :=
  by classical exact if n ≤ X ∧ ¬ (∀ p : ℕ, p.Prime → p ∣ n → p ≤ R) then -1 else 0
def vf919SharpPhysicalWeight (X n : ℕ) : ℂ := if n ≤ X then 1 else 0

theorem vf919Smooth_sub_transport_eq_sharp (R X : ℕ) :
    (fun n => vf919SmoothPhysicalWeight R X n -
      vf919HighTransportPhysicalWeight R X n) = vf919SharpPhysicalWeight X := by
  funext n
  by_cases hn : n ≤ X <;>
    by_cases hs : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ R <;>
    simp [vf919SmoothPhysicalWeight, vf919HighTransportPhysicalWeight,
      vf919SharpPhysicalWeight, hn, hs]

/-- The original low/high mask cancellation commutes with conversion at
EACH norm, before summation or taking any energy. -/
theorem vf919LowHigh_kernel_commutes (R X N m : ℕ) :
    vf919PhysicalHeckeKernel N (vf919SmoothPhysicalWeight R X) m -
      vf919PhysicalHeckeKernel N (vf919HighTransportPhysicalWeight R X) m =
        vf919PhysicalHeckeKernel N (vf919SharpPhysicalWeight X) m := by
  rw [← vf919PhysicalHeckeKernel_sub, vf919Smooth_sub_transport_eq_sharp]

def vf919IntegerCharacter (n : ℕ) : ℤ :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1
def vf919IntegerCharacterPrefix (N : ℕ) : ℤ :=
  ∑ d ∈ Finset.Icc 1 N, vf919IntegerCharacter d

theorem vf919IntegerCharacterPrefix_eq_residue (N : ℕ) :
    vf919IntegerCharacterPrefix N = if N % 3 = 1 then 1 else 0 := by
  induction N with
  | zero => simp [vf919IntegerCharacterPrefix]
  | succ N ih =>
    unfold vf919IntegerCharacterPrefix at *
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih]
    have hn := Nat.mod_lt N (by decide : 0 < 3)
    interval_cases h : N % 3
    · have hs : (N + 1) % 3 = 1 := by omega
      simp [vf919IntegerCharacter, hs]
    · have hs : (N + 1) % 3 = 2 := by omega
      simp [vf919IntegerCharacter, hs]
    · have hs : (N + 1) % 3 = 0 := by omega
      simp [vf919IntegerCharacter, hs]

def vf919SharpQuotientKernel36 (N : ℕ) : ℤ :=
  vf919IntegerCharacterPrefix N - vf919IntegerCharacterPrefix (N / 3) -
    vf919IntegerCharacterPrefix (N / 4) + vf919IntegerCharacterPrefix (N / 12)

theorem vf919SharpQuotientKernel36_period (N : ℕ) :
    vf919SharpQuotientKernel36 (N + 36) = vf919SharpQuotientKernel36 N := by
  have h₁ : (N + 36) % 3 = N % 3 := by omega
  have h₃ : ((N + 36) / 3) % 3 = (N / 3) % 3 := by omega
  have h₄ : ((N + 36) / 4) % 3 = (N / 4) % 3 := by omega
  have h₁₂ : ((N + 36) / 12) % 3 = (N / 12) % 3 := by omega
  simp [vf919SharpQuotientKernel36, vf919IntegerCharacterPrefix_eq_residue,
    h₁, h₃, h₄, h₁₂]

theorem vf919SharpQuotientKernel36_mod (N : ℕ) :
    vf919SharpQuotientKernel36 N = vf919SharpQuotientKernel36 (N % 36) := by
  have hshift : ∀ q r, vf919SharpQuotientKernel36 (r + 36 * q) =
      vf919SharpQuotientKernel36 r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have h : r + 36 * (q + 1) = (r + 36 * q) + 36 := by omega
      rw [h, vf919SharpQuotientKernel36_period, ih]
  have h : N % 36 + 36 * (N / 36) = N := by omega
  calc
    vf919SharpQuotientKernel36 N =
        vf919SharpQuotientKernel36 (N % 36 + 36 * (N / 36)) := congrArg _ h.symm
    _ = vf919SharpQuotientKernel36 (N % 36) := hshift _ _

theorem vf919SharpQuotientKernel36_bounds (N : ℕ) :
    -2 ≤ vf919SharpQuotientKernel36 N ∧ vf919SharpQuotientKernel36 N ≤ 1 := by
  rw [vf919SharpQuotientKernel36_mod]
  have h := Nat.mod_lt N (by decide : 0 < 36)
  interval_cases hn : N % 36 <;>
    norm_num [vf919SharpQuotientKernel36, vf919IntegerCharacterPrefix_eq_residue]

theorem vf919SharpQuotientKernel36_mean_zero :
    (∑ j ∈ Finset.range 36, vf919SharpQuotientKernel36 j) = 0 := by
  norm_num [Finset.sum_range_succ, vf919SharpQuotientKernel36,
    vf919IntegerCharacterPrefix_eq_residue]

private theorem vf919DivisorAntidiagonal_eq_box (N n : ℕ)
    (hn : n ∈ Finset.Icc 1 N) :
    n.divisorsAntidiagonal =
      ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
        (fun x : ℕ × ℕ => x.1 * x.2 = n) := by
  ext x
  simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_filter,
    Finset.mem_product, Finset.mem_Icc]
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hnN := (Finset.mem_Icc.mp hn).2
  constructor
  · rintro ⟨hprod, _hne⟩
    have hx1 : 1 ≤ x.1 := by
      by_contra h
      have hz : x.1 = 0 := by omega
      simp [hz] at hprod
      omega
    have hx2 : 1 ≤ x.2 := by
      by_contra h
      have hz : x.2 = 0 := by omega
      simp [hz] at hprod
      omega
    have hleft : x.1 ≤ x.1 * x.2 := by
      simpa using Nat.mul_le_mul_left x.1 hx2
    have hright : x.2 ≤ x.1 * x.2 := by
      simpa using Nat.mul_le_mul_right x.2 hx1
    exact ⟨⟨⟨hx1, by omega⟩, ⟨hx2, by omega⟩⟩, hprod⟩
  · rintro ⟨_hbox, hprod⟩
    exact ⟨hprod, by omega⟩

/-- Finite Dirichlet Fubini with every physical coefficient unchanged.
The support hypothesis is ONLY a cutoff, not a cancellation assumption. -/
theorem vf919DirichletWeightedPairing (N : ℕ)
    (f g : ArithmeticFunction ℂ) (w : ℕ → ℂ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ n ∈ Finset.Icc 1 N, (f * g) n * w n) =
      ∑ m ∈ Finset.Icc 1 N, f m *
        ∑ d ∈ Finset.Icc 1 N, g d * w (m * d) := by
  calc
    (∑ n ∈ Finset.Icc 1 N, (f * g) n * w n) =
        ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          ∑ d ∈ Finset.Icc 1 N,
            if m * d = n then f m * g d * w n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.mul_apply, vf919DivisorAntidiagonal_eq_box N n hn,
        Finset.sum_filter, Finset.sum_mul, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro m _hm
      apply Finset.sum_congr rfl
      intro d _hd
      split_ifs <;> simp
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
          ∑ n ∈ Finset.Icc 1 N,
            if m * d = n then f m * g d * w n else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.Icc 1 N, f m *
          ∑ d ∈ Finset.Icc 1 N, g d * w (m * d) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hpos : 1 ≤ m * d := by
        have hm1 := (Finset.mem_Icc.mp hm).1
        have hd1 := (Finset.mem_Icc.mp hd).1
        nlinarith
      by_cases hle : m * d ≤ N
      · have hmem : m * d ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hpos, hle⟩
        simp [eq_comm, hmem, mul_assoc]
      · have hnot : m * d ∉ Finset.Icc 1 N := by simp [hle]
        simp [eq_comm, hnot, hw (m * d) (by omega)]

private theorem vf919DeltaWeightedPairing (N k : ℕ) (hk : k ∈ Finset.Icc 1 N)
    (f : ArithmeticFunction ℂ) (w : ℕ → ℂ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ n ∈ Finset.Icc 1 N, (vf919DirichletDelta k * f) n * w n) =
      ∑ m ∈ Finset.Icc 1 N, f m * w (k * m) := by
  rw [vf919DirichletWeightedPairing N (vf919DirichletDelta k) f w hw]
  have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  simp [vf919DirichletDelta, hk0, hk]

private theorem vf919RestoringFactorsWeightedPairing (N : ℕ) (hN : 12 ≤ N)
    (f : ArithmeticFunction ℂ) (w : ℕ → ℂ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ n ∈ Finset.Icc 1 N,
      (((1 - vf919DirichletDelta 3) * (1 - vf919DirichletDelta 4)) * f) n * w n) =
      ∑ n ∈ Finset.Icc 1 N, f n *
        (w n - w (3 * n) - w (4 * n) + w (12 * n)) := by
  have h34 := vf919DirichletDelta_mul 3 4 (by decide) (by decide)
  change vf919DirichletDelta 3 * vf919DirichletDelta 4 = vf919DirichletDelta 12 at h34
  have hfactor : ((1 - vf919DirichletDelta 3) * (1 - vf919DirichletDelta 4)) * f =
      f - vf919DirichletDelta 3 * f - vf919DirichletDelta 4 * f +
        vf919DirichletDelta 12 * f := by rw [← h34]; ring
  rw [hfactor]
  simp only [ArithmeticFunction.add_apply, vf919ArithmeticFunction_sub_apply,
    sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [vf919DeltaWeightedPairing N 3 (by simp; omega) f w hw,
    vf919DeltaWeightedPairing N 4 (by simp; omega) f w hw,
    vf919DeltaWeightedPairing N 12 (by simp; omega) f w hw]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- COMPLETE rational-to-excluded-norm dictionary for arbitrary complex
physical weights, using the actual Mathlib Mobius function. No coefficient
identification hypothesis or arithmetic estimate occurs in this theorem. -/
theorem vf919WeightedMobius_eq_excludedNormKernel
    (N : ℕ) (hN : 12 ≤ N) (w : ℕ → ℂ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) * w n) =
      ∑ m ∈ Finset.Icc 1 N,
        vf919ExcludedNormCoefficients m * vf919PhysicalHeckeKernel N w m := by
  let v : ℕ → ℂ := fun n => w n - w (3 * n) - w (4 * n) + w (12 * n)
  have hv : ∀ n, N < n → v n = 0 := by
    intro n hn
    dsimp [v]
    rw [hw n hn, hw (3 * n) (by omega), hw (4 * n) (by omega),
      hw (12 * n) (by omega)]
    ring
  have hcoef : vf919RationalMobius =
      ((1 - vf919DirichletDelta 3) * (1 - vf919DirichletDelta 4)) *
        (vf919ExcludedNormCoefficients * vf919QuadraticCharacter) := by
    rw [← vf919ExcludedNorm_restored_character_eq_mobius]
    ring
  calc
    (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) * w n) =
        ∑ n ∈ Finset.Icc 1 N, vf919RationalMobius n * w n := rfl
    _ = ∑ n ∈ Finset.Icc 1 N,
        (((1 - vf919DirichletDelta 3) * (1 - vf919DirichletDelta 4)) *
          (vf919ExcludedNormCoefficients * vf919QuadraticCharacter)) n * w n := by rw [hcoef]
    _ = ∑ n ∈ Finset.Icc 1 N,
        (vf919ExcludedNormCoefficients * vf919QuadraticCharacter) n * v n :=
      vf919RestoringFactorsWeightedPairing N hN _ w hw
    _ = ∑ m ∈ Finset.Icc 1 N, vf919ExcludedNormCoefficients m *
        ∑ d ∈ Finset.Icc 1 N, vf919QuadraticCharacter d * v (m * d) :=
      vf919DirichletWeightedPairing N _ _ v hv
    _ = ∑ m ∈ Finset.Icc 1 N,
        vf919ExcludedNormCoefficients m * vf919PhysicalHeckeKernel N w m := by
      simp [vf919PhysicalHeckeKernel, v]

private theorem vf919CharacterSum_sharp_dilation (N X m : ℕ)
    (hX : X ≤ N) (hm : 0 < m) :
    (∑ d ∈ Finset.Icc 1 N, if m * d ≤ X then vf919ChiMinusThree d else 0) =
      (vf919IntegerCharacterPrefix (X / m) : ℂ) := by
  have hdiv : X / m ≤ N := (Nat.div_le_self X m).trans hX
  have hfilter : (Finset.Icc 1 N).filter (fun d => m * d ≤ X) =
      Finset.Icc 1 (X / m) := by
    ext d
    have hiff : m * d ≤ X ↔ d ≤ X / m := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).symm
    simp only [Finset.mem_filter, Finset.mem_Icc, hiff]
    omega
  rw [← Finset.sum_filter, hfilter]
  simp only [vf919IntegerCharacterPrefix, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  unfold vf919IntegerCharacter vf919ChiMinusThree
  split_ifs <;> norm_num

theorem vf919SharpPhysicalHeckeKernel_eq_periodic_quotient (N X m : ℕ)
    (hX : X ≤ N) (hm : 0 < m) :
    vf919PhysicalHeckeKernel N (vf919SharpPhysicalWeight X) m =
      (vf919SharpQuotientKernel36 (X / m) : ℂ) := by
  unfold vf919PhysicalHeckeKernel vf919SharpPhysicalWeight
  simp only [mul_sub, mul_add, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [← Nat.mul_assoc]
  rw [vf919CharacterSum_sharp_dilation N X m hX hm,
    vf919CharacterSum_sharp_dilation N X (3 * m) hX (by omega),
    vf919CharacterSum_sharp_dilation N X (4 * m) hX (by omega),
    vf919CharacterSum_sharp_dilation N X (12 * m) hX (by omega)]
  simp [vf919SharpQuotientKernel36, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- The actual sharp Mertens prefix in excluded principal norm currency.
The 36-periodic coefficient is applied to floor(X/m), not to m. -/
theorem vf919Mertens_eq_excludedNorm_periodicKernel (X : ℕ) (hX : 12 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℂ)) =
      ∑ m ∈ Finset.Icc 1 X, vf919ExcludedNormCoefficients m *
        (vf919SharpQuotientKernel36 (X / m) : ℂ) := by
  have hw : ∀ n, X < n → vf919SharpPhysicalWeight X n = 0 := by
    intro n hn
    simp [vf919SharpPhysicalWeight, Nat.not_le.mpr hn]
  calc
    (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℂ)) =
        ∑ n ∈ Finset.Icc 1 X,
          (ArithmeticFunction.moebius n : ℂ) * vf919SharpPhysicalWeight X n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [vf919SharpPhysicalWeight, (Finset.mem_Icc.mp hn).2]
    _ = ∑ m ∈ Finset.Icc 1 X, vf919ExcludedNormCoefficients m *
          vf919PhysicalHeckeKernel X (vf919SharpPhysicalWeight X) m :=
      vf919WeightedMobius_eq_excludedNormKernel X hX _ hw
    _ = ∑ m ∈ Finset.Icc 1 X, vf919ExcludedNormCoefficients m *
          (vf919SharpQuotientKernel36 (X / m) : ℂ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [vf919SharpPhysicalHeckeKernel_eq_periodic_quotient X X m le_rfl
        (by have := (Finset.mem_Icc.mp hm).1; omega)]

end RHLean.Analysis
