import Mathlib
import «research.VF_MID_919_OAI_QUADRATIC_NORM_EULER»

/-!
# #919: exact excluded-(2,3) signed Hecke coefficient inlet for physical VF

All identities in this file are finite.  They preserve the **same** site
weight in the rational coefficient system and in the norm/character system.
The four shifts 1,3,4,12 are the excluded Euler factors of F = Q(sqrt(-3)):
ramified norm 3 and inert norm 4.  Neither a norm-grouped ideal-Mobius
identification nor an OAI uniform moment bound is silently assumed here.

The arithmetic statement mu_Z = chi_{-3} * a_F, with the actual global ideal
coefficient a_F, is a separate ideal-factorization identification.  Given
that standard identification, the finite kernel below is exactly its
coefficient-level application to arbitrary physical VF site weights.

The sign of the complete amplifier divisor cross-terms is kept.  Squaring
each summand separately is explicitly NOT part of these theorems.
-/

noncomputable section

namespace RHLean.Analysis

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The coefficient of the prime-norm term in
    (1-t)(1-chi_{-3}(p)t), including split/inert/ramified cases. -/
def vf919NormPrimeLinearCoefficient (p : ℕ) : ℝ :=
  -(1 + vf919QuadraticMinusThreePrimeValue p)

/-- The local Euler equality with its linear and quadratic coefficients
    displayed, so that selected prime multiplicities are NOT replaced
    by a one-to-one ideal/physical-owner correspondence. -/
theorem vf919EisensteinNormEuler_explicit_coefficients (p : ℕ) (t : ℝ) :
    vf919EisensteinNormMobiusEulerFactor p t =
      1 + vf919NormPrimeLinearCoefficient p * t +
        vf919QuadraticMinusThreePrimeValue p * t ^ 2 := by
  rw [vf919EisensteinNormMobiusEuler_eq_rational_mul_quadratic]
  unfold vf919NormPrimeLinearCoefficient
  ring

/-- Exact TWO-LEG cancellation: inserting p into the ideal-norm leg
    changes its coefficient by -(1+chi(p)); inserting it into the
    quadratic-character leg contributes chi(p).  Any distinct physical
    parent and child weights remain attached. -/
theorem vf919HeckePrimeTwoLeg_retains_physical_weights
    (p : ℕ) (a parentWeight childWeight : ℝ) :
    a * parentWeight +
        (vf919NormPrimeLinearCoefficient p * a +
          vf919QuadraticMinusThreePrimeValue p * a) * childWeight =
      a * (parentWeight - childWeight) := by
  unfold vf919NormPrimeLinearCoefficient
  ring

/-- For a genuine ideal-norm coefficient pair the only needed hypothesis
    is its local p-free Euler recursion.  This theorem DOES NOT claim to
    prove that recursion for actual Eisenstein ideals. -/
theorem vf919HeckePrimeTwoLeg_of_norm_recursion
    (p : ℕ) (a ap parentWeight childWeight : ℝ)
    (hprime : ap = vf919NormPrimeLinearCoefficient p * a) :
    a * parentWeight +
        (ap + vf919QuadraticMinusThreePrimeValue p * a) * childWeight =
      a * (parentWeight - childWeight) := by
  rw [hprime]
  exact vf919HeckePrimeTwoLeg_retains_physical_weights
    p a parentWeight childWeight

/-- One excluded-(2,3) physical site, with all four sharp positions
    retained. No smooth approximation is inserted. -/
def vf919SixExcludedSiteWeight (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  w n - w (3 * n) - w (4 * n) + w (12 * n)

/-- The same four-shift transform on an arbitrary ideal norm m, with a
    finite (signed) quadratic-character leg d. -/
def vf919SixExcludedNormKernel
    (ds : Finset ℕ) (chi : ℕ → ℝ)
    (w : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ ds, chi d * vf919SixExcludedSiteWeight w (m * d)

/-- The signed norm/character functional. The coefficient a(m) may
    represent the actual norm-grouped ideal Mobius coefficient and may
    carry split-prime multiplicity. -/
def vf919FiniteSixExcludedHecke
    (ms ds : Finset ℕ) (a chi : ℕ → ℝ)
    (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ ms, a m * vf919SixExcludedNormKernel ds chi w m

/-- The exact low-scale/high-scale cancellation commutes with the
    excluded Euler-factor transform at EACH norm. -/
theorem vf919SixExcludedSiteWeight_sub
    (u v : ℕ → ℝ) (n : ℕ) :
    vf919SixExcludedSiteWeight (fun k => u k - v k) n =
      vf919SixExcludedSiteWeight u n -
        vf919SixExcludedSiteWeight v n := by
  unfold vf919SixExcludedSiteWeight
  ring

theorem vf919SixExcludedNormKernel_sub
    (ds : Finset ℕ) (chi : ℕ → ℝ)
    (u v : ℕ → ℝ) (m : ℕ) :
    vf919SixExcludedNormKernel ds chi (fun k => u k - v k) m =
      vf919SixExcludedNormKernel ds chi u m -
        vf919SixExcludedNormKernel ds chi v m := by
  unfold vf919SixExcludedNormKernel
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [vf919SixExcludedSiteWeight_sub]
  ring

theorem vf919FiniteSixExcludedHecke_sub
    (ms ds : Finset ℕ) (a chi : ℕ → ℝ)
    (u v : ℕ → ℝ) :
    vf919FiniteSixExcludedHecke ms ds a chi (fun k => u k - v k) =
      vf919FiniteSixExcludedHecke ms ds a chi u -
        vf919FiniteSixExcludedHecke ms ds a chi v := by
  unfold vf919FiniteSixExcludedHecke
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [vf919SixExcludedNormKernel_sub]
  ring

/-- In particular an EXACT physical S=A-T mask is transported as a
    single signed Hecke sum; neither leg is bounded independently. -/
theorem vf919FiniteSixExcludedHecke_S_eq_A_sub_T
    (ms ds : Finset ℕ) (a chi : ℕ → ℝ)
    (smooth high sharp : ℕ → ℝ)
    (hmask : ∀ n, smooth n - high n = sharp n) :
    vf919FiniteSixExcludedHecke ms ds a chi smooth -
        vf919FiniteSixExcludedHecke ms ds a chi high =
      vf919FiniteSixExcludedHecke ms ds a chi sharp := by
  rw [← vf919FiniteSixExcludedHecke_sub]
  have heq : (fun n : ℕ => smooth n - high n) = sharp :=
    by
      funext n
      exact hmask n
  rw [heq]

/-- Four signed mask coefficients at one rational site. -/
def vf919SixExcludedSiteMask (n k : ℕ) : ℝ :=
  (if n = k then 1 else 0) -
  (if n = 3 * k then 1 else 0) -
  (if n = 4 * k then 1 else 0) +
  (if n = 12 * k then 1 else 0)

/-- A finite rational coefficient generated by norm/character legs.
    Here s can list repeated ideal norms as separate signed occurrences,
    so ideal-norm multiplicities are NOT silently discarded. -/
def vf919FiniteSixExcludedRationalCoefficient
    (s : Finset (ℕ × ℕ)) (a chi : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ s, a x.1 * chi x.2 *
    vf919SixExcludedSiteMask n (x.1 * x.2)

/-- Exact finite character/ideal-norm source corresponding to the
    coefficient above. -/
def vf919FiniteSixExcludedPairSource
    (s : Finset (ℕ × ℕ)) (a chi : ℕ → ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ x ∈ s, (a x.1 * chi x.2) *
    vf919SixExcludedSiteWeight w (x.1 * x.2)

/-- Pairing a four-site mask against an arbitrary physical site weight.
    The coverage hypothesis guarantees NO dropped endpoint. -/
theorem vf919SixExcludedSiteMask_sum_eq_weight
    (ns : Finset ℕ) (w : ℕ → ℝ) (k : ℕ)
    (hk : k ∈ ns) (h3 : 3 * k ∈ ns)
    (h4 : 4 * k ∈ ns) (h12 : 12 * k ∈ ns) :
    (∑ n ∈ ns, vf919SixExcludedSiteMask n k * w n) =
      vf919SixExcludedSiteWeight w k := by
  unfold vf919SixExcludedSiteMask vf919SixExcludedSiteWeight
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [ite_mul, hk, h3, h4, h12]

/-- FINITE FUBINI IDENTIFICATION with completely arbitrary physical
    weights, all excluded factors, and all norm multiplicities intact. -/
theorem vf919FiniteSixExcludedRationalPairing_eq_Hecke
    (s : Finset (ℕ × ℕ)) (ns : Finset ℕ)
    (a chi : ℕ → ℝ) (w : ℕ → ℝ)
    (hcover : ∀ x ∈ s,
      x.1 * x.2 ∈ ns ∧
      3 * (x.1 * x.2) ∈ ns ∧
      4 * (x.1 * x.2) ∈ ns ∧
      12 * (x.1 * x.2) ∈ ns) :
    (∑ n ∈ ns,
        vf919FiniteSixExcludedRationalCoefficient s a chi n * w n) =
      vf919FiniteSixExcludedPairSource s a chi w := by
  unfold vf919FiniteSixExcludedRationalCoefficient
    vf919FiniteSixExcludedPairSource
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨h1, h3, h4, h12⟩ := hcover x hx
  calc
    (∑ n ∈ ns,
        (a x.1 * chi x.2 *
          vf919SixExcludedSiteMask n (x.1 * x.2)) * w n) =
        (a x.1 * chi x.2) *
          (∑ n ∈ ns,
            vf919SixExcludedSiteMask n (x.1 * x.2) * w n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = (a x.1 * chi x.2) *
          vf919SixExcludedSiteWeight w (x.1 * x.2) := by
      rw [vf919SixExcludedSiteMask_sum_eq_weight ns w
        (x.1 * x.2) h1 h3 h4 h12]

/-- Explicit quadratic-character prefix, using its exact period-three
    0/1 formula on integer cutoffs (C_chi(N)=sum_{1<=d<=N}chi(d)). -/
def vf919MinusThreeCharacterPrefix (N : ℕ) : ℤ :=
  if N % 3 = 1 then 1 else 0

theorem vf919MinusThreeCharacterPrefix_add_triple (N k : ℕ) :
    vf919MinusThreeCharacterPrefix (N + 3 * k) =
      vf919MinusThreeCharacterPrefix N := by
  have hmod : (N + 3 * k) % 3 = N % 3 := by omega
  simp [vf919MinusThreeCharacterPrefix, hmod]

/-- The actual 1,3,4,12 norm shifts, evaluated on the sharp prefix
    w(n)=1[n<=X].  The quotient N=floor(X/m) is the low/high variable. -/
def vf919SixExcludedSharpQuotientKernel (N : ℕ) : ℤ :=
  vf919MinusThreeCharacterPrefix N -
    vf919MinusThreeCharacterPrefix (N / 3) -
    vf919MinusThreeCharacterPrefix (N / 4) +
    vf919MinusThreeCharacterPrefix (N / 12)

/-- An exact 36-periodic arithmetic quotient comb. -/
theorem vf919SixExcludedSharpQuotientKernel_periodic (N : ℕ) :
    vf919SixExcludedSharpQuotientKernel (N + 36) =
      vf919SixExcludedSharpQuotientKernel N := by
  have h1 : vf919MinusThreeCharacterPrefix (N + 36) =
      vf919MinusThreeCharacterPrefix N := by
    simpa using vf919MinusThreeCharacterPrefix_add_triple N 12
  have h3div : (N + 36) / 3 = N / 3 + 12 := by omega
  have h4div : (N + 36) / 4 = N / 4 + 9 := by omega
  have h12div : (N + 36) / 12 = N / 12 + 3 := by omega
  have h3 : vf919MinusThreeCharacterPrefix ((N + 36) / 3) =
      vf919MinusThreeCharacterPrefix (N / 3) := by
    rw [h3div]
    simpa using vf919MinusThreeCharacterPrefix_add_triple (N / 3) 4
  have h4 : vf919MinusThreeCharacterPrefix ((N + 36) / 4) =
      vf919MinusThreeCharacterPrefix (N / 4) := by
    rw [h4div]
    simpa using vf919MinusThreeCharacterPrefix_add_triple (N / 4) 3
  have h12 : vf919MinusThreeCharacterPrefix ((N + 36) / 12) =
      vf919MinusThreeCharacterPrefix (N / 12) := by
    rw [h12div]
    simpa using vf919MinusThreeCharacterPrefix_add_triple (N / 12) 1
  simp only [vf919SixExcludedSharpQuotientKernel, h1, h3, h4, h12]

/-- Finite exact signed mass across one complete period. -/
theorem vf919SixExcludedSharpQuotientKernel_full_period_zero :
    (∑ n ∈ Finset.range 36,
      vf919SixExcludedSharpQuotientKernel n) = 0 := by
  decide

/-- A true uniform bound on individual sharp quotient coefficients,
    NOT a bound on their signed sum against ideal Mobius coefficients. -/
theorem vf919SixExcludedSharpQuotientKernel_bounds (N : ℕ) :
    -2 ≤ vf919SixExcludedSharpQuotientKernel N ∧
      vf919SixExcludedSharpQuotientKernel N ≤ 2 := by
  unfold vf919SixExcludedSharpQuotientKernel vf919MinusThreeCharacterPrefix
  split_ifs <;> omega

/-- The complete REAL principal-row amplified cross matrix, retaining
    all signed d/e terms rather than replacing them with separate norms.
    The actual ideal six-power identity is a separate upstream input. -/
theorem vf919PrincipalSignedSixthPowerCrossMatrix
    {ι : Type*} (s : Finset ι) (c H J : ι → ℝ) :
    -2 * (∑ d ∈ s, c d * H d) *
        (∑ e ∈ s, c e * J e) =
      ∑ d ∈ s, ∑ e ∈ s,
        -2 * c d * c e * H d * J e := by
  calc
    -2 * (∑ d ∈ s, c d * H d) *
        (∑ e ∈ s, c e * J e) =
      (∑ d ∈ s, -2 * (c d * H d)) *
        (∑ e ∈ s, c e * J e) := by
      rw [← Finset.mul_sum]
    _ = ∑ d ∈ s, ∑ e ∈ s,
          -2 * c d * c e * H d * J e := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      ring

end RHLean.Analysis
