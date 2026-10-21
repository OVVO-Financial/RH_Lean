import Mathlib
import RHLean.Proof.SignedCanonicalHeight
import «research.VF_919_ACTUAL_WEIGHTED_NNS_COVARIANCE_KERNEL_20261021»

/-!
# Weighted low/high canonical gate extension for the actual OAI/NNS source

No independence assumption, high-sector dispersion theorem, new Mertens
exponent, or imported OpenAI analytical bound is asserted.

The proven canonical factor-gap population count is lifted to arbitrary
complex amplitudes; the global post-root high owner is confined to a
fixed-width root boundary if it is also low canonical height. At
height cutoff 2*n, the overlap is empty.

The high source still requires an independent signed bound.  OAI ideal
labels, row multiplicities, physical weights, rescalings and masks must
be faithfully mapped before using the canonical bound on the
production detector moment.
-/

noncomputable section
open scoped BigOperators Classical

namespace RHLean.Proof
namespace NNSLowHighGateExtension

open SignedHeight

/-- The canonical factor-gap count controls any complex weighted
source on a faithful one-pair-per-atom carrier. -/
theorem weightedCanonicalLow_norm_le
    {n H : ℕ} (hn : 1 ≤ n)
    (S : Finset (ℕ × ℕ))
    (hS : ∀ v ∈ S, SignedHeight.Admissible n H v.1 v.2)
    (a : ℕ × ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ v ∈ S, ‖a v‖ ≤ B) :
    ‖∑ v ∈ S, a v‖ ≤ ((H / n + 1 : ℕ) : ℝ) * B := by
  have hcard : (S.card : ℝ) ≤ ((H / n + 1 : ℕ) : ℝ) := by
    exact_mod_cast SignedHeight.card_le hn S hS
  calc
    ‖∑ v ∈ S, a v‖ ≤ ∑ v ∈ S, ‖a v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ S, B := Finset.sum_le_sum (fun v hv => ha v hv)
    _ = (S.card : ℝ) * B := by simp [nsmul_eq_mul]
    _ ≤ ((H / n + 1 : ℕ) : ℝ) * B :=
      mul_le_mul_of_nonneg_right hcard hB

/-- Unnormalized complex low-gate squared-energy operator estimate.
Unlike an L-infinity bound, this retains heterogeneous source weights. -/
theorem weightedCanonicalLow_energy_le
    {n H : ℕ} (hn : 1 ≤ n)
    (S : Finset (ℕ × ℕ))
    (hS : ∀ v ∈ S, SignedHeight.Admissible n H v.1 v.2)
    (a : ℕ × ℕ → ℂ) :
    ‖∑ v ∈ S, a v‖ ^ 2 ≤
      ((H / n + 1 : ℕ) : ℝ) * ∑ v ∈ S, ‖a v‖ ^ 2 := by
  have hcard : (S.card : ℝ) ≤ ((H / n + 1 : ℕ) : ℝ) := by
    exact_mod_cast SignedHeight.card_le hn S hS
  have hnorm : ‖∑ v ∈ S, a v‖ ≤ ∑ v ∈ S, ‖a v‖ :=
    norm_sum_le _ _
  have hsumNonneg : 0 ≤ ∑ v ∈ S, ‖a v‖ :=
    Finset.sum_nonneg (fun v hv => norm_nonneg (a v))
  have hfac : 0 ≤
      ((∑ v ∈ S, ‖a v‖) - ‖∑ v ∈ S, a v‖) *
      ((∑ v ∈ S, ‖a v‖) + ‖∑ v ∈ S, a v‖) :=
    mul_nonneg (sub_nonneg.mpr hnorm)
      (add_nonneg hsumNonneg (norm_nonneg _))
  have hsq : ‖∑ v ∈ S, a v‖ ^ 2 ≤
      (∑ v ∈ S, ‖a v‖) ^ 2 := by nlinarith [hfac]
  have hCS :
      (∑ v ∈ S, ‖a v‖) ^ 2 ≤
      (S.card : ℝ) * ∑ v ∈ S, ‖a v‖ ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq S
        (fun _ => (1 : ℝ)) (fun v => ‖a v‖))
  have hmass : 0 ≤ ∑ v ∈ S, ‖a v‖ ^ 2 :=
    Finset.sum_nonneg (fun v hv => sq_nonneg (‖a v‖))
  calc
    ‖∑ v ∈ S, a v‖ ^ 2 ≤
        (∑ v ∈ S, ‖a v‖) ^ 2 := hsq
    _ ≤ (S.card : ℝ) * ∑ v ∈ S, ‖a v‖ ^ 2 := hCS
    _ ≤ ((H / n + 1 : ℕ) : ℝ) * ∑ v ∈ S, ‖a v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcard hmass

/-- For q=c+d>R and cq<R squared, membership in a low-height
canonical pair gate forces 2<=d<=Lambda, c<R and q<R+Lambda.
The high-owner/low-height intersection is microscopic at the root. -/
theorem highOwner_lowHeight_gap_fence
    {R Lambda n c d : ℕ} (hn : 1 ≤ n)
    (hA : SignedHeight.Admissible n (Lambda * n) c d)
    (hHigh : R < c + d) (hCeil : c * (c + d) < R ^ 2) :
    2 ≤ d ∧ d ≤ Lambda ∧ c < R ∧
      R < c + d ∧ c + d < R + Lambda := by
  have hgap : d * n ≤ Lambda * n :=
    SignedHeight.gap_mul_le hA
  have hdn : d ≤ Lambda := by
    by_contra hnot
    have hdl : Lambda + 1 ≤ d := by omega
    have hmul : (Lambda + 1) * n ≤ d * n :=
      Nat.mul_le_mul_right n hdl
    have hmul' : Lambda * n + n ≤ d * n := by
      nlinarith [hmul]
    omega
  have hprod : c * (c + d) < R * R := by
    simpa only [pow_two] using hCeil
  have hc : c < R := by
    by_contra hnot
    have hcR : R ≤ c := by omega
    have hqR : R ≤ c + d := Nat.le_of_lt hHigh
    have hmul : R * R ≤ c * (c + d) :=
      Nat.mul_le_mul hcR hqR
    omega
  have htwo : 2 ≤ d := by omega
  exact ⟨htwo, hdn, hc, hHigh, by omega⟩

/-- At the fixed canonical height cutoff 2*n there is NO
intersection with primes exceeding R below the endpoint R squared. -/
theorem highOwner_lowHeight_two_impossible
    {R n c d : ℕ} (hn : 1 ≤ n)
    (hA : SignedHeight.Admissible n (2 * n) c d)
    (hHigh : R < c + d) (hCeil : c * (c + d) < R ^ 2) :
    False := by
  have hfence := highOwner_lowHeight_gap_fence hn hA hHigh hCeil
  have hd : d = 2 := by omega
  rcases hA with ⟨_hc, hBlockLow, _hBlockHigh, hGapLow⟩
  subst d
  nlinarith [hBlockLow, hGapLow]

/-- Two DIFFERENT OAI Euler masks create three exact disjoint faces:
mutually admitted weight/phase defect, A-only boundary, B-only
boundary. No phase cancellation or arithmetic gain is assumed. -/
theorem twoAdmissionGates_exact_three_faces
    {alpha : Type*} (S : Finset alpha)
    (admitA admitB : alpha → Prop) (A B : alpha → ℂ) :
    (∑ i ∈ S,
       (if admitA i then A i else 0) -
       (if admitB i then B i else 0)) =
    (∑ i ∈ S,
       if admitA i ∧ admitB i then A i - B i else 0) +
    (∑ i ∈ S,
       if admitA i ∧ ¬admitB i then A i else 0) -
    (∑ i ∈ S,
       if ¬admitA i ∧ admitB i then B i else 0) := by
  classical
  calc
    _ = ∑ i ∈ S,
       ((if admitA i ∧ admitB i then A i - B i else 0) +
        (if admitA i ∧ ¬admitB i then A i else 0) -
        (if ¬admitA i ∧ admitB i then B i else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hA : admitA i <;> by_cases hB : admitB i <;>
        simp [hA, hB]
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- The low/high NNS cross contribution remains present. -/
theorem phiLowHigh_energy_exact (lx ly hx hy : ℝ) :
    (((lx + hx) ^ 2 + (ly + hy) ^ 2) / 2) =
      (lx ^ 2 + ly ^ 2) / 2 +
      (hx ^ 2 + hy ^ 2) / 2 +
      (lx * hx + ly * hy) := by
  ring

end NNSLowHighGateExtension
end RHLean.Proof

#print axioms RHLean.Proof.NNSLowHighGateExtension.weightedCanonicalLow_norm_le
#print axioms RHLean.Proof.NNSLowHighGateExtension.weightedCanonicalLow_energy_le
#print axioms RHLean.Proof.NNSLowHighGateExtension.highOwner_lowHeight_gap_fence
#print axioms RHLean.Proof.NNSLowHighGateExtension.highOwner_lowHeight_two_impossible
#print axioms RHLean.Proof.NNSLowHighGateExtension.twoAdmissionGates_exact_three_faces
