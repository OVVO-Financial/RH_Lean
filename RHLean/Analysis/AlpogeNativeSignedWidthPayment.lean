import Mathlib
import RHLean.Analysis.AlpogeNativeSharpASKBalance
import RHLean.Analysis.AlpogeASKTangentCovariance

/-!
# One-sided signed width payment for the complete native ASK source

This file keeps the actual Frobenius/inertia kernel and Lambda at every prime
power. The central finite result compares the full ASK-MAIN at the pointwise
midpoint of two physical width profiles with the average at those profiles.

The ASK collar has the favorable sign in this direction. Its positivity is
proved from the actual Fourier-inverted inertia weights; it is not bounded
by a host-size charge. The only upper cost is the logarithmic MAIN curvature,
at most `a * d^2 / (8*b^2)` for widths at least `b` separated by at most `d`.

The affine-row instance uses the genuine pairing `j <-> m-1-j` and requires
no lattice at the midpoint. It does not bound the average source at the two
physical rows, supply lattice maps, or assert a critical Gz estimate.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The scalar curvature paid by the MAIN logarithm. -/
def alpogeWidthLogMidpointGap (u v : ℝ) : ℝ :=
  Real.log ((u + v) / 2) - (Real.log u + Real.log v) / 2

/-- A quantitative logarithmic Jensen inequality, with its full denominator.
There is no small-width or infinitesimal approximation. -/
theorem alpogeWidthLogMidpointGap_nonneg_le
    (b u v d : ℝ) (hb : 0 < b) (hu : b ≤ u) (hv : b ≤ v)
    (hd : |u - v| ≤ d) :
    0 ≤ alpogeWidthLogMidpointGap u v ∧
      alpogeWidthLogMidpointGap u v ≤ d ^ 2 / (8 * b ^ 2) := by
  have hu0 : 0 < u := lt_of_lt_of_le hb hu
  have hv0 : 0 < v := lt_of_lt_of_le hb hv
  let c : ℝ := (u + v) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have huv0 : 0 < u * v := mul_pos hu0 hv0
  have hbb : b ^ 2 ≤ u * v := by
    simpa only [pow_two] using mul_le_mul hu hv hb.le hu0.le
  have hsq : (u - v) ^ 2 ≤ d ^ 2 := by
    have hleft : 0 ≤ d - (u - v) := by linarith [(abs_le.mp hd).2]
    have hright : 0 ≤ d + (u - v) := by linarith [(abs_le.mp hd).1]
    nlinarith [mul_nonneg hleft hright]
  have hprod : u * v ≤ c ^ 2 := by
    dsimp [c]
    nlinarith [sq_nonneg (u - v)]
  have hlog : Real.log (c ^ 2 / (u * v)) =
      2 * alpogeWidthLogMidpointGap u v := by
    rw [Real.log_div (pow_ne_zero 2 hc.ne') huv0.ne',
      Real.log_pow, Real.log_mul hu0.ne' hv0.ne']
    dsimp [alpogeWidthLogMidpointGap, c]
    ring
  have hratio : (c ^ 2 / (u * v) - 1) / 2 =
      (u - v) ^ 2 / (8 * (u * v)) := by
    dsimp [c]
    field_simp [hu0.ne', hv0.ne']
    ring
  constructor
  · have h := Real.log_le_log huv0 hprod
    rw [Real.log_mul hu0.ne' hv0.ne', Real.log_pow] at h
    dsimp [alpogeWidthLogMidpointGap, c] at *
    linarith
  · have ht := Real.log_le_sub_one_of_pos
      (div_pos (sq_pos_of_pos hc) huv0)
    rw [hlog] at ht
    have hfirst : alpogeWidthLogMidpointGap u v ≤
        (u - v) ^ 2 / (8 * (u * v)) := by
      rw [← hratio]
      linarith
    have hnum : (u - v) ^ 2 / (8 * (u * v)) ≤
        d ^ 2 / (8 * (u * v)) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have hden : d ^ 2 / (8 * (u * v)) ≤ d ^ 2 / (8 * b ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg d) (by positivity)
        (by nlinarith [hbb])
    exact hfirst.trans (hnum.trans hden)

section Native

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Real, physical Fourier-inverted weight including the full Lambda.
At non-prime-powers Lambda is zero; no prime-only replacement is made. -/
def alpogeNativeASKRealWeight
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (n : ℕ) (g : AlpogeNativeE0 × H) : ℝ :=
  Λ n * (alpogeNativeColourKernel inertia frob n g).re

/-- The physical weight is nonnegative even though its original character
expansion is signed. The proof retains every positive prime-power exponent. -/
theorem alpogeNativeASKRealWeight_nonneg
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (n : ℕ) (g : AlpogeNativeE0 × H) :
    0 ≤ alpogeNativeASKRealWeight inertia frob n g := by
  classical
  unfold alpogeNativeASKRealWeight
  by_cases hn : Λ n = 0
  · simp [hn]
  · have hpow : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
    apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    rw [alpogeNativeColourKernel_primePower inertia frob p k hp hk g]
    split_ifs
    · have hcast :
          (2 / (((Finset.univ.filter
            (fun u : AlpogeNativeE0 × H => u ∈ inertia p)).card : ℕ) : ℂ)) =
          (((2 : ℝ) / ((Finset.univ.filter
            (fun u : AlpogeNativeE0 × H => u ∈ inertia p)).card : ℝ)) : ℂ) := by
        push_cast
      rw [hcast, Complex.ofReal_re]
      positivity
    · simp

/-- Exact real expansion of the complete native ASK, before any inequality. -/
theorem alpogeNativeFullKernelASK_re_eq_weighted
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) :
    (alpogeNativeFullKernelASK inertia frob N a t w).re =
      ∑ n ∈ Finset.Icc 1 N,
        ∑ g ∈ Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
            ¬ alpogeNativeInPhi g),
          alpogeNativeASKRealWeight inertia frob n g *
            alpogeASKPos (a / (n : ℝ)) (w (alpogeNativePartner t g)) := by
  classical
  simp [alpogeNativeFullKernelASK, alpogeNativeSiteCut,
    alpogeNativeASKRealWeight, alpogeASKPos, Complex.mul_re,
    Finset.mul_sum, mul_assoc]

/-- Pointwise arithmetic midpoint. No geometric realization is presumed. -/
def alpogeWidthMidpoint (w₀ w₁ : AlpogeNativeE0 × H → ℝ) :
    AlpogeNativeE0 × H → ℝ :=
  fun ρ => (w₀ ρ + w₁ ρ) / 2

/-- The actual complete one-sided physical source. -/
def alpogeNativeSignedWidthSource
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) : ℝ :=
  (alpogeNativeFullKernelASK inertia frob N a t w -
    alpogeNativeMAIN ell a w).re

/-- The complete physical ASK midpoint collar. -/
def alpogeNativeASKMidpointCollar
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H)
    (w₀ w₁ : AlpogeNativeE0 × H → ℝ) : ℝ :=
  ((alpogeNativeFullKernelASK inertia frob N a t w₀).re +
      (alpogeNativeFullKernelASK inertia frob N a t w₁).re) / 2 -
    (alpogeNativeFullKernelASK inertia frob N a t
      (alpogeWidthMidpoint w₀ w₁)).re

/-- Only the MAIN logarithmic curvature is charged in the upper direction. -/
def alpogeNativeWidthLogPayment (a : ℝ)
    (w₀ w₁ : AlpogeNativeE0 × H → ℝ) : ℝ :=
  (a / ((alpogeNativePhiSet H).card : ℝ)) *
    ∑ ρ ∈ alpogeNativePhiSet H, alpogeWidthLogMidpointGap (w₀ ρ) (w₁ ρ)

/-- Convexity holds on the full physical source, including inertia, every
character and every prime power, with no factor depending on the host size. -/
theorem alpogeNativeASKMidpointCollar_nonneg
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H)
    (w₀ w₁ : AlpogeNativeE0 × H → ℝ) :
    0 ≤ alpogeNativeASKMidpointCollar inertia frob N a t w₀ w₁ := by
  classical
  have hpoint (z u v : ℝ) :
      alpogeASKPos z ((u + v) / 2) ≤
        (alpogeASKPos z u + alpogeASKPos z v) / 2 := by
    unfold alpogeASKPos
    apply max_le
    · linarith [le_max_left (z - u) 0, le_max_left (z - v) 0]
    · linarith [le_max_right (z - u) 0, le_max_right (z - v) 0]
  have hsum :
      (alpogeNativeFullKernelASK inertia frob N a t
          (alpogeWidthMidpoint w₀ w₁)).re ≤
        ((alpogeNativeFullKernelASK inertia frob N a t w₀).re +
          (alpogeNativeFullKernelASK inertia frob N a t w₁).re) / 2 := by
    simp_rw [alpogeNativeFullKernelASK_re_eq_weighted]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro n hn
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro g hg
    dsimp [alpogeWidthMidpoint]
    have h := mul_le_mul_of_nonneg_left
      (hpoint (a / (n : ℝ)) (w₀ (alpogeNativePartner t g))
        (w₁ (alpogeNativePartner t g)))
      (alpogeNativeASKRealWeight_nonneg inertia frob n g)
    nlinarith
  unfold alpogeNativeASKMidpointCollar
  linarith

/-- Exact recombination in the direction needed for a one-sided source bound.
The complete ASK collar is subtracted, not charged as a positive loss. -/
theorem alpogeNativeSignedWidthSource_midpoint_eq
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a : ℝ) (t : H)
    (w₀ w₁ : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeSignedWidthSource inertia frob ell N a t
        (alpogeWidthMidpoint w₀ w₁) =
      (alpogeNativeSignedWidthSource inertia frob ell N a t w₀ +
        alpogeNativeSignedWidthSource inertia frob ell N a t w₁) / 2 +
      alpogeNativeWidthLogPayment a w₀ w₁ -
      alpogeNativeASKMidpointCollar inertia frob N a t w₀ w₁ := by
  classical
  unfold alpogeNativeSignedWidthSource alpogeNativeASKMidpointCollar
    alpogeNativeWidthLogPayment alpogeWidthLogMidpointGap
    alpogeNativeMAIN alpogeWidthMidpoint
  simp only [Complex.sub_re, Complex.mul_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
  ring

/-- Uniform positive width and displacement give a complete explicit payment;
the cardinal of Phi cancels from the bound, not from an unproved norm. -/
theorem alpogeNativeWidthLogPayment_nonneg_le
    (a b d : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (w₀ w₁ : AlpogeNativeE0 × H → ℝ)
    (hw₀ : ∀ ρ ∈ alpogeNativePhiSet H, b ≤ w₀ ρ)
    (hw₁ : ∀ ρ ∈ alpogeNativePhiSet H, b ≤ w₁ ρ)
    (hd : ∀ ρ ∈ alpogeNativePhiSet H, |w₀ ρ - w₁ ρ| ≤ d) :
    0 ≤ alpogeNativeWidthLogPayment a w₀ w₁ ∧
      alpogeNativeWidthLogPayment a w₀ w₁ ≤ a * d ^ 2 / (8 * b ^ 2) := by
  classical
  have hcardNat : 0 < (alpogeNativePhiSet H).card := by
    apply Finset.card_pos.mpr
    exact ⟨0, by simp [alpogeNativePhiSet, alpogeNativeInPhi]⟩
  have hcard : (0 : ℝ) < ((alpogeNativePhiSet H).card : ℝ) := by
    exact_mod_cast hcardNat
  have hgap (ρ) (hρ : ρ ∈ alpogeNativePhiSet H) :=
    alpogeWidthLogMidpointGap_nonneg_le b (w₀ ρ) (w₁ ρ) d hb
      (hw₀ ρ hρ) (hw₁ ρ hρ) (hd ρ hρ)
  unfold alpogeNativeWidthLogPayment
  constructor
  · apply mul_nonneg (div_nonneg ha hcard.le)
    exact Finset.sum_nonneg (fun ρ hρ => (hgap ρ hρ).1)
  · calc
      _ ≤ (a / ((alpogeNativePhiSet H).card : ℝ)) *
          ∑ _ρ ∈ alpogeNativePhiSet H, d ^ 2 / (8 * b ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg ha hcard.le)
            exact Finset.sum_le_sum (fun ρ hρ => (hgap ρ hρ).2)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp [hcard.ne', hb.ne']

/-- Genuine quantitative one-sided width payment for the complete native
source. Neither row average is assumed small, and no lattice is postulated at
the midpoint. Any geometric upper bound on the actual row average can now be
transported at this fully explicit cost. -/
theorem alpogeNativeSignedWidthSource_midpoint_le
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a b d : ℝ) (t : H) (ha : 0 ≤ a) (hb : 0 < b)
    (w₀ w₁ : AlpogeNativeE0 × H → ℝ)
    (hw₀ : ∀ ρ ∈ alpogeNativePhiSet H, b ≤ w₀ ρ)
    (hw₁ : ∀ ρ ∈ alpogeNativePhiSet H, b ≤ w₁ ρ)
    (hd : ∀ ρ ∈ alpogeNativePhiSet H, |w₀ ρ - w₁ ρ| ≤ d) :
    alpogeNativeSignedWidthSource inertia frob ell N a t
        (alpogeWidthMidpoint w₀ w₁) ≤
      (alpogeNativeSignedWidthSource inertia frob ell N a t w₀ +
        alpogeNativeSignedWidthSource inertia frob ell N a t w₁) / 2 +
        a * d ^ 2 / (8 * b ^ 2) := by
  rw [alpogeNativeSignedWidthSource_midpoint_eq]
  have hcoll := alpogeNativeASKMidpointCollar_nonneg inertia frob N a t w₀ w₁
  have hlog := (alpogeNativeWidthLogPayment_nonneg_le a b d ha hb
    w₀ w₁ hw₀ hw₁ hd).2
  linarith

/-- The source used above is the existing complete native De whenever the
same physical cutoff is valid at every Phi site. -/
theorem alpogeNativeSignedWidthSource_eq_De_re
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ)) :
    alpogeNativeSignedWidthSource inertia frob ell N a t w =
      (alpogeNativeDe inertia frob ell a t w).re := by
  unfold alpogeNativeSignedWidthSource
  rw [alpogeNativeFullASK_sub_MAIN_eq_De inertia frob ell N a t w ha hw hN]

/-- The original HC row progression, allowing every sector and torsion shift
to have its own base `v rho`. Only the actual common row step is shared. -/
def alpogeAffineWidthRow (v : AlpogeNativeE0 × H → ℝ) (h₀ : ℝ)
    (j : ℕ) : AlpogeNativeE0 × H → ℝ :=
  fun ρ => v ρ + ((j : ℝ) + 1 / 2) * h₀

omit [AddCommGroup H] [Fintype H] [DecidableEq H] in
/-- Actual HC row pairs have a pointwise midpoint independent of the row.
This is algebra on their widths, not a claim that a midpoint lattice exists. -/
theorem alpogeAffineWidthRow_pair_midpoint
    (v : AlpogeNativeE0 × H → ℝ) (h₀ : ℝ) (m j : ℕ) (hj : j < m) :
    alpogeWidthMidpoint (alpogeAffineWidthRow v h₀ j)
      (alpogeAffineWidthRow v h₀ (m - 1 - j)) =
        fun ρ => v ρ + (m : ℝ) * h₀ / 2 := by
  have hnat : j + (m - 1 - j) + 1 = m := by omega
  have hcast : (j : ℝ) + ((m - 1 - j : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast hnat
  funext ρ
  dsimp [alpogeWidthMidpoint, alpogeAffineWidthRow]
  nlinarith [congrArg (fun x : ℝ => x * h₀) hcast]

/-- Quantitative payment for the original affine row pairs. The common kernel,
height parameter and j-independent sector/torsion bases are retained. -/
theorem alpogeNativeSignedWidthSource_affine_pair_le
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N m j : ℕ) (a b h₀ : ℝ) (t : H)
    (v : AlpogeNativeE0 × H → ℝ)
    (hj : j < m) (ha : 0 ≤ a) (hb : 0 < b) (hh₀ : 0 ≤ h₀)
    (hv : ∀ ρ ∈ alpogeNativePhiSet H, b ≤ v ρ) :
    alpogeNativeSignedWidthSource inertia frob ell N a t
        (fun ρ => v ρ + (m : ℝ) * h₀ / 2) ≤
      (alpogeNativeSignedWidthSource inertia frob ell N a t
          (alpogeAffineWidthRow v h₀ j) +
        alpogeNativeSignedWidthSource inertia frob ell N a t
          (alpogeAffineWidthRow v h₀ (m - 1 - j))) / 2 +
        a * ((m : ℝ) * h₀) ^ 2 / (8 * b ^ 2) := by
  have hwidth (k : ℕ) (ρ) (hρ : ρ ∈ alpogeNativePhiSet H) :
      b ≤ alpogeAffineWidthRow v h₀ k ρ := by
    dsimp [alpogeAffineWidthRow]
    have hk : (0 : ℝ) ≤ (k : ℝ) + 1 / 2 := by positivity
    nlinarith [hv ρ hρ, mul_nonneg hk hh₀]
  have hnat : j + (m - 1 - j) + 1 = m := by omega
  have hcast : (j : ℝ) + ((m - 1 - j : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast hnat
  have hdist (ρ) (_hρ : ρ ∈ alpogeNativePhiSet H) :
      |alpogeAffineWidthRow v h₀ j ρ -
        alpogeAffineWidthRow v h₀ (m - 1 - j) ρ| ≤ (m : ℝ) * h₀ := by
    dsimp [alpogeAffineWidthRow]
    rw [abs_le]
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ ((m - 1 - j : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor <;> nlinarith [mul_nonneg hj0 hh₀, mul_nonneg hk0 hh₀,
      congrArg (fun x : ℝ => x * h₀) hcast]
  have h := alpogeNativeSignedWidthSource_midpoint_le inertia frob ell N
    a b ((m : ℝ) * h₀) t ha hb
    (alpogeAffineWidthRow v h₀ j) (alpogeAffineWidthRow v h₀ (m - 1 - j))
    (hwidth j) (hwidth (m - 1 - j)) hdist
  rw [alpogeAffineWidthRow_pair_midpoint v h₀ m j hj] at h
  exact h

end Native
end RHLean.Analysis
