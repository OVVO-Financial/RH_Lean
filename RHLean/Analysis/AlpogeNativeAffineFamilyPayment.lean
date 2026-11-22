import RHLean.Analysis.AlpogeNativeWidthRecombination

/-!
# Averaging actual HC row pairs with the derived original normalizer

All row indices occur with their true multiplicity. The involution
`j <-> m - 1 - j` turns the pairwise one-sided width theorem into a bound on
the actual finite family, with variable height `a_t` and unchanged physical
kernel at each frame. The reference is the site-dependent midpoint, not an
artificial constant thick profile and not a newly asserted lattice.

For `Q = |T|*m*b*Delta/2`, minimum width `beta`, and `a_t <= A`, the normalized
curvature price is exactly bounded by

  A*(m*h0)^2 / (4*b*beta^2*Delta).

At the original thin minimum `beta=b/(n*X')`, this is
  A*(m*h0)^2*n^2*X'^2 / (4*b^3*Delta).
These are proved finite formulas, with no asymptotic assertion or critical
source bound hidden in the hypotheses.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- A common cutoff is constructed from the actual height envelope and true
minimum width. This includes ratios from every thin-sector prime power. -/
theorem alpogeWidthRatio_le_natCeil
    (a A beta w : ℝ) (ha : 0 ≤ a) (haA : a ≤ A)
    (hbeta : 0 < beta) (hw : beta ≤ w) :
    a / w ≤ (Nat.ceil (A / beta) : ℝ) := by
  calc
    a / w ≤ a / beta := div_le_div_of_nonneg_left ha hbeta hw
    _ ≤ A / beta := div_le_div_of_nonneg_right haA hbeta.le
    _ ≤ (Nat.ceil (A / beta) : ℝ) := Nat.le_ceil _

/-- Every actual affine row and its pointwise midpoint shares this explicitly
constructed cutoff, even for variable heights. Positivity is supplied too. -/
theorem alpogeAffineWidthFamily_constructed_cutoff
    {ι : Type*} (T : Finset ι) (m : ℕ)
    (a : ι → ℝ) (v : ι → AlpogeNativeE0 × H → ℝ)
    (A beta h₀ : ℝ) (hbeta : 0 < beta) (hh₀ : 0 ≤ h₀)
    (ha : ∀ r ∈ T, 0 ≤ a r) (haA : ∀ r ∈ T, a r ≤ A)
    (hv : ∀ r ∈ T, ∀ ρ ∈ alpogeNativePhiSet H, beta ≤ v r ρ) :
    ∀ r ∈ T,
      (∀ j : Fin m, ∀ ρ ∈ alpogeNativePhiSet H,
        0 < alpogeAffineWidthRow (v r) h₀ j.val ρ ∧
          a r / alpogeAffineWidthRow (v r) h₀ j.val ρ ≤
            (Nat.ceil (A / beta) : ℝ)) ∧
      (∀ ρ ∈ alpogeNativePhiSet H,
        0 < v r ρ + (m : ℝ) * h₀ / 2 ∧
          a r / (v r ρ + (m : ℝ) * h₀ / 2) ≤
            (Nat.ceil (A / beta) : ℝ)) := by
  intro r hr
  constructor
  · intro j ρ hρ
    have hwidth : beta ≤ alpogeAffineWidthRow (v r) h₀ j.val ρ := by
      dsimp [alpogeAffineWidthRow]
      have hstep : 0 ≤ ((j.val : ℝ) + 1 / 2) * h₀ := by positivity
      linarith [hv r hr ρ hρ]
    exact ⟨hbeta.trans_le hwidth, alpogeWidthRatio_le_natCeil
      (a r) A beta _ (ha r hr) (haA r hr) hbeta hwidth⟩
  · intro ρ hρ
    have hwidth : beta ≤ v r ρ + (m : ℝ) * h₀ / 2 := by
      have hstep : 0 ≤ (m : ℝ) * h₀ / 2 := by positivity
      linarith [hv r hr ρ hρ]
    exact ⟨hbeta.trans_le hwidth, alpogeWidthRatio_le_natCeil
      (a r) A beta _ (ha r hr) (haA r hr) hbeta hwidth⟩

/-- The constructed cutoff reaches the existing complete native De. Neither
an arbitrary cutoff premise nor a truncated thin source is assumed. -/
theorem alpogeNativeSignedWidthSource_eq_De_re_at_natCeil
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a A beta : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hbeta : 0 < beta)
    (hw : ∀ ρ ∈ alpogeNativePhiSet H, beta ≤ w ρ) :
    alpogeNativeSignedWidthSource inertia frob ell (Nat.ceil (A / beta)) a t w =
      (alpogeNativeDe inertia frob ell a t w).re := by
  classical
  have hwidth (ρ) (hρ : alpogeNativeInPhi ρ) : beta ≤ w ρ := by
    apply hw ρ
    simpa [alpogeNativePhiSet] using hρ
  exact alpogeNativeSignedWidthSource_eq_De_re inertia frob ell
    (Nat.ceil (A / beta)) a t w ha
    (fun ρ hρ => hbeta.trans_le (hwidth ρ hρ))
    (fun ρ hρ => alpogeWidthRatio_le_natCeil a A beta (w ρ)
      ha.le haA hbeta (hwidth ρ hρ))

/-- Every real HC row is counted once. Its genuine reflected partner supplies
exact first-order cancellation; odd m includes the middle row without loss. -/
theorem alpogeNativeSignedWidthSource_affine_rows_sum_le
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N m : ℕ) (a beta h₀ : ℝ) (t : H)
    (v : AlpogeNativeE0 × H → ℝ)
    (ha : 0 ≤ a) (hbeta : 0 < beta) (hh₀ : 0 ≤ h₀)
    (hv : ∀ ρ ∈ alpogeNativePhiSet H, beta ≤ v ρ) :
    (m : ℝ) * alpogeNativeSignedWidthSource inertia frob ell N a t
        (fun ρ => v ρ + (m : ℝ) * h₀ / 2) ≤
      (∑ j : Fin m, alpogeNativeSignedWidthSource inertia frob ell N a t
        (alpogeAffineWidthRow v h₀ j.val)) +
        (m : ℝ) * a * ((m : ℝ) * h₀) ^ 2 / (8 * beta ^ 2) := by
  classical
  let rev : Fin m → Fin m := fun j => ⟨m - 1 - j.val, by omega⟩
  have hrev : Function.Involutive rev := by
    intro j
    apply Fin.ext
    dsimp [rev]
    omega
  have hreverse :
      (∑ j : Fin m, alpogeNativeSignedWidthSource inertia frob ell N a t
        (alpogeAffineWidthRow v h₀ (m - 1 - j.val))) =
      ∑ j : Fin m, alpogeNativeSignedWidthSource inertia frob ell N a t
        (alpogeAffineWidthRow v h₀ j.val) := by
    exact Fintype.sum_equiv (Equiv.ofInvolutive rev hrev) _ _ (fun _ => rfl)
  have hpoint (j : Fin m) := alpogeNativeSignedWidthSource_affine_pair_le
    inertia frob ell N m j.val a beta h₀ t v j.isLt ha hbeta hh₀ hv
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (fun j _hj => hpoint j)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
    hreverse] at hsum
  nlinarith only [hsum]

/-- The original positive normalizer, retaining frame count, actual theta-row
count, thick base width and density separately. -/
def alpogeNativeHCNormalizer {ι : Type*} (T : Finset ι)
    (m : ℕ) (b Delta : ℝ) : ℝ :=
  (T.card : ℝ) * (m : ℝ) * b * Delta / 2

/-- The complete finite-family comparison with variable frame heights.
The displayed normalized price is derived from the true sum and Q; no factor
of m, host size or width is divided away without its exact identity. -/
theorem alpogeNativeSignedWidthSource_affine_family_normalized_le
    {ι : Type*} (T : Finset ι)
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N m : ℕ) (a : ι → ℝ) (t : ι → H)
    (v : ι → AlpogeNativeE0 × H → ℝ)
    (A b beta Delta h₀ : ℝ)
    (hT : T.Nonempty) (hm : 0 < m)
    (hb : 0 < b) (hbeta : 0 < beta) (hDelta : 0 < Delta)
    (hh₀ : 0 ≤ h₀)
    (ha : ∀ r ∈ T, 0 ≤ a r)
    (haA : ∀ r ∈ T, a r ≤ A)
    (hv : ∀ r ∈ T, ∀ ρ ∈ alpogeNativePhiSet H, beta ≤ v r ρ) :
    (∑ r ∈ T, (m : ℝ) * alpogeNativeSignedWidthSource
        inertia frob ell N (a r) (t r)
          (fun ρ => v r ρ + (m : ℝ) * h₀ / 2)) /
        alpogeNativeHCNormalizer T m b Delta ≤
      (∑ r ∈ T, ∑ j : Fin m, alpogeNativeSignedWidthSource
        inertia frob ell N (a r) (t r) (alpogeAffineWidthRow (v r) h₀ j.val)) /
        alpogeNativeHCNormalizer T m b Delta +
        A * ((m : ℝ) * h₀) ^ 2 / (4 * b * beta ^ 2 * Delta) := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hTR : (0 : ℝ) < (T.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hQ : 0 < alpogeNativeHCNormalizer T m b Delta := by
    unfold alpogeNativeHCNormalizer
    positivity
  have hframe (r) (hr : r ∈ T) :
      (m : ℝ) * alpogeNativeSignedWidthSource inertia frob ell N (a r) (t r)
          (fun ρ => v r ρ + (m : ℝ) * h₀ / 2) ≤
        (∑ j : Fin m, alpogeNativeSignedWidthSource inertia frob ell N
          (a r) (t r) (alpogeAffineWidthRow (v r) h₀ j.val)) +
          (m : ℝ) * A * ((m : ℝ) * h₀) ^ 2 / (8 * beta ^ 2) := by
    have h := alpogeNativeSignedWidthSource_affine_rows_sum_le inertia frob
      ell N m (a r) beta h₀ (t r) (v r) (ha r hr) hbeta hh₀ (hv r hr)
    have hcost : (m : ℝ) * (a r) * ((m : ℝ) * h₀) ^ 2 / (8 * beta ^ 2) ≤
        (m : ℝ) * A * ((m : ℝ) * h₀) ^ 2 / (8 * beta ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (haA r hr) hmR.le) (sq_nonneg _)
    linarith
  have hsum := Finset.sum_le_sum hframe
  have hdiv := div_le_div_of_nonneg_right hsum hQ.le
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hdiv
  calc
    _ ≤ ((∑ r ∈ T, ∑ j : Fin m, alpogeNativeSignedWidthSource
          inertia frob ell N (a r) (t r) (alpogeAffineWidthRow (v r) h₀ j.val)) +
        (T.card : ℝ) * ((m : ℝ) * A * ((m : ℝ) * h₀) ^ 2 /
          (8 * beta ^ 2))) / alpogeNativeHCNormalizer T m b Delta := hdiv
    _ = _ := by
      unfold alpogeNativeHCNormalizer
      field_simp [hTR.ne', hmR.ne', hb.ne', hbeta.ne', hDelta.ne']
      ring

/-- Substituting the actual smallest HC base keeps the host and exponential
thin scale visible. This is a finite exact identity, not an asymptotic claim. -/
theorem alpogeNativeHC_thin_minimum_payment
    (A b n Xprime Delta d : ℝ)
    (hb : b ≠ 0) (hn : n ≠ 0) (hXprime : Xprime ≠ 0) (hDelta : Delta ≠ 0) :
    A * d ^ 2 / (4 * b * (b / (n * Xprime)) ^ 2 * Delta) =
      A * d ^ 2 * n ^ 2 * Xprime ^ 2 / (4 * b ^ 3 * Delta) := by
  field_simp [hb, hn, hXprime, hDelta]
  ring

/-- The actual height window A <= 2*x*b pays the full-profile curvature at
the explicit thin-scale cost. This still exposes every host/row factor. -/
theorem alpogeNativeHC_thin_minimum_payment_le
    (A x b n Xprime Delta d : ℝ)
    (hb : 0 < b) (hn : n ≠ 0) (hXprime : Xprime ≠ 0) (hDelta : 0 < Delta)
    (hA : A ≤ 2 * x * b) :
    A * d ^ 2 / (4 * b * (b / (n * Xprime)) ^ 2 * Delta) ≤
      x * d ^ 2 * n ^ 2 * Xprime ^ 2 / (2 * b ^ 2 * Delta) := by
  rw [alpogeNativeHC_thin_minimum_payment A b n Xprime Delta d
    hb.ne' hn hXprime hDelta.ne']
  have hcoef : 0 ≤ d ^ 2 * n ^ 2 * Xprime ^ 2 := by positivity
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hA hcoef)
    (show 0 ≤ 4 * b ^ 3 * Delta by positivity)
  calc
    _ = A * (d ^ 2 * n ^ 2 * Xprime ^ 2) / (4 * b ^ 3 * Delta) := by ring
    _ ≤ (2 * x * b) * (d ^ 2 * n ^ 2 * Xprime ^ 2) / (4 * b ^ 3 * Delta) := h
    _ = _ := by
      field_simp [hb.ne', hDelta.ne']
      ring

end RHLean.Analysis
