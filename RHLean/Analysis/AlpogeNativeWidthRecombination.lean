import RHLean.Analysis.AlpogeNativeSignedWidthPayment

/-!
# Oriented full-source tangent recombination and exact normalization

The sign convention is `D(c) = D(w) + C + Jlog - Jcoll`. Both remainders are
nonnegative under the physical positivity hypotheses, but only Jlog is a cost
in this upper direction. C is the single complete centered linear response,
including the MAIN logarithm. At the pointwise midpoint of two actual rows,
the two responses cancel exactly without requiring a midpoint lattice.

Common positive scaling of all widths and the height parameter scales the
complete physical ASK-MAIN by exactly the same amount. This is the scaling
that may be used in a derived normalization; arbitrary division is not used.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

section Tangent

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The physical ASK part of the linear width response. -/
def alpogeNativeASKWidthResponse
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H) (c w : AlpogeNativeE0 × H → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ∑ g ∈ Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
        ¬ alpogeNativeInPhi g),
      alpogeNativeASKRealWeight inertia frob n g *
        alpogeASKLinearWidthShift (a / (n : ℝ))
          (c (alpogeNativePartner t g)) (w (alpogeNativePartner t g))

/-- The single centered response, including the MAIN logarithmic slope. -/
def alpogeNativeCenteredWidthResponse
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H) (c w : AlpogeNativeE0 × H → ℝ) : ℝ :=
  alpogeNativeASKWidthResponse inertia frob N a t c w -
    (a / ((alpogeNativePhiSet H).card : ℝ)) *
      ∑ ρ ∈ alpogeNativePhiSet H, (w ρ - c ρ) / c ρ

/-- Positive logarithmic curvature left after removing the MAIN slope. -/
def alpogeNativeWidthLogTangentCost (a : ℝ)
    (c w : AlpogeNativeE0 × H → ℝ) : ℝ :=
  (a / ((alpogeNativePhiSet H).card : ℝ)) *
    ∑ ρ ∈ alpogeNativePhiSet H,
      ((w ρ - c ρ) / c ρ - (Real.log (w ρ) - Real.log (c ρ)))

/-- The complete positive physical collar, with the actual site cutoffs. -/
def alpogeNativeWidthTangentCollar
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H) (c w : AlpogeNativeE0 × H → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ∑ g ∈ Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
        ¬ alpogeNativeInPhi g),
      alpogeNativeASKRealWeight inertia frob n g *
        alpogeASKSharpCollarRemainder (a / (n : ℝ))
          (c (alpogeNativePartner t g)) (w (alpogeNativePartner t g))

theorem alpogeNativeWidthTangentCollar_nonneg
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H) (c w : AlpogeNativeE0 × H → ℝ) :
    0 ≤ alpogeNativeWidthTangentCollar inertia frob N a t c w := by
  classical
  unfold alpogeNativeWidthTangentCollar
  apply Finset.sum_nonneg
  intro n hn
  apply Finset.sum_nonneg
  intro g hg
  exact mul_nonneg (alpogeNativeASKRealWeight_nonneg inertia frob n g)
    (alpogeASKSharpCollarRemainder_nonneg _ _ _)

theorem alpogeNativeWidthLogTangentCost_nonneg
    (a : ℝ) (ha : 0 ≤ a) (c w : AlpogeNativeE0 × H → ℝ)
    (hc : ∀ ρ ∈ alpogeNativePhiSet H, 0 < c ρ)
    (hw : ∀ ρ ∈ alpogeNativePhiSet H, 0 < w ρ) :
    0 ≤ alpogeNativeWidthLogTangentCost a c w := by
  classical
  unfold alpogeNativeWidthLogTangentCost
  apply mul_nonneg (div_nonneg ha (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro ρ hρ
  have h := Real.log_le_sub_one_of_pos (div_pos (hw ρ hρ) (hc ρ hρ))
  rw [Real.log_div (hw ρ hρ).ne' (hc ρ hρ).ne'] at h
  have heq : (w ρ - c ρ) / c ρ = w ρ / c ρ - 1 := by
    field_simp [(hc ρ hρ).ne']
  rw [heq]
  linarith

/-- Exact tangent identity on every prime power and physical site. -/
theorem alpogeNativeFullKernelASK_re_eq_tangent
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H) (c w : AlpogeNativeE0 × H → ℝ) :
    (alpogeNativeFullKernelASK inertia frob N a t w).re =
      (alpogeNativeFullKernelASK inertia frob N a t c).re -
        alpogeNativeASKWidthResponse inertia frob N a t c w +
        alpogeNativeWidthTangentCollar inertia frob N a t c w := by
  classical
  simp_rw [alpogeNativeFullKernelASK_re_eq_weighted]
  unfold alpogeNativeASKWidthResponse alpogeNativeWidthTangentCollar
    alpogeASKSharpCollarRemainder
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- The exact oriented recombination requested by the one-sided consumer.
The real physical character source is preserved throughout. -/
theorem alpogeNativeSignedWidthSource_eq_oriented_recombination
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a : ℝ) (t : H) (c w : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeSignedWidthSource inertia frob ell N a t c =
      alpogeNativeSignedWidthSource inertia frob ell N a t w +
        alpogeNativeCenteredWidthResponse inertia frob N a t c w +
        alpogeNativeWidthLogTangentCost a c w -
        alpogeNativeWidthTangentCollar inertia frob N a t c w := by
  classical
  unfold alpogeNativeSignedWidthSource
  simp only [Complex.sub_re]
  rw [alpogeNativeFullKernelASK_re_eq_tangent inertia frob N a t c w]
  unfold alpogeNativeCenteredWidthResponse alpogeNativeWidthLogTangentCost
    alpogeNativeMAIN
  simp only [Complex.sub_re, Complex.mul_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [Finset.sum_sub_distrib]
  ring

/-- The complete first-order response cancels on each actual row pair.
The reference may vary by site, including j-independent torsion shifts. -/
theorem alpogeNativeCenteredWidthResponse_midpoint_pair
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H)
    (w₀ w₁ : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeCenteredWidthResponse inertia frob N a t
        (alpogeWidthMidpoint w₀ w₁) w₀ +
      alpogeNativeCenteredWidthResponse inertia frob N a t
        (alpogeWidthMidpoint w₀ w₁) w₁ = 0 := by
  classical
  have hlin (z u v : ℝ) :
      alpogeASKLinearWidthShift z ((u + v) / 2) u +
        alpogeASKLinearWidthShift z ((u + v) / 2) v = 0 := by
    unfold alpogeASKLinearWidthShift
    split_ifs <;> ring
  have hraw :
      alpogeNativeASKWidthResponse inertia frob N a t
          (alpogeWidthMidpoint w₀ w₁) w₀ +
        alpogeNativeASKWidthResponse inertia frob N a t
          (alpogeWidthMidpoint w₀ w₁) w₁ = 0 := by
    unfold alpogeNativeASKWidthResponse alpogeWidthMidpoint
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro n hn
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro g hg
    rw [← mul_add, hlin, mul_zero]
  have hmain :
      (∑ ρ ∈ alpogeNativePhiSet H,
        (w₀ ρ - alpogeWidthMidpoint w₀ w₁ ρ) /
          alpogeWidthMidpoint w₀ w₁ ρ) +
      (∑ ρ ∈ alpogeNativePhiSet H,
        (w₁ ρ - alpogeWidthMidpoint w₀ w₁ ρ) /
          alpogeWidthMidpoint w₀ w₁ ρ) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro ρ hρ
    dsimp [alpogeWidthMidpoint]
    ring
  unfold alpogeNativeCenteredWidthResponse
  nlinarith [congrArg (fun x : ℝ =>
    (a / ((alpogeNativePhiSet H).card : ℝ)) * x) hmain]

end Tangent

section Scaling

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Exact homogeneity of the original complete De. All character coefficients,
including ell and the Frobenius/inertia data, are held fixed. -/
theorem alpogeNativeDe_mul_scale
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a α : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (hα : α ≠ 0) :
    alpogeNativeDe inertia frob ell (α * a) t (fun ρ => α * w ρ) =
      (α : ℂ) * alpogeNativeDe inertia frob ell a t w := by
  classical
  have hratio (x : ℝ) : (α * a) / (α * x) = a / x := by
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hα, hx]
  unfold alpogeNativeDe
  simp_rw [hratio]
  have hterm (g : AlpogeNativeE0 × H)
      (ψ : AddChar (AlpogeNativeE0 × H) ℂ) :
      starRingEnd ℂ (ψ g) * ((α * w (alpogeNativePartner t g) : ℝ) : ℂ) *
          alpogeNativeFrobInertiaGPsi inertia frob ell ψ
            (a / w (alpogeNativePartner t g)) =
        (α : ℂ) * (starRingEnd ℂ (ψ g) *
          ((w (alpogeNativePartner t g) : ℝ) : ℂ) *
            alpogeNativeFrobInertiaGPsi inertia frob ell ψ
              (a / w (alpogeNativePartner t g))) := by
    push_cast
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  ring

/-- Positive scaling of ASK-MAIN follows through the original complete native
identity, with the same cutoff N. The cutoff condition is transported exactly,
not dropped or enlarged. -/
theorem alpogeNativeSignedWidthSource_pos_scale
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a α : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a) (hα : 0 < α)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ)) :
    alpogeNativeSignedWidthSource inertia frob ell N (α * a) t
        (fun ρ => α * w ρ) =
      α * alpogeNativeSignedWidthSource inertia frob ell N a t w := by
  have hw' : ∀ ρ, alpogeNativeInPhi ρ → 0 < α * w ρ := by
    intro ρ hρ
    exact mul_pos hα (hw ρ hρ)
  have hN' : ∀ ρ, alpogeNativeInPhi ρ →
      (α * a) / (α * w ρ) ≤ (N : ℝ) := by
    intro ρ hρ
    have hratio : (α * a) / (α * w ρ) = a / w ρ := by
      field_simp [hα.ne', (hw ρ hρ).ne']
    rw [hratio]
    exact hN ρ hρ
  rw [alpogeNativeSignedWidthSource_eq_De_re inertia frob ell N (α * a) t
      (fun ρ => α * w ρ) (mul_pos hα ha) hw' hN',
    alpogeNativeSignedWidthSource_eq_De_re inertia frob ell N a t w ha hw hN,
    alpogeNativeDe_mul_scale inertia frob ell a α t w hα.ne']
  simp [Complex.mul_re]

/-- A source/Q normalization is invariant precisely when Q scales with the
actual common height/width scaling. This does not supply a geometric value of Q. -/
theorem alpogeNativeSignedWidthSource_normalized_pos_scale
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a α Q : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a) (hα : 0 < α) (hQ : Q ≠ 0)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ)) :
    alpogeNativeSignedWidthSource inertia frob ell N (α * a) t
        (fun ρ => α * w ρ) / (α * Q) =
      alpogeNativeSignedWidthSource inertia frob ell N a t w / Q := by
  rw [alpogeNativeSignedWidthSource_pos_scale inertia frob ell N a α t w
    ha hα hw hN]
  field_simp [hα.ne', hQ]

/-- The exact quantitative midpoint payment after a positive, explicitly
specified normalization. All dependence on a/Q and the true minimum width
remains visible for the geometric supplier. -/
theorem alpogeNativeSignedWidthSource_midpoint_normalized_le
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a b d Q : ℝ) (t : H)
    (ha : 0 ≤ a) (hb : 0 < b) (hQ : 0 < Q)
    (w₀ w₁ : AlpogeNativeE0 × H → ℝ)
    (hw₀ : ∀ ρ ∈ alpogeNativePhiSet H, b ≤ w₀ ρ)
    (hw₁ : ∀ ρ ∈ alpogeNativePhiSet H, b ≤ w₁ ρ)
    (hd : ∀ ρ ∈ alpogeNativePhiSet H, |w₀ ρ - w₁ ρ| ≤ d) :
    alpogeNativeSignedWidthSource inertia frob ell N a t
        (alpogeWidthMidpoint w₀ w₁) / Q ≤
      (alpogeNativeSignedWidthSource inertia frob ell N a t w₀ +
        alpogeNativeSignedWidthSource inertia frob ell N a t w₁) / (2 * Q) +
        (a / Q) * d ^ 2 / (8 * b ^ 2) := by
  calc
    _ ≤ ((alpogeNativeSignedWidthSource inertia frob ell N a t w₀ +
          alpogeNativeSignedWidthSource inertia frob ell N a t w₁) / 2 +
          a * d ^ 2 / (8 * b ^ 2)) / Q :=
      div_le_div_of_nonneg_right
        (alpogeNativeSignedWidthSource_midpoint_le inertia frob ell N a b d t
          ha hb w₀ w₁ hw₀ hw₁ hd) hQ.le
    _ = _ := by
      field_simp [hQ.ne', hb.ne']
      ring

end Scaling

end RHLean.Analysis
