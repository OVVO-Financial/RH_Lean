import RHLean.Geometry.NativeThetaCuspShiftedLattice

/-!
# One actual half-root phase for the original and shifted lattices

The rational common phase is identified with the literal trace expression
on the original E-space. Integral self-duality and the actual integral
half-root prove its square-one and semicharacter laws on any of the
constructed conjugate-level shifts. Both lattices therefore use the same
function on the same ambient space; no inverse outside an integral image
and no independent phase choice is involved.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/
IsSystem.lean (`epsW`) and Proofs/SiegelThetaTransformation/
TensorLatticeSelfDualSemicharacterIndex.lean (`epsW_semichar`). The native
symplectic coordinates use Omega = +EF, so the displayed Heisenberg cocycle
has the same positive sign as the previously verified native vacuum.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module
open scoped Pointwise nonZeroDivisors BigOperators TensorProduct

namespace RHLean.Geometry.NativeTheta.Cusp.ShiftedPhase

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open NativePrescribedHermitian ShiftedLattice

variable {φ : Frame} (H : HostRaw φ)

/-- The half-root quadratic function on the entire literal field ambient. -/
def quadratic {N : ℕ} (neg : Fin N → Bool) (w : 𝓞 H.E) (x : Fin N → H.E) : ℚ :=
  Ambient.pair H neg x (w • x)

theorem quadratic_add {N : ℕ} (neg : Fin N → Bool) (w : 𝓞 H.E)
    (hw : w + bar H w = 1) (x y : Fin N → H.E) :
    quadratic H neg w (x + y) = quadratic H neg w x + quadratic H neg w y +
      Ambient.pair H neg x y - 2 * Ambient.pair H neg x (bar H w • y) := by
  have h1 : Ambient.pair H neg y (w • x) =
      -Ambient.pair H neg x (bar H w • y) := by
    rw [Ambient.pair_skew, Ambient.pair_adjoint]
    rfl
  have h2 : Ambient.pair H neg x (w • y) + Ambient.pair H neg x (bar H w • y) =
      Ambient.pair H neg x y := by
    rw [← Ambient.pair_add_right, ← add_smul, hw, one_smul]
  simp only [quadratic, smul_add, Ambient.pair_add_left, Ambient.pair_add_right]
  linarith

variable {κ : Type} [Fintype κ]

/-- A single phase, independent of the original or shifted lattice. -/
def phase {N : ℕ} (neg : Fin N → Bool) (w : 𝓞 H.E) (x : κ → Fin N → H.E) : ℂ :=
  Complex.exp (Real.pi * Complex.I * ((∑ k, quadratic H neg w (x k) : ℚ) : ℂ))

theorem norm_phase {N : ℕ} (neg : Fin N → Bool) (w : 𝓞 H.E)
    (x : κ → Fin N → H.E) : ‖phase H neg w x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

@[simp] theorem phase_zero {N : ℕ} (neg : Fin N → Bool) (w : 𝓞 H.E) :
    phase H (κ := κ) neg w 0 = 1 := by
  simp [phase, quadratic, Ambient.pair]

/-- Square-one values follow from actual integral pairings, including on
the shifted lattice. -/
theorem phase_sq {N : ℕ} {neg : Fin N → Bool} (w : 𝓞 H.E)
    {L : Submodule (𝓞 H.E) (Fin N → H.E)} (hL : SelfDual H neg L)
    (x : κ → Fin N → H.E) (hx : ∀ k, x k ∈ L) : phase H neg w x ^ 2 = 1 := by
  choose z hz using fun k => (hL.2 (x k)).1 (hx k) (w • x k) (L.smul_mem w (hx k))
  have hq : (∑ k, quadratic H neg w (x k) : ℚ) = ((∑ k, z k : ℤ) : ℚ) := by
    simp only [quadratic, hz, Int.cast_sum]
  rw [phase, pow_two, ← Complex.exp_add, hq]
  have he : Real.pi * Complex.I * (((∑ k, z k : ℤ) : ℚ) : ℂ) +
      Real.pi * Complex.I * (((∑ k, z k : ℤ) : ℚ) : ℂ) =
        ((∑ k, z k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- The same global phase satisfies the required Heisenberg cocycle on
each actual self-dual integral lattice. -/
theorem phase_add {N : ℕ} {neg : Fin N → Bool} (w : 𝓞 H.E)
    (hw : w + bar H w = 1)
    {L : Submodule (𝓞 H.E) (Fin N → H.E)} (hL : SelfDual H neg L)
    (x y : κ → Fin N → H.E) (hx : ∀ k, x k ∈ L) (hy : ∀ k, y k ∈ L) :
    phase H neg w (x + y) = phase H neg w x * phase H neg w y *
      Complex.exp (Real.pi * Complex.I *
        ((∑ k, Ambient.pair H neg (x k) (y k) : ℚ) : ℂ)) := by
  choose z hz using fun k =>
    (hL.2 (x k)).1 (hx k) (bar H w • y k) (L.smul_mem _ (hy k))
  have hq : (∑ k, quadratic H neg w ((x + y) k)) =
      (∑ k, quadratic H neg w (x k)) + (∑ k, quadratic H neg w (y k)) +
        (∑ k, Ambient.pair H neg (x k) (y k)) - 2 * ((∑ k, z k : ℤ) : ℚ) := by
    simp only [Pi.add_apply, quadratic_add H neg w hw, hz, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Int.cast_sum, Finset.mul_sum]
  simp only [phase]
  rw [hq]
  have he : Real.pi * Complex.I *
      (((∑ k, quadratic H neg w (x k)) + (∑ k, quadratic H neg w (y k)) +
        (∑ k, Ambient.pair H neg (x k) (y k)) - 2 * ((∑ k, z k : ℤ) : ℚ) : ℚ) : ℂ) =
      Real.pi * Complex.I * ((∑ k, quadratic H neg w (x k) : ℚ) : ℂ) +
      Real.pi * Complex.I * ((∑ k, quadratic H neg w (y k) : ℚ) : ℂ) +
      Real.pi * Complex.I * ((∑ k, Ambient.pair H neg (x k) (y k) : ℚ) : ℂ) +
      ((-(∑ k, z k) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    Complex.exp_add, Complex.exp_add]

theorem phase_two {N : ℕ} {neg : Fin N → Bool} (w : 𝓞 H.E)
    (hw : w + bar H w = 1)
    {L : Submodule (𝓞 H.E) (Fin N → H.E)} (hL : SelfDual H neg L)
    (x : κ → Fin N → H.E) (hx : ∀ k, x k ∈ L) : phase H neg w (2 • x) = 1 := by
  rw [two_nsmul, phase_add H w hw hL x x hx hx]
  simp only [Ambient.pair_self, Finset.sum_const_zero, Rat.cast_zero, mul_zero,
    Complex.exp_zero, ← pow_two, phase_sq H w hL x hx, one_pow]

section Prescribed

variable [IsCMField H.E]
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = starRingEnd ℂ (τ x))
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m)

set_option backward.isDefEq.respectTransparency false in
/-- The global field phase equals the already constructed common rational
phase of the exact prescribed datum. -/
theorem prescribed_commonPhase
    (x : κ → RationalCoordinates.Space (prescribedLattice H B k m)) :
    RationalCoordinates.commonPhase
        (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj) x =
      phase H (negTail (k + m - 1) (m - j)) G.w0
        (fun a => Ambient.equiv H B hB (k + m - 1) (x a)) := by
  have hq (a : κ) :
      RationalCoordinates.quadratic
          (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj) (x a) =
        quadratic H (negTail (k + m - 1) (m - j)) G.w0
          (Ambient.equiv H B hB (k + m - 1) (x a)) := by
    unfold RationalCoordinates.quadratic RationalCoordinates.form
    rw [prescribedGeometricDatum_form]
    change (twistedTraceForm H B hB (negTail (k + m - 1) (m - j))).baseChange ℚ
      (x a) (((LinearMap.lsmul (𝓞 H.E) (prescribedLattice H B k m) G.w0).restrictScalars ℤ).
        baseChange ℚ (x a)) = _
    rw [Ambient.equiv_pairing, Ambient.equiv_action]
  simp only [RationalCoordinates.commonPhase, phase, hq]

include hbar in
/-- The half-root identity used for both lattices is supplied by the same
actual geometric host, with its proved native conjugation comparison. -/
theorem prescribed_halfRoot : G.w0 + bar H G.w0 = 1 := by
  have h := AppellHumbert.weight_add_bar G
  rw [hbar] at h
  exact h

end Prescribed

end RHLean.Geometry.NativeTheta.Cusp.ShiftedPhase
