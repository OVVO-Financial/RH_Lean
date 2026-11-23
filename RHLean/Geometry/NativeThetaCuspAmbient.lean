import RHLean.Geometry.NativeThetaCuspRationalCoordinates

/-!
# The literal field ambient of the rationalized native lattice

Localization of the actual inverse-half-different lattice identifies its
integer rationalization with the original prescribed E-vector space. The
identification is proved on pure tensors and carries the original integer
polarization to its literal rational trace formula, without a basis or
principal-ideal replacement. This permits the conjugate level shift to be
performed in the same rational ambient used by the common half-root phase.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/
HMatMulVecPerCrd.lean (`vecQ`, `EF_vecQ`). The proof uses native localization
and Mathlib's universal base-change equivalence. The source mirror states
no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module
open scoped TensorProduct Pointwise nonZeroDivisors BigOperators

namespace RHLean.Geometry.NativeTheta.Cusp.Ambient

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open NativePrescribedHermitian

variable {φ : Frame} (H : HostRaw φ)

private theorem localized_over_int {N : ℕ}
    (L : Submodule (𝓞 H.E) (Fin N → H.E))
    [IsLocalizedModule (𝓞 H.E)⁰ L.subtype] :
    IsLocalizedModule (nonZeroDivisors ℤ) (L.subtype.restrictScalars ℤ) := by
  let T := Algebra.algebraMapSubmonoid (𝓞 H.E) (nonZeroDivisors ℤ)
  have hdvd : ∀ s ∈ (𝓞 H.E)⁰, ∃ n : ℤ, n ≠ 0 ∧ s ∣ (n : 𝓞 H.E) := fun s hs => by
    obtain ⟨r, hr, hd⟩ := IsAlgebraic.exists_nonzero_dvd (R := ℤ)
      (Algebra.IsIntegral.isIntegral (R := ℤ) s).isAlgebraic hs
    exact ⟨r, hr, by simpa using hd⟩
  have hT : ∀ t ∈ T, t ≠ 0 := by
    rintro _ ⟨n, hn, rfl⟩
    simpa using nonZeroDivisors.ne_zero hn
  have : IsLocalization T H.E :=
    { map_units := fun t => IsLocalization.map_units H.E (M := (𝓞 H.E)⁰)
        ⟨t, mem_nonZeroDivisors_of_ne_zero (hT t t.2)⟩
      surj := fun z => by
        obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj (𝓞 H.E)⁰ z
        obtain ⟨n, hn, t, ht⟩ := hdvd s s.2
        refine ⟨⟨a * t, ⟨(n : 𝓞 H.E), n,
          mem_nonZeroDivisors_of_ne_zero hn, by simp⟩⟩, ?_⟩
        simp only [ht, map_mul] at hz ⊢
        rw [← hz]
        ring
      exists_of_eq := fun {x y} h =>
        ⟨1, by simpa using IsFractionRing.injective (𝓞 H.E) H.E h⟩ }
  have : IsLocalizedModule T L.subtype := by
    rw [isLocalizedModule_iff_isBaseChange T H.E,
      ← isLocalizedModule_iff_isBaseChange (𝓞 H.E)⁰ H.E]
    infer_instance
  exact IsLocalizedModule.restrictScalars _ L.subtype

/-- The rationalization is the actual original field space. -/
def equiv (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    RationalCoordinates.Space (twistedLattice H B N) ≃ₗ[ℚ] (Fin N → H.E) := by
  have := twistedLattice_isLocalized H B hB N
  have := localized_over_int H (twistedLattice H B N)
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ
    ((twistedLattice H B N).subtype.restrictScalars ℤ)).equiv

@[simp] theorem equiv_tmul (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (q : ℚ) (x : twistedLattice H B N) :
    equiv H B hB N (q ⊗ₜ[ℤ] x) = q • (x : Fin N → H.E) := rfl

@[simp] theorem equiv_integral (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (x : twistedLattice H B N) :
    equiv H B hB N ((1 : ℚ) ⊗ₜ[ℤ] x) = (x : Fin N → H.E) := by
  rw [equiv_tmul, one_smul]

attribute [local instance] NativeRawHostPolarization.conjugationStar

/-- The original trace formula on every field vector. -/
def pair {N : ℕ} (neg : Fin N → Bool) (x y : Fin N → H.E) : ℚ :=
  Algebra.trace ℚ H.E (xi H * diagForm N neg x y)

theorem pair_add_left {N : ℕ} (neg : Fin N → Bool) (x x' y : Fin N → H.E) :
    pair H neg (x + x') y = pair H neg x y + pair H neg x' y := by
  simp only [pair, LinearMap.map_add₂, mul_add, map_add]

theorem pair_add_right {N : ℕ} (neg : Fin N → Bool) (x y y' : Fin N → H.E) :
    pair H neg x (y + y') = pair H neg x y + pair H neg x y' := by
  simp only [pair, map_add, mul_add]

theorem pair_smul_left {N : ℕ} (neg : Fin N → Bool) (q : ℚ)
    (x y : Fin N → H.E) : pair H neg (q • x) y = q * pair H neg x y := by
  change Algebra.trace ℚ H.E
    (xi H * ∑ i, H.conj (q • x i) * sgn (neg i) * y i) =
      q * Algebra.trace ℚ H.E (xi H * ∑ i, H.conj (x i) * sgn (neg i) * y i)
  simp only [map_smul, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm,
    smul_eq_mul]

theorem pair_smul_right {N : ℕ} (neg : Fin N → Bool) (q : ℚ)
    (x y : Fin N → H.E) : pair H neg x (q • y) = q * pair H neg x y := by
  change Algebra.trace ℚ H.E
    (xi H * ∑ i, H.conj (x i) * sgn (neg i) * (q • y i)) =
      q * Algebra.trace ℚ H.E (xi H * ∑ i, H.conj (x i) * sgn (neg i) * y i)
  simp only [mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul]

/-- Conjugate adjointness on the entire original E-space. -/
theorem pair_adjoint_field {N : ℕ} (neg : Fin N → Bool) (a : H.E)
    (x y : Fin N → H.E) :
    pair H neg (a • x) y = pair H neg x (H.conj a • y) := by
  change Algebra.trace ℚ H.E
    (xi H * ∑ i, H.conj (a * x i) * sgn (neg i) * y i) =
      Algebra.trace ℚ H.E
        (xi H * ∑ i, H.conj (x i) * sgn (neg i) * (H.conj a * y i))
  congr 2
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring

theorem pair_adjoint {N : ℕ} (neg : Fin N → Bool) (a : 𝓞 H.E)
    (x y : Fin N → H.E) :
    pair H neg (a • x) y = pair H neg x ((H.conj • a) • y) :=
  pair_adjoint_field H neg (a : H.E) x y

theorem pair_self {N : ℕ} (neg : Fin N → Bool) (x : Fin N → H.E) :
    pair H neg x x = 0 := by
  have he : H.conj (diagForm N neg x x) = diagForm N neg x x := by
    change H.conj (∑ i, H.conj (x i) * sgn (neg i) * x i) =
      ∑ i, H.conj (x i) * sgn (neg i) * x i
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_mul, map_mul, conj_conj, map_sgn]
      ring
  have ht := Algebra.trace_eq_of_algEquiv H.conj (xi H * diagForm N neg x x)
  rw [map_mul, conj_xi, he, neg_mul, map_neg] at ht
  dsimp only [pair]
  linarith

theorem pair_skew {N : ℕ} (neg : Fin N → Bool) (x y : Fin N → H.E) :
    pair H neg y x = -pair H neg x y := by
  have h := pair_self H neg (x + y)
  rw [pair_add_left, pair_add_right, pair_add_right, pair_self, pair_self] at h
  linarith

/-- The rationalized perfect form is exactly the literal ambient trace. -/
theorem equiv_pairing (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool)
    (x y : RationalCoordinates.Space (twistedLattice H B N)) :
    (twistedTraceForm H B hB neg).baseChange ℚ x y =
      pair H neg (equiv H B hB N x) (equiv H B hB N y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, pair_add_left, hx, hx']
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [map_add, pair_add_right, hy, hy']
    | tmul q' y =>
      rw [LinearMap.BilinForm.baseChange_tmul, equiv_tmul, equiv_tmul,
        pair_smul_left, pair_smul_right]
      change (twistedTraceForm H B hB neg x y : ℤ) • (q * q') = _
      rw [zsmul_eq_mul, twistedTraceForm_cast]
      change _ = q * (q' * Algebra.trace ℚ H.E (xi H * diagForm N neg x.1 y.1))
      ring

/-- The ambient equivalence respects the actual CM action on pure tensors
and hence on the full rationalization. -/
theorem equiv_action (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (a : 𝓞 H.E) (x : RationalCoordinates.Space (twistedLattice H B N)) :
    equiv H B hB N
      (((LinearMap.lsmul (𝓞 H.E) (twistedLattice H B N) a).restrictScalars ℤ).baseChange ℚ x) =
        a • equiv H B hB N x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul q x =>
    rw [LinearMap.baseChange_tmul, equiv_tmul, equiv_tmul]
    change q • (a • (x : Fin N → H.E)) = a • (q • (x : Fin N → H.E))
    exact smul_comm _ _ _

end RHLean.Geometry.NativeTheta.Cusp.Ambient
