import RHLean.Geometry.NativeThetaCuspFlagConstruction
import RHLean.Geometry.NativeThetaCuspAmbient
import RHLean.Geometry.NativePrescribedGeometricDatum

/-!
# Full flag data on the literal native trace-polarized lattice

The flag form is linear in its first argument. Its matrix is the NEGATIVE
of the original native diagonal Gram matrix, on the same ambient space and
the same inverse-half-different lattice. Thus its positive flag dimension
is the original Datum.q, and trace conjugation proves that its alternating
form is exactly +EF. An explicit reversal matrix proves its signature.

The principal congruence modulus is five. The integral transvection depth
is exactly 5*|discr(E)|; integrality follows from the actual trace-dual
lattice, not a newly assumed denominator. The constructed record has the
proved finite-index/free-action fields and the actual integral transvections.
No global moduli uniformization or physical Petersson mass is asserted.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean
(`rank_integral_selfDual`, its trace-dual integrality proof),
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TransvectionMemPrincipalCongruenceGroup.lean
(`transv_mem_princ`, the discriminant denominator),
src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SplitPrimeLabelOperatorsEqChartHeckeOperators.lean
(`revM`, `revM_mul`, `mul_revM`, `revM_mul_revM`), and
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SmulMemOfIsIntegral.lean
(`exists_data`). The diagonal specialization and its exact +EF comparison
are proved directly from the existing native construction. The source
mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Matrix
open scoped Pointwise nonZeroDivisors Classical BigOperators

namespace RHLean.Geometry.NativeTheta.Cusp.NativeFlag

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open NativePrescribedHermitian

section Reversal

variable {L : Type} [Field L] {N : ℕ}

def reversal (L : Type) [Field L] (N : ℕ) : Matrix (Fin N) (Fin N) L :=
  fun i j => if i.rev = j then 1 else 0

theorem reversal_mul (A : Matrix (Fin N) (Fin N) L) (i j : Fin N) :
    (reversal L N * A) i j = A i.rev j := by
  simp [reversal, Matrix.mul_apply]

theorem mul_reversal (A : Matrix (Fin N) (Fin N) L) (i j : Fin N) :
    (A * reversal L N) i j = A i j.rev := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j.rev]
  · simp [reversal]
  · intro b _ hb
    have : b.rev ≠ j := fun e => hb (by rw [← e, Fin.rev_rev])
    simp [reversal, this]
  · simp

theorem reversal_mul_self : reversal L N * reversal L N = 1 := by
  ext i j
  rw [reversal_mul, reversal, Matrix.one_apply, Fin.rev_rev]

theorem reversal_det_ne_zero : (reversal L N).det ≠ 0 := by
  intro h
  have e := congrArg Matrix.det (reversal_mul_self (L := L) (N := N))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at e
  exact zero_ne_one e

theorem reversal_transpose : (reversal L N)ᵀ = reversal L N := by
  ext i j
  simp only [Matrix.transpose_apply, reversal]
  have h : j.rev = i ↔ i.rev = j :=
    ⟨fun h => by rw [← h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
  simp only [h]

theorem reversal_map {L' : Type} [Field L'] (f : L →+* L') :
    (reversal L N).map f = reversal L' N := by
  ext i j
  by_cases h : i.rev = j <;> simp [reversal, h]

end Reversal

variable {φ : Frame} (H : HostRaw φ)

attribute [local instance] conjugationStar

/-- The first-linear flag matrix with the original +EF trace normalization. -/
def matrix (N q : ℕ) : Matrix (Fin N) (Fin N) H.E :=
  Matrix.diagonal fun i => -(NativePrescribedHermitian.sgn (negTail N q i) : H.E)

theorem matrix_eq_neg_native_gram (N q : ℕ) :
    matrix H N q = -(dSpace (E := H.E) N q).gram := by
  ext i j
  change (if i = j then -(NativePrescribedHermitian.sgn (negTail N q i) : H.E) else 0) =
    -((stdSpace (E := H.E) N (negTail N q) (N - q) q).gram i j)
  rw [stdSpace_gram_apply]
  split_ifs <;> simp

theorem matrix_det_ne_zero (N q : ℕ) : (matrix H N q).det ≠ 0 := by
  rw [matrix, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    neg_ne_zero.mpr (NativePrescribedHermitian.sgn_ne_zero _)

theorem matrix_signature (N q : ℕ) (hq : q ≤ N) (τ : H.E →+* ℂ) :
    ∃ P : Matrix (Fin N) (Fin N) ℂ, P.det ≠ 0 ∧
      FlagDomain.gram τ (matrix H N q) P =
        Matrix.diagonal fun i : Fin N => ((FlagDomain.sgn q (i : ℕ) : ℝ) : ℂ) := by
  refine ⟨reversal ℂ N, reversal_det_ne_zero, ?_⟩
  rw [FlagDomain.FrameDegreeData.gram_eq, reversal_transpose, reversal_map]
  have hs (i : Fin N) :
      τ (-(NativePrescribedHermitian.sgn (negTail N q i.rev) : H.E)) =
        ((FlagDomain.sgn q (i : ℕ) : ℝ) : ℂ) := by
    by_cases hi : (i : ℕ) < q
    · have hr : N - q ≤ (i.rev : ℕ) := by rw [Fin.val_rev]; omega
      rw [negTail_true N q i.rev hr]
      simp [NativePrescribedHermitian.sgn, FlagDomain.sgn, hi]
    · have hr : (i.rev : ℕ) < N - q := by rw [Fin.val_rev]; omega
      rw [negTail_false N q i.rev hr]
      simp [NativePrescribedHermitian.sgn, FlagDomain.sgn, hi]
  ext a b
  rw [mul_reversal, reversal_mul, Matrix.map_apply]
  by_cases hab : a = b
  · subst b
    simp only [matrix, Matrix.diagonal_apply_eq]
    exact hs a
  · have hr : a.rev ≠ b.rev := fun e => hab (Fin.rev_injective e)
    rw [matrix, Matrix.diagonal_apply_ne _ hr, map_zero,
      Matrix.diagonal_apply_ne _ hab]

/-- The actual inverse half-different lattice spans the original E-space. -/
theorem lattice_span (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    Submodule.span H.E (twistedLattice H B N : Set (Fin N → H.E)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun H.E (Fin N)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hi : (Pi.single i 1 : Fin N → H.E) ∈ twistedLattice H B N := by
    apply (mem_twistedLattice H B N _).mpr
    intro a
    by_cases ha : a = i
    · subst a
      simpa using integer_mem_coefficientIdeal H B hB 1
    · rw [Pi.single_eq_of_ne ha]
      exact (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).zero_mem
  simpa only [Pi.basisFun_apply] using Submodule.subset_span hi

/-- Source transvection depth at the fixed principal congruence modulus five. -/
def transvectionDepth : ℕ := 5 * (NumberField.discr H.E).natAbs

theorem transvectionDepth_pos : 0 < transvectionDepth H :=
  Nat.mul_pos (by norm_num) (Int.natAbs_pos.mpr (NumberField.discr_ne_zero H.E))

section CM

variable [IsCMField H.E]

theorem matrix_hermitian (N q : ℕ) (a b : Fin N) :
    FlagDomain.cc (matrix H N q a b) = matrix H N q b a := by
  by_cases h : a = b
  · subst b
    cases ht : negTail N q a <;>
      simp [matrix, FlagDomain.cc, NativePrescribedHermitian.sgn, ht]
  · simp [matrix, Matrix.diagonal_apply_ne, h, Ne.symm h, FlagDomain.cc]

/-- Explicit convention bridge, before taking a trace. -/
theorem herm_matrix (hconj : ∀ x : H.E, H.conj x = IsCMField.complexConj H.E x)
    (N q : ℕ) (x y : Fin N → H.E) :
    FlagDomain.herm (matrix H N q) x y = -diagForm N (negTail N q) y x := by
  have hd : FlagDomain.herm (matrix H N q) x y =
      ∑ a, x a * -(NativePrescribedHermitian.sgn (negTail N q a) : H.E) *
        FlagDomain.cc (y a) := by
    unfold FlagDomain.herm
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a (fun b _ hb => by
      rw [matrix, Matrix.diagonal_apply_ne _ hb.symm]; simp) (by simp),
      matrix, Matrix.diagonal_apply_eq]
  rw [hd, diagForm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FlagDomain.cc, ← hconj]
  change x i * -(NativePrescribedHermitian.sgn (negTail N q i) : H.E) * H.conj (y i) =
    -(H.conj (y i) * NativePrescribedHermitian.sgn (negTail N q i) * x i)
  ring

/-- The native physical alternating trace is preserved with its positive sign. -/
theorem trace_matrix (hconj : ∀ x : H.E, H.conj x = IsCMField.complexConj H.E x)
    (N q : ℕ) (x y : Fin N → H.E) :
    Algebra.trace ℚ H.E (xi H * FlagDomain.herm (matrix H N q) x y) =
      Algebra.trace ℚ H.E (xi H * diagForm N (negTail N q) x y) := by
  rw [herm_matrix H hconj, mul_neg, map_neg]
  change -Ambient.pair H (negTail N q) y x = Ambient.pair H (negTail N q) x y
  rw [Ambient.pair_skew, neg_neg]

private theorem herm_smul_left {N : ℕ} (G : Matrix (Fin N) (Fin N) H.E)
    (c : 𝓞 H.E) (x y : Fin N → H.E) :
    FlagDomain.herm G (c • x) y = (c : H.E) * FlagDomain.herm G x y := by
  simp only [FlagDomain.herm, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def, show algebraMap (𝓞 H.E) H.E c = (c : H.E) from rfl]
  ring

/-- The original discriminant clears the actual trace-dual values. -/
theorem discr_mul_integral
    (hconj : ∀ x : H.E, H.conj x = IsCMField.complexConj H.E x)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N q : ℕ)
    (x y : twistedLattice H B N) :
    IsIntegral ℤ ((NumberField.discr H.E : H.E) *
      (xi H * FlagDomain.herm (matrix H N q) x.1 y.1)) := by
  have hEF (u v : twistedLattice H B N) :
      ((twistedTraceForm H B hB (negTail N q) u v : ℤ) : ℚ) =
        Algebra.trace ℚ H.E (xi H * FlagDomain.herm (matrix H N q) u.1 v.1) :=
    (twistedTraceForm_cast H B hB _ u v).trans (trace_matrix H hconj N q u.1 v.1).symm
  have hmem : xi H * FlagDomain.herm (matrix H N q) x.1 y.1 ∈
      Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 H.E) H.E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_one.mp ha
    refine ⟨twistedTraceForm H B hB (negTail N q) (c • x) y, ?_⟩
    rw [eq_intCast, hEF, Submodule.coe_smul, herm_smul_left,
      Algebra.traceForm_apply]
    change _ = Algebra.trace ℚ H.E
      ((xi H * FlagDomain.herm (matrix H N q) x.1 y.1) * (c : H.E))
    congr 1
    ring
  have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis H.E i) := fun i => by
    rw [NumberField.integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  have hint := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := H.E)
    (B := 𝓞 H.E) 1 hb (Submodule.one_le.mp le_rfl) hmem
  rw [← NumberField.coe_discr] at hint
  convert hint using 1
  rw [Algebra.smul_def, mul_one]
  simp

theorem transvection_integral
    (hconj : ∀ x : H.E, H.conj x = IsCMField.complexConj H.E x)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N q : ℕ)
    (x y : twistedLattice H B N) :
    IsIntegral ℤ ((transvectionDepth H : H.E) / 5 * (-(2 * xi H)) *
      FlagDomain.herm (matrix H N q) x.1 y.1) := by
  have hd := discr_mul_integral H hconj B hB N q x y
  have hi : IsIntegral ℤ (((NumberField.discr H.E).natAbs : H.E) *
      (xi H * FlagDomain.herm (matrix H N q) x.1 y.1)) := by
    rcases Int.natAbs_eq (NumberField.discr H.E) with h | h
    · rw [h] at hd
      simpa only [Int.cast_natCast] using hd
    · rw [h] at hd
      simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] using hd.neg
  have hr : (transvectionDepth H : H.E) / 5 = ((NumberField.discr H.E).natAbs : H.E) := by
    unfold transvectionDepth
    push_cast
    field_simp
  rw [hr]
  have h2 : IsIntegral ℤ (2 : H.E) := isIntegral_natCast 2
  convert (h2.mul hi).neg using 1
  ring

/-- Construct the full flag datum on the same prescribed projective lattice,
with the trace sign, original q, exact congruence subgroup and denominator. -/
theorem exists_prescribed_data
    (hconj : ∀ x : H.E, H.conj x = IsCMField.complexConj H.E x)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (_hj : j ≤ m) :
    ∃ X : FlagDomain.Data H.E (k + m - 1),
      X.Ψ = cmTypeFinset H ∧ X.Gm = matrix H (k + m - 1) (m - j) ∧
      X.p0 = m - j ∧ X.Λ = prescribedLattice H B k m ∧
      X.ξ0 = xi H ∧ X.κ0 = -(2 * xi H) ∧ X.m = transvectionDepth H ∧
      (∀ γ, γ ∈ X.Γ ↔ FlagDomain.IsUStab (matrix H (k + m - 1) (m - j))
        (prescribedLattice H B k m) γ ∧ ∀ v ∈ prescribedLattice H B k m,
          ∃ w ∈ prescribedLattice H B k m,
            (γ : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) H.E) *ᵥ v = v + 5 • w) ∧
      (∀ la γ, X.χ la γ = 1) ∧
      ∀ x y : prescribedLattice H B k m,
        ((prescribedTraceForm H B hB k m j x y : ℤ) : ℚ) =
          Algebra.trace ℚ H.E (X.ξ0 * FlagDomain.herm X.Gm x.1 y.1) := by
  have hfg : (prescribedLattice H B k m).FG :=
    Module.Finite.iff_fg.mp (twistedLattice_finite H B (k + m - 1))
  obtain ⟨X, hΨ, hG, hp, hΛ, hξ, hκ, hm, hΓ, hχ⟩ :=
    FlagConstruction.exists_data H.E (k + m - 1) (m - j) 5 (transvectionDepth H)
      (cmTypeFinset H) (matrix H (k + m - 1) (m - j)) (prescribedLattice H B k m)
      (xi H) (-(2 * xi H)) (cmTypeFinset_conjugate H)
      (matrix_hermitian H _ _) (matrix_det_ne_zero H _ _) (by omega)
      (fun τ _ => matrix_signature H _ _ (by omega) τ)
      hfg (lattice_span H B hB _) (by norm_num)
      (by rw [FlagDomain.cc, ← hconj]; exact conj_xi H) (xi_ne_zero H)
      (Or.inr rfl) (fun τ hτ => by
        have hpos := xi_im_pos H τ ((mem_cmTypeFinset H τ).mp hτ)
        simpa [map_mul, map_ofNat, Complex.mul_im] using
          (neg_lt_zero.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hpos)))
      (transvectionDepth_pos H)
      (fun x hx y hy => transvection_integral H hconj B hB _ _ ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨X, hΨ, hG, hp, hΛ, hξ, hκ, hm, hΓ, hχ, ?_⟩
  intro x y
  rw [hξ, hG, trace_matrix H hconj]
  exact prescribedTraceForm_cast H B hB k m j x y

end CM

/-- The canonical native CM involution supplies the remaining compatibility;
all flag-data existence fields above are conclusions. -/
theorem exists_native_data
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostRaw e q d he hH
    let _ : IsCMField H.E := nativeDyadicHostRaw_cm e q d he hH
    ∃ X : FlagDomain.Data H.E (k + m - 1),
      X.Ψ = cmTypeFinset H ∧ X.Gm = matrix H (k + m - 1) (m - j) ∧
      X.p0 = m - j ∧ X.Λ = prescribedLattice H B k m ∧
      X.ξ0 = xi H ∧ X.κ0 = -(2 * xi H) ∧ X.m = transvectionDepth H ∧
      (∀ γ, γ ∈ X.Γ ↔ FlagDomain.IsUStab (matrix H (k + m - 1) (m - j))
        (prescribedLattice H B k m) γ ∧ ∀ v ∈ prescribedLattice H B k m,
          ∃ w ∈ prescribedLattice H B k m,
            (γ : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) H.E) *ᵥ v = v + 5 • w) ∧
      (∀ la γ, X.χ la γ = 1) ∧
      ∀ x y : prescribedLattice H B k m,
        ((prescribedTraceForm H B hB k m j x y : ℤ) : ℚ) =
          Algebra.trace ℚ H.E (X.ξ0 * FlagDomain.herm X.Gm x.1 y.1) := by
  let H := nativeDyadicHostRaw e q d he hH
  let _ : IsCMField H.E := nativeDyadicHostRaw_cm e q d he hH
  exact exists_prescribed_data H (nativeDyadicHostRaw_prescribed_conj e q d he hH)
    B hB k m j hk hj

end RHLean.Geometry.NativeTheta.Cusp.NativeFlag
