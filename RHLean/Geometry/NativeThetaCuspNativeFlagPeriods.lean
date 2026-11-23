import RHLean.Geometry.NativeThetaCuspFlagFramePeriod
import RHLean.Geometry.NativeThetaCuspNativeFlag
import RHLean.Geometry.NativePeriodTypeCoordinates

/-!
# A varying polarized period lattice on the actual native flag domain

At every signed flag frame, the source's explicit local periods are
composed with the real realization of the SAME literal projective lattice
(B^-1)^(k+m-1). The resulting period maps are injective, discrete and span
the whole complex space over R. Their positive Hermitian forms have
imaginary part exactly the constructed +EF, and the original multiplicities
are k+j-1 and m-j. The first m-j frame coordinates are conjugated.

No period, lattice discreteness, positive-form, or varying-family premise
is assumed at the native endpoint. These are periods of polarized complex
tori; algebraic moduli realization and the geometric coefficient/Fourier
comparison remain separate constructions.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean,
`isPeriod_frame`. The actual lattice equivalence and all compatibility
identities are supplied by the existing native prescribed construction.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open NumberField Matrix
open scoped Classical TensorProduct Pointwise ComplexConjugate

namespace RHLean.Geometry.NativeTheta.Cusp.NativeFlagPeriods

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open NativeGeometricPeriods

variable {φ : Frame} (H : HostRaw φ)

/-- The finite enumeration is chosen once for the entire varying family. -/
def index (N : ℕ) :
    Fin ((cmTypeFinset H).card * N) ≃ cmTypeFinset H × Fin N :=
  (NativePeriodCoordinates.indexEquiv (cmTypeFinset H) N).symm

/-- The source frame-period type: conjugate exactly the first q rows. -/
def periodType (N q : ℕ) (i : Fin ((cmTypeFinset H).card * N)) : H.E →+* ℂ :=
  if ((index H N i).2 : ℕ) < q then
    ComplexEmbedding.conjugate (index H N i).1.1 else (index H N i).1.1

/-- The actual signed domain has a frame; the varying-period conclusion
therefore applies to a nonempty family. -/
theorem domain_nonempty (N q : ℕ) (hq : q ≤ N) :
    (FlagDomain.GG (cmTypeFinset H) (NativeFlag.matrix H N q) q).Nonempty := by
  choose P hPd hPG using fun τ : cmTypeFinset H =>
    NativeFlag.matrix_signature H N q hq τ.1
  refine ⟨fun τ => P τ, fun τ => ⟨hPd τ, fun i => ?_⟩⟩
  change 0 < FlagDomain.psgn q i *
    (FlagDomain.lminor (FlagDomain.gram τ.1 (NativeFlag.matrix H N q) (P τ)) i).re
  rw [hPG τ, FlagDomain.FrameDegreeData.lminor_diagonal]
  have hp : (∏ a : Fin i, ((FlagDomain.sgn q a : ℝ) : ℂ)) =
      ((FlagDomain.psgn q i : ℝ) : ℂ) := by
    rw [FlagDomain.psgn, ← Fin.prod_univ_eq_prod_range, Complex.ofReal_prod]
  change 0 < FlagDomain.psgn q i *
    (∏ a : Fin i, ((FlagDomain.sgn q a : ℝ) : ℂ)).re
  rw [hp, Complex.ofReal_re]
  have hs : FlagDomain.psgn q i * FlagDomain.psgn q i = 1 := by
    simp only [FlagDomain.psgn]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro a _
    unfold FlagDomain.sgn
    split_ifs <;> norm_num
  rw [hs]
  norm_num

section CM

variable [IsCMField H.E]

/-- Complete periods for every frame of the actual native signed domain.
The arguments identifying the geometric host are all supplied at the
canonical native endpoint below. -/
theorem prescribed_frame_periods
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (v : H.E), τ (H.conj v) = conj (τ v))
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (hc : ∀ v : H.E, H.conj v = IsCMField.complexConj H.E v)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    IsTypeFn G (k + j - 1) (m - j)
      (periodType H (k + m - 1) (m - j)) ∧
    ∀ x ∈ FlagDomain.GG (cmTypeFinset H)
        (NativeFlag.matrix H (k + m - 1) (m - j)) (m - j),
      ∃ P : prescribedLattice H B k m →+
          (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ),
        (∀ v i, P v i = if ((index H (k + m - 1) i).2 : ℕ) < m - j then
          FlagDomain.hermC (index H (k + m - 1) i).1.1
            (NativeFlag.matrix H (k + m - 1) (m - j))
            (FlagDomain.col (FlagDomain.mat x (index H (k + m - 1) i).1)
              (index H (k + m - 1) i).2)
            (FlagDomain.Data.emb (index H (k + m - 1) i).1.1 v.1)
          else ((FlagDomain.mat x (index H (k + m - 1) i).1)⁻¹ *ᵥ
            FlagDomain.Data.emb (index H (k + m - 1) i).1.1 v.1)
              (index H (k + m - 1) i).2) ∧
        IsPeriod (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj)
          (periodType H (k + m - 1) (m - j)) P := by
  let D := prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj
  have : Module.Free ℤ D.La := twistedLattice_free_int H B (k + m - 1)
  have : Module.Finite ℤ D.La := twistedLattice_finite_int H B (k + m - 1)
  refine FlagFramePeriod.isPeriod_frame G D (xi H)
    (NativeFlag.matrix H (k + m - 1) (m - j))
    (prescribedLattice H B k m).subtype (cmTypeFinset H)
    (fun τ => (mem_cmTypeFinset H τ).trans (hΨ τ).symm)
    _ (index H (k + m - 1)) (periodType H (k + m - 1) (m - j))
    (fun _ => rfl) (prescribedRealEquiv H B hB k m) ?_ ?_ ?_
    (NativeFlag.matrix_hermitian H _ _) ?_ ?_
  · intro v
    simpa only [Complex.ofReal_one, one_mul] using
      prescribedRealEquiv_tmul H B hB k m (1 : ℝ) v
  · rw [FlagDomain.cc, ← hc]
    exact conj_xi H
  · intro τ hτ
    exact xi_im_pos H τ ((mem_cmTypeFinset H τ).mp hτ)
  · intro v w
    change ((D.EF v w : ℤ) : ℚ) =
      Algebra.trace ℚ H.E (xi H * FlagDomain.herm
        (NativeFlag.matrix H (k + m - 1) (m - j)) v.1 w.1)
    rw [NativeFlag.trace_matrix H hc]
    have hform : D.EF = prescribedTraceForm H B hB k m j :=
      prescribedGeometricDatum_form H B hB G hΨ hconj hbar k m j hk hj
    rw [hform]
    exact prescribedTraceForm_cast H B hB k m j v w
  · change k + m - 1 = (k + j - 1) + (m - j)
    omega

end CM

/-- The canonical native host supplies every compatibility in the varying
period construction. The same chosen half-different is retained. -/
theorem native_frame_periods
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostRaw e q d he hH
    let _ : IsCMField H.E := nativeDyadicHostRaw_cm e q d he hH
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    IsTypeFn G (k + j - 1) (m - j)
      (periodType H (k + m - 1) (m - j)) ∧
    ∀ x ∈ FlagDomain.GG (cmTypeFinset H)
        (NativeFlag.matrix H (k + m - 1) (m - j)) (m - j),
      ∃ P : prescribedLattice H B k m →+
          (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ),
        (∀ v i, P v i = if ((index H (k + m - 1) i).2 : ℕ) < m - j then
          FlagDomain.hermC (index H (k + m - 1) i).1.1
            (NativeFlag.matrix H (k + m - 1) (m - j))
            (FlagDomain.col (FlagDomain.mat x (index H (k + m - 1) i).1)
              (index H (k + m - 1) i).2)
            (FlagDomain.Data.emb (index H (k + m - 1) i).1.1 v.1)
          else ((FlagDomain.mat x (index H (k + m - 1) i).1)⁻¹ *ᵥ
            FlagDomain.Data.emb (index H (k + m - 1) i).1.1 v.1)
              (index H (k + m - 1) i).2) ∧
        IsPeriod D (periodType H (k + m - 1) (m - j)) P := by
  let H := nativeDyadicHostRaw e q d he hH
  let _ : IsCMField H.E := nativeDyadicHostRaw_cm e q d he hH
  exact prescribed_frame_periods H B hB
    (nativeDyadicGeometricHostOfDerived e q d he hH)
    (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH)
    (nativeDyadicHostRaw_prescribed_embedding_conj e q d he hH)
    (nativeDyadicGeometricHost_bar_eq e q d he hH)
    (nativeDyadicHostRaw_prescribed_conj e q d he hH) k m j hk hj

end RHLean.Geometry.NativeTheta.Cusp.NativeFlagPeriods
