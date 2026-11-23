import RHLean.Geometry.NativeThetaCuspSplitLevel
import RHLean.Geometry.NativeThetaCuspTensorLattices

/-!
# The actual full-GL level on the native projective lattice

The level ideal is the constructed conjugate half of `(5)`. The finite
group is the full general linear group of its coefficient quotient, and
the character is literally the trivial character used by the source's
base-level construction. Quotient coordinates and all integral lifts are
constructed on the original projective lattice; no integral free basis is
assumed. Coprime ideal constraints on lifts are proved by Bezout.

This is the analytic full-GL level. The coefficient-matched cover character
in `ExistsClassicalLevelDataCoverSelfDual` additionally needs the actual
geometric cover, its global section and its `PhiPin` identity.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SelfDualCLatP.lean
(`exists_level`, with the already proved native fixed-five ideal),
src/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IsSystem.lean
(`Level.J`, `Level.lam`, integral `Level.β`), and
src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardLevGrpAndSpan.lean
(projective quotient coordinates). The source mirror states no license;
attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module Matrix
open scoped Pointwise BigOperators Classical

namespace RHLean.Geometry.NativeTheta.Cusp.FiniteLevel

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open TensorLattices

section Quotient

variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]

/-- Membership in the ideal multiple is unchanged by the actual subtype
inclusion of the integral lattice. -/
theorem mem_ideal_smul_top (L : Submodule O V) (P : Ideal O) (x : L) :
    x ∈ (P • ⊤ : Submodule O L) ↔ (x : V) ∈ P • L := by
  have he : (P • (⊤ : Submodule O L)).map L.subtype = P • L := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  constructor
  · intro hx
    rw [← he]
    exact Submodule.mem_map_of_mem hx
  · intro hx
    rw [← he] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hyx : y = x := Subtype.ext hxy
    rwa [hyx] at hy

/-- Every quotient class has a lift in any coprime ideal multiple. -/
theorem exists_coprime_lift (L : Submodule O V) (P C : Ideal O)
    (hPC : IsCoprime P C) (z : L ⧸ (P • ⊤ : Submodule O L)) :
    ∃ x : L, (x : V) ∈ C • L ∧ Submodule.Quotient.mk x = z := by
  obtain ⟨p, hp, c, hc, hpc⟩ := Ideal.isCoprime_iff_exists.mp hPC
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine ⟨c • x, Submodule.smul_mem_smul hc x.2, ?_⟩
  apply Submodule.Quotient.eq.mpr
  have he : c • x - x = (-p) • x := by
    calc
      c • x - x = (c - 1) • x := by rw [sub_smul, one_smul]
      _ = (-p) • x := by rw [show c - 1 = -p by linear_combination hpc]
  rw [he]
  exact Submodule.smul_mem_smul (P.neg_mem hp) (Submodule.mem_top : x ∈ (⊤ : Submodule O L))

end Quotient

variable {φ : Frame} (H : HostRaw φ)

/-- A constructed finite split level and actual quotient coordinates of
the original integral module. -/
structure FullLevel {r : ℕ} (L : Lt H.E r) where
  P : Ideal (𝓞 H.E)
  proper : P ≠ ⊤
  ne_bot : P ≠ ⊥
  cop : IsCoprime P (H.conj • P)
  odd : IsCoprime P (Ideal.span {(2 : 𝓞 H.E)})
  product : P * (H.conj • P) = Ideal.span {(5 : 𝓞 H.E)}
  coordinates : (L ⧸ (P • ⊤ : Submodule (𝓞 H.E) L)) ≃ₗ[𝓞 H.E]
    (Fin r → 𝓞 H.E ⧸ P)

namespace FullLevel

variable {H} {r : ℕ} {L : Lt H.E r} (D : FullLevel H L)

instance quotient_finite : Finite (𝓞 H.E ⧸ D.P) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ D.ne_bot

/-- The actual finite matrix group, retaining the full coefficient rank. -/
abbrev Group := GL (Fin r) (𝓞 H.E ⧸ D.P)

/-- The source's full subgroup, with no chosen smaller set of matrices. -/
def J : Subgroup D.Group := ⊤

/-- The actual character in the source's analytic base construction. -/
def lam : D.J →* ℂˣ := 1

theorem lam_apply (a : D.J) : D.lam a = 1 := rfl

instance group_finite : Finite D.Group := inferInstance

theorem group_card_pos : 0 < Nat.card D.Group := Nat.card_pos

theorem group_card_le : Nat.card D.Group ≤ Nat.card (𝓞 H.E ⧸ D.P) ^ (r ^ 2) := by
  refine (Nat.card_le_card_of_injective _ Units.val_injective).trans (le_of_eq ?_)
  change Nat.card (Fin r → Fin r → 𝓞 H.E ⧸ D.P) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul, pow_two]

/-- The reduction map of the original lattice, not a replacement lattice. -/
def reduction : L →ₗ[𝓞 H.E] (Fin r → 𝓞 H.E ⧸ D.P) :=
  D.coordinates.toLinearMap.comp (D.P • (⊤ : Submodule (𝓞 H.E) L)).mkQ

theorem reduction_eq_zero (x : L) : D.reduction x = 0 ↔ (x : Fin r → H.E) ∈ D.P • L := by
  change D.coordinates (Submodule.Quotient.mk x) = 0 ↔ _
  rw [map_eq_zero_iff D.coordinates.injective, Submodule.Quotient.eq_zero_iff_mem]
  exact mem_ideal_smul_top L D.P x

/-- The quotient frame corresponding to an actual invertible matrix. -/
def column (a : D.Group) (i : Fin r) : L ⧸ (D.P • ⊤ : Submodule (𝓞 H.E) L) :=
  D.coordinates.symm (fun j => (a : Matrix (Fin r) (Fin r) (𝓞 H.E ⧸ D.P)) j i)

theorem column_injective {a a' : D.Group} (h : ∀ i, D.column a i = D.column a' i) : a = a' := by
  apply Units.ext
  ext j i
  simpa only [column, LinearEquiv.apply_symm_apply] using
    congrFun (congrArg D.coordinates (h i)) j

/-- A literal integral lift of every column of every full-level marking. -/
def liftColumn (C : Ideal (𝓞 H.E)) (hPC : IsCoprime D.P C) (a : D.Group) (i : Fin r) : L :=
  Classical.choose (exists_coprime_lift L D.P C hPC (D.column a i))

theorem liftColumn_mem (C : Ideal (𝓞 H.E)) (hPC : IsCoprime D.P C) (a : D.Group) (i : Fin r) :
    (D.liftColumn C hPC a i : Fin r → H.E) ∈ C • L :=
  (Classical.choose_spec (exists_coprime_lift L D.P C hPC (D.column a i))).1

theorem liftColumn_mk (C : Ideal (𝓞 H.E)) (hPC : IsCoprime D.P C) (a : D.Group) (i : Fin r) :
    Submodule.Quotient.mk (D.liftColumn C hPC a i) = D.column a i :=
  (Classical.choose_spec (exists_coprime_lift L D.P C hPC (D.column a i))).2

theorem liftColumn_reduction (C : Ideal (𝓞 H.E)) (hPC : IsCoprime D.P C)
    (a : D.Group) (i j : Fin r) :
    D.reduction (D.liftColumn C hPC a i) j =
      (a : Matrix (Fin r) (Fin r) (𝓞 H.E ⧸ D.P)) j i := by
  change D.coordinates (Submodule.Quotient.mk (D.liftColumn C hPC a i)) j = _
  rw [D.liftColumn_mk, column, LinearEquiv.apply_symm_apply]

/-- The original rational prime remains in the actual half-level ideal. -/
theorem five_mem : (5 : 𝓞 H.E) ∈ D.P := by
  apply (show Ideal.span {(5 : 𝓞 H.E)} ≤ D.P from by
    rw [← D.product]
    exact Ideal.mul_le_left)
  exact Ideal.mem_span_singleton_self _

theorem cop_two_conjugate : IsCoprime D.P (Ideal.span {(2 : 𝓞 H.E)} * (H.conj • D.P)) :=
  D.odd.mul_right D.cop

end FullLevel

/-- The full finite level is constructed on the same actual inverse-half-
different projective module used by the native polarization. -/
theorem exists_native_full_level
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (r : ℕ) :
    Nonempty (FullLevel (nativeDyadicHostRaw e q d he hH)
      (twistedLattice (nativeDyadicHostRaw e q d he hH) B r)) := by
  let H := nativeDyadicHostRaw e q d he hH
  obtain ⟨P, hP1, hP0, hPc, hPo, hP5⟩ :=
    SplitLevel.exists_five_split_level e q d he hH
  let := twistedLattice_finite H B r
  let := twistedLattice_projective H B r
  let : Finite (𝓞 H.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hP0
  obtain ⟨c⟩ := NativeThetaFullLevelCost.nonempty_equiv_mod (𝓞 H.E)
    (twistedLattice H B r) P r (twistedLattice_rank H B hB r)
  exact ⟨⟨P, hP1, hP0, hPc, hPo, hP5, c⟩⟩

end RHLean.Geometry.NativeTheta.Cusp.FiniteLevel
