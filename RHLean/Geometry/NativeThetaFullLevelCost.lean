import RHLean.Geometry.NativeThetaPeriodTorsion

/-!
# The actual full-level marking cost on the native projective lattice

For a finite projective module of rank `N` over a domain `O`, reduction modulo
an ideal with finite quotient is free of rank `N`. Its `O`-linear full-level
group therefore has cardinality at most `card (O / I) ^ (N ^ 2)`.

We apply this to the original inverse-half-different lattice, rather than
replacing it by a free `O_E`-lattice. At a rational level `g` the resulting
bound is `g ^ ([E : Q] * N ^ 2)`: the field degree occurs once, not twice.
The quotient is identified with the existing actual period `g`-torsion, and
the fixed level-five logarithmic cost is at most `[E : Q] * N^2 * log 5`.
The source's fourth-power-level cost is retained as a separate comparison.

These are counts of compatible linear markings of the same torsion module.
They do not construct an algebraic moduli cover or a theta section, supply
the Petersson mass of the base, or change the complete signed source's
normalizer `Q = T * m * b * Delta / 2`. Full rational level five is distinct
from a split-ideal level `I * conjugate(I) = (5)`; no such ideal is asserted.

The three finite-projective reduction proofs reconstruct
`GlobalTheory.EtaCard.finrank_fibre`, `nonempty_equiv_mod`, and
`nonempty_aut_equiv` from
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`CardLevGrpAndSpan.lean`, at
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The native specialization uses the already constructed projective lattice,
its proved rank, and its original period map. The source archive/mirror
states no license; attribution is retained without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open NumberField
open scoped TensorProduct Pointwise

namespace RHLean.Geometry.NativeThetaFullLevelCost

/-- All field fibres of the original finite projective module have its
actual coefficient rank. -/
theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O]
    [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K],
      Module.finrank K (K ⊗[O] M) =
        Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M)
      (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans
      ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O),
    (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

/-- A basis is constructed after reduction of the actual projective module;
global freeness over `O` is not assumed. -/
theorem nonempty_equiv_mod (O M : Type) [CommRing O] [IsDomain O]
    [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] (I : Ideal O) [Finite (O ⧸ I)]
    (r : ℕ) (hr : Module.finrank O M = r) :
    Nonempty ((M ⧸ (I • ⊤ : Submodule O M)) ≃ₗ[O] (Fin r → O ⧸ I)) := by
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I)
    ((O ⧸ I) ⊗[O] M) r fun P => by
      let := P.isMaximal
      let := Ideal.Quotient.field P.asIdeal
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I)
          ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
        finrank_fibre, hr]
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul M I).symm ≪≫ₗ
    B.equivFun.restrictScalars O⟩

/-- The linear automorphisms of the reduced module are exactly the
invertible matrices over the actual coefficient quotient. -/
theorem nonempty_aut_equiv (O M : Type) [CommRing O] [AddCommGroup M]
    [Module O M] (I : Ideal O) (r : ℕ)
    (e : M ≃ₗ[O] (Fin r → O ⧸ I)) :
    Nonempty ((M ≃ₗ[O] M) ≃ GL (Fin r) (O ⧸ I)) := by
  have hs : Function.Surjective (algebraMap O (O ⧸ I)) := Ideal.Quotient.mk_surjective
  let e1 : (M ≃ₗ[O] M) ≃ ((Fin r → O ⧸ I) ≃ₗ[O ⧸ I] (Fin r → O ⧸ I)) :=
    { toFun := fun a => (e.symm ≪≫ₗ a ≪≫ₗ e).extendScalarsOfSurjective hs
      invFun := fun a => e ≪≫ₗ a.restrictScalars O ≪≫ₗ e.symm
      left_inv := fun a => by ext x; simp
      right_inv := fun a => by ext x; simp }
  exact ⟨e1.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm.toEquiv.trans
    Matrix.GeneralLinearGroup.toLin.symm.toEquiv)⟩

/-- Full linear marking changes of the actual quotient form a finite set. -/
theorem finite_quotient_aut (O M : Type) [CommRing O] [IsDomain O]
    [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] (I : Ideal O) [Finite (O ⧸ I)] :
    Finite ((M ⧸ (I • ⊤ : Submodule O M)) ≃ₗ[O]
      (M ⧸ (I • ⊤ : Submodule O M))) := by
  obtain ⟨e⟩ := nonempty_equiv_mod O M I (Module.finrank O M) rfl
  obtain ⟨a⟩ := nonempty_aut_equiv O _ I _ e
  exact Finite.of_equiv _ a.symm

/-- Counting matrices pays the complete finite marking group, retaining
the coefficient rank rather than squaring the full integer rank. -/
theorem natCard_quotient_aut_le (O M : Type) [CommRing O] [IsDomain O]
    [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] (I : Ideal O) [Finite (O ⧸ I)]
    (r : ℕ) (hr : Module.finrank O M = r) :
    Nat.card ((M ⧸ (I • ⊤ : Submodule O M)) ≃ₗ[O]
      (M ⧸ (I • ⊤ : Submodule O M))) ≤ Nat.card (O ⧸ I) ^ (r ^ 2) := by
  obtain ⟨e⟩ := nonempty_equiv_mod O M I r hr
  obtain ⟨a⟩ := nonempty_aut_equiv O _ I r e
  rw [Nat.card_congr a]
  refine (Nat.card_le_card_of_injective _ Units.val_injective).trans (le_of_eq ?_)
  change Nat.card (Fin r → Fin r → O ⧸ I) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul, pow_two]

/-- The rational-level quotient of the original module. -/
abbrev LevelQuotient (O M : Type) [CommRing O] [AddCommGroup M]
    [Module O M] (g : ℕ) :=
  M ⧸ (Ideal.span {(g : O)} • ⊤ : Submodule O M)

/-- Changes between full `O`-linear markings of this same quotient. -/
abbrev FullLevelGroup (O M : Type) [CommRing O] [AddCommGroup M]
    [Module O M] (g : ℕ) :=
  LevelQuotient O M g ≃ₗ[O] LevelQuotient O M g

/-- The module quotient uses the same subgroup `gL` as the constructed
period-torsion equivalence. -/
theorem rationalLevel_toAddSubgroup (O M : Type) [CommRing O]
    [AddCommGroup M] [Module O M] (g : ℕ) :
    (Ideal.span {(g : O)} • (⊤ : Submodule O M)).toAddSubgroup =
      (nsmulAddMonoidHom (α := M) g).range := by
  ext x
  change x ∈ (Ideal.span {(g : O)} • (⊤ : Submodule O M)) ↔ ∃ y, g • y = x
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]

/-- The actual period map identifies the rational module quotient with
its full `g`-torsion, without a split-ideal or degree-one-prime assumption. -/
def levelQuotientEquivTorsion (O : Type) [CommRing O]
    {L V : Type} [AddCommGroup L] [Module O L] [AddCommGroup V]
    [Module ℝ V] (P : L →+ V) (hP : Function.Injective P)
    (g : ℕ) (hg : g ≠ 0) :
    LevelQuotient O L g ≃+ NativeThetaPeriodTorsion.torsion P g :=
  (QuotientAddGroup.quotientAddEquivOfEq (rationalLevel_toAddSubgroup O L g)).trans
    (NativeThetaPeriodTorsion.latticeQuotientEquivTorsion P hP g hg)

variable (E : Type) [Field E] [NumberField E]

/-- The rational coefficient quotient is genuinely finite at every nonzero
integer level, including ramified levels. -/
theorem finite_integer_quotient (g : ℕ) (hg : g ≠ 0) :
    Finite (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hg)

/-- The full field degree is the exact coefficient-quotient exponent. -/
theorem natCard_integer_quotient (g : ℕ) :
    Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) = g ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_span_natCast, RingOfIntegers.rank]

end RHLean.Geometry.NativeThetaFullLevelCost

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativeThetaFullLevelCost

variable {φ : Frame} (H : HostRaw φ)

/-- The finite full-level group is attached to the same actual
inverse-half-different lattice. -/
theorem twistedLattice_fullLevelGroup_finite (B : Ideal (𝓞 H.E))
    (N g : ℕ) (hg : g ≠ 0) :
    Finite (FullLevelGroup (𝓞 H.E) (twistedLattice H B N) g) := by
  let := twistedLattice_finite H B N
  let := twistedLattice_projective H B N
  let := finite_integer_quotient H.E g hg
  exact finite_quotient_aut (𝓞 H.E) (twistedLattice H B N) _

/-- An unconditional finite cost on the actual projective lattice, with
only one factor of the coefficient-field degree. -/
theorem twistedLattice_fullLevelGroup_card_le (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (N g : ℕ) (hg : g ≠ 0) :
    Nat.card (FullLevelGroup (𝓞 H.E) (twistedLattice H B N) g) ≤
      g ^ (Module.finrank ℚ H.E * N ^ 2) := by
  let := twistedLattice_finite H B N
  let := twistedLattice_projective H B N
  let := finite_integer_quotient H.E g hg
  have h := natCard_quotient_aut_le (𝓞 H.E) (twistedLattice H B N)
    (Ideal.span {(g : 𝓞 H.E)}) N (twistedLattice_rank H B hB N)
  simpa only [natCard_integer_quotient, ← pow_mul] using h

/-- The full finite-level multiplicity contributes its proved logarithmic
cost; the remaining cover and metric costs are separate. -/
theorem twistedLattice_fullLevelGroup_log_le (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (N g : ℕ) (hg : g ≠ 0) :
    Real.log (Nat.card (FullLevelGroup (𝓞 H.E) (twistedLattice H B N) g) : ℝ) ≤
      (Module.finrank ℚ H.E : ℝ) * (N : ℝ) ^ 2 * Real.log (g : ℝ) := by
  let := twistedLattice_fullLevelGroup_finite H B N g hg
  have hpos : 0 < (Nat.card (FullLevelGroup (𝓞 H.E) (twistedLattice H B N) g) : ℝ) :=
    Nat.cast_pos.mpr Nat.card_pos
  have h := Real.log_le_log hpos
    (Nat.cast_le.mpr (twistedLattice_fullLevelGroup_card_le H B hB N g hg))
  simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_mul] using h

/-- At the fixed rational level five, the level logarithm is constant.
The original growing rank `k + m - 1` remains fully charged. -/
theorem prescribedLattice_fullLevelFive_log_le (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m : ℕ) :
    Real.log (Nat.card (FullLevelGroup (𝓞 H.E) (prescribedLattice H B k m) 5) : ℝ) ≤
      (Module.finrank ℚ H.E : ℝ) * ((k + m - 1 : ℕ) : ℝ) ^ 2 * Real.log 5 := by
  exact twistedLattice_fullLevelGroup_log_le H B hB (k + m - 1) 5 (by norm_num)

/-- The fourth-power level reproduces the source's complete degree/rank
bill, so the fixed-five comparison does not hide an extra field-degree cost. -/
theorem twistedLattice_fourthLevelGroup_card_le (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (N R : ℕ) (hR : R ≠ 0) :
    Nat.card (FullLevelGroup (𝓞 H.E) (twistedLattice H B N) (R ^ 4)) ≤
      R ^ (4 * Module.finrank ℚ H.E * N ^ 2) := by
  have h := twistedLattice_fullLevelGroup_card_le H B hB N (R ^ 4)
    (pow_ne_zero _ hR)
  simpa only [← pow_mul, mul_assoc] using h

/-- The actual period torsion admits full coefficient-compatible marking
coordinates. This supplies the finite marking fibre, not a moduli cover. -/
theorem prescribedPeriod_fullLevel_marking_exists (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j g : ℕ) (hg : g ≠ 0) :
    ∃ _e : LevelQuotient (𝓞 H.E) (prescribedLattice H B k m) g ≃ₗ[𝓞 H.E]
        (Fin (k + m - 1) → 𝓞 H.E ⧸ Ideal.span {(g : 𝓞 H.E)}),
      Nonempty ((Fin (k + m - 1) → 𝓞 H.E ⧸ Ideal.span {(g : 𝓞 H.E)}) ≃+
        RHLean.Geometry.NativeThetaPeriodTorsion.torsion
          (prescribedPeriodMap H B hB k m j) g) := by
  let := twistedLattice_finite H B (k + m - 1)
  let := twistedLattice_projective H B (k + m - 1)
  let := finite_integer_quotient H.E g hg
  obtain ⟨e⟩ := nonempty_equiv_mod (𝓞 H.E) (prescribedLattice H B k m)
    (Ideal.span {(g : 𝓞 H.E)}) (k + m - 1) (twistedLattice_rank H B hB _)
  exact ⟨e, ⟨e.symm.toAddEquiv.trans (levelQuotientEquivTorsion (𝓞 H.E)
    (prescribedPeriodMap H B hB k m j)
    (prescribedPeriodMap_injective H B hB k m j) g hg)⟩⟩

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
