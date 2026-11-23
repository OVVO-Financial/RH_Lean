import RHLean.Geometry.NativeThetaOrbitLattice
import RHLean.Geometry.NativeThetaOrbitTorsion
import RHLean.Geometry.NativePrescribedGeometricPeriod

/-!
# The primary torsion of the actual native period quotient

For an injective lattice map `P : L →+ V` into a real vector space, division
in `V` constructs the quotient's multiplication-by-`g` preimages. The map
`l ↦ [P(l) / g]` identifies its `g`-torsion with the original `L / gL`.
This proves the cardinality and divisibility needed by the finite-order
unipotent argument on the genuine primary subgroup of `V / P(L)`.

The final declarations instantiate every lattice and period input with
`prescribedPeriodMap` and its already constructed real tensor equivalence.
The rational-prime torsion exponent is the full integer rank
`(k + m - 1) * [E : Q]`. There is no assumed Tate isomorphism, degree-one
prime, quotient cardinality, or divisible finite group. The endpoint fixes
the actual primary subgroup under the stated finite-order and unipotence
conditions. Identifying a moduli stabilizer with that action, and separating
its orbit by sections, remain later geometric steps.

The finite-order argument is reconstructed in `NativeThetaOrbitTorsion`
from `FiniteOrderUnipotentAutDivisiblePrimaryEqId.lean` at the pinned Alpöge
source `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`. The quotient/torsion
identification here is proved directly for the native period map.
-/

set_option autoImplicit false

noncomputable section

open NumberField
open scoped TensorProduct Pointwise

namespace RHLean.Geometry.NativeThetaPeriodTorsion

section Quotient

variable {L V : Type} [AddCommGroup L] [AddCommGroup V] [Module ℝ V]

/-- The additive quotient by the range of the original period map. -/
abbrev PeriodQuotient (P : L →+ V) := V ⧸ P.range

/-- The actual multiplication-by-`g` kernel in the period quotient. -/
def torsion (P : L →+ V) (g : ℕ) : AddSubgroup (PeriodQuotient P) :=
  (nsmulAddMonoidHom (α := PeriodQuotient P) g).ker

private theorem nsmul_inv_smul (g : ℕ) (hg : g ≠ 0) (v : V) :
    g • ((g : ℝ)⁻¹ • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hg), one_smul]

private theorem inv_smul_nsmul (g : ℕ) (hg : g ≠ 0) (v : V) :
    (g : ℝ)⁻¹ • (g • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hg), one_smul]

/-- Actual division of ambient vectors supplies quotient divisibility. -/
theorem quotient_divisible (P : L →+ V) (g : ℕ) (hg : g ≠ 0) :
    ∀ x : PeriodQuotient P, ∃ y : PeriodQuotient P, g • y = x := by
  intro x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective P.range x
  refine ⟨QuotientAddGroup.mk' P.range ((g : ℝ)⁻¹ • v), ?_⟩
  rw [← map_nsmul, nsmul_inv_smul g hg]

/-- A lattice vector gives the torsion point represented by its actual
period vector divided by `g`. -/
def torsionParam (P : L →+ V) (g : ℕ) (hg : g ≠ 0) : L →+ torsion P g where
  toFun x := ⟨QuotientAddGroup.mk' P.range ((g : ℝ)⁻¹ • P x), by
    change g • QuotientAddGroup.mk' P.range ((g : ℝ)⁻¹ • P x) = 0
    rw [← map_nsmul, nsmul_inv_smul g hg, QuotientAddGroup.eq_zero_iff]
    exact ⟨x, rfl⟩⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp only [map_add, smul_add])

/-- The only lattice vectors producing zero torsion are the genuine
multiples of `g` in the same lattice. -/
theorem torsionParam_ker (P : L →+ V) (hP : Function.Injective P)
    (g : ℕ) (hg : g ≠ 0) :
    (nsmulAddMonoidHom (α := L) g).range = (torsionParam P g hg).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change torsionParam P g hg (g • y) = 0
    apply Subtype.ext
    change QuotientAddGroup.mk' P.range ((g : ℝ)⁻¹ • P (g • y)) = 0
    rw [map_nsmul, inv_smul_nsmul g hg, QuotientAddGroup.eq_zero_iff]
    exact ⟨y, rfl⟩
  · intro hx
    change torsionParam P g hg x = 0 at hx
    have hx' := congrArg Subtype.val hx
    change QuotientAddGroup.mk' P.range ((g : ℝ)⁻¹ • P x) = 0 at hx'
    obtain ⟨y, hy⟩ := (QuotientAddGroup.eq_zero_iff _).mp hx'
    change ∃ y, g • y = x
    refine ⟨y, hP ?_⟩
    rw [map_nsmul, hy, nsmul_inv_smul g hg]

/-- Every torsion point is obtained from the original lattice. -/
theorem torsionParam_surjective (P : L →+ V) (g : ℕ) (hg : g ≠ 0) :
    Function.Surjective (torsionParam P g hg) := by
  intro x
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk'_surjective P.range x.1
  have hmem : g • v ∈ P.range := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    rw [map_nsmul, hv]
    exact x.2
  obtain ⟨l, hl⟩ := hmem
  refine ⟨l, Subtype.ext ?_⟩
  change QuotientAddGroup.mk' P.range ((g : ℝ)⁻¹ • P l) = x.1
  rw [hl, inv_smul_nsmul g hg, hv]

/-- The canonical isomorphism keeps the actual integral quotient. -/
def latticeQuotientEquivTorsion (P : L →+ V) (hP : Function.Injective P)
    (g : ℕ) (hg : g ≠ 0) :
    (L ⧸ (nsmulAddMonoidHom (α := L) g).range) ≃+ torsion P g :=
  QuotientAddGroup.liftEquiv _ (torsionParam_surjective P g hg)
    (torsionParam_ker P hP g hg)

/-- The torsion cardinal is derived from the proved integer lattice rank. -/
theorem natCard_torsion [Module.Free ℤ L] [Module.Finite ℤ L]
    (P : L →+ V) (hP : Function.Injective P) (g : ℕ) (hg : g ≠ 0) :
    Nat.card (torsion P g) = g ^ Module.finrank ℤ L := by
  rw [← Nat.card_congr (latticeQuotientEquivTorsion P hP g hg).toEquiv]
  change (nsmulAddMonoidHom (α := L) g).range.index = _
  exact AddSubgroup.index_range_nsmul L g

theorem finite_torsion [Module.Free ℤ L] [Module.Finite ℤ L]
    (P : L →+ V) (hP : Function.Injective P) (g : ℕ) (hg : g ≠ 0) :
    Finite (torsion P g) := by
  apply Nat.finite_of_card_ne_zero
  rw [natCard_torsion P hP g hg]
  exact pow_ne_zero _ hg

/-- The compatible primary tower inside the actual quotient, rather than
one finite layer of that tower. -/
abbrev primary (P : L →+ V) (g : ℕ) : AddSubgroup (PeriodQuotient P) :=
  AddCommGroup.primaryComponent (PeriodQuotient P) g

/-- Dividing a point killed by `g^j` produces one killed by `g^(j+1)`. -/
theorem primary_divisible (P : L →+ V) (g : ℕ) (hg : g ≠ 0) :
    ∀ x : primary P g, ∃ y : primary P g, g • y = x := by
  intro x
  obtain ⟨y, hy⟩ := quotient_divisible P g hg x.1
  have hyt : y ∈ primary P g := by
    obtain ⟨j, hj⟩ := x.2
    refine ⟨j + 1, ?_⟩
    rw [pow_succ, mul_smul, hy]
    exact hj
  exact ⟨⟨y, hyt⟩, Subtype.ext hy⟩

/-- Every first-layer torsion point lies in the same primary tower. -/
def torsionToPrimary (P : L →+ V) (g : ℕ) : torsion P g →+ primary P g where
  toFun x := ⟨x.1, ⟨1, by simpa only [pow_one] using x.2⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem torsionToPrimary_injective (P : L →+ V) (g : ℕ) :
    Function.Injective (torsionToPrimary P g) := by
  intro x y h
  exact Subtype.ext (congrArg Subtype.val h)

/-- The original quotient count supplies the finite set required by the
finite-order theorem on the actual primary group. -/
theorem primary_small_torsion_set [Module.Free ℤ L] [Module.Finite ℤ L]
    (P : L →+ V) (hP : Function.Injective P) (g : ℕ) (hg : g ≠ 0) :
    ∃ T : Finset (primary P g), T.card ≤ g ^ Module.finrank ℤ L ∧
      ∀ x : primary P g, g • x = 0 → x ∈ T := by
  classical
  letI := finite_torsion P hP g hg
  letI := Fintype.ofFinite (torsion P g)
  let e : torsion P g ↪ primary P g :=
    ⟨torsionToPrimary P g, torsionToPrimary_injective P g⟩
  refine ⟨Finset.univ.map e, ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact (natCard_torsion P hP g hg).le
  · intro x hx
    have hx' : g • x.1 = 0 := congrArg Subtype.val hx
    apply Finset.mem_map.mpr
    exact ⟨⟨x.1, hx'⟩, Finset.mem_univ _, Subtype.ext rfl⟩

/-- Any additive endomorphism preserves the actual primary subgroup. -/
def primaryMap (P : L →+ V) (g : ℕ) (β : PeriodQuotient P →+ PeriodQuotient P) :
    primary P g →+ primary P g where
  toFun x := ⟨β x.1, by
    obtain ⟨j, hj⟩ := x.2
    exact ⟨j, by rw [← map_nsmul, hj, map_zero]⟩⟩
  map_zero' := Subtype.ext (map_zero β)
  map_add' x y := Subtype.ext (map_add β x.1 y.1)

theorem primaryMap_iterate (P : L →+ V) (g : ℕ)
    (β : PeriodQuotient P →+ PeriodQuotient P) (n : ℕ) (x : primary P g) :
    ((primaryMap P g β)^[n] x : PeriodQuotient P) = β^[n] x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change β (((primaryMap P g β)^[n] x : primary P g) : PeriodQuotient P) = _
    rw [ih]

theorem primaryMap_sub_iterate (P : L →+ V) (g : ℕ)
    (β : PeriodQuotient P →+ PeriodQuotient P) (n : ℕ) (x : primary P g) :
    (((fun z => primaryMap P g β z - z)^[n] x : primary P g) : PeriodQuotient P) =
      (fun z => β z - z)^[n] x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change β (((fun z => primaryMap P g β z - z)^[n] x : primary P g) : PeriodQuotient P) -
      (((fun z => primaryMap P g β z - z)^[n] x : primary P g) : PeriodQuotient P) = _
    rw [ih]

/-- Apply the finite-order theorem to the genuine period-primary group.
Divisibility, primary torsion, and the first-layer count are all supplied. -/
theorem finite_order_unipotent_primary_eq_id [Module.Free ℤ L] [Module.Finite ℤ L]
    (P : L →+ V) (hP : Function.Injective P)
    (β : PeriodQuotient P →+ PeriodQuotient P) (n g m : ℕ)
    (hn : 0 < n) (hβ : ∀ x, β^[n] x = x) (hg : g.Prime)
    (hrg : Module.finrank ℤ L + 2 ≤ g)
    (hu : ∀ x : PeriodQuotient P, g • x = 0 →
      (fun z => β z - z)^[m] x = 0) :
    ∀ x : PeriodQuotient P, (∃ j : ℕ, g ^ j • x = 0) → β x = x := by
  have hfix := NativeThetaOrbitTorsion.finite_order_unipotent_eq_id
    (primary P g) (primaryMap P g β) n g (Module.finrank ℤ L) m hn
    (fun x => Subtype.ext (by rw [primaryMap_iterate, hβ])) hg hrg
    (primary_divisible P g hg.ne_zero)
    (fun x => by
      obtain ⟨j, hj⟩ := x.2
      exact ⟨j, Subtype.ext hj⟩)
    (primary_small_torsion_set P hP g hg.ne_zero)
    (fun x hx => Subtype.ext (by
      rw [primaryMap_sub_iterate]
      exact hu x.1 (congrArg Subtype.val hx)))
  intro x hx
  exact congrArg Subtype.val (hfix ⟨x, hx⟩)

end Quotient

/-- Injectivity of the period map follows from its real tensor equivalence
and the actual free integral lattice. -/
theorem periodOfRealEquiv_injective {L : Type} [AddCommGroup L] [Module.Free ℤ L]
    {d : ℕ} (e : (ℝ ⊗[ℤ] L) ≃ₗ[ℝ] (Fin d → ℂ)) :
    Function.Injective (NativeGeometricPeriods.periodOfRealEquiv e) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [NativeGeometricPeriods.periodOfRealEquiv_apply, e.map_eq_zero_iff] at hx
  let b := Module.Free.chooseBasis ℤ L
  apply b.ext_elem
  intro i
  have := congrArg (fun v => (b.baseChange ℝ).repr v i) hx
  simpa using this

end RHLean.Geometry.NativeThetaPeriodTorsion

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativeThetaPeriodTorsion

variable {φ : Frame} (H : HostRaw φ)

theorem prescribedPeriodMap_injective (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m j : ℕ) :
    Function.Injective (prescribedPeriodMap H B hB k m j) := by
  letI := twistedLattice_free_int H B (k + m - 1)
  exact periodOfRealEquiv_injective (twistedPeriodRealEquiv H B hB (k + m - 1) (m - j))

/-- Exact torsion count on the actual prescribed complex period quotient. -/
theorem prescribedPeriodTorsion_card (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j g : ℕ) (hg : g ≠ 0) :
    Nat.card (torsion (prescribedPeriodMap H B hB k m j) g) =
      g ^ ((k + m - 1) * Module.finrank ℚ H.E) := by
  letI := twistedLattice_free_int H B (k + m - 1)
  letI := twistedLattice_finite_int H B (k + m - 1)
  rw [natCard_torsion _ (prescribedPeriodMap_injective H B hB k m j) g hg,
    twistedLattice_rank_int H B hB]

/-- The native period-primary group supplies all finite-order freeness
inputs except the actual endomorphism's order and first-layer unipotence. -/
theorem prescribedPeriod_primary_fixed (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ)
    (β : PeriodQuotient (prescribedPeriodMap H B hB k m j) →+
      PeriodQuotient (prescribedPeriodMap H B hB k m j))
    (n g u : ℕ) (hn : 0 < n) (hβ : ∀ x, β^[n] x = x) (hg : g.Prime)
    (hrg : (k + m - 1) * Module.finrank ℚ H.E + 2 ≤ g)
    (hu : ∀ x, g • x = 0 → (fun z => β z - z)^[u] x = 0) :
    ∀ x, (∃ a : ℕ, g ^ a • x = 0) → β x = x := by
  letI := twistedLattice_free_int H B (k + m - 1)
  letI := twistedLattice_finite_int H B (k + m - 1)
  apply finite_order_unipotent_primary_eq_id
    (prescribedPeriodMap H B hB k m j) (prescribedPeriodMap_injective H B hB k m j)
    β n g u hn hβ hg ?_ hu
  rwa [twistedLattice_rank_int H B hB]

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
