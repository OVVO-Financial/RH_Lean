import RHLean.Geometry.NativeCMLineBundleTransport

/-!
# Actual generators under products and formal signed identities

The unit-valued generators are glued on the original scheme opens. A
formal equality of signed pullbacks transports a genuine generator by
first gluing its regular section and then proving that every local
coefficient is a unit. No equality in a freely assigned Picard group is
used as a geometric existence premise.

Native declaration cuts from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`:

- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ValCalc.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/CubicalStructures/CubeSymmetricSwapFirst.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBPull.lean`
- `src/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MulPullOfCubeOfSymm.lean`

Only the generator calculus required for the actual tensor bundle is
reconstructed. The source archive states no license; attribution is
retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

namespace RHLean.Geometry.NativeCM.SchemeTheory

variable {X Y Z : Scheme.{0}}

namespace LBGerm

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def genSec {M : LB Y} (t : LB.Gen M) (ht : t.IsGen) : LB.Sec M :=
  ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩

theorem sval_genSec {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (genSec t ht) r z J = (val t r z J).val := by
  simp only [sval, val, genSec]
  exact gs_unit r z _ (hJ.mem φ r) _

theorem sval_trans (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (y : Y) (j : K → L.ι)
    (hy : y ∈ LB.wchart L φ j) :
    ∃ J, Good L y J ∧ gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL y
    (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim
    (fun a => a.elim) (fun k => k.elim)
  exact ⟨J, hJ, sec_trans s (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))⟩

/-- The regular-section transport is actually unit-valued, so it gives
the required generator on every target chart. -/
theorem exists_gen (hL : L.IsLB)
    {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε'), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J,
        Good L z J → val t' r z J = val t r z J := by
  obtain ⟨s, hs⟩ := exists_sec hL h (genSec t ht)
  have hu : ∀ j, IsUnit (s.f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
      rw [hs _ _ y J hJ, sval_genSec t ht _ y hJ, ← Units.val_mul] at e
      exact (congrArg IsUnit
        ((gs_eq (𝟙 Y) y (LB.wchart L φ' j) hy _).symm.trans e)).mpr (Units.isUnit _)
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j),
    fun Z r z J hJ => Units.ext ?_⟩
  exact (gs_unit r z _ (hJ.mem φ' r) _).symm.trans
    ((hs Z r z J hJ).trans (sval_genSec t ht r z hJ))

end LBGerm

namespace LB

open LBGerm

variable (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

def oneGen : Gen (LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s _ := 1

theorem isGen_oneGen : (oneGen L (Y := Y)).IsGen := by
  intro i j
  have hg : (LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
    delta LinComb
    exact Fintype.prod_empty _
  rw [hg, one_mul]
  exact (map_one _).trans (map_one _).symm

def mulGen (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : Gen (LinComb L φ ε)) (t' : Gen (LinComb L φ' ε')) :
    Gen (LinComb L (Sum.elim φ φ') (Sum.elim ε ε')) where
  s j := res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)) :
      wchart L (Sum.elim φ φ') j ≤ wchart L φ (j ∘ Sum.inl)) (t.s _) *
    res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)) :
      wchart L (Sum.elim φ φ') j ≤ wchart L φ' (j ∘ Sum.inr)) (t'.s _)

theorem gm_mulGen (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : Gen (LinComb L φ ε)) (t' : Gen (LinComb L φ' ε'))
    (r : Z ⟶ Y) (z : Z) (j : K ⊕ K' → L.ι)
    (hj : r z ∈ wchart L (Sum.elim φ φ') j) :
    gm r z _ ((mulGen L φ ε φ' ε' t t').s j) =
      gm r z _ (t.s (j ∘ Sum.inl)) * gm r z _ (t'.s (j ∘ Sum.inr)) := by
  change gm r z _ (res _ _ * res _ _) = _
  exact (map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_res r z _ hj _) (gm_res r z _ hj _))

theorem isGen_mulGen (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : Gen (LinComb L φ ε)) (t' : Gen (LinComb L φ' ε'))
    (ht : t.IsGen) (ht' : t'.IsGen) :
    (mulGen L φ ε φ' ε' t t').IsGen := by
  intro j j'
  apply unit_ext
  intro y hy
  have hj : (𝟙 Y : Y ⟶ Y) y ∈ wchart L φ (j ∘ Sum.inl) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (Sum.inl k)
  have hj' : (𝟙 Y : Y ⟶ Y) y ∈ wchart L φ (j' ∘ Sum.inl) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (Sum.inl k)
  have hk : (𝟙 Y : Y ⟶ Y) y ∈ wchart L φ' (j ∘ Sum.inr) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (Sum.inr k)
  have hk' : (𝟙 Y : Y ⟶ Y) y ∈ wchart L φ' (j' ∘ Sum.inr) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (Sum.inr k)
  refine (gm_res (𝟙 Y) y _ hy _).trans
    ((gm_mulGen L φ ε φ' ε' t t' (𝟙 Y) y j hy.1).trans (Eq.trans ?_
      ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)
        ((gm_res (𝟙 Y) y _ hy _).trans
          (gm_mulGen L φ ε φ' ε' t t' (𝟙 Y) y j' hy.2)))).symm))
  have hprod : (∏ k : K ⊕ K', gm (𝟙 Y ≫ Sum.elim φ φ' k) y (L.U (j k) ⊓ L.U (j' k))
      (L.g (j k) (j' k)) ^ Sum.elim ε ε' k) =
      trF φ ε (𝟙 Y) y (j ∘ Sum.inl) (j' ∘ Sum.inl) *
        trF φ' ε' (𝟙 Y) y (j ∘ Sum.inr) (j' ∘ Sum.inr) := by
    rw [Fintype.prod_sum_type]
    rfl
  exact (congrArg₂ (· * ·) (gen_trans ht (𝟙 Y) y hj hj') (gen_trans ht' (𝟙 Y) y hk hk')).trans
    ((mul_mul_mul_comm _ _ _ _).trans (congrArg (· * _) hprod.symm))

end LB

/-- Existence of a genuine chart generator for the signed pullback. -/
def HasGen (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen

namespace HasGen

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem mul (h : HasGen L φ ε) (h' : HasGen L φ' ε') :
    HasGen L (Sum.elim φ φ') (Sum.elim ε ε') := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  exact ⟨_, LB.isGen_mulGen L _ _ _ _ t t' ht ht'⟩

theorem inv (h : HasGen L φ ε) : HasGen L φ (fun k => -ε k) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, LB.isGen_invGen L _ _ t ht⟩

theorem pull (h : HasGen L φ ε) (f : Z ⟶ Y) :
    HasGen L (fun k => f ≫ φ k) ε := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, LB.isGen_pullGen L _ _ t ht f⟩

theorem of_formEq (hL : L.IsLB) (h : HasGen L φ ε)
    (e : LBGerm.FormEq φ ε φ' ε') : HasGen L φ' ε' := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := LBGerm.exists_gen hL e t ht
  exact ⟨t', ht'⟩

end HasGen

end RHLean.Geometry.NativeCM.SchemeTheory

end
