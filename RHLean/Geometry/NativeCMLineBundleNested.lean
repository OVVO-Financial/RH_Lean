import RHLean.Geometry.NativeCMLineBundleTransport

/-!
# Explicit generators of nested signed pullbacks

A generator is retained on every original chart. Products of its actual
pullbacks, with the original integer exponents, give a generator of the
nested atlas. This is a direct chart calculation; no Picard-group equality
or existence of a line-bundle isomorphism is assumed.

The motivating source construction is Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/`
`ExistsPrimitiveNormalisation.lean`, `hasGen_nested`. The declarations here
are a smaller native derivation for explicit families of generators,
using the previously attributed atlas and restriction maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

namespace RHLean.Geometry.NativeCM.SchemeTheory.LB

variable {X Y Z : Scheme.{0}} (L : LB X)
    {K J : Type} [Fintype K] [Fintype J]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : J → (Z ⟶ Y)) (δ : J → ℤ)

theorem wchart_nested_le (j : J → K → L.ι) (k : K) :
    wchart (LinComb L φ ε) ψ j ≤
      wchart L (fun b => ψ b ≫ φ k) (fun b => j b k) :=
  fun _ hz => Set.mem_iInter.2 fun b =>
    Set.mem_iInter.1 (Set.mem_iInter.1 hz b) k

theorem wchart_nested_inter_le (j j' : J → K → L.ι) (k : K) :
    wchart (LinComb L φ ε) ψ j ⊓ wchart (LinComb L φ ε) ψ j' ≤
      wchart L (fun b => ψ b ≫ φ k) (fun b => j b k) ⊓
        wchart L (fun b => ψ b ≫ φ k) (fun b => j' b k) :=
  le_inf (inf_le_left.trans (wchart_nested_le L φ ε ψ j k))
    (inf_le_right.trans (wchart_nested_le L φ ε ψ j' k))

/-- The transition unit of the nested atlas is the product of the
original pulled transition units, with both integer exponents retained. -/
theorem lcg_nested (j j' : J → K → L.ι) :
    lcg (LinComb L φ ε) ψ δ j j' =
      ∏ k, (res (wchart_nested_inter_le L φ ε ψ j j' k)
        (lcg L (fun b => ψ b ≫ φ k) δ (fun b => j b k) (fun b => j' b k))) ^ ε k := by
  let u (b : J) (k : K) :
      Γ(Z, wchart (LinComb L φ ε) ψ j ⊓ wchart (LinComb L φ ε) ψ j')ˣ :=
    res ((wchart_nested_inter_le L φ ε ψ j j' k).trans
      (wchart_inter_le L (fun b => ψ b ≫ φ k) (fun b => j b k) (fun b => j' b k) b))
      (pullU (ψ b ≫ φ k) _ (L.g (j b k) (j' b k)))
  have hleft (b : J) :
      res (wchart_inter_le (LinComb L φ ε) ψ j j' b)
          (pullU (ψ b) _ ((LinComb L φ ε).g (j b) (j' b))) =
        ∏ k, u b k ^ ε k := by
    change res _ (pullU (ψ b) _ (lcg L φ ε (j b) (j' b))) = _
    rw [lcg, map_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, map_zpow]
    exact congrArg (· ^ ε k) (pull_res_comp (ψ b) (φ k) _ _ _ _ _)
  have hright (k : K) :
      res (wchart_nested_inter_le L φ ε ψ j j' k)
          (lcg L (fun b => ψ b ≫ φ k) δ (fun b => j b k) (fun b => j' b k)) =
        ∏ b, u b k ^ δ b := by
    exact res_lcg L (fun b => ψ b ≫ φ k) δ
      (fun b => j b k) (fun b => j' b k) _
  change (∏ b, (res _ (pullU (ψ b) _ ((LinComb L φ ε).g (j b) (j' b)))) ^ δ b) = _
  simp_rw [hleft, hright, Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← zpow_mul, ← zpow_mul, mul_comm]

/-- An explicit generator on the nested atlas, formed from the given
generators on every original signed pullback. -/
def nestedGen
    (t : ∀ k, Gen (LinComb L (fun b => ψ b ≫ φ k) δ)) :
    Gen (LinComb (LinComb L φ ε) ψ δ) where
  s j := ∏ k, (res (wchart_nested_le L φ ε ψ j k)
    ((t k).s (fun b => j b k))) ^ ε k

theorem isGen_nestedGen
    (t : ∀ k, Gen (LinComb L (fun b => ψ b ≫ φ k) δ))
    (ht : ∀ k, (t k).IsGen) :
    (nestedGen L φ ε ψ δ t).IsGen := by
  intro j j'
  change res inf_le_left (∏ k, (res (wchart_nested_le L φ ε ψ j k)
      ((t k).s (fun b => j b k))) ^ ε k) =
    lcg (LinComb L φ ε) ψ δ j j' *
      res inf_le_right (∏ k, (res (wchart_nested_le L φ ε ψ j' k)
        ((t k).s (fun b => j' b k))) ^ ε k)
  rw [lcg_nested, map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow, ← mul_zpow, res_res, res_res]
  have h := congrArg (res (wchart_nested_inter_le L φ ε ψ j j' k))
    (ht k (fun b => j b k) (fun b => j' b k))
  simp only [map_mul, res_res] at h
  exact congrArg (· ^ ε k) h

theorem exists_isGen_nested
    (ht : ∀ k, ∃ t : Gen (LinComb L (fun b => ψ b ≫ φ k) δ), t.IsGen) :
    ∃ t : Gen (LinComb (LinComb L φ ε) ψ δ), t.IsGen := by
  choose t ht using ht
  exact ⟨nestedGen L φ ε ψ δ t, isGen_nestedGen L φ ε ψ δ t ht⟩

end RHLean.Geometry.NativeCM.SchemeTheory.LB

end
