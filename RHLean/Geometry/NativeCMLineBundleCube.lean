import RHLean.Geometry.NativeCMLineBundleNested
import RHLean.Geometry.NativeCMSerreSchemeAction

/-!
# Actual eight-term cube generators and signed pullbacks

The cube is the original signed product of the eight addition maps on the
triple product. A generator means units on every chart with the literal
transition law. Pulling those units along the triple of an actual group
morphism, and then taking their signed product, constructs the generator
for a signed line-bundle pullback.

This is a native chart-level specialization of Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsTensorBundle.lean`, and of its `hasGen_nested` supplier in
`src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/`
`ExistsPrimitiveNormalisation.lean`.

The hypothesis is a genuine generator for the seed cube. This file does
not supply that geometric theorem for the seed, nor assert the normalized
face and cocycle conditions of a full cubical structure. The construction
is the specific cube-generator input used by the tensor pairing proof.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory

variable {S : Scheme.{0}} {A G T : Over S}

/-- The three original projections from the triple product. -/
def cubePoint (A : Over S) : Fin 3 → (A ⊗ (A ⊗ A) ⟶ A) :=
  ![fst A (A ⊗ A), snd A (A ⊗ A) ≫ fst A A,
    snd A (A ⊗ A) ≫ snd A A]

/-- The eight terms of the third multiplicative difference, in order. -/
def cubeTerm [GrpObj A] (x y z : T ⟶ A) : Fin 8 → (T ⟶ A) :=
  ![x * y * z, x * y, x * z, y * z, x, y, z, 1]

def cubeExponent : Fin 8 → ℤ := ![1, -1, -1, -1, 1, 1, 1, -1]

def cubeMap (A : Over S) [GrpObj A] : Fin 8 → (A ⊗ (A ⊗ A) ⟶ A) :=
  cubeTerm (cubePoint A 0) (cubePoint A 1) (cubePoint A 2)

/-- The actual cube atlas, without a quotient by line-bundle classes. -/
def cubeBundle (A : Over S) [GrpObj A] (L : LB A.left) :
    LB (A ⊗ (A ⊗ A)).left :=
  LB.LinComb L (fun k => (cubeMap A k).left) cubeExponent

/-- Existence of a literal trivialization of the actual cube atlas. -/
def HasCubeGenerator (A : Over S) [GrpObj A] (L : LB A.left) : Prop :=
  ∃ t : LB.Gen (cubeBundle A L), t.IsGen

def cubeTripleMap (f : A ⟶ G) : A ⊗ (A ⊗ A) ⟶ G ⊗ (G ⊗ G) :=
  lift (cubePoint A 0 ≫ f)
    (lift (cubePoint A 1 ≫ f) (cubePoint A 2 ≫ f))

@[reassoc]
theorem cubeTripleMap_point (f : A ⟶ G) (i : Fin 3) :
    cubeTripleMap f ≫ cubePoint G i = cubePoint A i ≫ f := by
  fin_cases i <;> simp [cubeTripleMap, cubePoint]

theorem cubeTerm_post [GrpObj A] [GrpObj G] (f : A ⟶ G) [IsMonHom f] (x y z : T ⟶ A) (k : Fin 8) :
    cubeTerm x y z k ≫ f = cubeTerm (x ≫ f) (y ≫ f) (z ≫ f) k := by
  fin_cases k <;> simp [cubeTerm, MonObj.mul_comp]

theorem cubeTerm_pre [GrpObj A] {T' : Over S} (r : T' ⟶ T) (x y z : T ⟶ A) (k : Fin 8) :
    r ≫ cubeTerm x y z k = cubeTerm (r ≫ x) (r ≫ y) (r ≫ z) k := by
  fin_cases k <;> simp [cubeTerm, MonObj.comp_mul]

theorem cubeMap_lift [GrpObj A] (x y z : T ⟶ A) (k : Fin 8) :
    lift x (lift y z) ≫ cubeMap A k = cubeTerm x y z k := by
  rw [cubeMap, cubeTerm_pre]
  simp only [cubePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, lift_fst, lift_snd_assoc, lift_snd]

/-- The universal generator pulls back to every actual triple of
scheme-valued points. -/
theorem HasCubeGenerator.at_triple [GrpObj A] {L : LB A.left}
    (hL : HasCubeGenerator A L) (x y z : T ⟶ A) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => (cubeTerm x y z k).left) cubeExponent),
      t.IsGen := by
  obtain ⟨t, ht⟩ := hL
  have e : (fun k : Fin 8 => (lift x (lift y z)).left ≫ (cubeMap A k).left) =
      fun k => (cubeTerm x y z k).left := by
    funext k
    exact congrArg Over.Hom.left (cubeMap_lift x y z k)
  have h : ∃ v : LB.Gen (LB.LinComb L
      (fun k => (lift x (lift y z)).left ≫ (cubeMap A k).left) cubeExponent), v.IsGen :=
    ⟨LB.pullGen L _ _ t (lift x (lift y z)).left,
      LB.isGen_pullGen L _ _ t ht (lift x (lift y z)).left⟩
  rw [e] at h
  exact h

@[reassoc]
theorem cubeMap_post [GrpObj A] [GrpObj G] (f : A ⟶ G) [IsMonHom f] (k : Fin 8) :
    cubeMap A k ≫ f = cubeTripleMap f ≫ cubeMap G k := by
  rw [cubeMap, cubeTerm_post, cubeMap, cubeTerm_pre]
  simp only [cubeTripleMap_point]

/-- Pull a seed cube generator along the triple of the actual group
morphism; the resulting maps are exactly the original cube maps followed
by that morphism. -/
theorem HasCubeGenerator.pull_terms [GrpObj A] [GrpObj G] {L : LB G.left} (hL : HasCubeGenerator G L)
    (f : A ⟶ G) [IsMonHom f] :
    ∃ t : LB.Gen (LB.LinComb L
      (fun k => (cubeMap A k).left ≫ f.left) cubeExponent), t.IsGen := by
  obtain ⟨t, ht⟩ := hL
  have e : (fun k : Fin 8 => (cubeTripleMap f).left ≫ (cubeMap G k).left) =
      fun k => (cubeMap A k).left ≫ f.left := by
    funext k
    exact (congrArg Over.Hom.left (cubeMap_post f k)).symm
  have h : ∃ v : LB.Gen (LB.LinComb L
      (fun k => (cubeTripleMap f).left ≫ (cubeMap G k).left) cubeExponent), v.IsGen :=
    ⟨LB.pullGen L _ _ t (cubeTripleMap f).left,
      LB.isGen_pullGen L _ _ t ht (cubeTripleMap f).left⟩
  rw [e] at h
  exact h

/-- The actual nested chart generator for every signed product of
pullbacks along group morphisms. No freeness of the represented group or
class-valued replacement of its bundle is used. -/
theorem HasCubeGenerator.linComb [GrpObj A] [GrpObj G] {L : LB G.left} (hL : HasCubeGenerator G L)
    {K : Type} [Fintype K] (f : K → (A ⟶ G))
    (hf : ∀ k, IsMonHom (f k)) (ε : K → ℤ) :
    HasCubeGenerator A (LB.LinComb L (fun k => (f k).left) ε) := by
  apply LB.exists_isGen_nested
  intro k
  have := hf k
  exact hL.pull_terms (f k)

end RHLean.Geometry.NativeCM.SchemeTheory

end
