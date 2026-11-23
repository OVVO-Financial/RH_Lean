import RHLean.Geometry.NativeThetaInvariantDerivatives
import RHLean.Geometry.NativeThetaTriangularFrame

/-!
# Triangular frame covariance of the actual native theta jets

The formal group is the same one used in the native directional derivative.
Its invariant derivatives commute by associativity and commutativity, as
proved in NativeThetaInvariantDerivatives. Their generated algebra therefore
supports polynomial evaluation. Contracting its tensor powers against the
original gauge-corrected germs transfers the native HHa triangular identity
to the original finite theta formula. No frame transformation of that formula
is assumed, and every short-value normalization is retained.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`InvariantOperatorValueTriangularChange.lean`, RowTriangular.Op and
`nabVal_triangular`; and
`ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/`
`WickVanishing/DofDApply.lean`, dofD.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeTheta.JetFrame

open MvPowerSeries JetEvaluation FormalCalculus RowTriangular
open scoped TensorProduct IsMulCommutative

section Operators

variable {S : Type} [CommRing S] {d : ℕ}

/-- Package the existing native derivative as an actual linear operator. -/
def dEnd (F : Fin d → PS S 2 d) (v : Fin d → S) : Module.End S (PS S 1 d) :=
  (∑ j : Fin d,
    (∑ i : Fin d, C (v i) *
      substituteCopies ![coordinatePoint 1 0, 0]
        (pderiv ((1 : Fin 2), i) (F j))) •
      pderiv ((0 : Fin 1), j)).toLinearMap

theorem dEnd_apply (F : Fin d → PS S 2 d) (v : Fin d → S) (g : PS S 1 d) :
    dEnd F v g = directionalDerivative F v g := by
  have h : ∀ (s : Finset (Fin d))
      (D : Fin d → Derivation S (PS S 1 d) (PS S 1 d)),
      (∑ j ∈ s, D j) g = ∑ j ∈ s, D j g := by
    intro s D
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  change (∑ j : Fin d,
    (∑ i : Fin d, C (v i) *
      substituteCopies ![coordinatePoint 1 0, 0]
        (pderiv ((1 : Fin 2), i) (F j))) •
      pderiv ((0 : Fin 1), j)) g = _
  rw [h]
  simp only [Derivation.smul_apply, smul_eq_mul, directionalDerivative]

theorem dEnd_comb (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (c : κ → S) (w : κ → Fin d → S) (v : Fin d → S)
    (hv : ∀ e, v e = ∑ j, c j * w j e) : dEnd F v = ∑ j, c j • dEnd F (w j) := by
  refine LinearMap.ext fun g => ?_
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, dEnd_apply, directionalDerivative, hv, map_sum, map_mul, Finset.sum_mul,
    Finset.smul_sum, MvPowerSeries.smul_eq_C_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem dmon_eq {A : Type} [CommRing A] [Algebra S A] (F : Fin d → PS S 2 d) (Ψ : A →ₐ[S] Module.End S (PS S 1 d))
    {I : Type} [Fintype I] (u : I → Fin d → S) (x : I → A) (hx : ∀ l, Ψ (x l) = dEnd F (u l)) (m : I →₀ ℕ)
    (g : PS S 1 d) : monomialDerivative F u m g = Ψ (∏ l, x l ^ m l) g := by
  classical
  have hD : ∀ v, ⇑(dEnd F v) = directionalDerivative F v := fun v => funext (dEnd_apply F v)
  have key : ∀ L : List I,
      L.foldr (fun l h => (directionalDerivative F (u l))^[m l] h) g = Ψ ((L.map fun l => x l ^ m l).prod) g := by
    intro L
    induction L with
    | nil => simp
    | cons l L ih =>
      rw [List.foldr_cons, List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ← ih, map_pow,
        hx, Module.End.pow_apply, hD]
  rw [monomialDerivative, key, Finset.prod_map_toList]

def prodForm {A : Type} [CommRing A] [Algebra S A] {n : ℕ} (lam : Fin n → A →ₗ[S] S) :
    (⨂[S] _ : Fin n, A) →ₗ[S] S :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra S (Fin n) S).compLinearMap lam)

theorem prodForm_prod {A : Type} [CommRing A] [Algebra S A] {n : ℕ} (lam : Fin n → A →ₗ[S] S) (x : Fin n → A) :
    prodForm lam (∏ b, PiTensorProduct.singleAlgHom (R := S) (A := fun _ : Fin n => A) b (x b)) = ∏ b, lam b (x b) := by
  have e : (∏ b, PiTensorProduct.singleAlgHom (R := S) (A := fun _ : Fin n => A) b (x b)) =
      PiTensorProduct.tprod S x := by
    simp only [PiTensorProduct.singleAlgHom_apply, MonoidHom.mulSingle_apply]
    rw [← PiTensorProduct.tprod_prod, Finset.univ_prod_mulSingle]
  rw [e]
  simp [prodForm]

end Operators

section FrameChange

variable {Ty K S : Type} [Fintype Ty] [Field K] [Infinite K]
  [CommRing S] [Algebra K S] [Algebra ℚ S]
  {r : Ty → ℕ} {n d : ℕ}

/-- The source triangular weight law for the actual native column jets.
The gauge and all section germs are shared on both sides. -/
theorem columnJet_triangular
    (G : FormalGroup S d) (actW0 : Fin d → Series S 1 d)
    (h : Series S 2 d) (k : ℕ) (f : Fin n → Series S 1 d)
    (u u' : Row Ty r → Fin d → S)
    (cf : ∀ τ, Fin (r τ) → Fin (r τ) → S)
    (hcf : ∀ τ i j, i < j → cf τ i j = 0)
    (huu : ∀ τ i e, u' ⟨τ, i⟩ e = ∑ j, cf τ i j * u ⟨τ, j⟩ e)
    (hu : ∀ τ i, IsUnit (cf τ i i))
    (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (P : MvPolynomial (Letter Ty r n) K) (hP : P ∈ HHa r n K cc isX a) :
    ∑ m ∈ P.support, algebraMap K S (P.coeff m) *
        ∏ b, formalColumnJet G.F actW0 h k (f b) u' (columnExponent m b) =
      (∏ l : Row Ty r, cf l.1 l.2 l.2 ^ a l.1 l.2) *
        ∑ m ∈ P.support, algebraMap K S (P.coeff m) *
          ∏ b, formalColumnJet G.F actW0 h k (f b) u (columnExponent m b) := by
  classical
  have hcomm : ∀ v w : Fin d → S,
      dEnd G.F v * dEnd G.F w = dEnd G.F w * dEnd G.F v := by
    intro v w
    refine LinearMap.ext fun g => ?_
    simp only [Module.End.mul_apply, dEnd_apply]
    exact dof_comm_law G v w g
  let s : Set (Module.End S (PS S 1 d)) :=
    Set.range fun e : Fin d => dEnd G.F (Pi.single e 1)
  have hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    exact hcomm _ _
  have : IsMulCommutative (Algebra.adjoin S s) :=
    Algebra.isMulCommutative_adjoin S (fun x hx y hy _ => hs x hx y hy)
  have hmem : ∀ v : Fin d → S, dEnd G.F v ∈ Algebra.adjoin S s := by
    intro v
    rw [dEnd_comb G.F (fun e => v e) (fun e => Pi.single e 1) v
      (fun e' => by simp [Pi.single_apply])]
    exact Subalgebra.sum_mem _ fun e _ =>
      Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self e)) _
  let lam : Fin n → Algebra.adjoin S s →ₗ[S] S := fun b =>
    { toFun := fun z => MvPowerSeries.constantCoeff
        ((z : Module.End S (PS S 1 d)) (gaugedGerm actW0 h k (f b)))
      map_add' := fun z z' => by simp
      map_smul' := fun r z => by simp [MvPowerSeries.smul_eq_C_mul] }
  let φ : K →+* (⨂[S] _ : Fin n, Algebra.adjoin S s) :=
    (algebraMap S (⨂[S] _ : Fin n, Algebra.adjoin S s)).comp (algebraMap K S)
  have hpull : ∀ (z : S) (t : ⨂[S] _ : Fin n, Algebra.adjoin S s),
      prodForm (S := S) (A := Algebra.adjoin S s) (n := n) lam
          (algebraMap S _ z * t) =
        z * prodForm (S := S) (A := Algebra.adjoin S s) (n := n) lam t := by
    intro z t
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hval : ∀ (U : Row Ty r → Fin d → S) (X : Row Ty r → Algebra.adjoin S s),
      (∀ l, (Algebra.adjoin S s).val (X l) = dEnd G.F (U l)) →
      ∑ m ∈ P.support, algebraMap K S (P.coeff m) *
          ∏ b, formalColumnJet G.F actW0 h k (f b) U (columnExponent m b) =
        prodForm (S := S) (A := Algebra.adjoin S s) (n := n) lam
          (MvPolynomial.eval₂Hom φ (fun l : Letter Ty r n =>
          PiTensorProduct.singleAlgHom (R := S)
            (A := fun _ : Fin n => Algebra.adjoin S s) l.2.2 (X ⟨l.1, l.2.1⟩)) P) := by
    intro U X hX
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show φ (P.coeff m) =
      algebraMap S _ (algebraMap K S (P.coeff m)) from rfl, hpull]
    congr 1
    have e1 : ∀ b, formalColumnJet G.F actW0 h k (f b) U (columnExponent m b) =
        lam b (∏ l, X l ^ (columnExponent m b) l) := by
      intro b
      rw [formalColumnJet,
        dmon_eq (S := S) (A := Algebra.adjoin S s) G.F (Algebra.adjoin S s).val U X hX]
      rfl
    simp only [e1]
    rw [← prodForm_prod (S := S) (A := Algebra.adjoin S s) (n := n) lam]
    congr 1
    simp only [map_prod, map_pow]
    rw [Finset.prod_comm, Fintype.prod_sigma, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun b _ => ?_
    simp [columnExponent]
  let X : Row Ty r → Algebra.adjoin S s := fun l => ⟨dEnd G.F (u l), hmem _⟩
  let X' : Row Ty r → Algebra.adjoin S s := fun l => ⟨dEnd G.F (u' l), hmem _⟩
  have hx' : ∀ τ i, X' ⟨τ, i⟩ = ∑ j, cf τ i j • X ⟨τ, j⟩ := by
    intro τ i
    apply Subtype.val_injective
    change dEnd G.F (u' ⟨τ, i⟩) = (Algebra.adjoin S s).val (∑ j, cf τ i j • X ⟨τ, j⟩)
    rw [map_sum]
    simp only [map_smul]
    exact dEnd_comb G.F (cf τ i) (fun j => u ⟨τ, j⟩) _ (huu τ i)
  rw [hval u' X' (fun l => rfl), hval u X (fun l => rfl)]
  have hY : (fun l : Letter Ty r n => PiTensorProduct.singleAlgHom (R := S)
        (A := fun _ : Fin n => Algebra.adjoin S s) l.2.2 (X' ⟨l.1, l.2.1⟩)) =
      fun l => ∑ j, algebraMap S (⨂[S] _ : Fin n, Algebra.adjoin S s) (cf l.1 l.2.1 j) *
        PiTensorProduct.singleAlgHom (R := S) (A := fun _ : Fin n => Algebra.adjoin S s)
          l.2.2 (X ⟨l.1, j⟩) := by
    funext l
    rw [hx', map_sum]
    simp only [map_smul]
    simp only [Algebra.smul_def]
  have h3 := eval₂_triangular φ hP.2.1 hP.2.2
    (fun τ i j => algebraMap S (⨂[S] _ : Fin n, Algebra.adjoin S s) (cf τ i j))
    (fun τ i j hlt => by simp [hcf τ i j hlt]) (fun τ i => (hu τ i).map _)
    (fun l : Letter Ty r n => PiTensorProduct.singleAlgHom (R := S)
      (A := fun _ : Fin n => Algebra.adjoin S s) l.2.2 (X ⟨l.1, l.2.1⟩))
  rw [hY]
  refine (congrArg (prodForm (S := S) (A := Algebra.adjoin S s) (n := n) lam) h3).trans ?_
  rw [← hpull]
  congr 2
  simp [map_prod, map_pow]

/-- The same triangular character acts on the complete finite short value;
the beta, lattice index, level-function cardinality and level-power factors
are kept unchanged. -/
theorem shortValueOfFormalGerms_triangular
    {Q J : Type} [Fintype Q] [Fintype J]
    (β : K) (index N : ℕ) (w : Q → K)
    (G : FormalGroup S d) (actW0 : Fin d → Series S 1 d) (h : Series S 2 d)
    (u u' : Row Ty r → Fin d → S)
    (germ : Q → J → Fin n → Series S 1 d)
    (cf : ∀ τ, Fin (r τ) → Fin (r τ) → S)
    (hcf : ∀ τ i j, i < j → cf τ i j = 0)
    (huu : ∀ τ i e, u' ⟨τ, i⟩ e = ∑ j, cf τ i j * u ⟨τ, j⟩ e)
    (hu : ∀ τ i, IsUnit (cf τ i i))
    (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (P : MvPolynomial (Letter Ty r n) K) (hP : P ∈ HHa r n K cc isX a) :
    shortValueOfFormalGerms β index N w G.F actW0 h u' germ P =
      (∏ l : Row Ty r, cf l.1 l.2 l.2 ^ a l.1 l.2) *
        shortValueOfFormalGerms β index N w G.F actW0 h u germ P := by
  classical
  let c : S := ∏ l : Row Ty r, cf l.1 l.2 l.2 ^ a l.1 l.2
  change shortValueOfFormalGerms β index N w G.F actW0 h u' germ P =
    c * shortValueOfFormalGerms β index N w G.F actW0 h u germ P
  simp only [shortValueOfFormalGerms, rawShortValue]
  rw [mul_left_comm c]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_left_comm c]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ =>
    columnJet_triangular G actW0 h (N ^ 2) (germ q j) u u' cf hcf huu hu cc isX a P hP

end FrameChange

end RHLean.Geometry.NativeTheta.JetFrame

end
