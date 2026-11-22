import RHLean.Geometry.NativeThetaRowHighest

/-!
# Column actions on the same paired theta polynomials

Construct the actual GL action, the disjoint-column base polynomial and its
orbit span. Laplacians, row degrees and row invariance are proved compatible
with that action. No full-span or irreducibility premise occurs.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/`,
`Definitions/ThetaMetrics/IsWeightedHomogeneousOfMemOrbitSpan.lean`;
`Proofs/CovolumeBounds/IsHarmonicProdOfDisjointColumns.lean`;
`Definitions/ThetaValues/ExistsMemRowHighestTotalDegreeEqTwo.lean`;
only the declarations used by the native highest-weight construction.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MvPolynomial Matrix

namespace RHLean.Geometry.NativeTheta.Paired

variable {R S : Type*} [CommRing R] [CommRing S]
  {T : Type*} {p q n : ℕ} {κ κ' κ'' : Type*}

section Subst

variable [Fintype κ] [Fintype κ'] [Fintype κ'']

noncomputable def colSubst (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) :
    Poly R T p q κ →ₐ[R] Poly R T p q κ' :=
  aeval fun v => match v with
    | (t, Sum.inl a, k) => xForm t a (A t k)
    | (t, Sum.inr b, k) => yForm t b fun l => B t l k

omit [Fintype κ] in

@[simp] theorem colSubst_X_xVar (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (a : Fin p)
    (k : κ) : colSubst A B (X (xVar t a k) : Poly R T p q κ) = xForm t a (A t k) := by
  simp [colSubst]

omit [Fintype κ] in

@[simp] theorem colSubst_X_yVar (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (b : Fin q)
    (k : κ) : colSubst A B (X (yVar t b k) : Poly R T p q κ) = yForm t b fun l => B t l k := by
  simp [colSubst]

theorem colSubst_xForm (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (a : Fin p)
    (ε : κ → R) : colSubst A B (xForm t a ε : Poly R T p q κ) = xForm t a (ε ᵥ* A t) := by
  have : ε ᵥ* A t = ∑ k, ε k • A t k := by ext l; simp [vecMul, dotProduct]
  rw [this, map_sum, xForm_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← smul_eq_C_mul, map_smul, map_smul, colSubst_X_xVar]

theorem colSubst_yForm (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (b : Fin q)
    (φ : κ → R) : colSubst A B (yForm t b φ : Poly R T p q κ) = yForm t b (B t *ᵥ φ) := by
  have : B t *ᵥ φ = ∑ k, φ k • fun l => B t l k := by ext l; simp [mulVec, dotProduct, mul_comm]
  rw [this, map_sum, yForm_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← smul_eq_C_mul, map_smul, map_smul, colSubst_X_yVar]

omit [Fintype κ] in
theorem colSubst_comp (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (A' : T → Matrix κ' κ'' R)
    (B' : T → Matrix κ'' κ' R) :
    (colSubst A' B').comp (colSubst (p := p) (q := q) A B) =
      colSubst (fun t => A t * A' t) (fun t => B' t * B t) := by
  refine MvPolynomial.algHom_ext fun ⟨t, r, k⟩ => ?_
  rcases r with a | b
  · rw [AlgHom.comp_apply, colSubst_X_xVar, colSubst_X_xVar, colSubst_xForm]; rfl
  · rw [AlgHom.comp_apply, colSubst_X_yVar, colSubst_X_yVar, colSubst_yForm]; rfl

theorem colSubst_one [DecidableEq κ] :
    colSubst (p := p) (q := q) (fun _ : T => (1 : Matrix κ κ R)) (fun _ => 1) = AlgHom.id R _ := by
  refine MvPolynomial.algHom_ext fun ⟨t, r, k⟩ => ?_
  rcases r with a | b
  · rw [colSubst_X_xVar, AlgHom.id_apply, ← xForm_single]
    congr 1; ext l; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · rw [colSubst_X_yVar, AlgHom.id_apply, ← yForm_single]
    congr 1; ext l; simp [Matrix.one_apply, Pi.single_apply]

theorem colSubst_minorProd [Fintype T] (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    colSubst A B (minorProd c c' ε φ) =
      minorProd c c' (fun t a => ε t a ᵥ* A t) (fun t b => B t *ᵥ φ t b) := by
  simp only [minorProd, map_prod, map_mul, map_pow]
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 1
  · exact Finset.prod_congr rfl fun i _ => congrArg (· ^ c t i)
      (ringHom_xMinor (colSubst A B).toRingHom t i (ε t) (fun a => ε t a ᵥ* A t)
        fun a b => colSubst_xForm _ _ _ _ _)
  · exact Finset.prod_congr rfl fun i _ => congrArg (· ^ c' t i)
      (ringHom_yMinor (colSubst A B).toRingHom t i (φ t) (fun a => B t *ᵥ φ t a)
        fun a b => colSubst_yForm _ _ _ _ _)

omit [Fintype κ] in

theorem eval_colSubst (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (z : Var T p q κ' → R)
    (P : Poly R T p q κ) :
    eval z (colSubst A B P) = eval (fun v => match v with
      | (t, Sum.inl a, k) => (A t *ᵥ fun l => z (xVar t a l)) k
      | (t, Sum.inr b, k) => ((fun l => z (yVar t b l)) ᵥ* B t) k) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    obtain ⟨t, a | b, k⟩ := v
    · rw [map_mul, map_mul, map_mul, hP, eval_X, colSubst_X_xVar, eval_xForm]; rfl
    · rw [map_mul, map_mul, map_mul, hP, eval_X, colSubst_X_yVar, eval_yForm, dotProduct_comm]; rfl

omit [Fintype κ] in

theorem colSubst_isWeightedHomogeneous {M : Type*} [AddCommMonoid M] (w : T → Fin p ⊕ Fin q → M)
    (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) {P : Poly R T p q κ} {m : M}
    (hP : IsWeightedHomogeneous (rowWeight w) P m) :
    IsWeightedHomogeneous (rowWeight w) (colSubst A B P) m := by
  rw [P.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [← hP (mem_support_iff.mp hd), colSubst, aeval_monomial, Finsupp.weight_apply, Finsupp.sum,
    Finsupp.prod]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun v _ => IsWeightedHomogeneous.pow ?_ _
  obtain ⟨t, a | b, k⟩ := v
  · exact rowForm_isWeightedHomogeneous w t _ _
  · exact rowForm_isWeightedHomogeneous w t _ _

end Subst

section Action

variable [Fintype κ] [DecidableEq κ]

def vecAct (g : GL κ R) (φ : κ → R) : κ → R := (g : Matrix κ κ R) *ᵥ φ

def covecAct (g : GL κ R) (ε : κ → R) : κ → R := ε ᵥ* ((g⁻¹ : GL κ R) : Matrix κ κ R)

theorem covecAct_dotProduct_vecAct (g : GL κ R) (ε φ : κ → R) :
    covecAct g ε ⬝ᵥ vecAct g φ = ε ⬝ᵥ φ := by
  rw [covecAct, vecAct, dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one]

theorem IsPerp.act {ε : T → Fin p → κ → R} {φ : T → Fin q → κ → R} (h : IsPerp ε φ)
    (g : T → GL κ R) :
    IsPerp (fun t a => covecAct (g t) (ε t a)) (fun t b => vecAct (g t) (φ t b)) := fun t a b => by
  rw [covecAct_dotProduct_vecAct, h]

noncomputable def colActHom (g : T → GL κ R) : Poly R T p q κ →ₐ[R] Poly R T p q κ :=
  colSubst (fun t => ((g t)⁻¹ : GL κ R)) (fun t => g t)

theorem colActHom_one : colActHom (p := p) (q := q) (1 : T → GL κ R) = AlgHom.id R _ := by
  rw [← colSubst_one, colActHom]; simp

theorem colActHom_mul (g h : T → GL κ R) :
    colActHom (p := p) (q := q) (g * h) = (colActHom g).comp (colActHom h) := by
  rw [colActHom, colActHom, colActHom, colSubst_comp]
  simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul]

variable (R T p q κ) in

noncomputable def colAct : (T → GL κ R) →* (Poly R T p q κ ≃ₐ[R] Poly R T p q κ) where
  toFun g := AlgEquiv.ofAlgHom (colActHom g) (colActHom g⁻¹)
    (by rw [← colActHom_mul, mul_inv_cancel, colActHom_one])
    (by rw [← colActHom_mul, inv_mul_cancel, colActHom_one])
  map_one' := AlgEquiv.ext fun P => DFunLike.congr_fun colActHom_one P
  map_mul' g h := AlgEquiv.ext fun P => DFunLike.congr_fun (colActHom_mul g h) P

theorem colAct_apply (g : T → GL κ R) (P : Poly R T p q κ) :
    colAct R T p q κ g P = colSubst (fun t => ((g t)⁻¹ : GL κ R)) (fun t => g t) P := rfl

variable (R T p q κ) in

noncomputable def colRep : Representation R (T → GL κ R) (Poly R T p q κ) where
  toFun g := (colAct R T p q κ g).toLinearMap
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

@[simp] theorem colRep_apply (g : T → GL κ R) (P : Poly R T p q κ) :
    colRep R T p q κ g P = colAct R T p q κ g P := rfl

theorem colAct_xForm (g : T → GL κ R) (t : T) (a : Fin p) (ε : κ → R) :
    colAct R T p q κ g (xForm t a ε) = xForm t a (covecAct (g t) ε) := colSubst_xForm _ _ _ _ _

theorem colAct_yForm (g : T → GL κ R) (t : T) (b : Fin q) (φ : κ → R) :
    colAct R T p q κ g (yForm t b φ) = yForm t b (vecAct (g t) φ) := colSubst_yForm _ _ _ _ _

theorem colAct_minorProd [Fintype T] (g : T → GL κ R) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    colAct R T p q κ g (minorProd c c' ε φ) =
      minorProd c c' (fun t a => covecAct (g t) (ε t a)) (fun t b => vecAct (g t) (φ t b)) :=
  colSubst_minorProd _ _ _ _ _ _

end Action

section Base

variable (R) in

def baseCovec (h : p + q ≤ n) (a : Fin p) : Fin n → R :=
  Pi.single (Fin.castLE (by omega) a) 1

variable (R) in

def baseVec (h : p + q ≤ n) (b : Fin q) : Fin n → R :=
  Pi.single (Fin.rev (Fin.castLE (by omega) b)) 1

variable (R T) in

theorem isPerp_base (h : p + q ≤ n) :
    IsPerp (fun _ : T => baseCovec R h) (fun _ => baseVec R h) := fun t a b => by
  have : Fin.castLE (by omega : p ≤ n) a ≠ Fin.rev (Fin.castLE (by omega : q ≤ n) b) := by
    intro e
    have := congrArg Fin.val e
    have := a.isLt; have := b.isLt
    simp only [Fin.val_castLE, Fin.val_rev] at *; omega
  simp [baseCovec, baseVec, Pi.single_apply, this]

theorem linearIndependent_baseCovec (h : p + q ≤ n) : LinearIndependent R (baseCovec R h) := by
  have := (Pi.basisFun R (Fin n)).linearIndependent.comp _
    (Fin.castLE_injective (by omega : p ≤ n))
  convert this using 1; ext1 a; simp [baseCovec]

theorem linearIndependent_baseVec (h : p + q ≤ n) : LinearIndependent R (baseVec R h) := by
  have := (Pi.basisFun R (Fin n)).linearIndependent.comp _
    (Fin.rev_injective.comp (Fin.castLE_injective (by omega : q ≤ n)))
  convert this using 1; ext1 a; simp [baseVec]

variable [Fintype T]

variable (R) in

noncomputable def basePoly (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) :
    Poly R T p q (Fin n) :=
  minorProd c c' (fun _ => baseCovec R h) (fun _ => baseVec R h)

variable (R) in

noncomputable def orbitSpan (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) :
    Submodule R (Poly R T p q (Fin n)) :=
  Submodule.span R (Set.range fun g : T → GL (Fin n) R =>
    colAct R T p q (Fin n) g (basePoly R h c c'))

variable (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)

theorem colAct_basePoly_mem (g : T → GL (Fin n) R) :
    colAct R T p q (Fin n) g (basePoly R h c c') ∈ orbitSpan R h c c' :=
  Submodule.subset_span ⟨g, rfl⟩

theorem basePoly_mem : basePoly R h c c' ∈ orbitSpan R h c c' := by
  simpa using colAct_basePoly_mem h c c' (1 : T → GL (Fin n) R)

theorem colAct_mem_orbitSpan (g : T → GL (Fin n) R) {P : Poly R T p q (Fin n)}
    (hP : P ∈ orbitSpan R h c c') : colAct R T p q (Fin n) g P ∈ orbitSpan R h c c' := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨g', rfl⟩ := hP
    have := colAct_basePoly_mem h c c' (g * g')
    rwa [map_mul] at this
  | zero => simp
  | add P Q _ _ hP hQ => rw [map_add]; exact add_mem hP hQ
  | smul r P _ hP => rw [map_smul]; exact Submodule.smul_mem _ _ hP

variable (R) in

noncomputable def orbitSubrep : Subrepresentation (colRep R T p q (Fin n)) where
  toSubmodule := orbitSpan R h c c'
  apply_mem_toSubmodule g _ hP := colAct_mem_orbitSpan h c c' g hP

theorem map_basePoly (f : R →+* S) : MvPolynomial.map f (basePoly R h c c') = basePoly S h c c' := by
  rw [basePoly, map_minorProd, basePoly]
  congr 1
  · ext t a k; simp [baseCovec, Pi.single_apply, apply_ite f]
  · ext t a k; simp [baseVec, Pi.single_apply, apply_ite f]

theorem eval_basePoly :
    eval (fun v : Var T p q (Fin n) =>
      Sum.elim (baseCovec R h) (baseVec R h) v.2.1 v.2.2) (basePoly R h c c') = 1 := by
  simp only [basePoly, minorProd, map_prod, map_mul, map_pow]
  refine Finset.prod_eq_one fun t _ => ?_
  rw [Finset.prod_eq_one, Finset.prod_eq_one, mul_one]
  · intro i _
    rw [yMinor, RingHom.map_det]
    refine (congrArg (fun A => det A ^ c' t i) (?_ : _ = (1 : Matrix _ _ R))).trans (by simp)
    ext a b
    simp [eval_yForm, baseVec, Pi.single_apply, Matrix.one_apply, eq_comm]
  · intro i _
    rw [xMinor, RingHom.map_det]
    refine (congrArg (fun A => det A ^ c t i) (?_ : _ = (1 : Matrix _ _ R))).trans (by simp)
    ext a b
    simp [eval_xForm, baseCovec, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem basePoly_ne_zero [Nontrivial R] : basePoly R h c c' ≠ 0 := fun e => by
  have := eval_basePoly (R := R) h c c'
  rw [e, map_zero] at this
  exact zero_ne_one this

theorem totalDegree_basePoly [Nontrivial R] :
    (basePoly R h c c').totalDegree = typeDegree c c' :=
  (minorProd_isHomogeneous c c' _ _).totalDegree (basePoly_ne_zero h c c')

end Base

section Subst

variable [Fintype κ] [Fintype κ']

theorem pderiv_xVar_colSubst (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (a : Fin p)
    (l : κ') (P : Poly R T p q κ) :
    pderiv (xVar t a l) (colSubst A B P) =
      ∑ k : κ, A t k l • colSubst A B (pderiv (xVar t a k) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ, smul_add, Finset.sum_add_distrib]
  | mul_X P v hP =>
    have : pderiv (xVar t a l) (colSubst A B (X v : Poly R T p q κ)) =
        ∑ k : κ, A t k l • colSubst A B (pderiv (xVar t a k) (X v : Poly R T p q κ)) := by
      obtain ⟨t', a' | b', k'⟩ := v
      · rw [colSubst_X_xVar, xForm, pderiv_rowForm]
        split_ifs with e
        · obtain ⟨rfl, e⟩ := e
          obtain rfl := Sum.inl_injective e
          rw [Finset.sum_eq_single k']
          · simp [smul_eq_C_mul]
          · intro k _ hk
            rw [pderiv_X_of_ne (by simp [hk.symm]), map_zero, smul_zero]
          · simp
        · refine (Finset.sum_eq_zero fun k _ => ?_).symm
          rw [pderiv_X_of_ne, map_zero, smul_zero]
          intro e'; simp only [Prod.mk.injEq] at e'; exact e ⟨e'.1, e'.2.1⟩
      · rw [colSubst_X_yVar, yForm, pderiv_rowForm, ite_eq_right (by simp)]
        refine (Finset.sum_eq_zero fun k _ => ?_).symm
        rw [pderiv_X_of_ne (by simp), map_zero, smul_zero]
    simp only [map_mul, pderiv_mul, map_add, hP, this, smul_add, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

theorem pderiv_yVar_colSubst (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (b : Fin q)
    (l : κ') (P : Poly R T p q κ) :
    pderiv (yVar t b l) (colSubst A B P) =
      ∑ k : κ, B t l k • colSubst A B (pderiv (yVar t b k) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ, smul_add, Finset.sum_add_distrib]
  | mul_X P v hP =>
    have : pderiv (yVar t b l) (colSubst A B (X v : Poly R T p q κ)) =
        ∑ k : κ, B t l k • colSubst A B (pderiv (yVar t b k) (X v : Poly R T p q κ)) := by
      obtain ⟨t', a' | b', k'⟩ := v
      · rw [colSubst_X_xVar, xForm, pderiv_rowForm, ite_eq_right (by simp)]
        refine (Finset.sum_eq_zero fun k _ => ?_).symm
        rw [pderiv_X_of_ne (by simp), map_zero, smul_zero]
      · rw [colSubst_X_yVar, yForm, pderiv_rowForm]
        split_ifs with e
        · obtain ⟨rfl, e⟩ := e
          obtain rfl := Sum.inr_injective e
          rw [Finset.sum_eq_single k']
          · simp [smul_eq_C_mul]
          · intro k _ hk
            rw [pderiv_X_of_ne (by simp [hk.symm]), map_zero, smul_zero]
          · simp
        · refine (Finset.sum_eq_zero fun k _ => ?_).symm
          rw [pderiv_X_of_ne, map_zero, smul_zero]
          intro e'; simp only [Prod.mk.injEq] at e'; exact e ⟨e'.1, e'.2.1⟩
    simp only [map_mul, pderiv_mul, map_add, hP, this, smul_add, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

theorem laplacian_colSubst (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (a : Fin p)
    (b : Fin q) (P : Poly R T p q κ) :
    laplacian t a b (colSubst A B P) = ∑ k : κ, ∑ k' : κ, (A t * B t) k k' •
      colSubst A B (pderiv (xVar t a k) (pderiv (yVar t b k') P)) := by
  simp only [laplacian_apply, pderiv_yVar_colSubst, map_sum, Derivation.map_smul,
    pderiv_xVar_colSubst, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

theorem laplacian_colSubst_of_mul_eq_one [DecidableEq κ] (A : T → Matrix κ κ' R)
    (B : T → Matrix κ' κ R) {t : T} (h : A t * B t = 1) (a : Fin p) (b : Fin q)
    (P : Poly R T p q κ) :
    laplacian t a b (colSubst A B P) = colSubst A B (laplacian t a b P) := by
  rw [laplacian_colSubst, h, laplacian_apply, map_sum]
  simp [Matrix.one_apply]

theorem IsHarmonic.colSubst [DecidableEq κ] {A : T → Matrix κ κ' R} {B : T → Matrix κ' κ R}
    (h : ∀ t, A t * B t = 1) {P : Poly R T p q κ} (hP : IsHarmonic P) :
    IsHarmonic (colSubst A B P) := fun t a b => by
  rw [laplacian_colSubst_of_mul_eq_one A B (h t), hP, map_zero]

end Subst

section Action

variable [Fintype κ] [DecidableEq κ]

theorem laplacian_colAct (g : T → GL κ R) (t : T) (a : Fin p) (b : Fin q) (P : Poly R T p q κ) :
    laplacian t a b (colAct R T p q κ g P) = colAct R T p q κ g (laplacian t a b P) :=
  laplacian_colSubst_of_mul_eq_one _ _ (Units.inv_mul (g t)) a b P

theorem IsHarmonic.colAct (g : T → GL κ R) {P : Poly R T p q κ} (hP : IsHarmonic P) :
    IsHarmonic (colAct R T p q κ g P) := fun t a b => by
  rw [laplacian_colAct, hP, map_zero]

variable (R T p q κ) in

noncomputable def harmonicSubrep : Subrepresentation (colRep R T p q κ) where
  toSubmodule := harmonicSubmodule R T p q κ
  apply_mem_toSubmodule g _ hP := IsHarmonic.colAct g hP

end Action

section RowHighestAction

variable [Fintype κ]

omit [Fintype κ] in
theorem rowAdd_colSubst [Fintype κ'] (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T)
    {r r' : Fin p ⊕ Fin q} (h : r.isLeft = r'.isLeft) (s : R) (P : Poly R T p q κ) :
    rowAdd t r r' s (colSubst A B P) = colSubst A B (rowAdd t r r' s P) := by
  refine DFunLike.congr_fun (?_ : (rowAdd t r r' s).comp (colSubst A B) =
    (colSubst A B).comp (rowAdd t r r' s)) P
  refine MvPolynomial.algHom_ext fun ⟨t', r'', k⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  by_cases e : t' = t ∧ r'' = r'
  · obtain ⟨rfl, rfl⟩ := e
    rw [rowAdd_X_self, map_add, map_mul, algHom_C, algebraMap_eq]
    rcases r with a | a <;> rcases r'' with b | b
    · rw [colSubst_X_xVar, colSubst_X_xVar]; exact rowAdd_rowForm_self _ _ _ _ _
    · simp at h
    · simp at h
    · rw [colSubst_X_yVar, colSubst_X_yVar]; exact rowAdd_rowForm_self _ _ _ _ _
  · rw [rowAdd_X_of_ne _ _ _ e]
    rcases r'' with b | b
    · rw [colSubst_X_xVar]; exact rowAdd_rowForm_of_ne _ _ _ e
    · rw [colSubst_X_yVar]; exact rowAdd_rowForm_of_ne _ _ _ e

variable {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {P : Poly R T p q κ}

theorem colSubst_mem_rowHighest [Fintype κ'] [DecidableEq κ] {A : T → Matrix κ κ' R}
    {B : T → Matrix κ' κ R} (h : ∀ t, A t * B t = 1) (hP : P ∈ rowHighest R c c') :
    colSubst A B P ∈ rowHighest R c c' := by
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  exact mem_rowHighest_iff_rowAdd.2 ⟨h₁.colSubst h,
    fun t r => colSubst_isWeightedHomogeneous _ A B (h₂ t r),
    fun t r r' hr s => by rw [rowAdd_colSubst A B t hr.isLeft_eq, h₃ t r r' hr]⟩

theorem colAct_mem_rowHighest [DecidableEq κ] (g : T → GL κ R) (hP : P ∈ rowHighest R c c') :
    colAct R T p q κ g P ∈ rowHighest R c c' :=
  colSubst_mem_rowHighest (fun t => Units.inv_mul (g t)) hP

theorem colAct_mem_rowHighest_iff [DecidableEq κ] (g : T → GL κ R) :
    colAct R T p q κ g P ∈ rowHighest R c c' ↔ P ∈ rowHighest R c c' := by
  refine ⟨fun h => ?_, colAct_mem_rowHighest g⟩
  have := colAct_mem_rowHighest g⁻¹ h
  rwa [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply] at this

variable (R κ c c') in

noncomputable def rowHighestSubrep [DecidableEq κ] : Subrepresentation (colRep R T p q κ) where
  toSubmodule := rowHighest R c c'
  apply_mem_toSubmodule g _ hP := colAct_mem_rowHighest g hP

theorem map_mem_rowHighest (f : R →+* S) (hP : P ∈ rowHighest R c c') :
    MvPolynomial.map f P ∈ rowHighest S c c' := by
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  refine mem_rowHighest_iff_rowAdd.2 ⟨h₁.map f, fun t r m hm => h₂ t r fun e => hm ?_,
    fun t r r' hr s => by rw [← map_intCast f, ← map_rowAdd, h₃ t r r' hr]⟩
  rw [coeff_map, e, map_zero]

theorem map_mem_rowHighest_iff {f : R →+* S} (hf : Function.Injective f) :
    MvPolynomial.map f P ∈ rowHighest S c c' ↔ P ∈ rowHighest R c c' := by
  refine ⟨fun hP => ?_, map_mem_rowHighest f⟩
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  refine mem_rowHighest_iff_rowAdd.2 ⟨(isHarmonic_map_iff hf).1 h₁,
    fun t r m hm => h₂ t r fun e => hm (hf ?_),
    fun t r r' hr s => map_injective f hf (by rw [map_rowAdd, map_intCast, h₃ t r r' hr])⟩
  rw [← coeff_map, e, map_zero]

end RowHighestAction

section Base

variable [Fintype T] (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)

theorem basePoly_mem_rowHighest : basePoly R h c c' ∈ rowHighest R c c' :=
  minorProd_mem_rowHighest c c' (isPerp_base R T h)

theorem orbitSpan_le_rowHighest : orbitSpan R h c c' ≤ rowHighest R c c' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  exact colAct_mem_rowHighest g (basePoly_mem_rowHighest h c c')

include h in

theorem rowHighest_ne_bot [Nontrivial R] :
    (rowHighest R c c' : Submodule R (Poly R T p q (Fin n))) ≠ ⊥ := fun e =>
  basePoly_ne_zero h c c' (by simpa [e] using basePoly_mem_rowHighest (R := R) h c c')

end Base

end RHLean.Geometry.NativeTheta.Paired

end
