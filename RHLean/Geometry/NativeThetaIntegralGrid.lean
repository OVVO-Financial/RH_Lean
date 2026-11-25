import RHLean.Geometry.NativeThetaGridParametrization
import RHLean.Geometry.NativeThetaIntegralJets

/-!
# Integral evaluations on the native theta grid

Factorial-scaled cardinal polynomials recover the scalar coefficients from the
integer box over a characteristic-zero domain. In a discrete valuation ring
a unit coefficient gives an explicit valuation bound at a grid point. The
same calculation applies to integral linear measurements of the native
determinant-adjugate family in its original parameter coordinates.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace RHLean.Geometry.NativeTheta.GridInterpolation

open MvPolynomial

variable {σ R : Type*} [CommRing R]

private def gridFalling (T : MvPolynomial σ R) (k : ℕ) : MvPolynomial σ R :=
  ∏ j ∈ Finset.range k, (T - C (j : R))

private theorem eval_gridFalling (x : σ → R) (T : MvPolynomial σ R) (n k : ℕ)
    (h : eval x T = (n : R)) : eval x (gridFalling T k) = (n.descFactorial k : R) := by
  rw [← descPochhammer_eval_eq_descFactorial R n k, descPochhammer_eval_eq_prod_range]
  simp [gridFalling, h]

private theorem degreeOf_gridFalling (w : σ) (T : MvPolynomial σ R) (k : ℕ) :
    (gridFalling T k).degreeOf w ≤ k * T.degreeOf w := by
  classical
  refine (degreeOf_prod_le w (Finset.range k) _).trans ?_
  calc
    _ ≤ ∑ _j ∈ Finset.range k, T.degreeOf w := by
      exact Finset.sum_le_sum fun j _ => (degreeOf_sub_le w T (C (j : R))).trans (by simp)
    _ = _ := by simp [nsmul_eq_mul]

/-- The integral cardinal polynomial for node `j`. Its value there is `d!`. -/
private def gridWeight (i : σ) (d j : ℕ) : MvPolynomial σ R :=
  C (d.choose j : R) * gridFalling (X i) j * gridFalling (C (d : R) - X i) (d - j)

private theorem eval_gridWeight (x : σ → ℕ) (i : σ) (d j : ℕ) (hx : x i ≤ d) (hj : j ≤ d) :
    eval (fun k => (x k : R)) (gridWeight i d j) = if x i = j then (d.factorial : R) else 0 := by
  have hleft : eval (fun k => (x k : R)) (X i) = (x i : R) := eval_X i
  have hright : eval (fun k => (x k : R)) (C (d : R) - X i) = ((d - x i : ℕ) : R) := by
    simp [Nat.cast_sub hx]
  rw [gridWeight, map_mul, map_mul, eval_C, eval_gridFalling _ _ _ _ hleft,
    eval_gridFalling _ _ _ _ hright]
  by_cases he : x i = j
  · rw [ite_eq_left he, he, Nat.descFactorial_self, Nat.descFactorial_self, ← Nat.cast_mul,
      ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial hj]
  · rw [ite_eq_right he]
    rcases lt_or_gt_of_ne he with h | h
    · simp [Nat.descFactorial_eq_zero_iff_lt.mpr h]
    · have hsub : d - x i < d - j := by omega
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr hsub]

private theorem degreeOf_gridWeight [Nontrivial R] [DecidableEq σ] (w i : σ) (d j : ℕ)
    (hj : j ≤ d) : (gridWeight i d j : MvPolynomial σ R).degreeOf w ≤ if w = i then d else 0 := by
  have hright : (C (d : R) - X i : MvPolynomial σ R).degreeOf w ≤ if w = i then 1 else 0 :=
    (degreeOf_sub_le w _ _).trans (by simp [degreeOf_X])
  calc
    _ ≤ j * (X i : MvPolynomial σ R).degreeOf w +
        (d - j) * (C (d : R) - X i : MvPolynomial σ R).degreeOf w :=
      (degreeOf_mul_le w _ _).trans (add_le_add
        ((degreeOf_C_mul_le _ _ _).trans (degreeOf_gridFalling _ _ _))
        (degreeOf_gridFalling _ _ _))
    _ ≤ j * (if w = i then 1 else 0) + (d - j) * (if w = i then 1 else 0) := by
      rw [degreeOf_X]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hright) _
    _ = _ := by
      by_cases h : w = i
      · simp only [ite_eq_left h, Nat.mul_one]
        omega
      · simp only [ite_eq_right h, Nat.mul_zero, Nat.add_zero]

variable [Fintype σ]

private def gridKernel (d : σ → ℕ) (a : (i : σ) → Fin (d i + 1)) : MvPolynomial σ R :=
  ∏ i, gridWeight i (d i) (a i)

private theorem degreeOf_gridKernel [Nontrivial R] (w : σ) (d : σ → ℕ)
    (a : (i : σ) → Fin (d i + 1)) : (gridKernel d a : MvPolynomial σ R).degreeOf w ≤ d w := by
  classical
  refine (degreeOf_prod_le w Finset.univ _).trans ?_
  calc
    _ ≤ ∑ i, (if w = i then d i else 0) :=
      Finset.sum_le_sum fun i _ => degreeOf_gridWeight w i (d i) (a i) (Nat.le_of_lt_succ (a i).isLt)
    _ = _ := by simp

private theorem eval_gridKernel [DecidableEq σ] (d : σ → ℕ) (x a : (i : σ) → Fin (d i + 1)) :
    eval (fun i => ((x i : ℕ) : R)) (gridKernel d a) =
      if x = a then ∏ i, ((d i).factorial : R) else 0 := by
  classical
  rw [gridKernel, map_prod]
  have hw (i : σ) := eval_gridWeight (R := R) (fun k => (x k : ℕ)) i (d i) (a i)
    (Nat.le_of_lt_succ (x i).isLt) (Nat.le_of_lt_succ (a i).isLt)
  by_cases h : x = a
  · subst a
    rw [ite_eq_left rfl]
    exact Finset.prod_congr rfl fun i _ => (hw i).trans (ite_eq_left rfl)
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
      by_contra! hall
      exact h (funext hall)
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((hw i).trans (ite_eq_right fun he => hi (Fin.ext he)))

variable [IsDomain R] [CharZero R]

/-- Every coefficient multiplied by the product of the coordinate factorials belongs to
any ideal containing all evaluations on the full integral box. -/
theorem factorial_mul_coeff_mem_of_grid_eval_mem (d : σ → ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d i) (I : Ideal R)
    (hI : ∀ x : (i : σ) → Fin (d i + 1), eval (fun i => ((x i : ℕ) : R)) P ∈ I)
    (m : σ →₀ ℕ) : (∏ i, ((d i).factorial : R)) * P.coeff m ∈ I := by
  classical
  let D : R := ∏ i, ((d i).factorial : R)
  let V (a : (i : σ) → Fin (d i + 1)) : R := eval (fun i => ((a i : ℕ) : R)) P
  let S : MvPolynomial σ R := ∑ a, C (V a) * gridKernel d a
  have hS (i : σ) : S.degreeOf i ≤ d i := by
    refine (degreeOf_sum_le i Finset.univ _).trans (Finset.sup_le fun a _ => ?_)
    exact (degreeOf_C_mul_le _ _ _).trans (degreeOf_gridKernel i d a)
  have hpoly : C D * P - S = 0 := by
    apply eq_zero_of_eval_box_eq_zero d
    · intro i
      exact (degreeOf_sub_le i _ _).trans (max_le ((degreeOf_C_mul_le _ _ _).trans (hdeg i)) (hS i))
    · intro x hx
      let b : (i : σ) → Fin (d i + 1) := fun i => ⟨x i, Nat.lt_succ_of_le (hx i)⟩
      have hev (a : (i : σ) → Fin (d i + 1)) :
          eval (fun i => (x i : R)) (gridKernel d a) = if b = a then D else 0 :=
        eval_gridKernel d b a
      simp only [S, map_sub, map_mul, eval_C, map_sum, hev]
      rw [Finset.sum_eq_single b]
      · rw [ite_eq_left rfl]
        change D * eval (fun i => (x i : R)) P - eval (fun i => (x i : R)) P * D = 0
        rw [mul_comm D, sub_self]
      · intro a _ hab
        simp [Ne.symm hab]
      · simp
  have hcoeff := congrArg (fun F : MvPolynomial σ R => F.coeff m) (sub_eq_zero.mp hpoly)
  change (C D * P).coeff m = (∑ a, C (V a) * gridKernel d a).coeff m at hcoeff
  rw [coeff_C_mul, coeff_sum] at hcoeff
  change D * P.coeff m ∈ I
  rw [hcoeff]
  exact I.sum_mem fun a _ => by
    rw [coeff_C_mul, mul_comm]
    exact I.mul_mem_left _ (hI a)

/-- A unit coefficient forces some integral grid value to divide the factorial budget in a
characteristic-zero DVR. Both quantities use the same normalized valuation. -/
theorem exists_grid_eval_addVal_le_factorial [IsDiscreteValuationRing R] (d : σ → ℕ)
    (P : MvPolynomial σ R) (hdeg : ∀ i, P.degreeOf i ≤ d i) (m : σ →₀ ℕ)
    (hm : IsUnit (P.coeff m)) :
    ∃ x : (i : σ) → Fin (d i + 1), IsDiscreteValuationRing.addVal R
      (eval (fun i => ((x i : ℕ) : R)) P) ≤
        IsDiscreteValuationRing.addVal R (∏ i, ((d i).factorial : R)) := by
  classical
  let V (a : (i : σ) → Fin (d i + 1)) : R := eval (fun i => ((a i : ℕ) : R)) P
  have hn : (Finset.univ : Finset ((i : σ) → Fin (d i + 1))).Nonempty :=
    ⟨fun _ => 0, Finset.mem_univ _⟩
  obtain ⟨q, _, hq⟩ := Finset.exists_min_image Finset.univ (fun a => IsDiscreteValuationRing.addVal R (V a)) hn
  let I : Ideal R := Ideal.span {V q}
  have hI (a : (i : σ) → Fin (d i + 1)) : V a ∈ I :=
    Ideal.mem_span_singleton.mpr (IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hq a (Finset.mem_univ a)))
  have hmem := factorial_mul_coeff_mem_of_grid_eval_mem d P hdeg I hI m
  obtain ⟨u, hu⟩ := hm
  rw [← hu, mul_comm] at hmem
  have hc := I.mul_mem_left (↑u⁻¹ : R) hmem
  rw [← mul_assoc, Units.inv_mul, one_mul] at hc
  exact ⟨q, IsDiscreteValuationRing.addVal_le_iff_dvd.mpr (Ideal.mem_span_singleton.mp hc)⟩

end RHLean.Geometry.NativeTheta.GridInterpolation

namespace RHLean.Geometry.NativeTheta.Paired

open MvPolynomial

variable {R : Type} [CommRing R] {T : Type*} [Fintype T] {ι : Type} [Fintype ι]
  {p q n : ℕ}

/-- The native determinant-adjugate family as a polynomial in its integral parameters. -/
def coordProdParameterPolynomial (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → R) :
    MvPolynomial ((Fin p ⊕ Fin p ⊕ Fin q) × ι) (Poly R T p q (Fin n)) :=
  swapVars (coordProd c c' (fun t i k => C (w t i k)) (fun t i k => C (w' t i k)) X)

private theorem coordProdParameterPolynomial_degree (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → R) :
    (coordProdParameterPolynomial c c' w w').totalDegree ≤ (2 * p + 1) * typeDegree c c' := by
  have hlin (r : Fin p ⊕ Fin p ⊕ Fin q) (u : ι → R) :
      (∑ i, X (r, i) * C (u i) : MvPolynomial _ R).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X R (r, i)).mul (isHomogeneous_C _ (u i))
  have hF : (coordProdParameterPolynomial c c' w w').IsHomogeneous _ :=
    swapVars_minorProd_isHomogeneous c c' _ _ (d := 1) (d' := 2 * p + 1)
      (fun t a k => hlin _ _) fun t b k =>
        perpVec_dotPairing_isHomogeneous _ _ _ (fun a k => hlin _ _) (fun a k => hlin _ _)
          (fun k => hlin _ _) k
  refine hF.totalDegree_le.trans ?_
  rw [typeDegree, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [mul_add]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _

private theorem eval_coordProdParameterPolynomial (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → R) (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → R) :
    eval (fun j => C (x j)) (coordProdParameterPolynomial c c' w w') = coordProd c c' w w' x := by
  rw [coordProdParameterPolynomial, eval_swapVars, map_coordProd]
  simp only [eval_C, eval_X]

/-- An integral linear measurement of the actual minor family is detected at some
point of its integer parameter box whenever it has a unit parameter coefficient. -/
theorem exists_coordProd_grid_addVal_le_factorial [IsDomain R] [CharZero R] [IsDiscreteValuationRing R]
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (w w' : T → ι → Fin n → R)
    (l : Poly R T p q (Fin n) →ₗ[R] R) (m : ((Fin p ⊕ Fin p ⊕ Fin q) × ι) →₀ ℕ)
    (hm : IsUnit (l ((coordProdParameterPolynomial c c' w w').coeff m))) :
    let dg := (2 * p + 1) * typeDegree c c'
    ∃ x : ((Fin p ⊕ Fin p ⊕ Fin q) × ι) → Fin (dg + 1),
      IsDiscreteValuationRing.addVal R (l (coordProd c c' w w' fun i => ((x i : ℕ) : R))) ≤
        IsDiscreteValuationRing.addVal R (∏ _i : (Fin p ⊕ Fin p ⊕ Fin q) × ι, (dg.factorial : R)) := by
  classical
  let dg := (2 * p + 1) * typeDegree c c'
  let F := coordProdParameterPolynomial c c' w w'
  let P : MvPolynomial ((Fin p ⊕ Fin p ⊕ Fin q) × ι) R :=
    ∑ s ∈ F.support, monomial s (l (F.coeff s))
  have hcoeff (s : ((Fin p ⊕ Fin p ⊕ Fin q) × ι) →₀ ℕ) : P.coeff s = l (F.coeff s) := by
    simp only [P, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    by_cases hs : s ∈ F.support
    · rw [ite_eq_left hs]
    · rw [ite_eq_right hs, notMem_support_iff.mp hs, map_zero]
  have hdeg (i : (Fin p ⊕ Fin p ⊕ Fin q) × ι) : P.degreeOf i ≤ dg := by
    apply degreeOf_le_iff.mpr
    intro s hs
    have hmem : s ∈ F.support := by
      by_contra hn
      exact mem_support_iff.mp hs (by rw [hcoeff, notMem_support_iff.mp hn, map_zero])
    exact (monomial_le_degreeOf i hmem).trans ((degreeOf_le_totalDegree F i).trans
      (coordProdParameterPolynomial_degree c c' w w'))
  have hprim : IsUnit (P.coeff m) := (hcoeff m).symm ▸ hm
  obtain ⟨x, hx⟩ := GridInterpolation.exists_grid_eval_addVal_le_factorial
    (fun _ => dg) P hdeg m hprim
  refine ⟨x, ?_⟩
  let b (i : (Fin p ⊕ Fin p ⊕ Fin q) × ι) := ((x i : ℕ) : R)
  have hv : eval b P = l (coordProd c c' w w' b) := by
    rw [← eval_coordProdParameterPolynomial c c' w w' b]
    change eval b P = l (eval (fun j => C (b j)) F)
    rw [MvPolynomial.eval_eq (fun j => C (b j)) F]
    simp only [P, map_sum, eval_monomial]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hprod : (∏ i ∈ s.support, C (b i) ^ s i : Poly R T p q (Fin n)) =
        C (s.prod fun i t => b i ^ t) := by simp [Finsupp.prod]
    rw [hprod, mul_comm (F.coeff s), ← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
  change IsDiscreteValuationRing.addVal R (eval b P) ≤ _ at hx
  rwa [hv] at hx

end RHLean.Geometry.NativeTheta.Paired


namespace RHLean.Geometry.NativeTheta

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n)

/-- The zero-one matrix selecting the given columns in every row block. -/
def minorGridPoint (R : Type) [Zero R] [One R] (ℓ : Letter T r n) : R :=
  if ℓ.2.2 = col ℓ.1 ℓ.2.1 then 1 else 0

/-- Every leading minor at its own integral grid point is an identity determinant. -/
theorem minorMonomial_eval_gridPoint (R : Type) [CommRing R]
    (hcol : ∀ σ, Function.Injective (col σ)) (a : T → ℕ → ℕ) :
    MvPolynomial.eval (minorGridPoint r n col R) (minorsP r n col R a) = 1 := by
  classical
  simp only [minorsP, map_prod, map_pow, minor, RingHom.map_det]
  refine Finset.prod_eq_one fun σ _ => Finset.prod_eq_one fun s _ => ?_
  rw [show (MvPolynomial.eval _).mapMatrix _ = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) R) from ?_,
    Matrix.det_one, one_pow]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
    minorGridPoint, Matrix.one_apply, (hcol σ).eq_iff, (Fin.castLE_injective _).eq_iff, eq_comm]

/-- A missing column in a positive-weight minor gives an entire zero row at the
other grid point. The resulting off-diagonal evaluation vanishes over the integers. -/
theorem minorMonomial_eval_gridPoint_eq_zero (R : Type) [CommRing R]
    (test : ∀ τ, Fin (r τ) → Fin n) (a : T → ℕ → ℕ) (τ : T) (s : Fin (r τ))
    (u : Fin (s + 1)) (hpos : a τ (s + 1) < a τ s)
    (hmiss : ∀ v : Fin (s + 1), col τ (Fin.castLE s.isLt v) ≠ test τ (Fin.castLE s.isLt u)) :
    MvPolynomial.eval (minorGridPoint r n test R) (minorsP r n col R a) = 0 := by
  classical
  simp only [minorsP, map_prod, map_pow]
  refine Finset.prod_eq_zero (Finset.mem_univ τ) (Finset.prod_eq_zero (Finset.mem_univ s) ?_)
  have hz : MvPolynomial.eval (minorGridPoint r n test R) (minor r n col R τ s) = 0 := by
    rw [minor, RingHom.map_det]
    apply Matrix.det_eq_zero_of_row_eq_zero u
    intro v
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      minorGridPoint, ite_eq_right (hmiss v)]
  rw [hz, zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hpos))]

/-- Each zero-one evaluation reads one coefficient of a combination of separated
leading-minor products. The separation test only uses their column indices and weights. -/
theorem eval_minorCombination {ι : Type} [Fintype ι] (R : Type) [CommRing R]
    (cols : ι → ∀ τ, Fin (r τ) → Fin n) (hinj : ∀ j τ, Function.Injective (cols j τ))
    (a : T → ℕ → ℕ)
    (hsep : ∀ i j, i ≠ j → ∃ (τ : T) (s : Fin (r τ)) (u : Fin (s + 1)),
      a τ (s + 1) < a τ s ∧ ∀ v : Fin (s + 1),
        cols i τ (Fin.castLE s.isLt v) ≠ cols j τ (Fin.castLE s.isLt u))
    (c : ι → R) (j : ι) :
    MvPolynomial.eval (minorGridPoint r n (cols j) R)
      (∑ i, MvPolynomial.C (c i) * minorsP r n (cols i) R a) = c j := by
  classical
  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  rw [Finset.sum_eq_single j]
  · rw [minorMonomial_eval_gridPoint r n (cols j) R (hinj j) a, mul_one]
  · intro i _ hij
    obtain ⟨τ, s, u, hpos, hmiss⟩ := hsep i j hij
    rw [minorMonomial_eval_gridPoint_eq_zero r n (cols i) R (cols j) a τ s u hpos hmiss, mul_zero]
  · simp

/-- Keep the whole exponent in the chosen column of each row. -/
def minorDiagonalExponent (a : T → ℕ → ℕ) : Letter T r n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ =>
    if ℓ.2.2 = col ℓ.1 ℓ.2.1 then a ℓ.1 ℓ.2.1 else 0

/-- For a row-homogeneous polynomial the zero-one mask reads exactly one
coefficient, at the full diagonal exponent prescribed by those row degrees. -/
theorem eval_gridPoint_eq_diagonalCoeff (K : Type) [Field K] (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) K) (hP : RowDeg r n K a P) :
    MvPolynomial.eval (minorGridPoint r n col K) P =
      P.coeff (minorDiagonalExponent r n col a) := by
  classical
  let J := minorDiagonalExponent r n col a
  have hj (ℓ : Letter T r n) : J ℓ = if ℓ.2.2 = col ℓ.1 ℓ.2.1 then a ℓ.1 ℓ.2.1 else 0 := rfl
  have hdet (m : Letter T r n →₀ ℕ) (hm : m ∈ P.support)
      (hs : ∀ ℓ : Letter T r n, ℓ.2.2 ≠ col ℓ.1 ℓ.2.1 → m ℓ = 0) : m = J := by
    ext ⟨τ,i,b⟩
    rw [hj]
    by_cases hb : b = col τ i
    · subst b
      rw [ite_eq_left rfl]
      have hsum : (∑ k : Fin n, m ⟨τ,i,k⟩) = m ⟨τ,i,col τ i⟩ := by
        apply Finset.sum_eq_single (col τ i)
        · intro k _ hk
          exact hs ⟨τ,i,k⟩ hk
        · simp
      exact hsum.symm.trans (hP m hm τ i)
    · rw [ite_eq_right hb]
      exact hs ⟨τ,i,b⟩ hb
  change MvPolynomial.eval _ P = P.coeff J
  rw [MvPolynomial.eval_eq, Finset.sum_eq_single J]
  · have hprod : (∏ ℓ ∈ J.support, minorGridPoint r n col K ℓ ^ J ℓ) = 1 := by
      apply Finset.prod_eq_one
      intro ℓ hℓ
      have ht : ℓ.2.2 = col ℓ.1 ℓ.2.1 := by
        by_contra h
        exact (Finsupp.mem_support_iff.mp hℓ) ((hj ℓ).trans (ite_eq_right h))
      simp only [minorGridPoint, ite_eq_left ht, one_pow]
    rw [hprod, mul_one]
  · intro m hm hne
    obtain ⟨ℓ, hcol, hn⟩ : ∃ ℓ : Letter T r n, ℓ.2.2 ≠ col ℓ.1 ℓ.2.1 ∧ m ℓ ≠ 0 := by
      by_contra! h
      exact hne (hdet m hm h)
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hn)
      (show minorGridPoint r n col K ℓ ^ m ℓ = 0 from by
        simp only [minorGridPoint, ite_eq_right hcol, zero_pow hn]), mul_zero]
  · intro hn
    rw [MvPolynomial.notMem_support_iff.mp hn, zero_mul]

/-- A leading-minor symbol has coefficient exactly one at its multiplied
diagonal monomial. This identifies its top Hasse coordinate at zero. -/
theorem minorMonomial_diagonalCoeff (K : Type) [Field K]
    (hinj : ∀ τ, Function.Injective (col τ)) (a : T → ℕ → ℕ)
    (ha : ∀ τ, Antitone (a τ)) (h0 : ∀ τ, a τ (r τ) = 0) :
    (minorsP r n col K a).coeff (minorDiagonalExponent r n col a) = 1 :=
  (eval_gridPoint_eq_diagonalCoeff r n col K a _
    (minorMonomial_rowDegree r n K col a ha h0)).symm.trans
      (minorMonomial_eval_gridPoint r n col K hinj a)

/-- On the highest-weight minor product the full-order divided jet is
one at every center. All row multiplicities occur in the jet index. -/
theorem minorMonomial_dividedJet (K : Type) [Field K]
    (hinj : ∀ τ, Function.Injective (col τ)) (a : T → ℕ → ℕ)
    (ha : ∀ τ, Antitone (a τ)) (h0 : ∀ τ, a τ (r τ) = 0) (z : Letter T r n → K) :
    IntegralJets.dividedJet z (minorDiagonalExponent r n col a) (minorsP r n col K a) = 1 := by
  classical
  let J := minorDiagonalExponent r n col a
  let P := minorsP r n col K a
  have hj : P.coeff J = 1 := minorMonomial_diagonalCoeff r n col K hinj a ha h0
  have hm : P.coeff J ≠ 0 := hj.trans_ne one_ne_zero
  have hhom := isHomogeneous_of_rowDeg (minorMonomial_rowDegree r n K col a ha h0)
  have hweight : (∑ i, J i) = ∑ τ, ∑ i : Fin (r τ), a τ i := by
    have hw := hhom hm
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, smul_eq_mul] using hw
  have hdeg : P.totalDegree ≤ ∑ i, J i :=
    (hhom.totalDegree (minorMonomial_ne_zero r n K col hinj a)).le.trans_eq hweight.symm
  exact (IntegralJets.dividedJet_eq_coeff_of_totalDegree_le z J P hdeg).trans hj

end RHLean.Geometry.NativeTheta

end
