import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import RHLean.Geometry.NativeThetaInvariantDerivatives

/-!
# Integral divided-power jets in the native theta polynomial coordinates

The mixed Hasse jet of a monomial is the product of its one-variable
Taylor coefficients. The existing coefficient contraction extends these
values to every native polynomial. Ordering a finite family by total
exponent makes its translated jet matrix block triangular with identity
diagonal blocks. Thus its adjugate recovers each original coefficient
over the coefficient ring, including in positive residue characteristic.

The column formula uses the same exponents as the native short-value
operator. At the identity of the native formal group the integral group
translation recovers the coefficients of the supplied formal germ. An
ordinary invariant derivative on a gauged germ requires its own normalization.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeTheta.IntegralJets

open MvPolynomial

variable {σ R : Type} [Fintype σ] [CommRing R]

/-- The mixed Taylor coefficient of a basis monomial about the given center. -/
def mixedTaylorWeight (z : σ → R) (k m : σ →₀ ℕ) : R :=
  ∏ i, (Polynomial.taylor (z i) (Polynomial.monomial (m i) (1 : R))).coeff (k i)

/-- Binomial coefficients retain the full multiplicity in each coordinate. -/
theorem mixedTaylorWeight_eq_binomial (z : σ → R) (k m : σ →₀ ℕ) :
    mixedTaylorWeight z k m = ∏ i, (((m i).choose (k i) : ℕ) : R) * z i ^ (m i - k i) := by
  simp only [mixedTaylorWeight, Polynomial.taylor_coeff, Polynomial.hasseDeriv_monomial,
    mul_one, Polynomial.eval_monomial]

/-- Repeated ordinary coordinate derivatives carry exactly these factorials. -/
theorem unscaledWeight_eq_factorial_mul (z : σ → R) (k m : σ →₀ ℕ) :
    (∏ i, ((Polynomial.derivative^[k i]) (Polynomial.monomial (m i) (1 : R))).eval (z i)) =
      (∏ i, ((k i).factorial : R)) * mixedTaylorWeight z k m := by
  unfold mixedTaylorWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  let p := Polynomial.monomial (m i) (1 : R)
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := R) (k i)) p
  change (k i).factorial • (Polynomial.hasseDeriv (k i) p) = Polynomial.derivative^[k i] p at h
  change (Polynomial.derivative^[k i] p).eval (z i) =
    ((k i).factorial : R) * (Polynomial.taylor (z i) p).coeff (k i)
  rw [← h, Polynomial.taylor_coeff]
  change (Polynomial.evalRingHom (z i)) ((k i).factorial • Polynomial.hasseDeriv (k i) p) = _
  rw [map_nsmul, nsmul_eq_mul]

/-- Integral linear measurement of the original polynomial coefficients. -/
def dividedJet (z : σ → R) (k : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] R :=
  JetEvaluation.coefficientContraction (mixedTaylorWeight z k)

theorem dividedJet_monomial (z : σ → R) (k m : σ →₀ ℕ) (c : R) :
    dividedJet z k (monomial m c) = c * mixedTaylorWeight z k m := by
  simpa only [dividedJet, Algebra.algebraMap_self, RingHom.id_apply] using
    (JetEvaluation.coefficientContraction_monomial (mixedTaylorWeight z k) m c)

private theorem weight_self (z : σ → R) (m : σ →₀ ℕ) : mixedTaylorWeight z m m = 1 := by
  simp [mixedTaylorWeight_eq_binomial]

private theorem weight_zero (z : σ → R) {k m : σ →₀ ℕ} (h : ∃ i, m i < k i) :
    mixedTaylorWeight z k m = 0 := by
  obtain ⟨i, hi⟩ := h
  rw [mixedTaylorWeight_eq_binomial]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Nat.choose_eq_zero_of_lt hi, Nat.cast_zero, zero_mul])

private theorem missing_coordinate {k m : σ →₀ ℕ} (hne : m ≠ k)
    (hdegree : (∑ i, m i) ≤ ∑ i, k i) : ∃ i, m i < k i := by
  classical
  by_contra! hall
  have hnot : ¬ ∀ i, k i = m i := fun h => hne (Finsupp.ext fun i => (h i).symm)
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hlt : (∑ j, k j) < ∑ j, m j :=
    Finset.sum_lt_sum (fun j _ => hall j) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hall i) hi⟩
  exact hlt.not_ge hdegree

/-- At the top total order, an integral translated jet reads the actual
monomial coefficient, for every center. Greater orders give zero. -/
theorem dividedJet_eq_coeff_of_totalDegree_le (z : σ → R) (k : σ →₀ ℕ)
    (P : MvPolynomial σ R) (hdeg : P.totalDegree ≤ ∑ i, k i) :
    dividedJet z k P = P.coeff k := by
  classical
  rw [dividedJet, JetEvaluation.coefficientContraction_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  calc
    _ = ∑ m ∈ P.support, if m = k then P.coeff k else 0 := by
      refine Finset.sum_congr rfl fun m hm => ?_
      by_cases h : m = k
      · subst m
        rw [weight_self, mul_one, if_pos rfl]
      · have hmdeg := le_totalDegree hm
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hmdeg
        rw [if_neg h, weight_zero z (missing_coordinate h (hmdeg.trans hdeg)), mul_zero]
    _ = _ := by
      rw [Finset.sum_ite_eq']
      by_cases hk : k ∈ P.support
      · rw [if_pos hk]
      · rw [if_neg hk, notMem_support_iff.mp hk]

section Family

variable {I : Type}

/-- Rows are jet orders and columns are monomial exponents. -/
def jetMatrix (z : σ → R) (a : I → σ →₀ ℕ) : Matrix I I R :=
  Matrix.of fun i j => mixedTaylorWeight z (a i) (a j)

variable [Fintype I]

/-- Every finite injectively indexed monomial family has integral unit
jet determinant at every center. Equal-total-degree blocks are identities. -/
theorem jetMatrix_det [DecidableEq I] (z : σ → R) (a : I → σ →₀ ℕ) (ha : Function.Injective a) :
    (jetMatrix z a).det = 1 := by
  classical
  let grade (i : I) := ∑ v, a i v
  let M := jetMatrix z a
  have ht : M.BlockTriangular grade := by
    intro i j hij
    have hne : a j ≠ a i := fun h => hij.ne (congrArg (fun m : σ →₀ ℕ => ∑ v, m v) h)
    exact weight_zero z (missing_coordinate hne hij.le)
  have hb (d : ℕ) : M.toSquareBlock grade d = 1 := by
    ext i j
    change mixedTaylorWeight z (a i.val) (a j.val) = (1 : Matrix _ _ R) i j
    rw [Matrix.one_apply]
    by_cases h : i = j
    · subst j
      rw [if_pos rfl, weight_self]
    · have hne : a j.val ≠ a i.val := fun he => h (Subtype.ext (ha he).symm)
      have hle : grade j.val ≤ grade i.val := (j.property.trans i.property.symm).le
      exact (weight_zero z (missing_coordinate hne hle)).trans (if_neg h).symm
  change M.det = 1
  rw [ht.det]
  exact Finset.prod_eq_one fun d _ => by rw [hb d, Matrix.det_one]

theorem jetMatrix_mulVec (z : σ → R) (a : I → σ →₀ ℕ) (v : I → R) :
    (jetMatrix z a).mulVec v =
      fun i => dividedJet z (a i) (∑ j, monomial (a j) (v j)) := by
  funext i
  change (∑ j, mixedTaylorWeight z (a i) (a j) * v j) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [dividedJet_monomial, mul_comm]

/-- The integral adjugate is a single decoder for every coefficient vector
on this family. No factorial inverse enters its construction. -/
theorem recover_monomial_family [DecidableEq I] (z : σ → R) (a : I → σ →₀ ℕ)
    (ha : Function.Injective a) (v : I → R) :
    (jetMatrix z a).adjugate.mulVec
      (fun i => dividedJet z (a i) (∑ j, monomial (a j) (v j))) = v := by
  rw [← jetMatrix_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    jetMatrix_det z a ha, one_smul, Matrix.one_mulVec]

end Family

section FormalGerms

open FormalCalculus

/-- At the origin the divided-power measurement of a polynomial reads its
coefficient at every order over the integral ring. -/
theorem dividedJet_at_origin (k : σ →₀ ℕ) (P : MvPolynomial σ R) :
    dividedJet (0 : σ → R) k P = P.coeff k := by
  classical
  rw [dividedJet, JetEvaluation.coefficientContraction_apply, Finset.sum_eq_single k]
  · simp only [Algebra.algebraMap_self, RingHom.id_apply, weight_self, mul_one]
  · intro m _ hmk
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ k i := by
      by_contra! h
      exact hmk (Finsupp.ext h)
    have hz : mixedTaylorWeight (0 : σ → R) k m = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      change (Polynomial.taylor 0 (Polynomial.monomial (m i) (1 : R))).coeff (k i) = 0
      rw [Polynomial.taylor_zero, Polynomial.coeff_monomial, if_neg hi]
    rw [hz, mul_zero]
  · intro hk
    rw [notMem_support_iff.mp hk, map_zero, zero_mul]

/-- Read a pure-coordinate coefficient after pulling an actual formal germ back
along the native formal group law. The identity section removes the second
set of variables and keeps every exponent in the first set. -/
theorem formalGroupHasse_origin {d : ℕ} (G : FormalGroup R d) (f : PS R 1 d)
    (k : Fin 1 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff (k.embDomain (eXv d)) (ev (n := 2) ![G.F] f) =
      MvPowerSeries.coeff k f := by
  rw [← coeff_ev_zero_right, ezF]

/-- On an integral polynomial germ the coefficient of the genuine native
formal-group pullback agrees with the polynomial divided-power measurement. -/
theorem formalGroupHasse_polynomial_origin {d : ℕ} (G : FormalGroup R d)
    (P : MvPolynomial (Fin 1 × Fin d) R) (k : Fin 1 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff (k.embDomain (eXv d)) (ev (n := 2) ![G.F] (P : PS R 1 d)) =
      dividedJet (0 : Fin 1 × Fin d → R) k P := by
  rw [formalGroupHasse_origin, MvPolynomial.coeff_coe, dividedJet_at_origin]

/-- A single collection of coefficients of the native group pullback decodes all
vectors in the span of distinct integral formal monomial germs. -/
theorem formalGroupHasse_recovers_family {d : ℕ} {I : Type} [Fintype I]
    (G : FormalGroup R d) (a : I → Fin 1 × Fin d →₀ ℕ) (ha : Function.Injective a)
    (v : I → R) (i : I) :
    MvPowerSeries.coeff ((a i).embDomain (eXv d))
        (ev (n := 2) ![G.F] (∑ j, MvPowerSeries.monomial (a j) (v j))) = v i := by
  classical
  rw [formalGroupHasse_origin, map_sum, Finset.sum_eq_single i]
  · exact MvPowerSeries.coeff_monomial_same _ _
  · intro j _ hji
    exact MvPowerSeries.coeff_monomial_ne (fun h => hji (ha h).symm) _
  · simp

end FormalGerms

section Columns

variable {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ}

/-- The native column exponents partition every variable of a monomial,
including repeated powers at one letter. -/
theorem mixedTaylorWeight_columns (z : Letter T r n → R) (k m : Letter T r n →₀ ℕ) :
    mixedTaylorWeight z k m = ∏ b : Fin n,
      mixedTaylorWeight (fun l : JetEvaluation.Row T r => z ⟨l.1, l.2, b⟩)
        (JetEvaluation.columnExponent k b) (JetEvaluation.columnExponent m b) := by
  classical
  let e : Letter T r n ≃ Fin n × JetEvaluation.Row T r :=
    { toFun := fun l => (l.2.2, ⟨l.1, l.2.1⟩)
      invFun := fun u => ⟨u.2.1, u.2.2, u.1⟩
      left_inv := fun l => by rcases l with ⟨t, a, b⟩; rfl
      right_inv := fun u => by rcases u with ⟨b, t, a⟩; rfl }
  let f (u : Fin n × JetEvaluation.Row T r) :=
    (Polynomial.taylor (z ⟨u.2.1, u.2.2, u.1⟩)
      (Polynomial.monomial ((JetEvaluation.columnExponent m u.1) u.2) (1 : R))).coeff
        ((JetEvaluation.columnExponent k u.1) u.2)
  calc
    _ = ∏ u, f u := Fintype.prod_equiv e _ _ fun _ => rfl
    _ = _ := Fintype.prod_prod_type f

/-- The divided-power test contracts through exactly the column index
partition used by the native finite short-value formula. -/
theorem dividedJet_eq_column_sum (z : Letter T r n → R) (k : Letter T r n →₀ ℕ)
    (P : MvPolynomial (Letter T r n) R) :
    dividedJet z k P = ∑ m ∈ P.support, P.coeff m * ∏ b : Fin n,
      mixedTaylorWeight (fun l : JetEvaluation.Row T r => z ⟨l.1, l.2, b⟩)
        (JetEvaluation.columnExponent k b) (JetEvaluation.columnExponent m b) := by
  rw [dividedJet, JetEvaluation.coefficientContraction_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, mixedTaylorWeight_columns z k]

end Columns

end RHLean.Geometry.NativeTheta.IntegralJets

end
