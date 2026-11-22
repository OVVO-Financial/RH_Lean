import RHLean.Geometry.NativeThetaPolynomialNorm

/-!
# Explicit integral harmonic polynomials for the native theta construction

The polynomials are products of leading minors in actual row/column variables.
Their mixed Laplacians vanish because conjugate rows use disjoint columns.
Lower-row additions preserve each minor, and the prescribed row degrees are
proved by telescoping adjacent dominant weights. Their coefficients are
integers, they are nonzero, and their coefficient norm is explicitly bounded.
No harmonicity, integrality, nonzero polynomial or short-span premise is assumed.

The coefficient field K is independent of the host E; it is specialized to
Y.d.c₂.F in the original application. This constructs the harmonic-polynomial
input of theta sections. It does not yet construct their geometric evaluation,
the canonical connection, or a spanning family of cusp sections.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Formalism/LocalToGlobal/ProjectiveLattices/RowDeg.lean;
Development/AbelianVarietyTheory/Proofs/JetHarmonics/MinorsDisjointColumnsHarmonic.lean;
Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean,
ThetaClaimsCompare.{minor,minorsP,minorMonomial_ne_zero,exists_harmA_ne_zero};
Proofs/CuspFormEvaluations/ExistsBlockProductMemIntegralHarmonic.lean,
BlockProdEx.{minorMonomial_isHomogeneous,minors_polynomial_coefficient_norm_le_pow};
and ExistsIntegralHarmonicNeZeroAndIsHomogeneous.lean, isHomogeneous_of_rowDeg.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace RHLean.Geometry.NativeTheta

open MvPolynomial

section Definitions

abbrev Letter (T : Type) (r : T → ℕ) (n : ℕ) : Type := Σ σ : T, Fin (r σ) × Fin n

variable {T : Type} (r : T → ℕ) (n : ℕ)

def letMat (R : Type) [CommRing R] (σ : T) :
    Matrix (Fin (r σ)) (Fin n) (MvPolynomial (Letter T r n) R) :=
  fun a b => X ⟨σ, a, b⟩

variable (k : Type) [Field k]

def lap (hinv : Matrix (Fin n) (Fin n) k) (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) :
    MvPolynomial (Letter T r n) k →ₗ[k] MvPolynomial (Letter T r n) k :=
  ∑ b, ∑ b', hinv b b' •
    ((pderiv (⟨τ, a, b⟩ : Letter T r n)).toLinearMap ∘ₗ
      (pderiv (⟨τ', a', b'⟩ : Letter T r n)).toLinearMap)

def harmK (cc : T → T) (isX : T → Prop) (hinv : T → Matrix (Fin n) (Fin n) k) :
    Submodule k (MvPolynomial (Letter T r n) k) :=
  ⨅ (τ : T) (_ : isX τ) (a : Fin (r τ)) (a' : Fin (r (cc τ))),
    LinearMap.ker (lap r n k (hinv τ) τ (cc τ) a a')

def rowShift (σ : T) (i i' : Fin (r σ)) (t : k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ => open Classical in
    if ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ then X ℓ + C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ

def RowInv (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ (σ : T) (i i' : Fin (r σ)), i' < i → ∀ t : k, rowShift r n k σ i i' t P = P

def RowDeg (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ m ∈ P.support, ∀ (σ : T) (i : Fin (r σ)), ∑ b : Fin n, m ⟨σ, i, b⟩ = a σ i

def HHa (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) : Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ harmK r n k cc isX (fun _ => 1) ∧ RowInv r n k P ∧ RowDeg r n k a P}

def HaO (O : Subring k) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ HHa r n k cc isX a ∧ ∀ m, P.coeff m ∈ O}


end Definitions

theorem minorHarm_pderiv_comm {σ k : Type*} [CommRing k] (i j : σ)
    (p : MvPolynomial σ k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  have h : ⁅MvPolynomial.pderiv (R := k) i, MvPolynomial.pderiv (R := k) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro n
    rw [Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
    by_cases hj : j = n <;> by_cases hi : i = n <;>
      simp [hj, hi]
  have := DFunLike.congr_fun h p
  rw [Derivation.commutator_apply] at this
  simpa [sub_eq_zero] using this

theorem minorHarm_pderiv_eq_zero {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) {v : σ} (hv : v ∉ S) :
    MvPolynomial.pderiv v p = 0 := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact MvPolynomial.pderiv_X_of_ne (fun h => hv (h ▸ hs))
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [MvPolynomial.pderiv_mul, hx, hy]; simp


section Minors

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (col : ∀ σ, Fin (r σ) → Fin n)

def minor (R : Type) [CommRing R] (σ : T) (s : Fin (r σ)) : MvPolynomial (Letter T r n) R :=
  (Matrix.of fun i j : Fin (s + 1) =>
    (X ⟨σ, Fin.castLE s.isLt i, col σ (Fin.castLE s.isLt j)⟩ : MvPolynomial (Letter T r n) R)).det

def minorsP (R : Type) [CommRing R] (a : T → ℕ → ℕ) : MvPolynomial (Letter T r n) R :=
  ∏ σ, ∏ s : Fin (r σ), minor r n col R σ s ^ (a σ s - a σ (s + 1))

theorem minorMonomial_map {R R' : Type} [CommRing R] [CommRing R']
    (φ : R →+* R') (a : T → ℕ → ℕ) :
    MvPolynomial.map φ (minorsP r n col R a) = minorsP r n col R' a := by
  simp only [minorsP, map_prod, map_pow, minor, RingHom.map_det]
  refine Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 i j
  simp

theorem minorMonomial_coeff_mem (a : T → ℕ → ℕ) (O : Subring k) (m : Letter T r n →₀ ℕ) :
    (minorsP r n col k a).coeff m ∈ O := by
  rw [← minorMonomial_map r n col (Int.castRingHom k), coeff_map]
  exact intCast_mem O _

theorem minorMonomial_ne_zero (hcol : ∀ σ, Function.Injective (col σ)) (a : T → ℕ → ℕ) :
    minorsP r n col k a ≠ 0 := by
  classical
  intro h
  have h1 : MvPolynomial.eval (fun ℓ : Letter T r n => if ℓ.2.2 = col ℓ.1 ℓ.2.1 then (1 : k) else 0)
      (minorsP r n col k a) = 1 := by
    simp only [minorsP, map_prod, map_pow, minor, RingHom.map_det]
    refine Finset.prod_eq_one fun σ _ => Finset.prod_eq_one fun s _ => ?_
    rw [show (MvPolynomial.eval _).mapMatrix _ = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) k) from ?_,
      Matrix.det_one, one_pow]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X, Matrix.one_apply,
      (hcol σ).eq_iff, (Fin.castLE_injective _).eq_iff, eq_comm]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem minorMonomial_mem_harmonic (cc : T → T) (isX : T → Prop)
    (hdis : ∀ τ, isX τ → ∀ i j, col τ i ≠ col (cc τ) j) (a : T → ℕ → ℕ) :
    minorsP r n col k a ∈ harmK r n k cc isX (fun _ => 1) := by
  classical
  let S : Set (Letter T r n) := {v | ∃ j, col v.1 j = v.2.2}
  have hS : minorsP r n col k a ∈ MvPolynomial.supported k S := by
    refine Subalgebra.prod_mem _ fun t _ => Subalgebra.prod_mem _ fun s _ => Subalgebra.pow_mem _ ?_ _
    rw [minor, Matrix.det_apply']
    refine Subalgebra.sum_mem _ fun g _ => Subalgebra.mul_mem _ (intCast_mem _ _)
      (Subalgebra.prod_mem _ fun a _ => ?_)
    exact Algebra.subset_adjoin ⟨_, ⟨_, rfl⟩, rfl⟩
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ hτ i i'
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Derivation.coeFn_coe]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  by_cases hbb : b = b'
  · subst hbb
    by_cases hb : ∃ j, col (cc τ) j = b
    · obtain ⟨j', hj'⟩ := hb
      rw [minorHarm_pderiv_comm, minorHarm_pderiv_eq_zero hS, map_zero, smul_zero]
      rintro ⟨j, hj⟩
      exact hdis τ hτ j j' (hj.trans hj'.symm)
    · rw [minorHarm_pderiv_eq_zero hS (v := ⟨cc τ, i', b⟩) hb, map_zero, smul_zero]
  · rw [Matrix.one_apply_ne hbb, zero_smul]

omit [Fintype T] in
theorem rowShift_minor (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : k) (σ' : T) (s : Fin (r σ')) :
    rowShift r n k σ i i' t (minor r n col k σ' s) = minor r n col k σ' s := by
  classical
  rw [minor, AlgHom.map_det]
  by_cases h : ∃ u : Fin (s + 1), (⟨σ', Fin.castLE s.isLt u⟩ : Σ σ, Fin (r σ)) = ⟨σ, i⟩
  · obtain ⟨u, hu⟩ := h
    obtain ⟨rfl, hu'⟩ := Sigma.mk.inj_iff.1 hu
    have hu'' : Fin.castLE s.isLt u = i := eq_of_heq hu'
    subst hu''
    have hi' : (i' : ℕ) < u := hi
    let u' : Fin (s + 1) := ⟨i', hi'.trans u.isLt⟩
    have hne : u ≠ u' := fun e => by
      have := congrArg Fin.val e
      simp only [u'] at this
      omega
    refine Eq.trans ?_ (Matrix.det_updateRow_add_smul_self _ hne (C t))
    congr 1
    ext1 x y
    by_cases hx : x = u
    · subst hx
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X,
        Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [ite_eq_left ⟨_, rfl⟩]
      rfl
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X,
        Matrix.updateRow_ne hx]
      rw [ite_eq_right]
      rintro ⟨b, hb⟩
      have := eq_of_heq (Sigma.mk.inj_iff.1 hb).2
      exact hx (Fin.castLE_injective s.isLt (congrArg Prod.fst this))
  · congr 1
    ext1 x y
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X]
    rw [ite_eq_right]
    rintro ⟨b, hb⟩
    obtain ⟨rfl, hb'⟩ := Sigma.mk.inj_iff.1 hb
    exact h ⟨x, by rw [show Fin.castLE s.isLt x = i from congrArg Prod.fst (eq_of_heq hb')]⟩

theorem minorMonomial_rowInvariant (a : T → ℕ → ℕ) : RowInv r n k (minorsP r n col k a) := by
  intro σ i i' hi t
  simp only [minorsP, map_prod, map_pow, rowShift_minor r n k col σ i i' hi t]

omit [Fintype T] in
theorem minor_weighted (w : (Σ σ, Fin (r σ)) → ℕ) (σ : T) (s : Fin (r σ)) :
    (minor r n col k σ s).IsWeightedHomogeneous (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
      (∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩) := by
  rw [minor, Matrix.det_apply']
  refine IsWeightedHomogeneous.sum _ _ _ fun g _ => ?_
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
    (Finset.univ : Finset (Fin (s + 1)))
    (fun j => (X ⟨σ, Fin.castLE s.isLt (g j), col σ (Fin.castLE s.isLt j)⟩ : MvPolynomial (Letter T r n) k))
    (fun j => w ⟨σ, Fin.castLE s.isLt (g j)⟩) (fun j _ => isWeightedHomogeneous_X _ _ _)
  rw [Equiv.sum_comp g (fun j => w ⟨σ, Fin.castLE s.isLt j⟩)] at h
  have h2 := (isWeightedHomogeneous_C (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
    (((Equiv.Perm.sign g : ℤˣ) : ℤ) : k)).mul h
  simpa using h2

theorem gaps_sum (b : ℕ → ℕ) (hb : Antitone b) (N i : ℕ) (hi : i ≤ N) :
    ∑ s ∈ Finset.range N, (if i ≤ s then b s - b (s + 1) else 0) = b i - b N := by
  induction N, hi using Nat.le_induction with
  | base =>
    rw [Nat.sub_self]
    exact Finset.sum_eq_zero fun s hs => ite_eq_right (by simpa using hs)
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih, ite_eq_left hN]
    have := hb hN
    have := hb (Nat.le_succ N)
    simp only [Nat.succ_eq_add_one] at this
    omega

theorem minorMonomial_rowDegree (a : T → ℕ → ℕ) (ha : ∀ σ, Antitone (a σ)) (h0 : ∀ σ, a σ (r σ) = 0) :
    RowDeg r n k a (minorsP r n col k a) := by
  classical
  intro m hm σ i
  let w : (Σ σ, Fin (r σ)) → ℕ := fun ℓ => if ℓ = ⟨σ, i⟩ then 1 else 0
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) Finset.univ _ _
    fun σ' _ => IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) Finset.univ _ _
      fun (s : Fin (r σ')) _ => (minor_weighted r n k col w σ' s).pow (a σ' s - a σ' (s + 1))
  have h1 := h (mem_support_iff.1 hm)
  have hL : Finsupp.weight (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
      Finset.sum_eq_single σ, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp [w]
    · intro j _ hj
      simp [w, hj]
    · simp
    · intro σ' _ hσ
      simp [w, hσ]
    · simp
  rw [← hL, h1, Finset.sum_eq_single σ]
  · have e : ∀ s : Fin (r σ), (a σ s - a σ (s + 1)) • ∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩ =
        if (i : ℕ) ≤ s then a σ s - a σ (s + 1) else 0 := by
      intro s
      split_ifs with his
      · rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_of_le his⟩]
        · simp [w]
        · intro j _ hj
          simp only [w]
          rw [ite_eq_right]
          intro e
          have e' : Fin.castLE s.isLt j = i := eq_of_heq (Sigma.mk.inj_iff.1 e).2
          exact hj (Fin.ext (congrArg Fin.val e' :))
        · simp
      · rw [Finset.sum_eq_zero, smul_zero]
        intro j _
        simp only [w]
        rw [ite_eq_right]
        intro e
        have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.1 e).2)
        have := j.isLt
        simp only [Fin.val_castLE] at *
        omega
    rw [Finset.sum_congr rfl fun s _ => e s,
      Fin.sum_univ_eq_sum_range (fun s => if (i : ℕ) ≤ s then a σ s - a σ (s + 1) else 0),
      gaps_sum _ (ha σ) _ _ i.isLt.le, h0, Nat.sub_zero]
  · intro σ' _ hσ
    simp [w, hσ]
  · simp

theorem minorMonomial_isHomogeneous (a : T → ℕ → ℕ) :
    (minorsP r n col k a).IsHomogeneous (∑ σ, ∑ s : Fin (r σ), (s + 1) * (a σ s - a σ (s + 1))) := by
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => (1 : ℕ)) Finset.univ _ _
    fun σ' _ => IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => (1 : ℕ)) Finset.univ _ _
      fun (s : Fin (r σ')) _ => (minor_weighted r n k col (fun _ => 1) σ' s).pow (a σ' s - a σ' (s + 1))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    mul_comm (a _ _ - a _ _)] at h
  exact h

theorem minors_polynomial_coefficient_norm_le_pow (a : T → ℕ → ℕ) (N : ℕ) (hN : ∀ σ, r σ ≤ N) :
    CoeffNorm.l1Norm (minorsP r n col ℂ a) ≤
      (N : ℝ) ^ (∑ σ, ∑ s : Fin (r σ), (s + 1) * (a σ s - a σ (s + 1))) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine (CoeffNorm.l1Norm_prod_le _ _).trans
    (Finset.prod_le_prod₀ (fun _ _ => CoeffNorm.l1Norm_nonneg _) fun σ _ => ?_)
  rw [← Finset.prod_pow_eq_pow_sum]
  simp only [pow_mul]
  refine CoeffNorm.l1Norm_prod_pow_le _ _ _ _ fun s _ => ?_
  refine (CoeffNorm.l1Norm_det_le_pow _ (R := 1) fun i j => by simp).trans ?_
  rw [Fintype.card_fin, mul_one]
  refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
  exact_mod_cast (Nat.succ_le_of_lt s.isLt).trans (hN σ)

end Minors

/-- Row degrees determine the exact total degree of every harmonic polynomial. -/
theorem isHomogeneous_of_rowDeg {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
    {K : Type} [Field K] {a : T → ℕ → ℕ}
    {P : MvPolynomial (Letter T r n) K} (hP : RowDeg r n K a P) :
    P.IsHomogeneous (∑ τ, ∑ i : Fin (r τ), a τ i) := by
  intro m hm
  have h := hP m (MvPolynomial.mem_support_iff.2 hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using h τ i

section SignatureConstruction

variable {T : Type}

/-- Truncate outside the actual rows; the input weights on every row are preserved. -/
def trunc (r : T → ℕ) (a : T → ℕ → ℕ) : T → ℕ → ℕ :=
  fun τ i => if i < r τ then a τ i else 0

theorem trunc_row (r : T → ℕ) (a : T → ℕ → ℕ) (τ : T) (i : Fin (r τ)) :
    trunc r a τ i = a τ i := ite_eq_left i.isLt

theorem antitone_trunc (r : T → ℕ) (a : T → ℕ → ℕ)
    (ha : ∀ τ, Antitone (fun i : Fin (r τ) => a τ i)) (τ : T) :
    Antitone (trunc r a τ) := by
  intro i j hij
  simp only [trunc]
  split_ifs with hj hi hi
  · exact ha τ (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

variable [Fintype T]

/-- The explicit leading-minor construction in the source's original range
p+q ≤ n. The coefficient field and its chosen integral subring are arbitrary.
In particular, this does not identify the coefficient field with the CM host. -/
theorem exists_short_integral_harmonic_of_signature
    (K : Type) [Field K] (O : Subring K)
    (r : T → ℕ) (cc : T → T) (isX : T → Prop) [DecidablePred isX]
    (p q n : ℕ) (hn : p + q ≤ n)
    (hr : ∀ τ, r τ = if isX τ then p else q)
    (hcc : ∀ τ, isX τ → ¬ isX (cc τ))
    (a : T → ℕ → ℕ) (ha : ∀ τ, Antitone (fun i : Fin (r τ) => a τ i)) :
    ∃ P : MvPolynomial (Letter T r n) K,
      P ∈ HaO r n K O cc isX a ∧ P ≠ 0 ∧
      P.IsHomogeneous (∑ τ, ∑ i : Fin (r τ), a τ i) ∧
      P.totalDegree = (∑ τ, ∑ i : Fin (r τ), a τ i) ∧
      ∀ σ : K →+* ℂ, ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤
        ((p + q : ℕ) : ℝ) ^ (∑ τ, ∑ i : Fin (r τ), a τ i) := by
  classical
  let col : ∀ τ, Fin (r τ) → Fin n := fun τ i =>
    if h : isX τ then ⟨i, by have := i.isLt; have := hr τ; rw [ite_eq_left h] at this; omega⟩
    else ⟨p + i, by have := i.isLt; have := hr τ; rw [ite_eq_right h] at this; omega⟩
  have hinj : ∀ τ, Function.Injective (col τ) := by
    intro τ i j hij
    have hval := congrArg Fin.val hij
    by_cases h : isX τ
    · simp only [col, dite_eq_left h] at hval
      exact Fin.ext hval
    · simp only [col, dite_eq_right h] at hval
      exact Fin.ext (by omega)
  have hdis : ∀ τ, isX τ → ∀ i j, col τ i ≠ col (cc τ) j := by
    intro τ h i j hij
    have hval := congrArg Fin.val hij
    simp only [col, dite_eq_left h, dite_eq_right (hcc τ h)] at hval
    have hi := i.isLt
    have hrow := hr τ
    rw [ite_eq_left h] at hrow
    omega
  let b := trunc r a
  let P := minorsP r n col K b
  have hrow : RowDeg r n K a P := by
    have hb := minorMonomial_rowDegree r n K col b (antitone_trunc r a ha)
      (fun τ => ite_eq_right (lt_irrefl (r τ)))
    intro m hm τ i
    simpa only [b, trunc_row] using hb m hm τ i
  have hne : P ≠ 0 := minorMonomial_ne_zero r n K col hinj b
  have hhom := isHomogeneous_of_rowDeg hrow
  have hdeg := hhom.totalDegree hne
  have hgap : (∑ τ, ∑ s : Fin (r τ), (s + 1) * (b τ s - b τ (s + 1))) =
      (∑ τ, ∑ i : Fin (r τ), a τ i) :=
    ((minorMonomial_isHomogeneous r n K col b).totalDegree hne).symm.trans hdeg
  refine ⟨P, ⟨⟨minorMonomial_mem_harmonic r n K col cc isX hdis b,
    minorMonomial_rowInvariant r n K col b, hrow⟩,
      minorMonomial_coeff_mem r n K col b O⟩, hne, hhom, hdeg, ?_⟩
  intro σ
  change ∑ m ∈ (minorsP r n col K b).support,
    ‖σ ((minorsP r n col K b).coeff m)‖ ≤ _
  rw [← CoeffNorm.l1Norm_map, minorMonomial_map]
  have hbound := minors_polynomial_coefficient_norm_le_pow r n col b (p + q)
    (fun τ => by rw [hr τ]; split_ifs <;> omega)
  simpa only [hgap] using hbound

end SignatureConstruction

end RHLean.Geometry.NativeTheta

end
