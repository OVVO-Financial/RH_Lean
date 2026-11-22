import RHLean.Geometry.NativeThetaPolynomialNorm

/-!
# Paired harmonic polynomials for the finite native theta family

These are the literal row-linear forms, leading minors, mixed Laplacians and
partition degrees used by the source finite-family constructor. Orthogonal
coefficient vectors give harmonic polynomials by the product rule. No span
or theta-density conclusion is supplied as a premise here.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/`
`IsWeightedHomogeneousOfMemOrbitSpan.lean`, the Laplacian, Forms and Degree
sections, and `Proofs/CovolumeBounds/IsHarmonicProdOfDisjointColumns.lean`,
the Cross and Perp sections. The source archive/mirror states no license;
this notice preserves attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MvPolynomial Matrix

namespace RHLean.Geometry.NativeTheta.Paired

abbrev Var (T : Type*) (p q : ℕ) (κ : Type*) := T × (Fin p ⊕ Fin q) × κ

abbrev Poly (R : Type*) [CommRing R] (T : Type*) (p q : ℕ) (κ : Type*) :=
  MvPolynomial (Var T p q κ) R

variable {R S : Type*} [CommRing R] [CommRing S] {T : Type*} {p q n : ℕ} {κ κ' κ'' : Type*}

abbrev xVar (t : T) (a : Fin p) (k : κ) : Var T p q κ := (t, Sum.inl a, k)

abbrev yVar (t : T) (b : Fin q) (k : κ) : Var T p q κ := (t, Sum.inr b, k)

section Laplacian

variable [Fintype κ]

noncomputable def laplacian (t : T) (a : Fin p) (b : Fin q) : Module.End R (Poly R T p q κ) :=
  ∑ k : κ, (pderiv (xVar t a k)).toLinearMap ∘ₗ (pderiv (yVar t b k)).toLinearMap

theorem laplacian_apply (t : T) (a : Fin p) (b : Fin q) (P : Poly R T p q κ) :
    laplacian t a b P = ∑ k : κ, pderiv (xVar t a k) (pderiv (yVar t b k) P) := by
  simp [laplacian, LinearMap.sum_apply]

def IsHarmonic (P : Poly R T p q κ) : Prop := ∀ t a b, laplacian t a b P = 0

variable (R T p q κ) in

def harmonicSubmodule : Submodule R (Poly R T p q κ) where
  carrier := {P | IsHarmonic P}
  add_mem' hP hQ t a b := by rw [map_add, hP, hQ, add_zero]
  zero_mem' t a b := map_zero _
  smul_mem' r P hP t a b := by rw [map_smul, hP, smul_zero]

@[simp] theorem mem_harmonicSubmodule {P : Poly R T p q κ} :
    P ∈ harmonicSubmodule R T p q κ ↔ IsHarmonic P := Iff.rfl

theorem isHarmonic_C (r : R) : IsHarmonic (C r : Poly R T p q κ) := fun t a b => by
  simp [laplacian_apply]

theorem map_laplacian (f : R →+* S) (t : T) (a : Fin p) (b : Fin q) (P : Poly R T p q κ) :
    MvPolynomial.map f (laplacian t a b P) = laplacian t a b (MvPolynomial.map f P) := by
  simp [laplacian_apply, pderiv_map]

theorem IsHarmonic.map (f : R →+* S) {P : Poly R T p q κ} (hP : IsHarmonic P) :
    IsHarmonic (MvPolynomial.map f P) := fun t a b => by
  rw [← map_laplacian, hP, map_zero]

theorem isHarmonic_map_iff {f : R →+* S} (hf : Function.Injective f) {P : Poly R T p q κ} :
    IsHarmonic (MvPolynomial.map f P) ↔ IsHarmonic P :=
  ⟨fun h t a b => MvPolynomial.map_injective f hf (by rw [map_laplacian, h, map_zero]),
    fun h => h.map f⟩

end Laplacian

section Forms

variable [Fintype κ]

noncomputable def rowForm (t : T) (r : Fin p ⊕ Fin q) : (κ → R) →ₗ[R] Poly R T p q κ where
  toFun v := ∑ k : κ, C (v k) * X (t, r, k)
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, smul_eq_C_mul, mul_assoc]

noncomputable def xForm (t : T) (a : Fin p) : (κ → R) →ₗ[R] Poly R T p q κ :=
  rowForm t (Sum.inl a)

noncomputable def yForm (t : T) (b : Fin q) : (κ → R) →ₗ[R] Poly R T p q κ :=
  rowForm t (Sum.inr b)

theorem rowForm_apply (t : T) (r : Fin p ⊕ Fin q) (v : κ → R) :
    rowForm t r v = ∑ k : κ, C (v k) * X (t, r, k) := rfl

theorem xForm_apply (t : T) (a : Fin p) (ε : κ → R) :
    (xForm t a ε : Poly R T p q κ) = ∑ k : κ, C (ε k) * X (xVar t a k) := rfl

theorem yForm_apply (t : T) (b : Fin q) (φ : κ → R) :
    (yForm t b φ : Poly R T p q κ) = ∑ k : κ, C (φ k) * X (yVar t b k) := rfl

theorem rowForm_single [DecidableEq κ] (t : T) (r : Fin p ⊕ Fin q) (k : κ) :
    (rowForm t r (Pi.single k 1) : Poly R T p q κ) = X (t, r, k) := by
  rw [rowForm_apply, Finset.sum_eq_single k] <;> simp +contextual

@[simp] theorem xForm_single [DecidableEq κ] (t : T) (a : Fin p) (k : κ) :
    (xForm t a (Pi.single k 1) : Poly R T p q κ) = X (xVar t a k) := rowForm_single _ _ _

@[simp] theorem yForm_single [DecidableEq κ] (t : T) (b : Fin q) (k : κ) :
    (yForm t b (Pi.single k 1) : Poly R T p q κ) = X (yVar t b k) := rowForm_single _ _ _

theorem eval_xForm (z : Var T p q κ → R) (t : T) (a : Fin p) (ε : κ → R) :
    eval z (xForm t a ε) = ε ⬝ᵥ fun k => z (xVar t a k) := by
  simp [xForm_apply, dotProduct]

theorem eval_yForm (z : Var T p q κ → R) (t : T) (b : Fin q) (φ : κ → R) :
    eval z (yForm t b φ) = φ ⬝ᵥ fun k => z (yVar t b k) := by
  simp [yForm_apply, dotProduct]

abbrev lead {m : ℕ} (i : Fin m) : Fin (i.val + 1) → Fin m := Fin.castLE i.isLt

noncomputable def xMinor (t : T) (i : Fin p) (ε : Fin p → κ → R) : Poly R T p q κ :=
  (Matrix.of fun a b : Fin (i.val + 1) => xForm t (lead i a) (ε (lead i b))).det

noncomputable def yMinor (t : T) (i : Fin q) (φ : Fin q → κ → R) : Poly R T p q κ :=
  (Matrix.of fun a b : Fin (i.val + 1) => yForm t (lead i a) (φ (lead i b))).det

noncomputable def minorProd [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) : Poly R T p q κ :=
  ∏ t : T, ((∏ i : Fin p, xMinor t i (ε t) ^ c t i) * ∏ i : Fin q, yMinor t i (φ t) ^ c' t i)

def IsPerp (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) : Prop :=
  ∀ t a b, ε t a ⬝ᵥ φ t b = 0

theorem laplacian_xForm_mul_yForm (t : T) (a : Fin p) (b : Fin q) (ε φ : κ → R) :
    laplacian t a b (xForm t a ε * yForm t b φ : Poly R T p q κ) = C (ε ⬝ᵥ φ) := by
  classical
  have h1 (k : κ) : pderiv (yVar t b k) (xForm t a ε : Poly R T p q κ) = 0 := by
    simp [xForm_apply, pderiv_X]
  have h2 (k : κ) : pderiv (yVar t b k) (yForm t b φ : Poly R T p q κ) = C (φ k) := by
    simp [yForm_apply, pderiv_X, Pi.single_apply]
  have h3 (k : κ) : pderiv (xVar t a k) (xForm t a ε : Poly R T p q κ) = C (ε k) := by
    simp [xForm_apply, pderiv_X, Pi.single_apply]
  simp [laplacian_apply, h1, h2, h3, dotProduct, mul_comm]

theorem map_rowForm (f : R →+* S) (t : T) (r : Fin p ⊕ Fin q) (v : κ → R) :
    MvPolynomial.map f (rowForm t r v) = rowForm t r (f ∘ v) := by
  simp [rowForm_apply]

theorem map_xForm (f : R →+* S) (t : T) (a : Fin p) (ε : κ → R) :
    MvPolynomial.map f (xForm t a ε : Poly R T p q κ) = xForm t a (f ∘ ε) := map_rowForm _ _ _ _

theorem map_yForm (f : R →+* S) (t : T) (b : Fin q) (φ : κ → R) :
    MvPolynomial.map f (yForm t b φ : Poly R T p q κ) = yForm t b (f ∘ φ) := map_rowForm _ _ _ _

theorem ringHom_xMinor [Fintype κ'] (F : Poly R T p q κ →+* Poly S T p q κ') (t : T) (i : Fin p)
    (ε : Fin p → κ → R) (ε' : Fin p → κ' → S)
    (h : ∀ a b, F (xForm t a (ε b)) = xForm t a (ε' b)) : F (xMinor t i ε) = xMinor t i ε' := by
  rw [xMinor, RingHom.map_det]; congr 1; ext1 a b; exact h _ _

theorem ringHom_yMinor [Fintype κ'] (F : Poly R T p q κ →+* Poly S T p q κ') (t : T) (i : Fin q)
    (φ : Fin q → κ → R) (φ' : Fin q → κ' → S)
    (h : ∀ a b, F (yForm t a (φ b)) = yForm t a (φ' b)) : F (yMinor t i φ) = yMinor t i φ' := by
  rw [yMinor, RingHom.map_det]; congr 1; ext1 a b; exact h _ _

theorem map_minorProd [Fintype T] (f : R →+* S) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    MvPolynomial.map f (minorProd c c' ε φ) =
      minorProd c c' (fun t a => f ∘ ε t a) (fun t b => f ∘ φ t b) := by
  simp only [minorProd, map_prod, map_mul, map_pow]
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by
      rw [ringHom_xMinor _ t i (ε t) (fun a => f ∘ ε t a) fun a b => map_xForm _ _ _ _]
  · exact Finset.prod_congr rfl fun i _ => by
      rw [ringHom_yMinor _ t i (φ t) (fun a => f ∘ φ t a) fun a b => map_yForm _ _ _ _]

theorem IsPerp.map (f : R →+* S) {ε : T → Fin p → κ → R} {φ : T → Fin q → κ → R}
    (h : IsPerp ε φ) : IsPerp (fun t a => f ∘ ε t a) (fun t b => f ∘ φ t b) := fun t a b => by
  have := congrArg f (h t a b)
  simpa [dotProduct] using this

end Forms

section Degree

def partOf {m : ℕ} (c : Fin m → ℕ) (a : Fin m) : ℕ := ∑ i ∈ Finset.Ici a, c i

def partSize {m : ℕ} (c : Fin m → ℕ) : ℕ := ∑ i : Fin m, (i.val + 1) * c i

def typeDegree [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) : ℕ :=
  ∑ t : T, (partSize (c t) + partSize (c' t))

theorem partOf_antitone {m : ℕ} (c : Fin m → ℕ) : Antitone (partOf c) := fun _ _ h =>
  Finset.sum_le_sum_of_subset (Finset.Ici_subset_Ici.mpr h)

theorem sum_smul_sum_lead {M : Type*} [AddCommMonoid M] {m : ℕ} (c : Fin m → ℕ) (w : Fin m → M) :
    ∑ i : Fin m, c i • ∑ a : Fin (i.val + 1), w (lead i a) = ∑ a : Fin m, partOf c a • w a := by
  have h (i : Fin m) : ∑ a : Fin (i.val + 1), w (lead i a) = ∑ a ∈ Finset.Iic i, w a := by
    refine Finset.sum_bij (fun a _ => lead i a) ?_ ?_ ?_ ?_
    · intro a _; simpa [Fin.le_def] using Nat.lt_succ_iff.mp a.isLt
    · intro a _ b _ h; exact Fin.castLE_injective _ h
    · intro b hb
      exact ⟨⟨b.val, Nat.lt_succ_iff.mpr (Fin.le_def.mp (Finset.mem_Iic.mp hb))⟩, Finset.mem_univ _, rfl⟩
    · intros; rfl
  simp only [h, partOf, Finset.smul_sum, Finset.sum_smul]
  exact Finset.sum_comm' (by simp)

theorem sum_partOf {m : ℕ} (c : Fin m → ℕ) : ∑ a, partOf c a = partSize c := by
  have := sum_smul_sum_lead c (fun _ => (1 : ℕ))
  simp only [smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at this
  rw [← this, partSize]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

def diffOf {m : ℕ} (l : Fin m → ℕ) (i : Fin m) : ℕ :=
  l i - if h : i.val + 1 < m then l ⟨i.val + 1, h⟩ else 0

theorem partOf_eq_add {m : ℕ} (c : Fin m → ℕ) (i : Fin m) :
    partOf c i = c i + if h : i.val + 1 < m then partOf c ⟨i.val + 1, h⟩ else 0 := by
  rw [partOf, ← Finset.Ioi_insert, Finset.sum_insert (by simp)]
  congr 1
  split_ifs with h
  · rw [partOf]; congr 1; ext j
    rw [Finset.mem_Ioi, Finset.mem_Ici, Fin.lt_def, Fin.le_def]; exact Iff.rfl
  · rw [Finset.sum_eq_zero]; intro j hj
    have := j.isLt; rw [Finset.mem_Ioi, Fin.lt_def] at hj; omega

theorem partOf_diffOf {m : ℕ} {l : Fin m → ℕ} (hl : Antitone l) : partOf (diffOf l) = l := by
  funext i
  obtain ⟨i, hi⟩ := i
  induction' hd : m - i with d ih generalizing i
  · omega
  · rw [partOf_eq_add, diffOf]
    split_ifs with h
    · rw [ih (i + 1) h (by omega)]
      exact Nat.sub_add_cancel (hl (by simp [Fin.le_def]))
    · simp

variable [Fintype κ] {M : Type*} [AddCommMonoid M]

def rowWeight (w : T → Fin p ⊕ Fin q → M) : Var T p q κ → M := fun v => w v.1 v.2.1

theorem rowForm_isWeightedHomogeneous (w : T → Fin p ⊕ Fin q → M) (t : T) (r : Fin p ⊕ Fin q)
    (v : κ → R) : IsWeightedHomogeneous (rowWeight w) (rowForm t r v) (w t r) :=
  IsWeightedHomogeneous.sum _ _ _ fun k _ =>
    (isWeightedHomogeneous_X R (rowWeight w) (t, r, k)).C_mul _

theorem det_isWeightedHomogeneous {σ ι : Type*} [Fintype ι] [DecidableEq ι] (w : σ → M)
    (A : Matrix ι ι (MvPolynomial σ R)) (u : ι → M)
    (h : ∀ a b, IsWeightedHomogeneous w (A a b) (u a)) :
    IsWeightedHomogeneous w A.det (∑ a, u a) := by
  rw [det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
  have h1 := IsWeightedHomogeneous.prod Finset.univ (fun i => A (s i) i) (fun i => u (s i))
    fun i _ => h _ _
  rw [Equiv.sum_comp s u] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with e | e
  · simpa [e] using h1
  · simpa [e] using h1.neg

theorem minorProd_isWeightedHomogeneous [Fintype T] (w : T → Fin p ⊕ Fin q → M)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    IsWeightedHomogeneous (rowWeight w) (minorProd c c' ε φ)
      (∑ t, ((∑ a, partOf (c t) a • w t (Sum.inl a)) + ∑ b, partOf (c' t) b • w t (Sum.inr b))) := by
  refine IsWeightedHomogeneous.prod _ _ _ fun t _ => ?_
  rw [← sum_smul_sum_lead, ← sum_smul_sum_lead]
  refine IsWeightedHomogeneous.mul ?_ ?_
  · refine IsWeightedHomogeneous.prod _ _ _ fun i _ => IsWeightedHomogeneous.pow ?_ _
    exact det_isWeightedHomogeneous _ _ _ fun a b => rowForm_isWeightedHomogeneous w t _ _
  · refine IsWeightedHomogeneous.prod _ _ _ fun i _ => IsWeightedHomogeneous.pow ?_ _
    exact det_isWeightedHomogeneous _ _ _ fun a b => rowForm_isWeightedHomogeneous w t _ _

theorem minorProd_isHomogeneous [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    (minorProd c c' ε φ).IsHomogeneous (typeDegree c c') := by
  have := minorProd_isWeightedHomogeneous (fun _ _ => (1 : ℕ)) c c' ε φ
  simp only [smul_eq_mul, mul_one, sum_partOf] at this
  exact this

end Degree

end RHLean.Geometry.NativeTheta.Paired

open MvPolynomial Matrix

namespace RHLean.Geometry.NativeTheta.Paired

variable {R : Type*} [CommRing R] {T : Type*} {p q n : ℕ} {κ κ' : Type*}

section Cross

variable [Fintype κ]

noncomputable def cross (t : T) (a : Fin p) (b : Fin q) (P Q : Poly R T p q κ) : Poly R T p q κ :=
  ∑ k : κ, pderiv (xVar t a k) P * pderiv (yVar t b k) Q

theorem laplacian_mul (t : T) (a : Fin p) (b : Fin q) (P Q : Poly R T p q κ) :
    laplacian t a b (P * Q) =
      laplacian t a b P * Q + P * laplacian t a b Q + cross t a b P Q + cross t a b Q P := by
  simp only [laplacian_apply, cross, pderiv_mul, map_add, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cross_add_left (t : T) (a : Fin p) (b : Fin q) (P P' Q : Poly R T p q κ) :
    cross t a b (P + P') Q = cross t a b P Q + cross t a b P' Q := by
  simp only [cross, map_add, add_mul, Finset.sum_add_distrib]

theorem cross_add_right (t : T) (a : Fin p) (b : Fin q) (P Q Q' : Poly R T p q κ) :
    cross t a b P (Q + Q') = cross t a b P Q + cross t a b P Q' := by
  simp only [cross, map_add, mul_add, Finset.sum_add_distrib]

theorem cross_mul_left (t : T) (a : Fin p) (b : Fin q) (P P' Q : Poly R T p q κ) :
    cross t a b (P * P') Q = cross t a b P Q * P' + P * cross t a b P' Q := by
  simp only [cross, pderiv_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cross_mul_right (t : T) (a : Fin p) (b : Fin q) (P Q Q' : Poly R T p q κ) :
    cross t a b P (Q * Q') = cross t a b P Q * Q' + Q * cross t a b P Q' := by
  simp only [cross, pderiv_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

@[simp] theorem cross_C_left (t : T) (a : Fin p) (b : Fin q) (r : R) (Q : Poly R T p q κ) :
    cross t a b (C r) Q = 0 := by simp [cross]

@[simp] theorem cross_C_right (t : T) (a : Fin p) (b : Fin q) (r : R) (P : Poly R T p q κ) :
    cross t a b P (C r) = 0 := by simp [cross]

theorem IsHarmonic.mul_of_cross {P Q : Poly R T p q κ} (hP : IsHarmonic P) (hQ : IsHarmonic Q)
    (h : ∀ t a b, cross t a b P Q = 0) (h' : ∀ t a b, cross t a b Q P = 0) :
    IsHarmonic (P * Q) := fun t a b => by
  rw [laplacian_mul, hP, hQ, h, h']; simp

theorem cross_eq_zero_of_mem_adjoin (t : T) (a : Fin p) (b : Fin q) {s s' : Set (Poly R T p q κ)}
    (h : ∀ u ∈ s, ∀ v ∈ s', cross t a b u v = 0) {P Q : Poly R T p q κ}
    (hP : P ∈ Algebra.adjoin R s) (hQ : Q ∈ Algebra.adjoin R s') : cross t a b P Q = 0 := by
  induction hP using Algebra.adjoin_induction with
  | mem u hu =>
    induction hQ using Algebra.adjoin_induction with
    | mem v hv => exact h u hu v hv
    | algebraMap r => exact cross_C_right _ _ _ _ _
    | add x y _ _ hx hy => rw [cross_add_right, hx, hy, add_zero]
    | mul x y _ _ hx hy => rw [cross_mul_right, hx, hy, zero_mul, mul_zero, add_zero]
  | algebraMap r => exact cross_C_left _ _ _ _ _
  | add x y _ _ hx hy => rw [cross_add_left, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [cross_mul_left, hx, hy, zero_mul, mul_zero, add_zero]

theorem isHarmonic_of_mem_adjoin {s : Set (Poly R T p q κ)} (hs : ∀ u ∈ s, IsHarmonic u)
    (h : ∀ t a b, ∀ u ∈ s, ∀ v ∈ s, cross t a b u v = 0) {P : Poly R T p q κ}
    (hP : P ∈ Algebra.adjoin R s) : IsHarmonic P := by
  induction hP using Algebra.adjoin_induction with
  | mem u hu => exact hs u hu
  | algebraMap r => exact isHarmonic_C r
  | add x y _ _ hx hy => exact (harmonicSubmodule R T p q κ).add_mem hx hy
  | mul x y hx' hy' hx hy =>
    exact hx.mul_of_cross hy (fun t a b => cross_eq_zero_of_mem_adjoin t a b (h t a b) hx' hy')
      fun t a b => cross_eq_zero_of_mem_adjoin t a b (h t a b) hy' hx'

theorem pderiv_rowForm [DecidableEq T] (t t' : T) (r r' : Fin p ⊕ Fin q) (k : κ) (v : κ → R) :
    pderiv (t, r, k) (rowForm t' r' v : Poly R T p q κ) =
      if t' = t ∧ r' = r then C (v k) else 0 := by
  classical
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [rowForm_apply, pderiv_X, Pi.single_apply]
  · rw [rowForm_apply, map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [pderiv_C_mul, pderiv_X_of_ne, mul_zero]
    intro e
    simp only [Prod.mk.injEq] at e
    exact h ⟨e.1, e.2.1⟩

theorem isHarmonic_rowForm (t : T) (r : Fin p ⊕ Fin q) (v : κ → R) :
    IsHarmonic (rowForm t r v : Poly R T p q κ) := fun t' a b => by
  classical
  rw [laplacian_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pderiv_rowForm]; split_ifs <;> simp

theorem cross_rowForm [DecidableEq T] (t t₁ t₂ : T) (a : Fin p) (b : Fin q)
    (r₁ r₂ : Fin p ⊕ Fin q) (v w : κ → R) :
    cross t a b (rowForm t₁ r₁ v) (rowForm t₂ r₂ w : Poly R T p q κ) =
      if (t₁ = t ∧ r₁ = Sum.inl a) ∧ t₂ = t ∧ r₂ = Sum.inr b then C (v ⬝ᵥ w) else 0 := by
  simp only [cross, pderiv_rowForm]
  by_cases h₁ : t₁ = t ∧ r₁ = Sum.inl a <;> by_cases h₂ : t₂ = t ∧ r₂ = Sum.inr b <;>
    simp [h₁, h₂, dotProduct]

end Cross

section Perp

variable [Fintype κ] {ι ι' : Type*}

def formSet (ε : T → ι → κ → R) (φ : T → ι' → κ → R) : Set (Poly R T p q κ) :=
  {u | ∃ t a c, u = xForm t a (ε t c)} ∪ {u | ∃ t b d, u = yForm t b (φ t d)}

theorem isHarmonic_of_mem_adjoin_formSet {ε : T → ι → κ → R} {φ : T → ι' → κ → R}
    (h : ∀ t c d, ε t c ⬝ᵥ φ t d = 0) {P : Poly R T p q κ}
    (hP : P ∈ Algebra.adjoin R (formSet ε φ)) : IsHarmonic P := by
  classical
  refine isHarmonic_of_mem_adjoin ?_ ?_ hP
  · rintro _ (⟨t, a, c, rfl⟩ | ⟨t, a, c, rfl⟩) <;> exact isHarmonic_rowForm _ _ _
  · rintro t a b _ (⟨t₁, a₁, c₁, rfl⟩ | ⟨t₁, a₁, c₁, rfl⟩) _ (⟨t₂, a₂, c₂, rfl⟩ | ⟨t₂, a₂, c₂, rfl⟩)
    · rw [xForm, xForm, cross_rowForm, ite_eq_right (by simp)]
    · rw [xForm, yForm, cross_rowForm]
      split_ifs with e
      · obtain ⟨⟨rfl, -⟩, rfl, -⟩ := e
        rw [h, map_zero]
      · rfl
    · rw [yForm, xForm, cross_rowForm, ite_eq_right (by simp)]
    · rw [yForm, yForm, cross_rowForm, ite_eq_right (by simp)]

theorem det_mem_of_forall_mem {A σ m : Type*} [CommRing A] [SetLike σ A] [SubringClass σ A]
    [Fintype m] [DecidableEq m] (s : σ) (M : Matrix m m A) (h : ∀ i j, M i j ∈ s) : M.det ∈ s := by
  rw [det_apply']
  exact sum_mem fun e _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

theorem minorProd_mem_closure [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    minorProd c c' ε φ ∈ Subring.closure (formSet ε φ) := by
  refine prod_mem fun t _ => mul_mem (prod_mem fun i _ => pow_mem ?_ _)
    (prod_mem fun i _ => pow_mem ?_ _)
  · exact det_mem_of_forall_mem _ _ fun a b => Subring.subset_closure (Or.inl ⟨_, _, _, rfl⟩)
  · exact det_mem_of_forall_mem _ _ fun a b => Subring.subset_closure (Or.inr ⟨_, _, _, rfl⟩)

theorem isHarmonic_minorProd [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    {ε : T → Fin p → κ → R} {φ : T → Fin q → κ → R} (h : IsPerp ε φ) :
    IsHarmonic (minorProd c c' ε φ) :=
  isHarmonic_of_mem_adjoin_formSet h
    (Subring.closure_le (t := (Algebra.adjoin R (formSet ε φ)).toSubring).2 Algebra.subset_adjoin
      (minorProd_mem_closure c c' ε φ))

end Perp

end RHLean.Geometry.NativeTheta.Paired

end
