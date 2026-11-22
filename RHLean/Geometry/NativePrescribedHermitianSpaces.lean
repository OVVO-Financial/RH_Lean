import RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLattices.StatementLat

/-!
# The prescribed Hermitian spaces and their actual integral base lattices

The original W_j is the coordinate space E^(k+m-1), with k+j-1 positive
and m-j negative diagonal entries. We construct its nondegenerate Hermitian
form, coordinate frame and standard ring-of-integers lattice, and prove the
lattice is self-dual. The signature is proved by an explicit permutation
to the standard positive/negative blocks at every complex embedding.

These are the actual W, W_sig, W_rank and W_sigval data used in the source
Spaces record. The ranks k,m,j remain the original parameters. No empty
row record, replacement D7, finite-adelic isometry or complex structure is
inserted here. The latter compatibility data are separate constructions.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Formalism/LocalRingCardinality/DataSpaces.lean, HSpace and HSpace.SigOK;
SpanPowerMembership/Spaces.lean, diagForm, stdLat and stdSpace;
SpanPowerMembership/BaseFormAnisotropicOrthogonalSingle.lean, negTail,
hasSig_tail, dSpace and the W fields of spacesOfRanks; and
src/Formalism/SatakeDualWeyl/Statement.lean, cT, Jpq and HasSignature.
The self-duality proof below is direct on coordinates and uses the already
native all-place definition of Hermitian dual. No HermDual endpoint premise
is introduced. The source archive/mirror states no license; attribution is
preserved without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

open NumberField

namespace RHLean.Geometry.NativePrescribedHermitian

namespace Signature

def cT {A : Type} [CommRing A] (σ : A →+* A) {m p : Type}
    (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

theorem cT_one {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]
    (σ : A →+* A) : cT σ (1 : Matrix n n A) = 1 := by
  unfold cT
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- The original matrix-congruence definition of signature. -/
def HasSignature {n : Type} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ e : n ≃ Fin p ⊕ Fin q,
    ∃ P : Matrix.GeneralLinearGroup (Fin p ⊕ Fin q) ℂ,
      cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
        J.reindex e e * (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q

end Signature

/-- The complete source HSpace record, using the native Hermitian dual. -/
structure HSpace (E : Type) [Field E] [NumberField E] [StarRing E] where
  V : Type
  [acg : AddCommGroup V]
  [modE : Module E V]
  [modO : Module (𝓞 E) V]
  [tower : IsScalarTower (𝓞 E) E V]
  [fd : FiniteDimensional E V]
  hT : V →ₗ⋆[E] V →ₗ[E] E
  herm : hT.IsSymm
  nondeg : hT.Nondegenerate
  rank : ℕ
  rank_eq : Module.finrank E V = rank
  frame : Module.Basis (Fin rank) E V
  sig : (E →+* ℂ) → ℕ × ℕ
  L0 : Submodule (𝓞 E) V
  standardTuple_isLattice : Submodule.IsLattice E L0
  baseLattice_isUnimodular :
    AlpogeAllPlace.Formalism.HermitianLatticesTheory.IsUnimodular hT L0

attribute [instance] HSpace.acg HSpace.modE HSpace.modO HSpace.tower HSpace.fd

namespace HSpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def gram (S : HSpace E) : Matrix (Fin S.rank) (Fin S.rank) E :=
  fun i j => S.hT (S.frame i) (S.frame j)

def hD (S : HSpace E) (x y : S.V) : E := S.hT y x

def SigOK (S : HSpace E) : Prop :=
  ∀ τ : E →+* ℂ, Signature.HasSignature (S.gram.map τ) (S.sig τ).1 (S.sig τ).2

end HSpace

section Diagonal

def sgn {A : Type} [Ring A] (b : Bool) : A := if b then -1 else 1

theorem sgn_mul_self {A : Type} [Ring A] (b : Bool) :
    (sgn b : A) * sgn b = 1 := by
  cases b <;> simp [sgn]

theorem sgn_ne_zero {A : Type} [Ring A] [Nontrivial A] (b : Bool) :
    (sgn b : A) ≠ 0 := by
  cases b <;> simp [sgn]

theorem map_sgn {A B : Type} [Ring A] [Ring B] (f : A →+* B) (b : Bool) :
    f (sgn b) = sgn b := by
  cases b <;> simp [sgn]

variable {E : Type} [Field E] [StarRing E]

theorem star_sgn (b : Bool) : star (sgn b : E) = sgn b := by
  cases b <;> simp [sgn]

def diagForm (N : ℕ) (neg : Fin N → Bool) :
    (Fin N → E) →ₗ⋆[E] (Fin N → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E)
    (fun x y => ∑ i, star (x i) * sgn (neg i) * y i)
    (by intro m₁ m₂ n; simp [add_mul, Finset.sum_add_distrib])
    (by
      intro c m n
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [starRingEnd_apply]
      ring)
    (by intro m n₁ n₂; simp [mul_add, Finset.sum_add_distrib])
    (by
      intro c m n
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)

theorem diagForm_apply (N : ℕ) (neg : Fin N → Bool) (x y : Fin N → E) :
    diagForm N neg x y = ∑ i, star (x i) * sgn (neg i) * y i := rfl

theorem diagForm_single (N : ℕ) (neg : Fin N → Bool) (i j : Fin N) :
    diagForm N neg (Pi.single i 1) (Pi.single j 1) =
      if i = j then (sgn (neg i) : E) else 0 := by
  rw [diagForm_apply, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem diagForm_single_left (N : ℕ) (neg : Fin N → Bool)
    (j : Fin N) (b : E) (x : Fin N → E) :
    diagForm N neg (Pi.single j b) x = star b * sgn (neg j) * x j := by
  rw [diagForm_apply,
    Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem diagForm_isSymm (N : ℕ) (neg : Fin N → Bool) :
    (diagForm (E := E) N neg).IsSymm := by
  constructor
  intro x y
  simp only [diagForm_apply, map_sum, starRingEnd_apply, star_mul', star_star, star_sgn]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem diagForm_nondeg (N : ℕ) (neg : Fin N → Bool) :
    (diagForm (E := E) N neg).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have h := hx (Pi.single i 1)
    rw [diagForm_apply, Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (by simp)] at h
    simp only [Pi.single_eq_same, mul_one] at h
    have := (mul_eq_zero.1 h).resolve_right (sgn_ne_zero _)
    simpa using this
  · intro y hy
    funext i
    have h := hy (Pi.single i 1)
    rw [diagForm_apply, Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (by simp)] at h
    simp only [Pi.single_eq_same, star_one, one_mul] at h
    have := (mul_eq_zero.1 h).resolve_left (sgn_ne_zero _)
    simpa using this

end Diagonal

section StandardLattice

variable {E : Type} [Field E] [NumberField E]

def stdLat (N : ℕ) : Submodule (𝓞 E) (Fin N → E) :=
  Submodule.span (𝓞 E) (Set.range (Pi.basisFun E (Fin N)))

theorem stdLat_isLattice (N : ℕ) : Submodule.IsLattice E (stdLat (E := E) N) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [stdLat, Submodule.span_span_of_tower]
    exact (Pi.basisFun E (Fin N)).span_eq

/-- The chosen base lattice is literally the integral coordinate vectors. -/
theorem mem_stdLat_iff (N : ℕ) (x : Fin N → E) :
    x ∈ stdLat N ↔ ∀ i, IsIntegral ℤ (x i) := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro j
      by_cases h : j = i <;> simp [Pi.basisFun_apply, Pi.single_apply, h]
    | zero => intro i; exact isIntegral_zero
    | add x y _ _ hx hy => intro i; exact (hx i).add (hy i)
    | smul a x _ hx =>
      intro i
      change IsIntegral ℤ ((a : E) * x i)
      exact a.2.mul (hx i)
  · intro hx
    have hrepr :
        ∑ i : Fin N, (⟨x i, hx i⟩ : 𝓞 E) • (Pi.basisFun E (Fin N)) i = x := by
      funext j
      simp [Pi.basisFun_apply, Pi.single_apply, Algebra.smul_def]
    rw [← hrepr]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable [StarRing E]

omit [NumberField E] in
theorem star_isIntegral (x : E) (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd E).toIntAlgHom

omit [NumberField E] [StarRing E] in
theorem sgn_isIntegral (b : Bool) : IsIntegral ℤ (sgn b : E) := by
  cases b <;> simp [sgn]

/-- Actual Hermitian self-duality, proved by testing the coordinate vectors. -/
theorem stdLat_unimod (N : ℕ) (neg : Fin N → Bool) :
    AlpogeAllPlace.Formalism.HermitianLatticesTheory.IsUnimodular
      (diagForm (E := E) N neg) (stdLat N) := by
  classical
  unfold AlpogeAllPlace.Formalism.HermitianLatticesTheory.IsUnimodular
    AlpogeAllPlace.Formalism.HermitianLatticesTheory.dual
  ext x
  simp only [AlpogeAllPlace.Formalism.E.hdual, Submodule.mem_iInf,
    Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  constructor
  · intro hx
    apply (mem_stdLat_iff N x).mpr
    intro i
    obtain ⟨a, ha⟩ := hx ((Pi.basisFun E (Fin N)) i)
      (Submodule.subset_span ⟨i, rfl⟩)
    rw [Pi.basisFun_apply, diagForm_single_left, star_one, one_mul] at ha
    have hi : IsIntegral ℤ ((sgn (neg i) : E) * x i) := ha ▸ a.2
    cases h : neg i <;> simpa [h, sgn] using hi
  · intro hx y hy
    have hxi := (mem_stdLat_iff N x).mp hx
    have hyi := (mem_stdLat_iff N y).mp hy
    have hi : IsIntegral ℤ (diagForm N neg y x) :=
      IsIntegral.sum _ fun i _ =>
        ((star_isIntegral (y i) (hyi i)).mul (sgn_isIntegral (neg i))).mul (hxi i)
    exact ⟨⟨diagForm N neg y x, hi⟩, rfl⟩

end StandardLattice

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def stdSpace (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) : HSpace E where
  V := Fin N → E
  hT := diagForm N neg
  herm := diagForm_isSymm N neg
  nondeg := diagForm_nondeg N neg
  rank := N
  rank_eq := Module.finrank_fin_fun E
  frame := Pi.basisFun E (Fin N)
  sig := fun _ => (p, q)
  L0 := stdLat N
  standardTuple_isLattice := stdLat_isLattice N
  baseLattice_isUnimodular := stdLat_unimod N neg

theorem stdSpace_gram_apply (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) (i j : Fin N) :
    (stdSpace (E := E) N neg p q).gram i j =
      if i = j then (sgn (neg i) : E) else 0 := by
  show diagForm N neg ((Pi.basisFun E (Fin N)) i) ((Pi.basisFun E (Fin N)) j) = _
  simp only [Pi.basisFun_apply]
  exact diagForm_single N neg i j

def negTail (N q : ℕ) : Fin N → Bool := fun i => decide (N - q ≤ (i : ℕ))

theorem negTail_false (N q : ℕ) (i : Fin N) (h : (i : ℕ) < N - q) :
    negTail N q i = false := by
  unfold negTail
  exact decide_eq_false (by omega)

theorem negTail_true (N q : ℕ) (i : Fin N) (h : N - q ≤ (i : ℕ)) :
    negTail N q i = true := by
  unfold negTail
  exact decide_eq_true h

theorem hasSig_tail (N q : ℕ) (h : q ≤ N) : Signature.HasSignature
    (Matrix.diagonal fun i : Fin N => (sgn (negTail N q i) : ℂ)) (N - q) q := by
  let e : Fin N ≃ Fin (N - q) ⊕ Fin q :=
    (finCongr (by omega : N = (N - q) + q)).trans finSumFinEquiv.symm
  have hl : ∀ i, ((e.symm (Sum.inl i) : Fin N) : ℕ) = i := fun i => by simp [e]
  have hr : ∀ i, ((e.symm (Sum.inr i) : Fin N) : ℕ) = N - q + i := fun i => by simp [e]
  refine ⟨e, 1, ?_⟩
  simp only [Units.val_one, Signature.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply,
    e.symm.injective.eq_iff]
  rcases i with i | i <;> rcases j with j | j
  · have hn : negTail N q (e.symm (Sum.inl i)) = false :=
      negTail_false _ _ _ (by rw [hl]; exact i.isLt)
    simp only [Signature.Jpq, Matrix.fromBlocks_apply₁₁, Matrix.one_apply, Sum.inl.injEq, hn]
    simp [sgn]
  · simp [Signature.Jpq]
  · simp [Signature.Jpq]
  · have hn : negTail N q (e.symm (Sum.inr i)) = true :=
      negTail_true _ _ _ (by rw [hr]; omega)
    simp only [Signature.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply,
      Sum.inr.injEq, hn]
    split_ifs <;> simp [sgn]

def dSpace (N q : ℕ) : HSpace E := stdSpace N (negTail N q) (N - q) q

theorem dSpace_sigOK (N q : ℕ) (h : q ≤ N) : (dSpace (E := E) N q).SigOK := by
  intro τ
  have hg : (dSpace (E := E) N q).gram.map τ =
      Matrix.diagonal fun i : Fin N => (sgn (negTail N q i) : ℂ) := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (stdSpace_gram_apply N (negTail N q) (N - q) q i j)).trans ?_
    change τ (if i = j then (sgn (negTail N q i) : E) else 0) =
      if i = j then (sgn (negTail N q i) : ℂ) else 0
    by_cases h : i = j <;> simp [h, map_sgn]
  rw [hg]
  exact hasSig_tail N q h

/-- The literal prescribed W_j of the original spacesOfRanks construction. -/
def W (k m j : ℕ) : HSpace E := dSpace (k + m - 1) (m - j)

theorem W_rank (k m j : ℕ) : (W (E := E) k m j).rank = k + m - 1 := rfl

theorem W_sigOK (k m j : ℕ) (hk : m + 3 ≤ k) : (W (E := E) k m j).SigOK :=
  dSpace_sigOK _ _ (by omega)

theorem W_sigval (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) (τ : E →+* ℂ) :
    (W k m j).sig τ = (k + j - 1, m - j) := by
  change (k + m - 1 - (m - j), m - j) = (k + j - 1, m - j)
  exact Prod.ext (by omega) rfl

theorem W_hasSignature (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m)
    (τ : E →+* ℂ) :
    Signature.HasSignature ((W k m j).gram.map τ) (k + j - 1) (m - j) := by
  have h := W_sigOK (E := E) k m j hk τ
  simpa only [W_sigval k m j hk hj τ] using h

end Spaces

end RHLean.Geometry.NativePrescribedHermitian

end
