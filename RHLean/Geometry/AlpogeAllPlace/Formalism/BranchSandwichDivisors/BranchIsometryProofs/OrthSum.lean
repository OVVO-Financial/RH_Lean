import RHLean.Geometry.AlpogeAllPlace.Formalism.BranchSandwichDivisors.StatementL
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.ShiftInvariance
import RHLean.Geometry.AlpogeAllPlace.Formalism.BranchSandwichDivisors.BranchIsometryProofs.MapScale

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

open Module NumberField
open scoped Matrix

noncomputable section

namespace RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap

namespace OrthogonalSumAlt

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

omit [IsTotallyComplex K] in
theorem deg_bot (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) :
    RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = 0 := by
  have hl := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX ⊥ Submodule.fg_bot).1
  have h := ((RHLean.Geometry.AlpogeAllPlace.Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X)).2 ⊥ ⊥ hl hl (by
    intro x hx y hy
    rw [(Submodule.mem_bot _).1 hx]
    simp)).2.1
  rw [sup_idem] at h
  linarith

omit [NumberField K] [StarRing K] [IsTotallyComplex K] [IsScalarTower (𝓞 K) K V] in
theorem rkK_bot : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (⊥ : Submodule (𝓞 K) V) = 0 := by
  simp [RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK]

omit [NumberField K] [StarRing K] [IsTotallyComplex K] [IsScalarTower (𝓞 K) K V] [DecidableEq ι] in
theorem eq_bot_of_rkK (b : Basis ι K V) {L : Submodule (𝓞 K) V} (h : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L = 0) :
    L = ⊥ := by
  have : Module.Finite K V := Module.Finite.of_basis b
  have h1 : Submodule.span K (L : Set V) = ⊥ := Submodule.finrank_eq_zero.1 h
  rw [Submodule.span_eq_bot] at h1
  exact (Submodule.eq_bot_iff _).2 fun x hx => h1 x hx

omit [StarRing K] [IsTotallyComplex K] in
theorem finrank_pos' : 0 < Module.finrank ℚ K := Module.finrank_pos

omit [IsTotallyComplex K] in
theorem degD_eq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    degD b X L = 2 / (Module.finrank ℚ K : ℝ) * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L +
      (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L : ℝ) * (-Real.log 2 + RHLean.Geometry.AlpogeAllPlace.Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) := by
  by_cases h0 : L = ⊥
  · subst h0
    simp [degD, rkK_bot, deg_bot b X hX]
  · have hr : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L ≠ 0 := fun h => h0 (eq_bot_of_rkK b h)
    have hrk := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX L hL).2.1
    have hs : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.slope (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L =
        RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L / (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rk (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L : ℝ) := rfl
    have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
      exact_mod_cast (finrank_pos' (K := K)).ne'
    have hr' : (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [degD, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef, hs, hrk]
    push_cast
    field_simp
    ring

omit [StarRing K] [IsTotallyComplex K] [IsScalarTower (𝓞 K) K V] in
theorem orth_inner (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    {A B : Submodule (𝓞 K) V} (h : OrthAt b X A B) :
    ∀ x ∈ A, ∀ y ∈ B, inner ℝ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X x) (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  intro x hx y hy
  rw [RHLean.Geometry.AlpogeAllPlace.Formalism.HN.HeightGram.inner_realize]
  exact Finset.sum_eq_zero fun v _ => by rw [h v x hx y hy]; simp

omit [IsTotallyComplex K] in
theorem main (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {S : Type} (A : S → Submodule (𝓞 K) V) (hA : ∀ s, (A s).FG)
    (horth : ∀ s t, s ≠ t → OrthAt b X (A s) (A t)) (s : Finset S) :
    (⨆ i ∈ s, A i).FG ∧ RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (⨆ i ∈ s, A i) = ∑ i ∈ s, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (A i) ∧
      RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, A i) =
        ∑ i ∈ s, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) (A i) ∧
      ∀ c : ℝ, (∀ i ∈ s, A i ≠ ⊥ → RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMax (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) (A i) ≤ c) →
        (⨆ i ∈ s, A i) ≠ ⊥ → RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMax (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, A i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [rkK_bot, deg_bot b X hX, Submodule.fg_bot]
  | insert a s ha ih =>
    obtain ⟨ihfg, ihrk, ihdeg, ihmu⟩ := ih
    rw [Finset.iSup_insert]
    set B := ⨆ i ∈ s, A i with hB
    have ho : ∀ x ∈ A a, ∀ y ∈ B,
        inner ℝ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X x) (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
      intro x hx y hy
      obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum A y).1 hy
      rw [← hμ, map_sum, inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact orth_inner b X (horth a i (fun h => ha (h ▸ hi))) x hx _ (μ i).2
    have hlA := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX (A a) (hA a)).1
    have hlB := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX B ihfg).1
    obtain ⟨hl, hdeg, hmu⟩ :=
      (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X)).2 (A a) B hlA hlB ho
    have hfg : (A a ⊔ B).FG := (hA a).sup ihfg
    have hinf : A a ⊓ B = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have h1 := ho x hx.1 x hx.2
      rw [inner_self_eq_zero] at h1
      exact RHLean.Geometry.AlpogeAllPlace.Formalism.HN.HeightGram.realize_injective b X hX (by rw [h1, map_zero])
    have hrk := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.degSupermod (𝓞 K) V _ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) (A a ⊔ B) (A a) B hl
      le_sup_left le_sup_right).1
    rw [hinf, (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX _ hfg).2.1, (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX _ (hA a)).2.1,
      (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX _ ihfg).2.1,
      (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX _ Submodule.fg_bot).2.1, rkK_bot, mul_zero, add_zero,
      ← mul_add] at hrk
    have hrk' := Nat.eq_of_mul_eq_mul_left (finrank_pos' (K := K)) hrk
    refine ⟨hfg, ?_, ?_, ?_⟩
    · rw [hrk', Finset.sum_insert ha, ihrk]
    · rw [hdeg, Finset.sum_insert ha, ihdeg]
    · intro c hc hne
      have hcs : ∀ i ∈ s, A i ≠ ⊥ → RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMax (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) (A i) ≤ c :=
        fun i hi => hc i (Finset.mem_insert_of_mem hi)
      by_cases h1 : A a = ⊥
      · rw [h1, bot_sup_eq] at hne ⊢
        exact ihmu c hcs hne
      · by_cases h2 : B = ⊥
        · rw [h2, sup_bot_eq]
          exact hc a (Finset.mem_insert_self a s) h1
        · rw [(hmu h1 h2).1]
          exact max_le (hc a (Finset.mem_insert_self a s) h1) (ihmu c hcs h2)

end OrthogonalSumAlt

open OrthogonalSumAlt in
theorem orthogonal_sum_slope : OrthSum := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX S _ A hA horth
  obtain ⟨hfg, hrk, hdeg, hmu⟩ := main b X hX A hA horth Finset.univ
  have hu : (⨆ i ∈ (Finset.univ : Finset S), A i) = ⨆ i, A i := by simp
  rw [hu] at hfg hrk hdeg hmu
  refine ⟨hrk, ?_, ?_⟩
  · rw [degD_eq b X hX _ hfg, hdeg, hrk, Finset.mul_sum]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (degD_eq b X hX _ (hA i)).symm
  · intro c hc hne
    have h := hmu ((c + Real.log 2 - RHLean.Geometry.AlpogeAllPlace.Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) / 2)
      (fun i _ hi => by
        have := hc i hi
        unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMaxDef at this
        linarith) hne
    unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMaxDef
    linarith

namespace OrthogonalSumAlt

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

omit [NumberField K] [StarRing K] [IsTotallyComplex K] in
theorem blockInv (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (n : ℕ)
    (v : InfinitePlace K) :
    (Matrix.blockDiagonal' fun _ : Fin n => X v) * (Matrix.blockDiagonal' fun _ : Fin n => (X v)⁻¹)
      = 1 := by
  rw [← Matrix.blockDiagonal'_mul]
  simp only [Matrix.mul_nonsing_inv _ (hX v)]
  exact Matrix.blockDiagonal'_one

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
omit [NumberField K] [StarRing K] [IsTotallyComplex K] in
theorem fcoord_pi (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K) (x : Fin n → V) (j : Fin n)
    (a : ι) :
    RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord (Pi.basis fun _ : Fin n => b)
      (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v x ⟨j, a⟩ =
        RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord b X v (x j) a := by
  have hinv : (Matrix.blockDiagonal' fun _ : Fin n => X v)⁻¹ =
      Matrix.blockDiagonal' fun _ : Fin n => (X v)⁻¹ :=
    Matrix.inv_eq_right_inv (blockInv X hX n v)
  simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord, hinv, Matrix.mulVec, dotProduct, Fintype.sum_sigma,
    Matrix.blockDiagonal'_apply, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.vecAt]
  rw [Finset.sum_eq_single j]
  · simp [Pi.basis_repr]
  · intro k _ hk
    simp [hk.symm]
  · simp

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem majAt_pi (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K) (x y : Fin n → V) :
    RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.majAt (Pi.basis fun _ : Fin n => b)
      (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v x y =
        ∑ j, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.majAt b X v (x j) (y j) := by
  simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.majAt, Fintype.sum_sigma, fcoord_pi b X hX]

omit [NumberField K] [StarRing K] [IsTotallyComplex K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem majAt_zero_left (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (y : V) : RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.majAt b X v 0 y = 0 := by
  simp [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.majAt, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord_zero]

omit [NumberField K] [StarRing K] [IsTotallyComplex K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem majAt_zero_right (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (y : V) : RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.majAt b X v y 0 = 0 := by
  simp [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.majAt, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord_zero]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem normAt_single (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K) (i : Fin n) (x : V) :
    RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt (Pi.basis fun _ : Fin n => b)
      (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v (Pi.single i x) =
        RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt b X v x := by
  simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm, Fintype.sum_sigma, fcoord_pi b X hX]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord_zero]
  · simp

omit [NumberField K] [StarRing K] [IsTotallyComplex K] in
theorem rkK_map {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (ψ : V →ₗ[K] W) (hψ : Function.Injective ψ)
    (A : Submodule (𝓞 K) V) :
    RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (A.map (ψ.restrictScalars (𝓞 K))) = RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK A := by
  unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK
  have h : Submodule.span K ((A.map (ψ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) =
      (Submodule.span K (A : Set V)).map ψ := by
    rw [Submodule.map_span]
    rfl
  rw [h]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ψ hψ _)).symm

omit [IsTotallyComplex K] in
theorem muMax_mono (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {N L : Submodule (𝓞 K) V} (hN : N.FG) (hL : L.FG) (hNL : N ≤ L)
    (h0 : N ≠ ⊥) :
    RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMax (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) N ≤ RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMax (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L := by
  have hL0 : L ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hNL))
  have h1 := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muChar (𝓞 K) V _ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) N
    (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX N hN).1 h0).1
  have h2 := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muChar (𝓞 K) V _ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L
    (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX L hL).1 hL0).1
  exact (h1 _).2 fun M hM => (h2 _).1 le_rfl M (hM.trans hNL)

end OrthogonalSumAlt

open OrthogonalSumAlt in
theorem power_slope_mu : PowMu := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A n hA hA0 hn bn Xn An
  have hXn : ∀ v, IsUnit (Xn v).det := fun v =>
    Matrix.isUnit_det_of_right_inverse (blockInv X hX n v)
  let ψ : Fin n → V →ₗ[K] (Fin n → V) := fun i => LinearMap.single K (fun _ : Fin n => V) i
  have hψ : ∀ i, Function.Injective (ψ i) := fun i x y h =>
    Pi.single_injective (M := fun _ : Fin n => V) i h
  let Ai : Fin n → Submodule (𝓞 K) (Fin n → V) := fun i => A.map ((ψ i).restrictScalars (𝓞 K))
  have hAn : (⨆ i, Ai i) = An := by
    change (⨆ i, Submodule.map (LinearMap.single (𝓞 K) (fun _ : Fin n => V) i)
      ((fun _ : Fin n => A) i)) = Submodule.pi Set.univ (fun _ : Fin n => A)
    exact Submodule.iSup_map_single
  have hAifg : ∀ i, (Ai i).FG := fun i => hA.map _
  have hAi0 : ∀ i, Ai i ≠ ⊥ := by
    intro i h
    have h1 : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (Ai i) = RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK A := rkK_map (ψ i) (hψ i) A
    rw [h, rkK_bot] at h1
    exact hA0 (eq_bot_of_rkK b h1.symm)
  have hre := fun i => RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rerealize K V ι (Fin n → V) (Σ _ : Fin n, ι) b X bn Xn (ψ i) hX hXn
    (hψ i) (fun v x => normAt_single b X hX n v i x) A hA
  have horth : ∀ s t, s ≠ t → OrthAt bn Xn (Ai s) (Ai t) := by
    rintro s t hst v _ ⟨x, _, rfl⟩ _ ⟨y, _, rfl⟩
    change RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.majAt bn Xn v (Pi.single s x) (Pi.single t y) = 0
    rw [majAt_pi b X hX]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = s
    · subst hj
      rw [Pi.single_eq_of_ne hst, majAt_zero_right]
    · rw [Pi.single_eq_of_ne hj, majAt_zero_left]
  obtain ⟨hrk, hdeg, hmu⟩ := orthogonal_sum_slope K (Fin n → V) (Σ _ : Fin n, ι) bn Xn hXn (Fin n) Ai
    hAifg horth
  rw [hAn] at hrk hdeg hmu
  have hrkA : ∀ i, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (Ai i) = RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK A := fun i => rkK_map (ψ i) (hψ i) A
  have hmuA : ∀ i, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef bn Xn (Ai i) = RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef b X A := fun i => by
    unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef
    rw [(hre i).2.2.1]
  have hmxA : ∀ i, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMaxDef bn Xn (Ai i) = RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMaxDef b X A := fun i => by
    unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMaxDef
    rw [(hre i).2.2.2.1]
  have hrk' : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK An = n * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK A := by
    rw [hrk]
    simp [hrkA]
  have hr0 : (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK A : ℝ) ≠ 0 := by
    exact_mod_cast fun h => hA0 (eq_bot_of_rkK b h)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hAnfg : An.FG := by
    rw [← hAn]
    exact Submodule.fg_iSup _ hAifg
  have hAn0 : An ≠ ⊥ := by
    intro h
    apply hAi0 ⟨0, hn⟩
    rw [← hAn] at h
    exact le_bot_iff.1 (h ▸ le_iSup Ai ⟨0, hn⟩)
  refine ⟨hrk', ?_, le_antisymm ?_ ?_⟩
  · simp only [degD, hrkA, hmuA, hrk', Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hdeg
    push_cast at hdeg
    have : ((n : ℝ) * (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK A : ℝ)) * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef bn Xn An =
        ((n : ℝ) * (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK A : ℝ)) * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef b X A := by linarith
    exact mul_left_cancel₀ (mul_ne_zero hn0 hr0) this
  · exact hmu _ (fun i _ => (hmxA i).le) hAn0
  · rw [← hmxA ⟨0, hn⟩]
    have := muMax_mono bn Xn hXn (hAifg ⟨0, hn⟩) hAnfg (hAn ▸ le_iSup Ai ⟨0, hn⟩) (hAi0 ⟨0, hn⟩)
    unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMaxDef
    linarith

open OrthogonalSumAlt in
theorem orthSandwich_of (hS : ScaleSandwich) : OrthSandwich := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX S _ A A0 G hA0 hG horth hle hGA
  have hnoeth : IsNoetherian (𝓞 K) A0 := isNoetherian_of_fg_of_noetherian A0 hA0
  have hAfg : ∀ s, (A s).FG := fun s => by
    have := (isNoetherian_submodule.1 hnoeth) (A s) (hle s)
    exact this
  obtain ⟨hrk, hdeg, -⟩ := orthogonal_sum_slope K V ι b X hX S A hAfg horth
  have hB : (⨆ s, A s) ≤ A0 := iSup_le hle
  by_cases h0 : A0 = ⊥
  · have hB0 : (⨆ s, A s) = ⊥ := le_bot_iff.1 (h0 ▸ hB)
    rw [hB0] at hrk hdeg
    rw [← hrk, ← hdeg, h0]
    simp [degD, rkK_bot]
  · obtain ⟨h1, h2, h3, -, -⟩ := hS K V ι b X hX A0 (⨆ s, A s) G hA0 h0 hG hB hGA
    have hr : (0 : ℝ) ≤ (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK A0 : ℝ) := Nat.cast_nonneg _
    refine ⟨by rw [← h1, hrk], ?_, ?_⟩
    · rw [← hdeg, degD, degD, h1]
      exact mul_le_mul_of_nonneg_left h2 hr
    · rw [← hdeg, degD, degD, h1]
      nlinarith [mul_le_mul_of_nonneg_left h3 hr]

theorem orthogonal_sandwich_bound : OrthSandwich := orthSandwich_of scale_sandwich_bound

end RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap
