import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.ShiftInvariance
import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

noncomputable section

namespace RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt

open NumberField IsDedekindDomain MeasureTheory Module

section Gram

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

def IsGram {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : (K →+* ℂ) → V → ℝ) : Prop :=
  ∀ v, IsUnit (X v).det ∧ ∀ x, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt b X v x = N v.embedding x

def GramFr (N : (K →+* ℂ) → V → ℝ) : Type :=
  Σ n : ℕ, {p : Basis (Fin n) K V × (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) // IsGram p.1 p.2 N}

def HasGram (N : (K →+* ℂ) → V → ℝ) : Prop := Nonempty (GramFr N)

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

open Classical in

def slope_sq (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) : ℝ :=
  letI : StarRing K := starRingOfComm
  if h : HasGram N then RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef h.some.2.1.1 h.some.2.1.2 L else 0

open Classical in

def slopeMax_sq (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) : ℝ :=
  letI : StarRing K := starRingOfComm
  if h : HasGram N then RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMaxDef h.some.2.1.1 h.some.2.1.2 L else 0

open Classical in

def slopeMin_sq (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) : ℝ :=
  letI : StarRing K := starRingOfComm
  if h : HasGram N then RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muMinDef h.some.2.1.1 h.some.2.1.2 L else 0

def slope (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) : ℝ := slope_sq N L / 2

def deg (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) : ℝ := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L : ℝ) * slope N L

section Indep

variable [StarRing K]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem norm_realize_sq {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realizeRaw, sq]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem IsGram.norm_realize {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {b : Basis ι K V}
    {X : InfinitePlace K → Matrix ι ι ℂ} {b' : Basis κ K V} {X' : InfinitePlace K → Matrix κ κ ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) (h' : IsGram b' X' N) (x : V) :
    ‖RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X x‖ = ‖RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b' X' x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_realize_sq, norm_realize_sq]
  exact Finset.sum_congr rfl fun v _ => by rw [(h v).2, (h' v).2]

theorem IsGram.rk_deg {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {b : Basis ι K V}
    {X : InfinitePlace K → Matrix ι ι ℂ} {b' : Basis κ K V} {X' : InfinitePlace K → Matrix κ κ ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) (h' : IsGram b' X' N) {L : Submodule (𝓞 K) V} (hL : L.FG) :
    RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rk (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L = RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rk (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b' X') L ∧
      RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L = RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b' X') L := by
  obtain ⟨h1, h2, -⟩ := RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X (fun v => (h v).1) L hL
  obtain ⟨h1', h2', -⟩ := RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V κ b' X' (fun v => (h' v).1) L hL
  refine ⟨h2.trans h2'.symm, ?_⟩
  haveI := h1.2
  haveI := h1'.2
  unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg RHLean.Geometry.AlpogeAllPlace.Formalism.F.deg
  rw [RHLean.Geometry.AlpogeAllPlace.Formalism.HN.QuotientRealization.covol_eq_of_norm_eq ((RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X).comp L.toAddSubgroup.subtype)
    ((RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b' X').comp L.toAddSubgroup.subtype) (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.zl (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L)
    (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.zl (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b' X') L)
    (fun y => ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩)
    (fun y => ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩)
    (fun m => h.norm_realize h' m.1)]

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem IsGram.hasGram {ι : Type} [Fintype ι] [DecidableEq ι] {b : Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) : HasGram N := by
  let e := Fintype.equivFin ι
  refine ⟨⟨_, ⟨(b.reindex e, fun v => Matrix.reindex e e (X v)), fun v => ⟨?_, fun x => ?_⟩⟩⟩⟩
  · simpa using (h v).1
  · rw [← (h v).2 x]
    simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    rw [Matrix.inv_reindex]
    simp only [Matrix.mulVec, dotProduct]
    rw [← e.sum_comp]
    simp [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.vecAt]

theorem slope_sq_eq {ι : Type} [Fintype ι] [DecidableEq ι] {b : Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) {L : Submodule (𝓞 K) V} (hL : L.FG) :
    slope_sq N L = RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef b X L := by
  rw [slope_sq, dite_eq_left h.hasGram]
  show RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef h.hasGram.some.2.1.1 h.hasGram.some.2.1.2 L = _
  obtain ⟨h1, h2⟩ := IsGram.rk_deg h.hasGram.some.2.2 h hL
  unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rk at h1
  unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg at h2
  unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef RHLean.Geometry.AlpogeAllPlace.Formalism.HN.slope RHLean.Geometry.AlpogeAllPlace.Formalism.F.slope
  rw [h1, h2]


end Indep
end Gram
end RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt
