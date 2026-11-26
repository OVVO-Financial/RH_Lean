import RHLean.Geometry.NativeCMWeierstrassReducedGroup

/-!
# The actual integral dual-number Lie generator of the same Weierstrass scheme

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveFst.lean`;
only the five dual-number tangent definitions are taken from
`ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/`
`ToroidalCompactification/IsLieBasis.lean`.
The source archive states no license; attribution is retained without
assigning one.

The vector is the literal point [epsilon,-1,0] of the original projective
cubic over R[epsilon]/epsilon^2. Every tangent vector is proved uniquely
to be [c epsilon,-1,0]. These are maps of actual schemes, without a
PolAV, ThetaUnifAV, chart, or tangent-basis existence premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open RHLean.Geometry.NativeCM.SchemeTheory
open RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

namespace RHLean.Geometry.NativeCM.SchemeTheory

abbrev Sp (R : Type) [CommRing R] : Scheme := Spec (.of R)

abbrev spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Sp S ⟶ Sp R := Spec.map (CommRingCat.ofHom f)

abbrev epsR (R : Type) [CommRing R] : Over (Sp R) :=
  Over.mk (spMap (algebraMap R (DualNumber R)))

def epsScaleR {R : Type} [CommRing R] (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom

def IsTangent {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]
    (v : epsR R ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = η[G].left

def IsLieComb {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
    (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) : Prop :=
  ∃ u : Fin n → (epsR R ⟶ G),
    (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

def IsLieBasis {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
    (v : Fin n → (epsR R ⟶ G)) : Prop :=
  (∀ i, IsTangent (v i)) ∧ ∀ w, IsTangent w → ∃! c : Fin n → R, IsLieComb c v w

end RHLean.Geometry.NativeCM.SchemeTheory

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassLie

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem equation_inr (c : R) : (W.map (algebraMap R (DualNumber R))).toProjective.Equation
    ![TrivSqZeroExt.inr c, -1, 0] := by
  have h₂ : (TrivSqZeroExt.inr c : DualNumber R) ^ 2 = 0 := by
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
  have h₃ : (TrivSqZeroExt.inr c : DualNumber R) ^ 3 = 0 := by
    rw [pow_succ, h₂, zero_mul]
  rw [equation_origin_iff]
  simp only [h₃, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
    mul_zero, add_zero]

def vec (c : R) : Spec (.of (DualNumber R)) ⟶ scheme W :=
  ptHom W (algebraMap R (DualNumber R)) ![TrivSqZeroExt.inr c, -1, 0]
    (isUnimodularSol_origin (equation_inr W c))

theorem scale_vec (c : R) : spMap (epsScaleR c) ≫ vec W 1 = vec W c := by
  refine (SpecMap_ptHom W _ _ _ (epsScaleR c)).trans (ptHom_congr W _ _ _ ?_ ?_ _)
  · ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext1 j
    fin_cases j
    · ext <;> simp [epsScaleR]
    · simp
    · simp

theorem vec_inj {c d : R} (e : vec W c = vec W d) : c = d := by
  rw [vec, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W c),
    ← SpecMap_originEval_chartY W _ _ _ (equation_inr W d), cancel_mono] at e
  have e' : originEval W _ _ _ (equation_inr W c) = originEval W _ _ _ (equation_inr W d) :=
    congrArg (·.hom) (Spec.map_injective e)
  have := RingHom.congr_fun e' (originZ W)
  rw [originEval_originZ, originEval_originZ] at this
  simpa using congrArg TrivSqZeroExt.snd this

theorem fst_vec (c : R) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ vec W c = zero W := by
  refine (SpecMap_ptHom W _ _ _ (TrivSqZeroExt.fstHom R R R).toRingHom).trans ?_
  rw [zero, ← pt_smul W (A := R) _ _ isUnit_one.neg]
  refine ptHom_congr W _ _ _ ?_ ?_ _
  · ext a; simp
  · ext1 j
    fin_cases j <;> simp

theorem surjective_fst :
    Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  intro p
  refine ⟨PrimeSpectrum.comap (algebraMap R (DualNumber R)) p, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change algebraMap R (DualNumber R) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  have h : (TrivSqZeroExt.inr a.snd : DualNumber R) ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact zero_mem _)
  conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]
  exact (Ideal.add_mem_iff_left _ h).symm

theorem exists_eq_vec (g : Spec (.of (DualNumber R)) ⟶ scheme W)
    (hg : g ≫ toSpec W = spMap (algebraMap R (DualNumber R)))
    (h0 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g = zero W) : ∃ c, g = vec W c := by
  have hr : Set.range g ⊆ Set.range (chartY W) := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := surjective_fst p
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartY]
    have : q ∈ zero W ⁻¹ᵁ coordOpen W 1 := by
      rw [zero_preimage_coordOpen_one]; trivial
    rw [← h0] at this
    exact this
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift _ _ hr)
  have hl : Spec.map φ ≫ chartY W = g := hφ ▸ IsOpenImmersion.lift_fac _ _ hr
  have hc : φ.hom.comp (algebraMap R (OriginRing W)) = algebraMap R (DualNumber R) := by
    rw [← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp] at hg
    exact congrArg (·.hom) (Spec.map_injective hg)
  have ha : (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ.hom =
      (originAug W : OriginRing W →+* R) := by
    rw [← hl, ← SpecMap_originAug_chartY, ← Category.assoc, cancel_mono] at h0
    exact congrArg (·.hom) (Spec.map_injective ((Spec.map_comp _ _).trans h0))
  have hz : (φ.hom (originZ W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originZ W)
  have hw : (φ.hom (originW W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originW W)
  have hw0 : φ.hom (originW W) = 0 := by
    have e := congrArg φ.hom ((equation_origin_iff _ _ _).mp (equation_originZ_originW W))
    simp only [map_add, map_mul, map_pow] at e
    ext
    · exact hw
    · rw [e]
      simp [pow_succ, hz, hw]
  have hz0 : φ.hom (originZ W) = TrivSqZeroExt.inr (φ.hom (originZ W)).snd := by
    ext <;> simp [hz]
  refine ⟨(φ.hom (originZ W)).snd, ?_⟩
  rw [← hl, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W _)]
  congr 2
  ext1
  refine origin_hom_ext W (fun r => ?_) ?_ ?_
  · exact (RingHom.congr_fun hc r).trans (originEval_algebraMap W _ _ _ (equation_inr W _) r).symm
  · exact hz0.trans (originEval_originZ W _ _ _ (equation_inr W _)).symm
  · exact hw0.trans (originEval_originW W _ _ _ (equation_inr W _)).symm

theorem isLieBasis_eps : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R)
    [GrpObj (schemeOver W)], η[schemeOver W].left = zero W → ∃ v : epsR R ⟶ schemeOver W,
      (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
        v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
      IsLieBasis ![v] := by
  intro R _ W _ hη
  let v : epsR R ⟶ schemeOver W := Over.homMk (vec W 1) (ptHom_toSpec ..)
  have key : ∀ (c : Fin 1 → R) (w : epsR R ⟶ schemeOver W),
      IsLieComb c ![v] w ↔ w.left = vec W (c 0) := by
    intro c w
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : (List.ofFn u).prod = u 0 := by simp
      rw [this]
      exact (hu 0).trans (scale_vec W _)
    · intro h
      refine ⟨fun _ => w, fun i => ?_, by simp⟩
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact h.trans (scale_vec W _).symm
  refine ⟨v, ⟨isUnimodularSol_origin (equation_inr W 1), rfl⟩, fun i => ?_, fun w hw => ?_⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact (fst_vec W 1).trans hη.symm
  · obtain ⟨c, hc⟩ := exists_eq_vec W w.left (Over.w w) (hw.trans hη)
    refine ⟨fun _ => c, (key _ _).mpr hc, fun d hd => ?_⟩
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact vec_inj W (((key _ _).mp hd).symm.trans hc)

/-- The literal integral tangent generator, rather than an arbitrary
coordinate chosen after complex uniformization. -/
def integralVector : epsR R ⟶ schemeOver W :=
  Over.homMk (vec W 1) (ptHom_toSpec ..)

@[simp] theorem integralVector_left : (integralVector W).left = vec W 1 := rfl

/-- Its scheme-theoretic reduction is the actual origin. -/
theorem integralVector_isTangent [_root_.IsReduced R] [W.IsElliptic] :
    IsTangent (integralVector W) :=
  (fst_vec W 1).trans (one_left W).symm

/-- This specified integral generator spans every actual dual-number tangent. -/
theorem integralVector_isLieBasis [_root_.IsReduced R] [W.IsElliptic] :
    IsLieBasis ![integralVector W] := by
  obtain ⟨v, ⟨h, hv⟩, hb⟩ := isLieBasis_eps R W (one_left W)
  have heq : v = integralVector W := by
    apply Over.OverMorphism.ext
    exact hv
  simpa only [heq] using hb

/-- The integral coordinate of any actual tangent vector is unique. -/
theorem integral_tangent_coordinate [_root_.IsReduced R] [W.IsElliptic]
    (v : epsR R ⟶ schemeOver W) (hv : IsTangent v) :
    ∃! c : R, v.left = vec W c := by
  obtain ⟨c, hc⟩ := exists_eq_vec W v.left (Over.w v) (hv.trans (one_left W))
  exact ⟨c, hc, fun d hd => vec_inj W (hd.symm.trans hc)⟩

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassLie

end
