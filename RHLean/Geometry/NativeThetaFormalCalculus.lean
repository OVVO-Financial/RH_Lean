import RHLean.Geometry.NativeThetaJetEvaluation

/-!
# Formal calculus for the actual native theta jets

This supplies the formal substitution chain rule and the coordinate
coefficient identities used to derive commutation of invariant
formal-group derivatives. The series, coordinates and substitutions below
are the existing native theta objects; no additive-group replacement is
made.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CovolumeBounds/`
`NatCastMulCoeffOfPderivEq.lean`, section Chain;
`Proofs/FormalGroupCharts/ConstantCoeffEv.lean`; and
`ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/`
`WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean`, coordinate coefficients.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open MvPowerSeries Finsupp

namespace RHLean.Geometry.NativeTheta.FormalCalculus

abbrev PS (R : Type) [CommRing R] (n d : ℕ) := JetEvaluation.Series R n d
abbrev Pt (R : Type) [CommRing R] (n d : ℕ) := Fin d → PS R n d

def pt (R : Type) [CommRing R] {n : ℕ} (d : ℕ) (j : Fin n) : Pt R n d :=
  JetEvaluation.coordinatePoint n j

def ev {R : Type} [CommRing R] {d m n : ℕ}
    (a : Fin m → Pt R n d) (f : PS R m d) : PS R n d :=
  JetEvaluation.substituteCopies a f

section Chain

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem subst_zero' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [← substAlgHom_apply ha, map_zero]

theorem subst_one' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (1 : MvPowerSeries σ R) = 1 := by
  rw [← substAlgHom_apply ha, map_one]

theorem subst_neg' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (-f) = -subst a f := by
  rw [← substAlgHom_apply ha, map_neg, substAlgHom_apply]

theorem subst_sum' {κ : Type*} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (s : Finset κ)
    (f : κ → MvPowerSeries σ R) : subst a (∑ k ∈ s, f k) = ∑ k ∈ s, subst a (f k) := by
  rw [← substAlgHom_apply ha, map_sum]
  simp only [substAlgHom_apply]

theorem subst_C' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (r : R) :
    subst a (C r : MvPowerSeries σ R) = C (algebraMap R S r) := by
  rw [← substAlgHom_apply ha, show (C r : MvPowerSeries σ R) = algebraMap R _ r from rfl,
    AlgHom.commutes, MvPowerSeries.algebraMap_apply]

open MvPowerSeries.WithPiTopology in

theorem continuous_pderiv [TopologicalSpace R] [DiscreteTopology R] (i : σ) :
    Continuous (pderiv i : MvPowerSeries σ R → MvPowerSeries σ R) := by
  refine continuous_iff_continuousAt.mpr fun f => ?_
  rw [ContinuousAt, tendsto_iff_coeff_tendsto]
  intro d
  simp only [coeff_pderiv]
  exact ((continuous_coeff R (d + single i 1)).mul continuous_const).continuousAt

theorem pderiv_comm (i j : σ) (f : MvPowerSeries σ R) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  by_cases h : i = j
  · rw [h]
  ext d
  simp only [coeff_pderiv, Finsupp.add_apply, single_eq_of_ne h, single_eq_of_ne (Ne.symm h),
    add_zero]
  rw [add_right_comm]
  ring

open MvPowerSeries.WithPiTopology in

theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (f : MvPowerSeries σ R) (j : τ) :
    pderiv j (subst a f) = ∑ i, subst a (pderiv i f) * pderiv j (a i) := by
  classical
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  have hc := continuous_subst (R := R) ha
  refine congr_fun (DenseRange.equalizer (denseRange_toMvPowerSeries (σ := σ) (R := R))
    (g := fun f => pderiv j (subst a f))
    (h := fun f => ∑ i, subst a (pderiv i f) * pderiv j (a i))
    ((continuous_pderiv j).comp hc)
    (continuous_finsetSum _ fun i _ => (hc.comp (continuous_pderiv i)).mul continuous_const)
    ?_) f
  funext p
  simp only [Function.comp_apply]
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [MvPolynomial.coe_C, pderiv_C, subst_C' ha, subst_zero' ha]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, subst_add ha, map_add, hp, hq, add_mul,
      Finset.sum_add_distrib]
  | mul_X p n hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, Derivation.leibniz, hp,
      smul_eq_mul, subst_add ha, subst_X ha, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single n]
      · simp [subst_one' ha]
      · intro b _ hb
        simp [pderiv_X_of_ne (Ne.symm hb), subst_zero' ha]
      · simp
    · exact Finset.sum_congr rfl fun i _ => by ring

theorem constantCoeff_subst_of_zero {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = algebraMap R S (constantCoeff f) := by
  have h : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by simp
  have h' : constantCoeff (subst a (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero ha ha0 (by simp)
  conv_lhs => rw [h, subst_add ha, map_add, h', subst_C' ha]
  simp

theorem pderiv_map {T : Type*} [CommRing T] (φ : R →+* T) (i : σ) (f : MvPowerSeries σ R) :
    pderiv i (map φ f) = map φ (pderiv i f) := by
  ext d
  simp [coeff_pderiv]

end Chain

section Evaluation

variable {k : Type} [CommRing k] {d m n : ℕ}

def CZ (a : Fin m → Pt k n d) : Prop := ∀ j i, constantCoeff (a j i) = 0

theorem CZ.hasSubst {a : Fin m → Pt k n d} (ha : CZ a) : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2

theorem ev_add {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f + g) = ev a f + ev a g :=
  subst_add ha.hasSubst f g

theorem ev_mul {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f * g) = ev a f * ev a g :=
  subst_mul ha.hasSubst f g

def evHom {a : Fin m → Pt k n d} (ha : CZ a) : PS k m d →+* PS k n d :=
  (substAlgHom ha.hasSubst).toRingHom

theorem evHom_apply {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : evHom ha f = ev a f := by
  simp [evHom, ev, JetEvaluation.substituteCopies]

theorem ev_sub {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f - g) = ev a f - ev a g := by
  simp only [← evHom_apply ha, map_sub]

theorem ev_neg {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : ev a (-f) = -ev a f := by
  simp only [← evHom_apply ha, map_neg]

theorem ev_sum {a : Fin m → Pt k n d} (ha : CZ a) {ι : Type} (s : Finset ι) (f : ι → PS k m d) :
    ev a (∑ x ∈ s, f x) = ∑ x ∈ s, ev a (f x) := by
  simp only [← evHom_apply ha, map_sum]

theorem ev_C {a : Fin m → Pt k n d} (ha : CZ a) (c : k) : ev a (C c : PS k m d) = C c := by
  rw [← evHom_apply ha]
  show substAlgHom ha.hasSubst (algebraMap k _ c) = _
  rw [AlgHom.commutes]; rfl

theorem ev_X {a : Fin m → Pt k n d} (ha : CZ a) (j : Fin m) (i : Fin d) : ev a (X (j, i) : PS k m d) = a j i :=
  subst_X ha.hasSubst (j, i)

theorem ev_zero' {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  simp only [← evHom_apply ha, map_zero]

theorem constantCoeff_ev {a : Fin m → Pt k n d} (ha : CZ a) {f : PS k m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 :=
  constantCoeff_subst_eq_zero ha.hasSubst (fun p => ha p.1 p.2) hf

theorem CZ.ev {a : Fin m → Pt k n d} (ha : CZ a) {l : ℕ} {b : Fin l → Pt k m d} (hb : CZ b) :
    CZ (fun j i => ev a (b j i)) := fun j i => constantCoeff_ev ha (hb j i)

theorem ev_ev {l : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) {b : Fin l → Pt k m d} (hb : CZ b) (f : PS k l d) :
    ev a (ev b f) = ev (fun j i => ev a (b j i)) f := by
  unfold ev JetEvaluation.substituteCopies
  rw [subst_comp_subst_apply hb.hasSubst ha.hasSubst]

theorem ev_pt (f : PS k m d) : ev (fun j => pt k (n := m) d j) f = f := by
  unfold ev pt JetEvaluation.substituteCopies JetEvaluation.coordinatePoint
  exact congrFun subst_self f

theorem CZ.pt : CZ (fun j => pt k (n := n) d j) := fun j i => by
  show constantCoeff (X (j, i) : PS k n d) = 0
  simp

theorem pderiv_ev {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d) :
    pderiv v (ev a f) = ∑ p : Fin m × Fin d, ev a (pderiv p f) * pderiv v (a p.1 p.2) := by
  unfold ev JetEvaluation.substituteCopies
  exact pderiv_subst (a := fun p : Fin m × Fin d => a p.1 p.2) ha.hasSubst f v

theorem ev_zeroFam (f : PS k m d) : ev (fun _ _ => (0 : PS k n d)) f = C (constantCoeff f) := by
  classical
  have hz : CZ (fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d)) := fun _ _ => map_zero _
  ext e
  unfold ev JetEvaluation.substituteCopies
  rw [coeff_subst hz.hasSubst, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro x hx
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp) (zero_pow hp), map_zero, smul_zero]

end Evaluation

section CoordinateCoefficients

theorem coeff_subst_killCompl {σ τ R : Type*} [CommRing R] [Finite τ] (e : σ ↪ τ) (f : MvPowerSeries τ R)
    (a : τ → MvPowerSeries σ R) (ha : ∀ t, a t = killCompl e (X t)) (x : σ →₀ ℕ) :
    coeff x (subst a f) = coeff (embDomain e x) f := by
  classical
  have haS : HasSubst a := by
    apply hasSubst_of_constantCoeff_zero
    intro t
    rw [ha, ← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_X]
  have hterm : ∀ n : τ →₀ ℕ, coeff n f • coeff x (n.prod fun s m => a s ^ m) =
      if n = embDomain e x then coeff n f else 0 := by
    intro n
    have hprod : (n.prod fun s m => a s ^ m) = killCompl e (monomial n (1 : R)) := by
      have h1 := monomial_eq (R := R) n (fun _ => 1)
      simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
      rw [h1, map_prod]
      simp only [map_pow, ha, Finsupp.prod]
    rw [hprod, coeff_killCompl, coeff_monomial]
    by_cases hn : n = embDomain e x
    · subst hn
      simp
    · rw [ite_eq_right (Ne.symm hn), ite_eq_right hn, smul_zero]
  rw [coeff_subst haS, finsum_eq_single _ (embDomain e x)]
  · rw [hterm, ite_eq_left rfl]
  · intro n hn
    rw [hterm, ite_eq_right hn]

variable {k : Type} [CommRing k] {d : ℕ}

def eZ (d : ℕ) : Fin 1 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (1, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Subsingleton.elim _ _) h.2⟩

def eXv (d : ℕ) : Fin 1 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (0, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Subsingleton.elim _ _) h.2⟩

theorem coeff_ev_zero_left (h : PS k 2 d) (x : Fin 1 × Fin d →₀ ℕ) :
    coeff x (ev (n := 1) ![0, pt k d 0] h) = coeff (embDomain (eZ d) x) h := by
  have hnr : ∀ i : Fin d, ((0 : Fin 2), i) ∉ Set.range (eZ d) := by
    rintro i ⟨⟨c, j⟩, hc⟩
    have h10 : (1 : Fin 2) = 0 := congrArg Prod.fst hc
    exact absurd h10 (by decide)
  apply coeff_subst_killCompl (eZ d) h
  rintro ⟨b, i⟩
  fin_cases b
  · show (0 : PS k 1 d) = killCompl (eZ d) (X ((0 : Fin 2), i))
    ext m
    rw [coeff_killCompl, coeff_X, ite_eq_right]
    · simp
    · intro hm
      have h1 := congrArg (fun g => g ((0 : Fin 2), i)) hm
      rw [Finsupp.embDomain_of_notMem_range _ _ _ (hnr i), Finsupp.single_eq_same] at h1
      exact zero_ne_one h1
  · show X ((0 : Fin 1), i) = killCompl (eZ d) (X ((1 : Fin 2), i))
    exact (killCompl_X (e := eZ d) ((0 : Fin 1), i)).symm

theorem coeff_ev_zero_right (h : PS k 2 d) (x : Fin 1 × Fin d →₀ ℕ) :
    coeff x (ev (n := 1) ![pt k d 0, 0] h) = coeff (embDomain (eXv d) x) h := by
  have hnr : ∀ i : Fin d, ((1 : Fin 2), i) ∉ Set.range (eXv d) := by
    rintro i ⟨⟨c, j⟩, hc⟩
    have h10 : (0 : Fin 2) = 1 := congrArg Prod.fst hc
    exact absurd h10 (by decide)
  apply coeff_subst_killCompl (eXv d) h
  rintro ⟨b, i⟩
  fin_cases b
  · show X ((0 : Fin 1), i) = killCompl (eXv d) (X ((0 : Fin 2), i))
    exact (killCompl_X (e := eXv d) ((0 : Fin 1), i)).symm
  · show (0 : PS k 1 d) = killCompl (eXv d) (X ((1 : Fin 2), i))
    ext m
    rw [coeff_killCompl, coeff_X, ite_eq_right]
    · simp
    · intro hm
      have h1 := congrArg (fun g => g ((1 : Fin 2), i)) hm
      rw [Finsupp.embDomain_of_notMem_range _ _ _ (hnr i), Finsupp.single_eq_same] at h1
      exact zero_ne_one h1

def swE (d : ℕ) : Fin 2 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (Fin.rev p.1, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq, Fin.rev_inj] at h
  exact Prod.ext h.1 h.2⟩

theorem ev_swap_eq (h : PS k 2 d) : ev (n := 2) ![pt k d 1, pt k d 0] h = rename (swE d) h := by
  rw [rename_eq_subst]
  show subst (fun p : Fin 2 × Fin d => (![pt k d 1, pt k d 0] : Fin 2 → Pt k 2 d) p.1 p.2) h = _
  congr 1
  funext p
  obtain ⟨a, b⟩ := p
  fin_cases a <;> rfl

theorem coeff_ev_swap (h : PS k 2 d) (x : Fin 2 × Fin d →₀ ℕ) :
    coeff (embDomain (swE d) x) (ev (n := 2) ![pt k d 1, pt k d 0] h) = coeff x h := by
  rw [ev_swap_eq, ← coeff_killCompl]
  rw [show killCompl (swE d) (rename (swE d) h) = h from DFunLike.congr_fun killCompl_comp_rename h]

end CoordinateCoefficients

end RHLean.Geometry.NativeTheta.FormalCalculus

end
