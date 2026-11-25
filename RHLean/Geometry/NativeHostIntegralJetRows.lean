import RHLean.Geometry.NativePrescribedPolarizationLattice
import RHLean.Geometry.NativeThetaFiniteFamily
import RHLean.Geometry.NativeThetaLatticeNormalization

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial
open scoped BigOperators

namespace RHLean.Geometry.NativeTheta.Paired

variable {E K : Type} [Field E] [NumberField E] [IsCMField E] [Field K] [NumberField K]
    {T J σ : Type} [Fintype J] {p q n : ℕ}

/-- Substitute polynomial linear combinations of genuine Hermitian lattice
directions in each of the two sorts of rows. A constant parameter permits
translation before taking a coefficient. -/
def hermitianJetPoint (τ : T → E →+* K)
    (w : T → (Fin p ⊕ Fin q) → J → Fin n → E)
    (g : J → MvPolynomial σ (𝓞 K)) :
    Var T p q (Fin n) → MvPolynomial σ K :=
  fun k => ∑ s, C (τ k.1 (match k.2.1 with
    | .inl a => IsCMField.complexConj E (w k.1 (.inl a) s k.2.2)
    | .inr b => w k.1 (.inr b) s k.2.2)) *
    MvPolynomial.map (algebraMap (𝓞 K) K) (g s)

omit [NumberField K] in
private theorem contract_jet_row {κ : Type} [Fintype κ]
    (v : κ → K) (w : J → κ → K) (g : J → MvPolynomial σ K) :
    (∑ k, C (v k) * ∑ s, C (w s k) * g s) =
      ∑ s, C (∑ k, v k * w s k) * g s := by
  classical
  calc
    _ = ∑ k, ∑ s, (C (v k) * C (w s k)) * g s := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ s, ∑ k, (C (v k) * C (w s k)) * g s := Finset.sum_comm
    _ = _ := by simp only [map_sum, map_mul, Finset.sum_mul]

/-- On the native integral harmonic generators, a Hermitian-lattice
substitution has every coefficient in the original ring of integers.
This includes affine polynomial parameterizations of any number of rows. -/
theorem latticePolynomials_hermitianJet_integral
    (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y))
    (w : T → (Fin p ⊕ Fin q) → J → Fin n → E)
    (hw : ∀ t r s, w t r s ∈ Λ) (g : J → MvPolynomial σ (𝓞 K))
    {P : Poly K T p q (Fin n)} (hP : P ∈ latticePolynomials τ Λ) :
    ∃ Q : MvPolynomial σ (𝓞 K), MvPolynomial.map (algebraMap (𝓞 K) K) Q =
      aeval (hermitianJetPoint τ w g) P := by
  classical
  let emb := algebraMap (𝓞 K) K
  have lift_row (t : T) (h : J → E) (hh : ∀ s, IsIntegral ℤ (h s)) :
      ∃ Q : MvPolynomial σ (𝓞 K), MvPolynomial.map emb Q =
        ∑ s, C (τ t (h s)) * MvPolynomial.map emb (g s) := by
    let z : J → 𝓞 K := fun s => ⟨τ t (h s), (hh s).map (τ t).toIntAlgHom⟩
    refine ⟨∑ s, C (z s) * g s, ?_⟩
    simp only [map_sum, map_mul, MvPolynomial.map_C]
    rfl
  unfold latticePolynomials at hP
  induction hP using Algebra.adjoin_induction with
  | mem u hu =>
    rcases hu with ⟨t, a, v, hv, rfl⟩ | ⟨t, b, v, hv, rfl⟩
    · have heval :
          aeval (hermitianJetPoint τ w g) (xForm t a (fun k => τ t (v k))) =
            ∑ s, C (τ t (hermPairing E n v (w t (.inl a) s))) *
              MvPolynomial.map emb (g s) := by
        simp only [xForm_apply, map_sum, map_mul, aeval_C, aeval_X,
          MvPolynomial.algebraMap_eq, hermitianJetPoint, xVar]
        rw [contract_jet_row]
        simp only [hermPairing_apply, map_sum, map_mul]
        rfl
      rw [heval]
      exact lift_row t _ (fun s => hint _ hv _ (hw t (.inl a) s))
    · have heval :
          aeval (hermitianJetPoint τ w g)
              (yForm t b (fun k => τ t (IsCMField.complexConj E (v k)))) =
            ∑ s, C (τ t (hermPairing E n (w t (.inr b) s) v)) *
              MvPolynomial.map emb (g s) := by
        simp only [yForm_apply, map_sum, map_mul, aeval_C, aeval_X,
          MvPolynomial.algebraMap_eq, hermitianJetPoint, yVar]
        rw [contract_jet_row]
        refine Finset.sum_congr rfl fun s _ => ?_
        have hcoeff :
            (∑ k, τ t (IsCMField.complexConj E (v k)) * τ t (w t (.inr b) s k)) =
              τ t (hermPairing E n (w t (.inr b) s) v) := by
          simp only [hermPairing_apply, map_sum, map_mul]
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
        rw [hcoeff]
      rw [heval]
      exact lift_row t _ (fun s => hint _ (hw t (.inr b) s) _ hv)
  | algebraMap r =>
    refine ⟨C r, ?_⟩
    rw [MvPolynomial.map_C]
    change C (algebraMap (𝓞 K) K r) =
      aeval _ (C (algebraMap (𝓞 K) K r))
    rw [aeval_C, MvPolynomial.algebraMap_eq]
  | add P Q _ _ hP hQ =>
    obtain ⟨P₀, hP₀⟩ := hP
    obtain ⟨Q₀, hQ₀⟩ := hQ
    exact ⟨P₀ + Q₀, by rw [map_add, map_add, hP₀, hQ₀]⟩
  | mul P Q _ _ hP hQ =>
    obtain ⟨P₀, hP₀⟩ := hP
    obtain ⟨Q₀, hQ₀⟩ := hQ
    exact ⟨P₀ * Q₀, by rw [map_mul, map_mul, hP₀, hQ₀]⟩

theorem isIntegral_coeff_hermitianJet
    (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y))
    (w : T → (Fin p ⊕ Fin q) → J → Fin n → E)
    (hw : ∀ t r s, w t r s ∈ Λ) (g : J → MvPolynomial σ (𝓞 K))
    {P : Poly K T p q (Fin n)} (hP : P ∈ latticePolynomials τ Λ)
    (α : σ →₀ ℕ) :
    IsIntegral ℤ ((aeval (hermitianJetPoint τ w g) P).coeff α) := by
  obtain ⟨Q, hQ⟩ := latticePolynomials_hermitianJet_integral τ Λ hint w hw g hP
  rw [← hQ, coeff_map]
  exact (Q.coeff α).isIntegral_coe

/-- Apply the test with the original self-duality assumption of the evaluated
finite theta family. -/
theorem isIntegral_coeff_hermitianJet_of_unimodular
    (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E)) (hU : Lattice.Unimodular Λ)
    (w : T → (Fin p ⊕ Fin q) → J → Fin n → E)
    (hw : ∀ t r s, w t r s ∈ Λ) (g : J → MvPolynomial σ (𝓞 K))
    {P : Poly K T p q (Fin n)} (hP : P ∈ latticePolynomials τ Λ)
    (α : σ →₀ ℕ) :
    IsIntegral ℤ ((aeval (hermitianJetPoint τ w g) P).coeff α) :=
  isIntegral_coeff_hermitianJet τ Λ (fun x hx => ((Lattice.unimodular_iff Λ).mp hU x).mp hx)
    w hw g hP α

end RHLean.Geometry.NativeTheta.Paired

end

noncomputable section
open NumberField Matrix
open scoped Pointwise nonZeroDivisors BigOperators

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits

/-- A row on the actual prescribed lattice is integral exactly when each entry
belongs to the half-different ideal. The test uses the original inverse-ideal
coordinates of the host. -/
theorem prescribedLattice_row_integral_iff {φ : Frame} (H : HostRaw φ)
    (B : Ideal (𝓞 H.E)) (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m : ℕ) (c : Fin (k + m - 1) → H.E) :
    (∀ x ∈ prescribedLattice H B k m, (∑ i, c i * x i) ∈ (algebraMap (𝓞 H.E) H.E).range) ↔
      ∀ i, c i ∈ (B : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  classical
  have hn : coefficientIdeal H B ≠ 0 := inv_ne_zero (halfDifferent_ne_zero H B hB).1
  have hdual (z : H.E) : z ∈ (B : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∀ y ∈ coefficientIdeal H B, z * y ∈ (algebraMap (𝓞 H.E) H.E).range := by
    have h := FractionalIdeal.mem_inv_iff (x := z) hn
    rw [show (coefficientIdeal H B)⁻¹ = (B : FractionalIdeal (𝓞 H.E)⁰ H.E) from inv_inv _] at h
    exact h.trans ⟨fun hz y hy => (FractionalIdeal.mem_one_iff _).mp (hz y hy),
      fun hz y hy => (FractionalIdeal.mem_one_iff _).mpr (hz y hy)⟩
  constructor
  · intro h i
    apply (hdual _).mpr
    intro y hy
    have hx : Pi.single i y ∈ prescribedLattice H B k m := by
      apply (mem_twistedLattice H B _ _).mpr
      intro j
      by_cases hj : j = i
      · subst j
        simpa only [Pi.single_eq_same] using hy
      · rw [Pi.single_eq_of_ne hj]
        exact (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).zero_mem
    have ht := h (Pi.single i y) hx
    change dotProduct c (Pi.single i y) ∈ (algebraMap (𝓞 H.E) H.E).range at ht
    rw [dotProduct_single] at ht
    exact ht
  · intro h x hx
    apply (algebraMap (𝓞 H.E) H.E).range.sum_mem
    intro i _
    exact ((hdual _).mp (h i)) (x i) ((mem_twistedLattice H B _ _).mp hx i)

open RHLean.Geometry.NativeTheta

theorem prescribedLattice_top_eq_standard {φ : Frame} (H : HostRaw φ) (k m : ℕ) :
    prescribedLattice H ⊤ k m = Lattice.standard H.E (k + m - 1) := by
  change twistedLattice H ⊤ (k + m - 1) = _
  rw [twistedLattice_eq_pi]
  simp [coefficientIdeal, Lattice.standard]

/-- The unweighted Hermitian form of the native polynomial family is integral
on a nonzero-rank prescribed host exactly when the half-different is trivial. -/
theorem prescribedLattice_unweighted_integral_iff {φ : Frame} (H : HostRaw φ)
    [IsCMField H.E] (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m : ℕ) (i : Fin (k + m - 1)) :
    (∀ x ∈ prescribedLattice H B k m, ∀ y ∈ prescribedLattice H B k m,
      IsIntegral ℤ (Paired.hermPairing H.E (k + m - 1) x y)) ↔ B = ⊤ := by
  classical
  constructor
  · intro h
    have h1 : (1 : H.E) ∈ coefficientIdeal H B :=
      FractionalIdeal.one_mem_inv_coe_ideal
        (FractionalIdeal.coeIdeal_ne_zero.mp (halfDifferent_ne_zero H B hB).1)
    have hei : Pi.single i (1 : H.E) ∈ prescribedLattice H B k m := by
      apply (mem_twistedLattice H B _ _).mpr
      intro j
      by_cases hj : j = i
      · subst j
        simpa using h1
      · rw [Pi.single_eq_of_ne hj]
        exact (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).zero_mem
    have hi := (prescribedLattice_row_integral_iff H B hB k m (Pi.single i 1)).mp
      (fun x hx => by
        have hx' : IsIntegral ℤ (x i) := by
          simpa [Paired.hermPairing_apply, Pi.single_apply] using h x hx _ hei
        change dotProduct (Pi.single i (1 : H.E)) x ∈ (algebraMap (𝓞 H.E) H.E).range
        rw [single_dotProduct, one_mul]
        exact (Lattice.mem_range_iff_integral _).mpr hx') i
    simp only [Pi.single_eq_same] at hi
    obtain ⟨a, ha, hea⟩ := (FractionalIdeal.mem_coeIdeal _).mp hi
    have ha1 : a = 1 := RingOfIntegers.ext (by simpa using hea)
    exact (Ideal.eq_top_iff_one _).mpr (ha1 ▸ ha)
  · rintro rfl
    rw [prescribedLattice_top_eq_standard]
    exact fun x hx =>
      ((Lattice.unimodular_iff _).mp Lattice.standard_unimodular x).mp hx

/-- The actual relative different misses every prime above this whole
rational-prime class. -/
theorem relativeDifferent_not_le_of_prime {φ : Frame} (H : HostAx φ)
    (p : ℕ) (hp : ¬ p ∣ H.QS * H.q) (P : Ideal (𝓞 H.E))
    [hP : P.IsPrime] [hlo : P.LiesOver (Ideal.span {(p : ℤ)})] :
    ¬ differentIdeal (𝓞 H.K) (𝓞 H.E) ≤ P := by
  intro hle
  have hm := H.der.diffSupport P hP (Ideal.dvd_iff_le.mpr hle)
  have hcast : ((H.QS * H.q : ℕ) : ℤ) ∈ P.under ℤ := by
    change algebraMap ℤ (𝓞 H.E) ((H.QS * H.q : ℕ) : ℤ) ∈ P
    simpa only [map_natCast] using hm
  rw [← hlo.over, Ideal.mem_span_singleton] at hcast
  exact hp (by exact_mod_cast hcast)

/-- Both half-different factors become unit ideals at every prime above a
rational prime outside the actual relative-different support. -/
theorem halfDifferent_local_eq_top {φ : Frame} (H : HostAx φ) (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (p : ℕ) (hp : ¬ p ∣ H.QS * H.q) (P : Ideal (𝓞 H.E))
    [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.map (algebraMap (𝓞 H.E) (Localization.AtPrime P)) B = ⊤ ∧
      Ideal.map (algebraMap (𝓞 H.E) (Localization.AtPrime P)) (H.conj • B) = ⊤ := by
  have hD := relativeDifferent_not_le_of_prime H p hp P
  rw [hB] at hD
  constructor
  · apply IsLocalization.AtPrime.map_eq_top_of_not_le
    exact fun h => hD (Ideal.mul_le_left.trans h)
  · apply IsLocalization.AtPrime.map_eq_top_of_not_le
    exact fun h => hD (Ideal.mul_le_right.trans h)

/-- A member of the actual relative different clears every integral-weight
Hermitian pairing on the prescribed host, including its signed diagonal. -/
theorem prescribedLattice_weighted_herm_integral {φ : Frame} (H : HostRaw φ)
    (B : Ideal (𝓞 H.E)) (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (a : 𝓞 H.E) (ha : a ∈ differentIdeal (𝓞 H.K) (𝓞 H.E))
    (k m : ℕ) (c : Fin (k + m - 1) → 𝓞 H.E)
    (x y : prescribedLattice H B k m) :
    IsIntegral ℤ ((a : H.E) * ∑ i, (c i : H.E) * H.conj (x.1 i) * y.1 i) := by
  have h0 := FractionalIdeal.coeIdeal_ne_zero.mp (halfDifferent_ne_zero H B hB).1
  have hD0 : ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) :
      FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (differentIdeal_ne_bot (A := 𝓞 H.K) (B := 𝓞 H.E))
  rw [Finset.mul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  have hxi := (mem_twistedLattice H B _ _).mp x.2 i
  have hyi := (mem_twistedLattice H B _ _).mp y.2 i
  have hconj := (NativeRawHostDifferent.kc_mem_inv_smul H H.conj B h0 (x.1 i)).mpr hxi
  have hxy : H.conj (x.1 i) * y.1 i ∈
      ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ := by
    rw [hB, FractionalIdeal.coeIdeal_mul, mul_inv]
    simpa only [mul_comm] using FractionalIdeal.mul_mem_mul hyi hconj
  have hval := (FractionalIdeal.mem_inv_iff hD0).mp hxy (a : H.E)
    (FractionalIdeal.mem_coeIdeal_of_mem _ ha)
  have hint := (Lattice.mem_range_iff_integral _).mp ((FractionalIdeal.mem_one_iff _).mp hval)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using (c i).isIntegral_coe.mul hint

/-- The same denominator, a unit at the chosen prime, works for every
integral diagonal and every pair of host vectors. -/
theorem prescribedLattice_weighted_herm_local {φ : Frame} (H : HostAx φ)
    (B : Ideal (𝓞 H.E)) (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (p : ℕ) (hp : ¬ p ∣ H.QS * H.q) (P : Ideal (𝓞 H.E))
    [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ a : 𝓞 H.E, a ∉ P ∧ ∀ (k m : ℕ) (c : Fin (k + m - 1) → 𝓞 H.E)
      (x y : prescribedLattice H.toHostRaw B k m),
      IsIntegral ℤ ((a : H.E) * ∑ i, (c i : H.E) * H.conj (x.1 i) * y.1 i) := by
  have hD := relativeDifferent_not_le_of_prime H p hp P
  change ¬ ∀ a, a ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) → a ∈ P at hD
  push_neg at hD
  obtain ⟨a, ha, hnot⟩ := hD
  exact ⟨a, hnot, prescribedLattice_weighted_herm_integral H.toHostRaw B hB a ha⟩

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end

namespace RHLean.Geometry.NativeTheta

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq I]

/-- Evaluate the original scaled edge pairing on its adapted source basis
and the dual target basis with the two host cutoffs. The exponents are
integers because the torus weights before subtraction can be negative. -/
theorem adaptedEdge_pairing (b : Module.Basis I K V) (w p : K)
    (hw : w ≠ 0) (hp : p = w ^ 2) (A : ℤ) (π : I → ℤ)
    (tS tT : ℤ) (i j : I) :
    (((w ^ (-min (A - π j) tT) * p ^ (-π j)) • b.coord j : V →ₗ[K] K)
        ((p ^ A) • ((w ^ (-min (A - π i) tS)) • b i))) =
      if i = j then w ^ (max (A - π i - tS) 0 + max (A - π i - tT) 0) else 0 := by
  have hpz (a : ℤ) : p ^ a = w ^ (2 * a) := by
    calc
      p ^ a = (w ^ (2 : ℤ)) ^ a := by simpa using congrArg (fun z : K => z ^ a) hp
      _ = _ := (zpow_mul w (2 : ℤ) a).symm
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left (rfl : i = i)]
    simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, hpz, ← zpow_add₀ hw]
    congr 1
    omega
  · simp [LinearMap.smul_apply, map_smul, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, hij]

theorem adaptedEdge_pairing_same_cutoff (b : Module.Basis I K V) (w p : K)
    (hw : w ≠ 0) (hp : p = w ^ 2) (A : ℤ) (π : I → ℤ)
    (t : ℤ) (i j : I) :
    (((w ^ (-min (A - π j) t) * p ^ (-π j)) • b.coord j : V →ₗ[K] K)
        ((p ^ A) • ((w ^ (-min (A - π i) t)) • b i))) =
      if i = j then p ^ (max (A - π i - t) 0) else 0 := by
  rw [adaptedEdge_pairing b w p hw hp A π t t i j]
  by_cases hij : i = j
  · simp only [ite_eq_left hij]
    rw [← two_mul, zpow_mul]
    simpa using congrArg (fun z : K => z ^ (max (A - π i - t) 0)) hp.symm
  · simp only [ite_eq_right hij]

end RHLean.Geometry.NativeTheta
