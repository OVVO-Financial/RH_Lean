import RHLean.Analysis.AlpogeThin.NativeDyadicHostCore

/-!
# Core 33: actual host degree and local stabilizer exclusion

The prime-order obstruction is a rational cyclotomic degree argument, not
a mass formula. We then transport the local unipotent finite-order
argument through a faithful matrix comparison on the SAME native host.
In particular we do not replace a single-place unipotence premise with
unipotence on full rational torsion.

Mathematical source: Levent Alpöge (with Claude), pinned upstream
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Formalism/LogVandermondeBounds/LogVandermondeProofs/PrimePowerSubgroupTrivial.lean,
Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/EqOneOfMembership.lean,
and Formalism/SharpRestriction/GlobalSchurBounds/ThickPlacesCorollaryOfAnyTranslate.lean.
The upstream source mirror states no license; attribution is retained.
The native host specialization and explicit matrix comparison are supplied here.
This does NOT prove a Siegel mass ratio, a physical moduli stabilizer
identification, or the remaining signed cost estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open NumberField Polynomial Matrix

namespace RHLean.Geometry.NativeCore33

/-- A nonidentity prime-order matrix requires at least p-1 rational
dimensions. Hermitian geometry is not needed for this restriction. -/
theorem primeOrder_le_degree (E : Type) [Field E] [NumberField E]
    (r p : ℕ) (A : Matrix (Fin r) (Fin r) E)
    (hp : p.Prime) (hA : A ^ p = 1) (hne : A ≠ 1) :
    p - 1 ≤ Module.finrank ℚ E * r := by
  let : Fact p.Prime := ⟨hp⟩
  let f : (Fin r → E) →ₗ[ℚ] (Fin r → E) :=
    (Matrix.toLin' A).restrictScalars ℚ
  have hpow : ∀ v : Fin r → E, (f ^ p) v = v := by
    intro v
    rw [Module.End.pow_apply]
    show (⇑(Matrix.toLin' A))^[p] v = v
    rw [← Module.End.pow_apply, ← Matrix.toLin'_pow, hA,
      Matrix.toLin'_one, LinearMap.id_apply]
  have hf : f ^ p = 1 := LinearMap.ext hpow
  have hm : minpoly ℚ f ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite ℚ f)
  have hd : minpoly ℚ f ∣ cyclotomic p ℚ * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hf]
  have hi := cyclotomic.irreducible_rat hp.pos
  have hcdeg : (cyclotomic p ℚ).natDegree = p - 1 := by
    rw [natDegree_cyclotomic, Nat.totient_prime hp]
  have hdeg : (minpoly ℚ f).natDegree ≤ Module.finrank ℚ E * r := by
    have h := natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f)
      (LinearMap.charpoly_monic f).ne_zero
    rw [LinearMap.charpoly_natDegree] at h
    have he : Module.finrank ℚ (Fin r → E) = Module.finrank ℚ E * r := by
      rw [Module.finrank_pi_fintype]
      simp [mul_comm]
    omega
  by_cases hc : cyclotomic p ℚ ∣ minpoly ℚ f
  · have := natDegree_le_of_dvd hc hm
    omega
  · exfalso
    apply hne
    have hcop : IsCoprime (minpoly ℚ f) (cyclotomic p ℚ) :=
      ((hi.coprime_iff_not_dvd).2 hc).symm
    have h : minpoly ℚ f ∣ X - 1 := hcop.dvd_of_dvd_mul_left hd
    have ha : aeval f (X - 1 : Polynomial ℚ) = 0 := by
      obtain ⟨Q, hQ⟩ := h
      rw [hQ, map_mul, minpoly.aeval, zero_mul]
    have hf1 : f = 1 := by simpa [sub_eq_zero] using ha
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    refine LinearMap.ext fun v => ?_
    simpa [f] using LinearMap.congr_fun hf1 v

/-- A prime-power torsion element is trivial above the actual rank budget. -/
theorem primePower_eq_one (E : Type) [Field E] [NumberField E]
    (r p : ℕ) (hp : p.Prime) (hbig : Module.finrank ℚ E * r < p - 1)
    (a : ℕ) (A : Matrix (Fin r) (Fin r) E) (hA : A ^ (p ^ a) = 1) :
    A = 1 := by
  induction a with
  | zero => simpa using hA
  | succ a ih =>
    apply ih
    by_contra hne
    have hpow : (A ^ (p ^ a)) ^ p = 1 := by
      rw [← pow_mul, ← pow_succ, hA]
    have := primeOrder_le_degree E r p (A ^ (p ^ a)) hp hpow hne
    omega

section Local

variable {O : Type} [CommRing O] [IsLocalRing O] {r : ℕ}

/-- The geometric series is a unit when the matrix reduces to identity
and the exponent is a unit in the genuine local ring. -/
theorem local_eq_one_of_red_eq_one
    {M : Matrix (Fin r) (Fin r) O}
    (hM : M.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) = 1)
    {m : ℕ} (hm : IsUnit (m : O)) (hpow : M ^ m = 1) : M = 1 := by
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
  have hM' : π.mapMatrix M = 1 := hM
  have h1 : (∑ i ∈ Finset.range m, M ^ i) * (M - 1) = 0 := by
    rw [geom_sum_mul, hpow, sub_self]
  have h2 : π.mapMatrix (∑ i ∈ Finset.range m, M ^ i) =
      (m : Matrix (Fin r) (Fin r) _) := by
    rw [map_sum]
    simp only [map_pow, hM', one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have h3 : IsUnit (π (∑ i ∈ Finset.range m, M ^ i).det) := by
    rw [RingHom.map_det, h2, ← Matrix.isUnit_iff_isUnit_det]
    have := (hm.map π).map
      (algebraMap _ (Matrix (Fin r) (Fin r) (O ⧸ IsLocalRing.maximalIdeal O)))
    simpa using this
  have h4 : IsUnit (∑ i ∈ Finset.range m, M ^ i).det := by
    by_contra h
    have hz : π (∑ i ∈ Finset.range m, M ^ i).det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [hz] at h3
    exact not_isUnit_zero h3
  have hu : IsUnit (∑ i ∈ Finset.range m, M ^ i) :=
    (Matrix.isUnit_iff_isUnit_det _).2 h4
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 h1)

/-- A single local reduction is enough to remove the coprime part of
the actual finite order. No rational-level torsion assumption is made. -/
theorem local_unipotent_primePower
    {p : ℕ} (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O)
    {M : Matrix (Fin r) (Fin r) O}
    (hM : IsNilpotent (M.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) - 1))
    {n : ℕ} (hn : 0 < n) (hpow : M ^ n = 1) :
    ∃ a : ℕ, M ^ (p ^ a) = 1 := by
  obtain ⟨s, hs⟩ := hM
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
  have h0 : (p : Matrix (Fin r) (Fin r) (O ⧸ IsLocalRing.maximalIdeal O)) = 0 := by
    have hz : (p : O ⧸ IsLocalRing.maximalIdeal O) = 0 := by
      rw [← map_natCast π]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hpm
    rw [← map_natCast (algebraMap (O ⧸ IsLocalRing.maximalIdeal O) _), hz, map_zero]
  have hs' : (π.mapMatrix M - 1) ^ s = 0 := hs
  have hbin := (Commute.one_right (π.mapMatrix M - 1)).add_pow_prime_pow_eq hp s
  have hsle : s ≤ p ^ s := (Nat.lt_pow_self hp.one_lt).le
  rw [sub_add_cancel, h0, pow_eq_zero_of_le hsle hs'] at hbin
  have h1 : (π.mapMatrix M) ^ (p ^ s) = 1 := by simpa using hbin
  obtain ⟨a, m, hm, hn'⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := n) hn.ne' p hp.ne_one
  refine ⟨s + a, local_eq_one_of_red_eq_one (m := m) ?_ ?_ ?_⟩
  · change π.mapMatrix _ = 1
    rw [map_pow, pow_add, pow_mul, h1, one_pow]
  · have hc : IsCoprime (m : O) (p : O) := by
      have := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm
      simpa using this.map (Int.castRingHom O)
    by_contra h
    obtain ⟨u, v, huv⟩ := hc
    have hz : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [← huv]
      exact add_mem (Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 h))
        (Ideal.mul_mem_left _ _ hpm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hz)
  · rw [← pow_mul, pow_add, mul_assoc, ← hn', mul_comm, pow_mul, hpow, one_pow]

end Local

/-- Transport along an independently given faithful local matrix
comparison, retaining the original finite-order action. -/
theorem local_unipotent_eq_one
    (E O L : Type) [Field E] [NumberField E] [CommRing O] [IsLocalRing O] [Field L]
    (r p : ℕ) (hp : p.Prime) (hbig : Module.finrank ℚ E * r < p - 1)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (iE : E →+* L) (iO : O →+* L) (hiO : Function.Injective iO)
    (A : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) O)
    (P : GL (Fin r) L)
    (hTie : iO.mapMatrix M * (P : Matrix (Fin r) (Fin r) L) =
      (P : Matrix (Fin r) (Fin r) L) * iE.mapMatrix A)
    (hM : IsNilpotent (M.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) - 1))
    (n : ℕ) (hn : 0 < n) (hA : A ^ n = 1) : A = 1 := by
  have hpowers : ∀ t : ℕ, iO.mapMatrix (M ^ t) * (P : Matrix (Fin r) (Fin r) L) =
      (P : Matrix (Fin r) (Fin r) L) * iE.mapMatrix (A ^ t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      simp only [pow_succ, map_mul]
      calc
        _ = iO.mapMatrix (M ^ t) * (iO.mapMatrix M * (P : Matrix (Fin r) (Fin r) L)) :=
          mul_assoc _ _ _
        _ = (iO.mapMatrix (M ^ t) * (P : Matrix (Fin r) (Fin r) L)) * iE.mapMatrix A := by
          rw [hTie, mul_assoc]
        _ = _ := by rw [ih, mul_assoc]
  have hOinj : Function.Injective
      (iO.mapMatrix : Matrix (Fin r) (Fin r) O →+* Matrix (Fin r) (Fin r) L) := by
    intro B C h
    ext i j
    exact hiO (congrArg (fun X : Matrix (Fin r) (Fin r) L => X i j) h)
  have hEinj : Function.Injective
      (iE.mapMatrix : Matrix (Fin r) (Fin r) E →+* Matrix (Fin r) (Fin r) L) := by
    intro B C h
    ext i j
    exact iE.injective (congrArg (fun X : Matrix (Fin r) (Fin r) L => X i j) h)
  have hMn : M ^ n = 1 := by
    apply hOinj
    rw [map_one]
    have ht := hpowers n
    rw [hA, map_one, mul_one] at ht
    have hh := congrArg (fun B : Matrix (Fin r) (Fin r) L =>
      B * (↑(P⁻¹) : Matrix (Fin r) (Fin r) L)) ht
    simpa only [mul_assoc, Units.mul_inv, mul_one] using hh
  obtain ⟨a, ha⟩ := local_unipotent_primePower hp hpm hM hn hMn
  apply primePower_eq_one E r p hp hbig a A
  apply hEinj
  rw [map_one]
  have ht := hpowers (p ^ a)
  rw [ha, map_one, one_mul] at ht
  have hh := congrArg (fun B : Matrix (Fin r) (Fin r) L =>
    (↑(P⁻¹) : Matrix (Fin r) (Fin r) L) * B) ht.symm
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using hh

end RHLean.Geometry.NativeCore33

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

/-- Core 33's unconditional prime-order restriction, specialized to the
original constructed dyadic host; no auxiliary chosen field. -/
theorem nativeCore33_primeOrder_le
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) (r p : ℕ)
    (A : Matrix (Fin r) (Fin r) (nativeDyadicHostRaw e q d he hH).E)
    (hp : p.Prime) (hA : A ^ p = 1) (hne : A ≠ 1) :
    p - 1 ≤ 4 * 2 ^ e * r := by
  have h := Geometry.NativeCore33.primeOrder_le_degree
    (nativeDyadicHostRaw e q d he hH).E r p A hp hA hne
  rwa [nativeDyadicHostRaw_finrank_E, nativeDyadicFrame_ord] at h

/-- Same-host, one-place unipotence exclusion. The local integral matrix
and its comparison must come from the real stabilizer action, not an
assigned witness. Its dimension cost is now the actual native field degree. -/
theorem nativeCore33_localStabilizer_eq_one
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (O L : Type) [CommRing O] [IsLocalRing O] [Field L]
    (r p : ℕ) (hp : p.Prime) (hbig : 4 * 2 ^ e * r < p - 1)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (iE : (nativeDyadicHostRaw e q d he hH).E →+* L)
    (iO : O →+* L) (hiO : Function.Injective iO)
    (A : Matrix (Fin r) (Fin r) (nativeDyadicHostRaw e q d he hH).E)
    (M : Matrix (Fin r) (Fin r) O) (P : GL (Fin r) L)
    (hTie : iO.mapMatrix M * (P : Matrix (Fin r) (Fin r) L) =
      (P : Matrix (Fin r) (Fin r) L) * iE.mapMatrix A)
    (hM : IsNilpotent (M.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) - 1))
    (n : ℕ) (hn : 0 < n) (hA : A ^ n = 1) : A = 1 := by
  have hd : Module.finrank ℚ (nativeDyadicHostRaw e q d he hH).E * r < p - 1 := by
    rw [nativeDyadicHostRaw_finrank_E, nativeDyadicFrame_ord]
    exact hbig
  exact Geometry.NativeCore33.local_unipotent_eq_one
    (nativeDyadicHostRaw e q d he hH).E O L r p hp hd hpm
    iE iO hiO A M P hTie hM n hn hA

end RHLean.Analysis.AlpogeThin

end
