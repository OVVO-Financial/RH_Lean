import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import RHLean.Geometry.NativeThetaIntegralJets

/-!
# Signed binomial inversion on finite divisor-closed exponent sets

Translations by one and minus one preserve the entire box below each
column. Summing over this box proves the two inverse identities and
the exact absolute column mass, independently of any physical restriction.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativePrimeExponentJet

open RHLean.Geometry.NativeTheta

private def weight (t : ℤ) (a b : ℕ) : ℤ :=
  (Polynomial.taylor t (Polynomial.monomial b (1 : ℤ))).coeff a

private theorem weight_binomial (t : ℤ) (a b : ℕ) :
    weight t a b = (b.choose a : ℤ) * t ^ (b - a) := by
  simp only [weight, Polynomial.taylor_coeff, Polynomial.hasseDeriv_monomial,
    mul_one, Polynomial.eval_monomial]

private theorem weight_self_zero (a b : ℕ) :
    weight 0 a b = if a = b then 1 else 0 := by
  simp only [weight, Polynomial.taylor_zero, Polynomial.coeff_monomial]
  by_cases h : b = a
  · subst b
    rfl
  · rw [if_neg h, if_neg h.symm]

private theorem weight_comp (s t : ℤ) (a b : ℕ) :
    ∑ v : Fin (b + 1), weight s a v * weight t v b = weight (s + t) a b := by
  let Q := Polynomial.taylor t (Polynomial.monomial b (1 : ℤ))
  have hd : Q.natDegree < b + 1 := by
    simpa only [Q, Polynomial.natDegree_taylor,
      Polynomial.natDegree_monomial_eq b (one_ne_zero : (1 : ℤ) ≠ 0)] using Nat.lt_succ_self b
  have hrep : Q = ∑ v : Fin (b + 1), Q.coeff v • Polynomial.monomial v (1 : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => Q.coeff i • Polynomial.monomial i (1 : ℤ))]
    simpa only [Polynomial.smul_monomial, smul_eq_mul, mul_one] using Q.as_sum_range' _ hd
  have hand := congrArg (fun f : Polynomial ℤ => (Polynomial.taylor s f).coeff a) hrep
  simp only [map_sum, map_smul, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    smul_eq_mul] at hand
  change (∑ v : Fin (b + 1), (Polynomial.taylor s (Polynomial.monomial v (1 : ℤ))).coeff a *
      Q.coeff v) = (Polynomial.taylor (s + t) (Polynomial.monomial b (1 : ℤ))).coeff a
  rw [← Polynomial.taylor_taylor]
  exact (Finset.sum_congr rfl fun v _ => mul_comm _ _).trans hand.symm

variable {σ I : Type} [Fintype σ] [Fintype I]

/-- Every exponent vector below a selected column has a row in the same family. -/
def DivisorClosed (e : I → σ →₀ ℕ) : Prop :=
  ∀ h v, v ≤ e h → ∃ j, e j = v

private def boxEquiv (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (hclosed : DivisorClosed e) (h : I) :
    {j : I // e j ≤ e h} ≃ ((p : σ) → Fin (e h p + 1)) := by
  let f (j : {j : I // e j ≤ e h}) (p : σ) : Fin (e h p + 1) :=
    ⟨e j.val p, Nat.lt_succ_of_le (j.property p)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro j k hjk
    exact Subtype.ext (he (Finsupp.ext fun p => congrArg Fin.val (congrFun hjk p)))
  · intro x
    let v : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => (x p).val
    have hv : v ≤ e h := fun p => Nat.le_of_lt_succ (x p).isLt
    obtain ⟨j, hj⟩ := hclosed h v hv
    refine ⟨⟨j, hj.symm ▸ hv⟩, funext fun p => Fin.ext ?_⟩
    exact congrArg (fun w : σ →₀ ℕ => w p) hj

private theorem column_sum (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (hclosed : DivisorClosed e) (h : I) (f : σ → ℕ → ℕ → ℤ)
    (hz : ∀ p i j, j < i → f p i j = 0) :
    ∑ i, ∏ p, f p (e i p) (e h p) =
      ∏ p, ∑ v : Fin (e h p + 1), f p v (e h p) := by
  classical
  let g (i : I) := ∏ p, f p (e i p) (e h p)
  have hzero (i : {i : I // ¬e i ≤ e h}) : g i.val = 0 := by
    have hb : ¬∀ p, e i.val p ≤ e h p := i.property
    obtain ⟨p, hp⟩ := not_forall.mp hb
    exact Finset.prod_eq_zero (Finset.mem_univ p) (hz p _ _ (Nat.lt_of_not_ge hp))
  calc
    _ = ∑ i : {i : I // e i ≤ e h}, g i.val := by
      change (∑ i, g i) = _
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => e j ≤ e h) g]
      simp only [hzero, Finset.sum_const_zero, add_zero]
    _ = ∑ v : (p : σ) → Fin (e h p + 1), ∏ p, f p (v p) (e h p) :=
      Fintype.sum_equiv (boxEquiv e he hclosed h) _ _ fun _ => rfl
    _ = _ := by
      symm
      simpa using (Finset.prod_univ_sum (fun p : σ => (Finset.univ : Finset (Fin (e h p + 1))))
        (fun p v => f p v (e h p)))

/-- Integral Hasse translation on the original finite exponent list. -/
def translation (e : I → σ →₀ ℕ) (s : ℤ) : Matrix I I ℤ :=
  IntegralJets.jetMatrix (fun _ => s) e

omit [Fintype I] in
theorem translation_apply (e : I → σ →₀ ℕ) (s : ℤ) (i j : I) :
    translation e s i j = ∏ p, ((e j p).choose (e i p) : ℤ) * s ^ (e j p - e i p) :=
  IntegralJets.mixedTaylorWeight_eq_binomial _ _ _

/-- The restricted intermediate-exponent convolution is exactly translation. -/
theorem translation_mul (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (hclosed : DivisorClosed e) (s t : ℤ) :
    translation e s * translation e t = translation e (s + t) := by
  classical
  ext i h
  change (∑ j, (∏ p, weight s (e i p) (e j p)) * ∏ p, weight t (e j p) (e h p)) =
    ∏ p, weight (s + t) (e i p) (e h p)
  simp only [← Finset.prod_mul_distrib]
  rw [column_sum e he hclosed h (fun p a b => weight s (e i p) a * weight t a b)
    (fun p a b hab => by simp [weight_binomial, Nat.choose_eq_zero_of_lt hab])]
  exact Finset.prod_congr rfl fun p _ => weight_comp s t (e i p) (e h p)

omit [Fintype I] in
theorem translation_zero [DecidableEq I] (e : I → σ →₀ ℕ) (he : Function.Injective e) :
    translation e 0 = 1 := by
  classical
  ext i j
  change (∏ p, weight 0 (e i p) (e j p)) = (1 : Matrix I I ℤ) i j
  rw [Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp [weight_self_zero]
  · have hne : ¬∀ p, e i p = e j p := fun hw => h (he (Finsupp.ext hw))
    obtain ⟨p, hp⟩ := not_forall.mp hne
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by rw [weight_self_zero, ite_eq_right hp])

/-- Both integer matrix inverse identities on the given divisor-closed family. -/
theorem signed_inverse [DecidableEq I] (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (hclosed : DivisorClosed e) :
    translation e 1 * translation e (-1) = 1 ∧ translation e (-1) * translation e 1 = 1 := by
  constructor <;> rw [translation_mul e he hclosed] <;> norm_num [translation_zero e he]

theorem det_one [DecidableEq I] (e : I → σ →₀ ℕ) (he : Function.Injective e) :
    (translation e 1).det = 1 := IntegralJets.jetMatrix_det _ e he

theorem unsigned_entry (e : I → σ →₀ ℕ) (i j : I) :
    translation e 1 i j = ∏ p, ((e j p).choose (e i p) : ℤ) := by
  simp only [translation_apply, one_pow, mul_one]

theorem entry_zero_of_not_le (e : I → σ →₀ ℕ) (s : ℤ) {i j : I} (h : ¬e i ≤ e j) :
    translation e s i j = 0 := by
  classical
  obtain ⟨p, hp⟩ := not_forall.mp (show ¬∀ p, e i p ≤ e j p from h)
  rw [translation_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ p) (by rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hp), Nat.cast_zero, zero_mul])

theorem signed_entry (e : I → σ →₀ ℕ) {i j : I} (h : e i ≤ e j) :
    translation e (-1) i j = (-1 : ℤ) ^ ((e j).degree - (e i).degree) * translation e 1 i j := by
  have hs : (∑ p, (e j p - e i p)) + (∑ p, e i p) = ∑ p, e j p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => Nat.sub_add_cancel (h p)
  have hn : (∑ p, (e j p - e i p)) = (e j).degree - (e i).degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    omega
  rw [translation_apply, unsigned_entry, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hn, mul_comm]

theorem abs_signed_entry (e : I → σ →₀ ℕ) (i j : I) :
    |translation e (-1) i j| = translation e 1 i j := by
  by_cases h : e i ≤ e j
  · rw [signed_entry e h, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_nonneg (by rw [unsigned_entry]; positivity)]
  · rw [entry_zero_of_not_le e (-1) h, entry_zero_of_not_le e 1 h, abs_zero]

/-- The absolute column mass for either sign is exactly the binary power
of the total prime multiplicity. -/
theorem column_mass (e : I → σ →₀ ℕ) (he : Function.Injective e)
    (hclosed : DivisorClosed e) (j : I) :
    (∑ i, |translation e (-1) i j|) = (2 : ℤ) ^ (e j).degree ∧
    (∑ i, |translation e 1 i j|) = (2 : ℤ) ^ (e j).degree := by
  have hJ : (∑ i, translation e 1 i j) = (2 : ℤ) ^ (e j).degree := by
    simp only [unsigned_entry]
    rw [column_sum e he hclosed j (fun _ k n => (n.choose k : ℤ))
      (fun _ k n h => by rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero])]
    rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    have ht : (∑ v : Fin (e j p + 1), (e j p).choose v) = 2 ^ e j p := by
      rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_choose]
    exact_mod_cast ht
  have hp (i : I) : |translation e 1 i j| = translation e 1 i j :=
    abs_of_nonneg (by rw [unsigned_entry]; positivity)
  constructor
  · simpa only [abs_signed_entry] using hJ
  · simpa only [hp] using hJ

/-- The induced unweighted ℓ¹ norm is the largest absolute column sum. -/
def oneNorm (A : Matrix I I ℤ) : ℕ :=
  Finset.univ.sup fun h => (∑ i, |A i h|).toNat

theorem oneNorm_pair (e : I → σ →₀ ℕ) (he : Function.Injective e) (hclosed : DivisorClosed e) :
    oneNorm (translation e (-1)) = Finset.univ.sup (fun h => (2 : ℕ) ^ (e h).degree) ∧
    oneNorm (translation e 1) = Finset.univ.sup (fun h => (2 : ℕ) ^ (e h).degree) := by
  have hcast (n : ℕ) : ((2 : ℤ) ^ n).toNat = (2 : ℕ) ^ n := by
    have hz : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := Nat.cast_pow 2 n
    exact congrArg Int.toNat hz.symm
  constructor
  · exact Finset.sup_congr rfl fun h _ =>
      (congrArg Int.toNat (column_mass e he hclosed h).1).trans (hcast _)
  · exact Finset.sup_congr rfl fun h _ =>
      (congrArg Int.toNat (column_mass e he hclosed h).2).trans (hcast _)

/-- Entries factor across any disjoint partition of the prime coordinates. -/
theorem translation_partition (e : I → σ →₀ ℕ) (s : ℤ) (i h : I) (P : Finset σ)
    [DecidableEq σ] :
    translation e s i h =
      (∏ p ∈ P, ((e h p).choose (e i p) : ℤ) * s ^ (e h p - e i p)) *
        ∏ p ∈ Pᶜ, ((e h p).choose (e i p) : ℤ) * s ^ (e h p - e i p) := by
  rw [translation_apply, Finset.prod_mul_prod_compl]

section Integers

/-- The axes used by a finite arithmetic family are exactly its occurring primes. -/
def primeAxes (S : Finset ℕ) : Finset ℕ := S.biUnion Nat.primeFactors

/-- The original integer factorization restricted to the full set of occurring primes. -/
def factorizationProfile (S : Finset ℕ) (h : S) : primeAxes S →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => h.val.factorization p.val

private theorem off_axes (S : Finset ℕ) (n : S) {p : ℕ} (hp : p ∉ primeAxes S) :
    n.val.factorization p = 0 := by
  by_contra hn
  exact hp (Finset.mem_biUnion.mpr ⟨n.val, n.property, Finsupp.mem_support_iff.mpr hn⟩)

theorem factorizationProfile_injective (S : Finset ℕ) (hpos : ∀ n ∈ S, n ≠ 0) :
    Function.Injective (factorizationProfile S) := by
  intro h k hk
  apply Subtype.ext
  apply Nat.eq_of_factorization_eq (hpos h.val h.property) (hpos k.val k.property)
  intro p
  by_cases hp : p ∈ primeAxes S
  · exact congrArg (fun v : primeAxes S →₀ ℕ => v ⟨p, hp⟩) hk
  · rw [off_axes S h hp, off_axes S k hp]

theorem factorizationProfile_le_iff_dvd (S : Finset ℕ) (hpos : ∀ n ∈ S, n ≠ 0) (d h : S) :
    factorizationProfile S d ≤ factorizationProfile S h ↔ d.val ∣ h.val := by
  rw [← Nat.factorization_le_iff_dvd (hpos d.val d.property) (hpos h.val h.property)]
  constructor
  · intro hv p
    by_cases hp : p ∈ primeAxes S
    · exact hv ⟨p, hp⟩
    · rw [off_axes S d hp, off_axes S h hp]
  · exact fun hv p => hv p.val

/-- A divisor-closed family of positive integers contains the full intermediate
exponent box for each of its own elements. -/
theorem factorizationProfile_closed (S : Finset ℕ)
    (hd : ∀ n ∈ S, ∀ k, k ∣ n → k ∈ S) : DivisorClosed (factorizationProfile S) := by
  classical
  intro h v hv
  let emb : primeAxes S ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  let v' := v.embDomain emb
  have hle : v' ≤ h.val.factorization := by
    intro p
    by_cases hp : p ∈ primeAxes S
    · let q : primeAxes S := ⟨p, hp⟩
      change v.embDomain emb (emb q) ≤ h.val.factorization p
      rw [Finsupp.embDomain_apply_self]
      exact hv q
    · have hn : p ∉ Set.range emb := by
        rintro ⟨q, rfl⟩
        exact hp q.property
      change v.embDomain emb p ≤ h.val.factorization p
      rw [Finsupp.embDomain_of_notMem_range _ _ _ hn]
      exact Nat.zero_le _
  let k := v'.prod (fun p b => p ^ b)
  have hk : k ∈ S := hd h.val h.property k (Nat.prod_pow_dvd_of_le_factorization hle)
  refine ⟨⟨k, hk⟩, Finsupp.ext fun p => ?_⟩
  change k.factorization p.val = v p
  rw [show k.factorization = v' from Nat.factorization_prod_pow_eq_self_of_le_factorization hle]
  exact Finsupp.embDomain_apply_self emb v p

theorem factorizationProfile_degree (S : Finset ℕ) (h : S) :
    (factorizationProfile S h).degree = ∑ p ∈ h.val.primeFactors, h.val.factorization p := by
  rw [Finsupp.degree_eq_sum]
  change (∑ p : primeAxes S, h.val.factorization p.val) = _
  rw [Finset.sum_coe_sort]
  symm
  apply Finset.sum_subset (fun p hp => Finset.mem_biUnion.mpr ⟨h.val, h.property, hp⟩)
  intro p _ hp
  exact Finsupp.notMem_support_iff.mp hp

/-- In a fixed high-prime fibre every axis occurring in the matrix is above
the actual cutoff. -/
theorem primeAxes_gt_cutoff (S : Finset ℕ) (z : ℕ)
    (hr : ∀ n ∈ S, ∀ p ∈ n.primeFactors, z < p) (p : primeAxes S) : z < p.val := by
  obtain ⟨n, hn, hp⟩ := Finset.mem_biUnion.mp p.property
  exact hr n hn p.val hp

theorem factorization_unsigned_entry (S : Finset ℕ) (d h : S) :
    translation (factorizationProfile S) 1 d h =
      ∏ p ∈ primeAxes S, ((h.val.factorization p).choose (d.val.factorization p) : ℤ) := by
  rw [unsigned_entry]
  exact Finset.prod_coe_sort (primeAxes S)
    (fun p => ((h.val.factorization p).choose (d.val.factorization p) : ℤ))

/-- The inverse entry has the actual divisibility indicator and the parity
of the difference in total prime multiplicities. -/
theorem factorization_signed_entry (S : Finset ℕ) (hpos : ∀ n ∈ S, n ≠ 0) (d h : S) :
    translation (factorizationProfile S) (-1) d h =
      if d.val ∣ h.val then
        (-1 : ℤ) ^ ((∑ p ∈ h.val.primeFactors, h.val.factorization p) -
          ∑ p ∈ d.val.primeFactors, d.val.factorization p) * translation (factorizationProfile S) 1 d h
      else 0 := by
  by_cases hd : d.val ∣ h.val
  · rw [ite_eq_left hd, signed_entry _ ((factorizationProfile_le_iff_dvd S hpos d h).mpr hd),
      factorizationProfile_degree, factorizationProfile_degree]
  · exact (entry_zero_of_not_le _ (-1) (mt (factorizationProfile_le_iff_dvd S hpos d h).mp hd)).trans
      (ite_eq_right hd).symm

/-- Both inverse identities, determinant and exact column mass for the actual
integer factorization on an arbitrary finite divisor-closed positive prefix. -/
theorem factorization_recovery (S : Finset ℕ) (hpos : ∀ n ∈ S, n ≠ 0)
    (hd : ∀ n ∈ S, ∀ k, k ∣ n → k ∈ S) :
    let J := translation (factorizationProfile S) 1
    let K := translation (factorizationProfile S) (-1)
    J * K = 1 ∧ K * J = 1 ∧ J.det = 1 ∧
      ∀ h : S, (∑ d, |K d h|) = (2 : ℤ) ^ (∑ p ∈ h.val.primeFactors, h.val.factorization p) ∧
        (∑ d, |J d h|) = (2 : ℤ) ^ (∑ p ∈ h.val.primeFactors, h.val.factorization p) := by
  let e := factorizationProfile S
  have hi := factorizationProfile_injective S hpos
  have hc := factorizationProfile_closed S hd
  have hinv := signed_inverse e hi hc
  refine ⟨hinv.1, hinv.2, det_one e hi, fun h => ?_⟩
  have hm := column_mass e hi hc h
  simpa only [e, factorizationProfile_degree] using hm

end Integers

end RHLean.Geometry.NativePrimeExponentJet

end
