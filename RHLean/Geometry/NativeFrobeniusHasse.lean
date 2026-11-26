import RHLean.Analysis.AlpogeNativeDyadicHostSize
import RHLean.Analysis.AlpogeThin.NativeDyadicPrimePowerIncidence

/-!
# Hasse coefficients before and after the Frobenius period quotient

The exponent of a genuine prime power gives integral Hasse coefficients
on the free polynomial in that exponent. Distinct powers returning to
one inertia coset give a triangular change of coordinates, with the
exact Frobenius period on the diagonal. Imposing the group relation
on a nilpotent character deformation forces it to be constant wherever
the period is a unit.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Polynomial

namespace RHLean.Geometry.NativeFrobeniusHasse

open Polynomial

/-- An infinitesimal deformation of a cyclic character of unit order
vanishes over every commutative coefficient ring, including truncated
rings and quotients modulo a power of the residue characteristic. -/
theorem cyclic_period_rigid {O : Type*} [CommRing O] (n : ℕ) (hn : IsUnit (n : O))
    (u : O) (hu : IsNilpotent u) : (1 + u) ^ n = 1 ↔ u = 0 := by
  have expand (m : ℕ) : ∃ q : O, (1 + u) ^ m = 1 + u * ((m : O) + u * q) := by
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨(m : O) + q + u * q, ?_⟩
      rw [pow_succ, hq, Nat.cast_succ]
      ring
  obtain ⟨q, hq⟩ := expand n
  have hnil : IsNilpotent (u * q) := by
    obtain ⟨k, hk⟩ := hu
    exact ⟨k, by rw [mul_pow, hk, zero_mul]⟩
  have hunit : IsUnit ((n : O) + u * q) :=
    hnil.isUnit_add_left_of_commute hn (Commute.all _ _)
  constructor
  · intro he
    apply (IsUnit.mul_left_eq_zero hunit).mp
    calc u * ((n : O) + u * q) = (1 + u) ^ n - 1 := by rw [hq]; ring
         _ = 0 := by rw [he, sub_self]
  · rintro rfl
    simp

/-- Matrix of the first m integral Hasse coefficients of the monomials
with exponents a, a+o, ..., a+(m−1)o. -/
def progressionMatrix (a o m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun r j => ((a + o * j.val).choose r.val : ℤ)

/-- The entries are evaluations of Mathlib's divided Hasse derivative at
the original monomial, with coefficient ring ℤ. -/
theorem eval_hasseDeriv_at_one (n r : ℕ) :
    (Polynomial.hasseDeriv r (X ^ n : ℤ[X])).eval 1 = (n.choose r : ℤ) := by
  have hmon : (X : ℤ[X]) ^ n = Polynomial.monomial n 1 := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_one, one_mul]
  rw [hmon, Polynomial.hasseDeriv_monomial]
  simp only [Polynomial.eval_monomial, one_pow, mul_one]

private theorem expand_progression (z : ℤ[X]) {m : ℕ} (j : Fin m) :
    (z + 1) ^ j.val = ∑ h : Fin m, C (j.val.choose h.val : ℤ) * z ^ h.val := by
  have hdeg : ((X + 1 : ℤ[X]) ^ j.val).natDegree ≤ j.val := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [Polynomial.coeff_X_add_one_pow, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero]
  have he := Polynomial.eval₂_eq_sum_range' (C : ℤ →+* ℤ[X]) (hdeg.trans_lt j.isLt) z
  rw [Fin.sum_univ_eq_sum_range (fun h => C (j.val.choose h : ℤ) * z ^ h) m]
  simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_one, Polynomial.coeff_X_add_one_pow] using he

/-- Subtracting adjacent columns repeatedly replaces the jth monomial
by (X+1)^a times ((X+1)^o−1)^j. Its first surviving coefficient is o^j.
The integral Pascal change of basis has determinant one. -/
theorem det_progressionMatrix (a o m : ℕ) :
    (progressionMatrix a o m).det = (o : ℤ) ^ (∑ j : Fin m, j.val) := by
  classical
  let z : ℤ[X] := (X + 1) ^ o - 1
  let f (j : Fin m) := (X + 1 : ℤ[X]) ^ a * z ^ j.val
  let D : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun r j => (f j).coeff r.val
  let P : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun r j => (j.val.choose r.val : ℤ)
  have hexp (j : Fin m) : (X + 1 : ℤ[X]) ^ (a + o * j.val) =
      ∑ h : Fin m, f h * C (j.val.choose h.val : ℤ) := by
    have hz : (X + 1 : ℤ[X]) ^ o = z + 1 := (sub_add_cancel _ _).symm
    rw [pow_add, pow_mul, hz, expand_progression z j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    dsimp [f]
    ring
  have hmat : progressionMatrix a o m = D * P := by
    ext r j
    change ((a + o * j.val).choose r.val : ℤ) = (D * P) r j
    rw [← Polynomial.coeff_X_add_one_pow ℤ, hexp, Polynomial.finsetSum_coeff, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun h _ => Polynomial.coeff_mul_C _ _ _
  have hP : P.IsUpperTriangular := by
    intro r j hjr
    change (j.val.choose r.val : ℤ) = 0
    change j.val < r.val at hjr
    rw [Nat.choose_eq_zero_of_lt hjr, Nat.cast_zero]
  have hPdet : P.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hP]
    simp [P]
  obtain ⟨q, hq⟩ : (X : ℤ[X]) ∣ z := by
    apply Polynomial.X_dvd_iff.mpr
    rw [show z = (X + 1 : ℤ[X]) ^ o - 1 from rfl, Polynomial.coeff_sub,
      Polynomial.coeff_X_add_one_pow]
    simp
  have hq0 : q.coeff 0 = (o : ℤ) := by
    have h := congrArg (fun t : ℤ[X] => t.coeff 1) hq
    change (((X + 1 : ℤ[X]) ^ o - 1).coeff 1) = (X * q).coeff (0 + 1) at h
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_X_mul] at h
    simpa [Polynomial.coeff_one] using h.symm
  have hentry (r j : Fin m) : D r j =
      if j.val ≤ r.val then (((X + 1 : ℤ[X]) ^ a) * q ^ j.val).coeff (r.val - j.val) else 0 := by
    change ((X + 1 : ℤ[X]) ^ a * z ^ j.val).coeff r.val = _
    have hf : (X + 1 : ℤ[X]) ^ a * z ^ j.val = X ^ j.val * ((X + 1) ^ a * q ^ j.val) := by
      rw [hq, mul_pow]
      ring
    rw [hf, Polynomial.coeff_X_pow_mul']
  have hD : D.IsLowerTriangular := by
    intro r j hrj
    exact (hentry r j).trans (ite_eq_right (Nat.not_le_of_lt hrj))
  have hdiag (j : Fin m) : D j j = (o : ℤ) ^ j.val := by
    rw [hentry, ite_eq_left le_rfl, Nat.sub_self]
    change Polynomial.constantCoeff (((X + 1 : ℤ[X]) ^ a) * q ^ j.val) = _
    have hq' : Polynomial.constantCoeff q = (o : ℤ) := hq0
    have h1 : Polynomial.constantCoeff (X + 1 : ℤ[X]) = 1 := by simp
    rw [map_mul, map_pow, map_pow, h1, hq', one_pow, one_mul]
  rw [hmat, Matrix.det_mul, hPdet, mul_one, Matrix.det_of_isLowerTriangular D hD]
  simp_rw [hdiag]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- Iterating the ordinary derivative on these same monomials adds the
product of the row factorials to the determinant. -/
theorem det_ordinary_progression (a o m : ℕ) :
    (Matrix.of fun r j : Fin m =>
      ((Polynomial.derivative^[r.val]) (X ^ (a + o * j.val) : ℤ[X])).eval 1).det =
      (∏ r : Fin m, (r.val.factorial : ℤ)) * (o : ℤ) ^ (∑ j : Fin m, j.val) := by
  have he : (Matrix.of fun r j : Fin m =>
      ((Polynomial.derivative^[r.val]) (X ^ (a + o * j.val) : ℤ[X])).eval 1) =
      Matrix.diagonal (fun r : Fin m => (r.val.factorial : ℤ)) * progressionMatrix a o m := by
    ext r j
    rw [Matrix.of_apply, Matrix.diagonal_mul, Polynomial.iterate_derivative_X_pow_eq_natCast_mul,
      Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
      mul_one, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    rfl
  rw [he, Matrix.det_mul, Matrix.det_diagonal, det_progressionMatrix]

end RHLean.Geometry.NativeFrobeniusHasse

namespace RHLean.Analysis

open RHLean.Geometry.NativeFrobeniusHasse

attribute [local irreducible] alpogeNativeHostData

private theorem natCast_isUnit_of_dvd_two_pow {O : Type*} [CommRing O] (h2 : IsUnit (2 : O))
    {n k : ℕ} (h : n ∣ 2 ^ k) : IsUnit (n : O) := by
  obtain ⟨j, hj⟩ := h
  refine isUnit_of_dvd_unit (y := (2 : O) ^ k) ⟨(j : O), ?_⟩ (h2.pow _)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul] using congrArg (Nat.cast : ℕ → O) hj

section HostPeriod

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Period of the host Frobenius in its actual inertia quotient. -/
def AlpogeNativeArithData.frobeniusPeriod (D : AlpogeNativeArithData H) (p : ℕ) : ℕ :=
  frobeniusCosetOrder (G := AlpogeNativeE0 × H) (D.inertia p) (D.frob p)

private theorem host_frobPeriod_isUnit {O : Type*} [CommRing O] (h2 : IsUnit (2 : O))
    (D : AlpogeNativeArithData H) (p k : ℕ) (hcard : Nat.card (AlpogeNativeE0 × H) = 2 ^ k) :
    IsUnit (D.frobeniusPeriod p : O) :=
  natCast_isUnit_of_dvd_two_pow h2
    ((frobeniusCosetOrder_dvd_natCard (G := AlpogeNativeE0 × H)
      (D.inertia p) (D.frob p)).trans (dvd_of_eq hcard))

end HostPeriod

private theorem nativeDyadic_host_natCard (e : ℕ) :
    Nat.card (AlpogeNativeE0 × AlpogeNativeDyadicH e) = 2 ^ (e + 2) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, alpogeNativeDyadicH_card, pow_add]
  have h4 : Fintype.card AlpogeNativeE0 = 4 := by decide
  rw [h4]
  ring

set_option maxHeartbeats 1000000 in
attribute [local irreducible] AlpogeNativeArithData.frobeniusPeriod in
/-- The order of the actual Frobenius modulo inertia is a unit whenever
two is a unit. It divides the order of the native dyadic host. -/
theorem nativeDyadic_frobPeriod_isUnit {O : Type*} [CommRing O] (h2 : IsUnit (2 : O))
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime] :
    IsUnit ((alpogeNativeHostData e q d).frobeniusPeriod p : O) :=
  host_frobPeriod_isUnit (H := AlpogeNativeDyadicH e) h2 (alpogeNativeHostData e q d)
    p (e + 2) (nativeDyadic_host_natCard e)

/-- The original character relation forces all nilpotent Hasse deformation
parameters to vanish at the native Frobenius, at every odd local place. -/
theorem nativeDyadic_frobPeriod_rigid {O : Type*} [CommRing O] (h2 : IsUnit (2 : O))
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime] (u : O) (hu : IsNilpotent u) :
    (1 + u) ^ (alpogeNativeHostData e q d).frobeniusPeriod p = 1 ↔ u = 0 :=
  cyclic_period_rigid _ (nativeDyadic_frobPeriod_isUnit h2 e q d p) u hu

/-- Two unit-valued characters on the inertia quotient agree at the specified
Frobenius whenever their ratio there differs from one by a nilpotent. -/
def FrobeniusCharactersRigid (O : Type*) [CommRing O] {G : Type*} [AddCommGroup G]
    (I : AddSubgroup G) (g : G) : Prop :=
  let z := Multiplicative.ofAdd ((QuotientAddGroup.mk' I) g)
  ∀ χ ψ : Multiplicative (G ⧸ I) →* Oˣ,
    IsNilpotent (((ψ z / χ z : Oˣ) : O) - 1) → ψ z = χ z

private theorem frobeniusCharactersRigid_of_unit {O G : Type*} [CommRing O] [AddCommGroup G]
    (I : AddSubgroup G) (g : G) (hu : IsUnit (frobeniusCosetOrder I g : O)) :
    FrobeniusCharactersRigid O I g := by
  let x := (QuotientAddGroup.mk' I) g
  let z := Multiplicative.ofAdd x
  change ∀ χ ψ : Multiplicative (G ⧸ I) →* Oˣ,
    IsNilpotent (((ψ z / χ z : Oˣ) : O) - 1) → ψ z = χ z
  intro χ ψ hnil
  let ratio := ψ z / χ z
  have ho : z ^ addOrderOf x = 1 :=
    congrArg Multiplicative.ofAdd (addOrderOf_nsmul_eq_zero x)
  have hp : ratio ^ addOrderOf x = 1 := by
    change (ψ z / χ z) ^ addOrderOf x = 1
    calc (ψ z / χ z) ^ addOrderOf x = ψ (z ^ addOrderOf x) / χ (z ^ addOrderOf x) := by
           rw [div_pow, map_pow, map_pow]
         _ = 1 := by simp only [ho, map_one, div_one]
  have he : (1 + ((ratio : O) - 1)) ^ addOrderOf x = 1 := by
    rw [show 1 + ((ratio : O) - 1) = (ratio : O) by ring]
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hp
  have hzero := (cyclic_period_rigid (addOrderOf x) hu ((ratio : O) - 1) hnil).mp he
  have hratio : ratio = 1 := Units.ext (sub_eq_zero.mp hzero)
  exact div_eq_one.mp hratio

section HostCharacters

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Character rigidity for the Frobenius and inertia of a single host. -/
def AlpogeNativeArithData.rigidFrobeniusCharacters (D : AlpogeNativeArithData H)
    (O : Type*) [CommRing O] (p : ℕ) : Prop :=
  FrobeniusCharactersRigid O (G := AlpogeNativeE0 × H) (D.inertia p) (D.frob p)

private theorem host_frobCharacters_rigid {O : Type*} [CommRing O]
    (D : AlpogeNativeArithData H) (p : ℕ) (hu : IsUnit (D.frobeniusPeriod p : O)) :
    D.rigidFrobeniusCharacters O p :=
  frobeniusCharactersRigid_of_unit (G := AlpogeNativeE0 × H) (D.inertia p) (D.frob p) hu

end HostCharacters

set_option maxHeartbeats 1000000 in
attribute [local irreducible] AlpogeNativeArithData.rigidFrobeniusCharacters
  AlpogeNativeArithData.frobeniusPeriod in
/-- Rigidity at the actual dyadic Frobenius, proved from the period relation
of the two characters on the native inertia quotient. -/
theorem nativeDyadic_frob_characters_eq_of_nilpotent_ratio {O : Type*} [CommRing O]
    (h2 : IsUnit (2 : O)) (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime] :
    (alpogeNativeHostData e q d).rigidFrobeniusCharacters O p :=
  host_frobCharacters_rigid (H := AlpogeNativeDyadicH e) (alpogeNativeHostData e q d) p
    (nativeDyadic_frobPeriod_isUnit h2 e q d p)

private theorem returning_sub_mem {G : Type*} [AddCommGroup G] (I : AddSubgroup G)
    (g : G) (a j : ℕ) : a • g - (a + frobeniusCosetOrder I g * j) • g ∈ I := by
  have hk := (frobeniusCosetOrder_dvd_iff I g _).mp (dvd_mul_right (frobeniusCosetOrder I g) j)
  have hz : a • g - (a + frobeniusCosetOrder I g * j) • g =
      -((frobeniusCosetOrder I g * j) • g) := by rw [add_nsmul]; abel
  rw [hz]
  exact I.neg_mem hk

/-- Keep the exponent of the physical prime power before the quotient.
All these powers return to the same literal colour, whose integral
incidence is one. Their labelled Hasse minor has the displayed determinant. -/
theorem nativeDyadic_returning_hasse_minor (e q d p a m : ℕ) [Fact q.Prime] [Fact d.Prime] :
    let H := alpogeNativeHostData e q d
    let o := frobeniusCosetOrder (H.inertia p) (H.frob p)
    let n (j : Fin m) := a + o * j.val
    (Matrix.of fun r j : Fin m => nativeDyadicPrimePowerIncidence e q d p (n j) (a • H.frob p) *
      ((n j).choose r.val : ℤ)).det = (o : ℤ) ^ (∑ j : Fin m, j.val) := by
  classical
  let H := alpogeNativeHostData e q d
  let o := frobeniusCosetOrder (H.inertia p) (H.frob p)
  let n (j : Fin m) := a + o * j.val
  have hrow (j : Fin m) : nativeDyadicPrimePowerIncidence e q d p (n j) (a • H.frob p) = 1 := by
    exact ite_eq_left (returning_sub_mem (G := AlpogeNativeE0 × AlpogeNativeDyadicH e)
      (H.inertia p) (H.frob p) a j.val)
  have he : (Matrix.of fun r j : Fin m => nativeDyadicPrimePowerIncidence e q d p (n j) (a • H.frob p) *
      ((n j).choose r.val : ℤ)) = progressionMatrix a o m := by
    ext r j
    change nativeDyadicPrimePowerIncidence e q d p (n j) (a • H.frob p) * _ = _
    rw [hrow, one_mul]
    rfl
  exact (congrArg Matrix.det he).trans (det_progressionMatrix a o m)

/-- A divided Hasse determinant on the pre-quotient exponent labels is a
local unit on every square-clock place where two is invertible. -/
theorem nativeDyadic_returning_hasse_det_isUnit {O : Type*} [CommRing O] (h2 : IsUnit (2 : O))
    (e q d p a m : ℕ) [Fact q.Prime] [Fact d.Prime] :
    let H := alpogeNativeHostData e q d
    let o := frobeniusCosetOrder (H.inertia p) (H.frob p)
    let n (j : Fin m) := a + o * j.val
    IsUnit ((Int.castRingHom O) (Matrix.of fun r j : Fin m =>
      nativeDyadicPrimePowerIncidence e q d p (n j) (a • H.frob p) * ((n j).choose r.val : ℤ)).det) := by
  let H := alpogeNativeHostData e q d
  let o := frobeniusCosetOrder (H.inertia p) (H.frob p)
  let n (j : Fin m) := a + o * j.val
  change IsUnit ((Int.castRingHom O) (Matrix.of fun r j : Fin m =>
    nativeDyadicPrimePowerIncidence e q d p (n j) (a • H.frob p) * ((n j).choose r.val : ℤ)).det)
  have hdet : (Matrix.of fun r j : Fin m => nativeDyadicPrimePowerIncidence e q d p (n j)
      (a • H.frob p) * ((n j).choose r.val : ℤ)).det = (o : ℤ) ^ (∑ j : Fin m, j.val) :=
    nativeDyadic_returning_hasse_minor e q d p a m
  rw [hdet, map_pow, map_natCast]
  exact (nativeDyadic_frobPeriod_isUnit h2 e q d p).pow _

end RHLean.Analysis

end
