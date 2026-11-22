import RHLean.Analysis.AlpogeNativeQuadraticRoot
import RHLean.Analysis.AlpogeThin.NativeDyadicFrame
import RHLean.Analysis.AlpogeThin.NativeDyadicChiField
import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.CharacterBoxes.TwistForm

/-!
# The original HostRaw, constructed on the same native cyclotomic fixed field

The frame, Galois group, embedding, primitive root, quadratic square root and
Artin map are all the actual native constructions. The full-host equivalence
performs the explicit d/q bit-to-q/d-unit coordinate conversion. The remaining
`art_h`, `art_d` and `art_q` conditions follow from the original residue map
and the stated congruences; they are not supplied as premises.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/OfChar.lean`, `CharData.toHostRaw`, and
`ArtinMapSecondEqJacobiSym.lean`, `D7.{hIso,ggIso,artinMap_dyadic_eq}`.

This constructs `HostRaw` and its exact principal kernel condition on the
same `e,q,d`. The stronger `HostDer` prime-ideal inertia/Frobenius statements
and the downstream theta/geometric data remain separate proof obligations.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace RHLean.Analysis.AlpogeThin

open Formalism.FrobeniusOrbits Formalism.HC

/-- The original Artin map expressed in the genuinely constructed source frame. -/
def nativeDyadicArt (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    (ZMod (alpogeNativeHostN e q d))ˣ →* (nativeDyadicFrame e).GG :=
  (nativeDyadicFullHostEquiv e).toMonoidHom.comp (alpogeNativeRecMap e q d)

/-- The source's two sign coordinates are the actual q- and d-characters. -/
theorem nativeDyadicArt_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (u : (ZMod (alpogeNativeHostN e q d))ˣ) :
    nativeDyadicArt e q d u =
      ((alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d) u,
        alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u),
       Multiplicative.ofAdd ((nativeDyadicFrameEquiv e).symm
        (Additive.ofMul (QuotientGroup.mk
          (ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u))))) := by
  exact Prod.ext
    (Prod.ext (nativeDyadicSignEquiv.symm_apply_apply _)
      (nativeDyadicSignEquiv.symm_apply_apply _)) rfl

theorem nativeDyadicArt_surjective
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d) :
    Function.Surjective (nativeDyadicArt e q d) :=
  (nativeDyadicFullHostEquiv e).surjective.comp
    (alpogeNativeRecMap_surjective e q d hq2 hd2 hqd)

theorem nativeDyadicArt_neg_one
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    nativeDyadicArt e q d (-1) = (nativeDyadicFrame e).cc := by
  change nativeDyadicFullHostEquiv e (alpogeNativeRecMap e q d (-1)) = _
  rw [alpogeNativeRecMap_neg_one e q d hq4 hd4, nativeDyadicFullHostEquiv_cconj]

/-- The dyadic component of Artin is the literal reduction of the same unit. -/
theorem nativeDyadicArt_h
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (u : (ZMod (alpogeNativeHostN e q d))ˣ)
    (v : (ZMod (2 ^ (e + 2)))ˣ)
    (hv : (v : ZMod (2 ^ (e + 2))) =
      (((u : ZMod (alpogeNativeHostN e q d)).val : ℕ) : ZMod (2 ^ (e + 2)))) :
    (nativeDyadicFrame e).hH (nativeDyadicArt e q d u).2 = hcl e v := by
  have hu : ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u = v := by
    apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val]
    exact hv.symm
  change (nativeDyadicFrame e).hH
    (nativeDyadicFullHostEquiv e (alpogeNativeRecMap e q d u)).2 = _
  rw [nativeDyadicFullHostEquiv_hH]
  change QuotientGroup.mk (ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u) =
    QuotientGroup.mk v
  rw [hu]

private theorem nativeDyadicUnitsMap_eq_one
    {N c : ℕ} [NeZero N] (hc : c ∣ N) (u : (ZMod N)ˣ)
    (hu : (u : ZMod N).val ≡ 1 [MOD c]) : ZMod.unitsMap hc u = 1 := by
  apply Units.ext
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, Units.val_one]
  simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu

private theorem nativeDyadicTransport_eq_one
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (u : (ZMod (alpogeNativeHostN e q d))ˣ)
    (hu : ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u = 1) :
    Multiplicative.ofAdd ((nativeDyadicFrameEquiv e).symm
      (Additive.ofMul (QuotientGroup.mk
        (ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u)))) =
          (1 : (nativeDyadicFrame e).MA) := by
  rw [hu, QuotientGroup.mk_one]
  exact congrArg Multiplicative.ofAdd (map_zero (nativeDyadicFrameEquiv e).symm)

/-- Congruence one modulo the dyadic-and-q part leaves only the original
d-involution, with both possibilities proved from actual integer units. -/
theorem nativeDyadicArt_d
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (u : (ZMod (alpogeNativeHostN e q d))ˣ)
    (hu : (u : ZMod (alpogeNativeHostN e q d)).val ≡ 1 [MOD 2 ^ (e + 2) * q]) :
    nativeDyadicArt e q d u = 1 ∨ nativeDyadicArt e q d u = (nativeDyadicFrame e).iod := by
  have huq : ZMod.unitsMap (alpogeNativeQ_dvd_hostN e q d) u = 1 :=
    nativeDyadicUnitsMap_eq_one _ u (hu.of_dvd (dvd_mul_left q _))
  have hu2 : ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u = 1 :=
    nativeDyadicUnitsMap_eq_one _ u (hu.of_dvd (dvd_mul_right _ q))
  have hq : alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d) u = 1 := by
    rw [alpogeNativeLegU, MonoidHom.comp_apply, huq, map_one]
  have hh := nativeDyadicTransport_eq_one e q d u hu2
  have hshape : nativeDyadicArt e q d u =
      ((1, alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u), 1) := by
    rw [nativeDyadicArt_apply, hq, hh]
  rcases Int.units_eq_one_or
      (alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u) with hd | hd
  · left
    simpa only [hd, Prod.mk_one_one] using hshape
  · right
    simpa only [hd, Frame.iod] using hshape

/-- Congruence one modulo the dyadic-and-d part leaves only a quadratic
q-sign, hence the actual Artin image squares to one. -/
theorem nativeDyadicArt_q
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (u : (ZMod (alpogeNativeHostN e q d))ˣ)
    (hu : (u : ZMod (alpogeNativeHostN e q d)).val ≡ 1 [MOD 2 ^ (e + 2) * d]) :
    nativeDyadicArt e q d u ^ 2 = 1 := by
  have hud : ZMod.unitsMap (alpogeNativeD_dvd_hostN e q d) u = 1 :=
    nativeDyadicUnitsMap_eq_one _ u (hu.of_dvd (dvd_mul_left d _))
  have hu2 : ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u = 1 :=
    nativeDyadicUnitsMap_eq_one _ u (hu.of_dvd (dvd_mul_right _ d))
  have hd : alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u = 1 := by
    rw [alpogeNativeLegU, MonoidHom.comp_apply, hud, map_one]
  have hh := nativeDyadicTransport_eq_one e q d u hu2
  have hshape : nativeDyadicArt e q d u =
      ((alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d) u, 1), 1) := by
    rw [nativeDyadicArt_apply, hd, hh]
  rcases Int.units_eq_one_or
      (alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d) u) with hq | hq <;>
    simp [hshape, hq]

/-- The constructed field's Galois equivalence, in source-frame coordinates. -/
def nativeDyadicFieldGal
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d) :
    (alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) ≃*
      (nativeDyadicFrame e).GG :=
  (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).trans (nativeDyadicFullHostEquiv e)

theorem nativeDyadicFieldGal_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) :
    nativeDyadicFieldGal e q d hq2 hd2 hqd σ =
      nativeDyadicFullHostEquiv e (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ) := rfl

theorem nativeDyadicFieldGal_sqrtD
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) :
    σ (alpogeNativeSqrtD e q d) =
      ((((nativeDyadicFieldGal e q d hq2 hd2 hqd σ).1.2 : ℤˣ) : ℤ) :
        alpogeNativeHostField e q d) * alpogeNativeSqrtD e q d := by
  rw [nativeDyadicFieldGal_apply, nativeDyadicFullHostEquiv_chD_val]
  simpa only [Int.cast_ite, Int.cast_one, Int.cast_neg] using
    alpogeNativeSqrtD_galois_apply e q d hq2 hd2 hqd σ

theorem nativeDyadicFieldGal_art_spec
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (u : (ZMod (alpogeNativeHostN e q d))ˣ)
    (τ : AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d)
    (hτ : τ (alpogeNativeCyclotomicZeta e q d) =
      alpogeNativeCyclotomicZeta e q d ^
        (u : ZMod (alpogeNativeHostN e q d)).val)
    (x : alpogeNativeHostField e q d) :
    (((nativeDyadicFieldGal e q d hq2 hd2 hqd).symm
      (nativeDyadicArt e q d u) x : alpogeNativeHostField e q d) :
        AlpogeNativeCyclotomic e q d) = τ x := by
  change (((alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
    ((nativeDyadicFullHostEquiv e).symm
      (nativeDyadicFullHostEquiv e (alpogeNativeRecMap e q d u))) x :
        alpogeNativeHostField e q d) : AlpogeNativeCyclotomic e q d) = _
  rw [MulEquiv.symm_apply_apply]
  exact alpogeNativeHostField_art_spec e q d hq2 hd2 hqd u τ hτ x

/-- The complete original raw host, with no field, root, Galois or Artin
compatibility premise. Its only inputs are the original arithmetic regime. -/
def nativeDyadicHostRaw
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) : HostRaw (nativeDyadicFrame e) := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have h2q : Nat.Coprime 2 q := by
    rw [Nat.coprime_primes Nat.prime_two (show q.Prime from Fact.out)]
    exact Ne.symm hq2
  have h2d : Nat.Coprime 2 d := by
    rw [Nat.coprime_primes Nat.prime_two (show d.Prime from Fact.out)]
    exact Ne.symm hd2
  exact
    { q := q
      d := d
      QS := 2 ^ (e + 2)
      hyp := hH
      two_le_e := he
      QS_pos := pow_pos (by decide) _
      tower_dvd := dvd_rfl
      QS_coprime := (h2q.mul_right h2d).pow_left (e + 2)
      QS_split := fun l hl hl2 hldiv =>
        (hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
          (hl.dvd_of_dvd_pow hldiv))).elim
      E := alpogeNativeHostField e q d
      galois := inferInstance
      gal := nativeDyadicFieldGal e q d hq2 hd2 hqd
      sqd := alpogeNativeSqrtD e q d
      sqd_sq := alpogeNativeSqrtD_sq e q d hd4
      gal_sqd := nativeDyadicFieldGal_sqrtD e q d hq2 hd2 hqd
      cycEmb := (alpogeNativeHostField e q d).val
      cycZeta := alpogeNativeCyclotomicZeta e q d
      cycZeta_prim := alpogeNativeCyclotomicZeta_spec e q d
      art := nativeDyadicArt e q d
      art_spec := nativeDyadicFieldGal_art_spec e q d hq2 hd2 hqd
      art_neg_one := nativeDyadicArt_neg_one e q d hq4 hd4
      art_h := nativeDyadicArt_h e q d
      art_d := nativeDyadicArt_d e q d
      art_q := nativeDyadicArt_q e q d }

theorem nativeDyadicHostRaw_q
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).q = q := rfl

theorem nativeDyadicHostRaw_d
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).d = d := rfl

theorem nativeDyadicHostRaw_QS
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).QS = 2 ^ (e + 2) := rfl

theorem nativeDyadicHostRaw_field
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).E = (alpogeNativeHostField e q d) := rfl

theorem nativeDyadicHostRaw_conductor
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).condN = alpogeNativeHostN e q d := rfl

theorem nativeDyadicHostRaw_art
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).art = nativeDyadicArt e q d := rfl

/-- The principal source field predicate is preserved on this exact raw host. -/
theorem nativeDyadicHostRaw_isChiField
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (he : 2 ≤ e) (hH : HostHyp q d) :
    UpperTheory.Top.IsChiField PChar.one e q d (nativeDyadicHostRaw e q d he hH).E :=
  nativeDyadicHostField_isChiField e q d

/-- The raw host satisfies the original principal `KerChi`, on its actual Artin map. -/
theorem nativeDyadicHostRaw_kerChi
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (he : 2 ≤ e) (hH : HostHyp q d) :
    UpperTheory.Top.KerChi PChar.one (nativeDyadicHostRaw e q d he hH) := by
  refine ⟨one_dvd _, ?_⟩
  intro a ha
  have hprincipal : PChar.one.val a = 1 := by
    change (1 : DirichletCharacter ℂ 1) (a : ZMod 1) = 1
    rw [show (a : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  have hmap : nativeDyadicArt e q d (ZMod.unitOfCoprime a ha) = 1 ↔
      alpogeNativeRecMap e q d (ZMod.unitOfCoprime a ha) = 1 := by
    change nativeDyadicFullHostEquiv e
      (alpogeNativeRecMap e q d (ZMod.unitOfCoprime a ha)) = 1 ↔ _
    exact MulEquiv.map_eq_one_iff
      (M := Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e))
      (N := (nativeDyadicFrame e).GG) (nativeDyadicFullHostEquiv e)
  simpa only [hprincipal, true_and, nativeDyadicHostRaw_art,
    nativeDyadicHostRaw_q, nativeDyadicHostRaw_d, nativeDyadicFrame_e] using
    hmap.trans (nativeDyadicRecMap_unitOfCoprime_eq_one_iff e q d a ha)

/-- The same selected prime window already supplies the arithmetic HostHyp;
its divisibility q | d+1 gives the required quadratic splitting sign. -/
theorem nativeDyadicHostHyp_of_winPair
    {eps Y : ℝ} {q d : ℕ} (h : UpperTheory.Top.WinPair eps Y q d) : HostHyp q d := by
  refine ⟨h.q_prime, h.d_prime, h.q_mod, h.d_mod, ?_⟩
  obtain ⟨k, hk⟩ := h.d_q
  have hk' : (d : ℤ) + 1 = (q : ℤ) * k := by exact_mod_cast hk
  have hcast : -(d : ℤ) = 1 + (q : ℤ) * (-(k : ℤ)) := by linarith
  rw [jacobiSym.mod_left, hcast, Int.add_mul_emod_self_left,
    ← jacobiSym.mod_left (1 : ℤ) q, jacobiSym.one_left]

/-- A selected `WinPair` constructs the original raw host on the SAME primes. -/
def nativeDyadicHostRaw_of_winPair
    {eps Y : ℝ} {q d : ℕ} (e : ℕ) (he : 2 ≤ e)
    (h : UpperTheory.Top.WinPair eps Y q d) : HostRaw (nativeDyadicFrame e) :=
  let : Fact q.Prime := ⟨h.q_prime⟩
  let : Fact d.Prime := ⟨h.d_prime⟩
  nativeDyadicHostRaw e q d he (nativeDyadicHostHyp_of_winPair h)

/-- The constructed PageN regime already supplies the original lower bound
on the dyadic exponent, once the physical scale is at least two. -/
theorem nativeDyadicPageN_two_le
    {eps x : ℝ} {e : ℕ} (heps : 0 < eps) (hx : 2 ≤ x)
    (hP : UpperTheory.Top.PageN eps x e) : 2 ≤ e := by
  have hx1 : 1 ≤ x := by linarith
  have hfour : (4 : ℝ) ≤ (2 : ℝ) ^ e := by
    calc
      (4 : ℝ) ≤ x ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        nlinarith [sq_nonneg (x - 2)]
      _ ≤ x ^ (2 + 8 * eps) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ ≤ (2 : ℝ) ^ e := hP.1
  by_contra he
  have he1 : e ≤ 1 := by omega
  have htwo : (2 : ℝ) ^ e ≤ (2 : ℝ) ^ 1 :=
    pow_le_pow_right₀ (by norm_num) he1
  norm_num at htwo
  linarith

/-- Original PageN and the SAME selected WinPair construct the complete raw
host without a separate dyadic-exponent, field or quadratic-root premise. -/
def nativeDyadicHostRaw_of_pageN_winPair
    {eps x Y : ℝ} {q d : ℕ} (e : ℕ) (heps : 0 < eps) (hx : 2 ≤ x)
    (hP : UpperTheory.Top.PageN eps x e) (h : UpperTheory.Top.WinPair eps Y q d) :
    HostRaw (nativeDyadicFrame e) :=
  nativeDyadicHostRaw_of_winPair e (nativeDyadicPageN_two_le heps hx hP) h

end RHLean.Analysis.AlpogeThin

end
