import RHLean.Analysis.AlpogeNativeCyclotomicResidue
import RHLean.Analysis.AlpogePrimitiveDirichletFull

/-!
# Actual inertia and Frobenius of the native fixed field

This file identifies the existing native modular-unit inertia and Frobenius
with the action on prime ideals of the SAME cyclotomic kernel fixed field.
It includes every prime dividing the original conductor. The match is a
proved conclusion, not a field of a supplied host interface.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/CycBasic.lean`, `Der.gal_eq_art_iff`;
`RootEqOfSubMem.lean`, `Der.{inertia,frob_of_modEq,exists_frob,frob_any}`;
and `CycGrp.lean`, `Der.{exists_prime_liesOver,unramEF}`.
The last conclusion is reconstructed directly from the two distinct native
quadratic characters: at every prime at least one conjugation sign is
unramified. The source archive/mirror states no license; this notice preserves
attribution without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis

open NativeCyclotomicResidue

/-- Equality to the actual residue image is equivalent to intertwining
the actual fixed-field embedding with the cyclotomic power automorphism. -/
theorem alpogeNativeHostGalEquiv_eq_recMap_iff
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d)
    (u : (ZMod (alpogeNativeHostN e q d))ˣ) :
    alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ = alpogeNativeRecMap e q d u ↔
      ∀ x : alpogeNativeHostField e q d,
        algebraMap (alpogeNativeHostField e q d) (AlpogeNativeCyclotomic e q d) (σ x) =
          tauN (alpogeNativeHostN e q d) u
            (algebraMap (alpogeNativeHostField e q d) (AlpogeNativeCyclotomic e q d) x) := by
  have hbase : ∀ x : alpogeNativeHostField e q d,
      algebraMap (alpogeNativeHostField e q d) (AlpogeNativeCyclotomic e q d)
        ((alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm (alpogeNativeRecMap e q d u) x) =
      tauN (alpogeNativeHostN e q d) u
        (algebraMap (alpogeNativeHostField e q d) (AlpogeNativeCyclotomic e q d) x) := by
    intro x
    change (((alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
      (alpogeNativeRecMap e q d u) x : alpogeNativeHostField e q d) :
        AlpogeNativeCyclotomic e q d) = (alpogeNativeCyclotomicGalEquiv e q d).symm u x
    have hx := alpogeNativeHostGalEquiv_symm_apply e q d hq2 hd2 hqd
      ((alpogeNativeCyclotomicGalEquiv e q d).symm u) x
    rw [MulEquiv.apply_symm_apply] at hx
    exact hx
  constructor
  · intro h x
    rw [← h, MulEquiv.symm_apply_apply] at hbase
    exact hbase x
  · intro h
    have hσ : σ = (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
        (alpogeNativeRecMap e q d u) :=
      AlgEquiv.ext fun x => Subtype.ext ((h x).trans (hbase x).symm)
    rw [hσ, MulEquiv.apply_symm_apply]

/-- Genuine prime-ideal inertia is exactly the image of the local-unit
kernel at every prime, including the ramified primes. -/
theorem alpogeNativeHostField_inertia_iff
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (l : ℕ) [Fact l.Prime]
    (P : Ideal (𝓞 (alpogeNativeHostField e q d)))
    [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) :
    (∀ x : 𝓞 (alpogeNativeHostField e q d), σ • x - x ∈ P) ↔
      ∃ u : (ZMod (alpogeNativeHostN e q d))ˣ,
        (u : ZMod (alpogeNativeHostN e q d)).val ≡
          1 [MOD ordCompl[l] (alpogeNativeHostN e q d)] ∧
        alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ = alpogeNativeRecMap e q d u := by
  obtain ⟨Q, hQp, hQP, hQl, hI, _hF⟩ := NativePrimeLift.exists_over
    (E := alpogeNativeHostField e q d) (L := AlpogeNativeCyclotomic e q d) l P
  let : Q.IsPrime := hQp
  let : Q.LiesOver P := hQP
  let : Q.LiesOver (span {(l : ℤ)}) := hQl
  rw [hI σ]
  constructor
  · rintro ⟨τ, hres, hτ⟩
    obtain ⟨u, rfl⟩ := (tauN (alpogeNativeHostN e q d)).surjective τ
    exact ⟨u, (tauN_inertia_iff _ l Q u).mp hτ,
      (alpogeNativeHostGalEquiv_eq_recMap_iff e q d hq2 hd2 hqd σ u).mpr hres⟩
  · rintro ⟨u, hu, hσ⟩
    exact ⟨tauN (alpogeNativeHostN e q d) u,
      (alpogeNativeHostGalEquiv_eq_recMap_iff e q d hq2 hd2 hqd σ u).mp hσ,
      (tauN_inertia_iff _ l Q u).mpr hu⟩

/-- The finite inertia subgroup already used in the native all-prime-power
source is now identified with actual inertia of the constructed number field. -/
theorem alpogeNativeHostField_inertia_iff_hostData
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (l : ℕ) [Fact l.Prime]
    (P : Ideal (𝓞 (alpogeNativeHostField e q d)))
    [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) :
    (∀ x : 𝓞 (alpogeNativeHostField e q d), σ • x - x ∈ P) ↔
      (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ).toAdd ∈
        (alpogeNativeHostData e q d).inertia l := by
  rw [alpogeNativeHostField_inertia_iff e q d hq2 hd2 hqd l P σ]
  change (∃ u : (ZMod (alpogeNativeHostN e q d))ˣ,
      (u : ZMod (alpogeNativeHostN e q d)).val ≡
      1 [MOD ordCompl[l] (alpogeNativeHostN e q d)] ∧
      alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ = alpogeNativeRecMap e q d u) ↔
    alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ ∈
      (alpogeNativeLocalUnits (alpogeNativeHostN e q d) l).map (alpogeNativeRecMap e q d)
  constructor
  · rintro ⟨u, hu, hσ⟩
    exact ⟨u, (val_modEq_one_iff (Nat.ordCompl_dvd _ _) u).mp hu, hσ.symm⟩
  · rintro ⟨u, hu, hσ⟩
    exact ⟨u, (val_modEq_one_iff (Nat.ordCompl_dvd _ _) u).mpr hu, hσ.symm⟩

/-- A cyclotomic residue exponent congruent to the rational prime on the
prime-to-prime part of the modulus restricts to arithmetic Frobenius. -/
theorem alpogeNativeHostField_frob_of_modEq
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (l : ℕ) [Fact l.Prime]
    (P : Ideal (𝓞 (alpogeNativeHostField e q d)))
    [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d)
    (u : (ZMod (alpogeNativeHostN e q d))ˣ)
    (hu : (u : ZMod (alpogeNativeHostN e q d)).val ≡
      l [MOD ordCompl[l] (alpogeNativeHostN e q d)])
    (hσ : alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ = alpogeNativeRecMap e q d u) :
    IsArithFrobAt ℤ σ P := by
  obtain ⟨Q, hQp, hQP, hQl, _hI, hF⟩ := NativePrimeLift.exists_over
    (E := alpogeNativeHostField e q d) (L := AlpogeNativeCyclotomic e q d) l P
  let : Q.IsPrime := hQp
  let : Q.LiesOver P := hQP
  let : Q.LiesOver (span {(l : ℤ)}) := hQl
  exact hF σ (tauN (alpogeNativeHostN e q d) u)
    ((alpogeNativeHostGalEquiv_eq_recMap_iff e q d hq2 hd2 hqd σ u).mp hσ)
    (tauN_frob _ l Q u hu)

/-- The existing CRT Frobenius choice is an actual arithmetic Frobenius
at each prime of the same constructed field above the rational prime. -/
theorem alpogeNativeHostField_hostData_frob
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (l : ℕ) [Fact l.Prime]
    (P : Ideal (𝓞 (alpogeNativeHostField e q d)))
    [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    IsArithFrobAt ℤ
      ((alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
        (Multiplicative.ofAdd ((alpogeNativeHostData e q d).frob l))) P := by
  apply alpogeNativeHostField_frob_of_modEq e q d hq2 hd2 hqd l P _
    (alpogeNativeFrobUnit (alpogeNativeHostN e q d) l)
    (alpogeNativeFrobUnit_modEq (Fact.out : l.Prime)).1
  exact (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).apply_symm_apply _

/-- All actual Frobenius lifts have exactly the original tame residue
congruence. The ramified case retains the full inertia coset. -/
theorem alpogeNativeHostField_frob_iff
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (l : ℕ) [Fact l.Prime]
    (P : Ideal (𝓞 (alpogeNativeHostField e q d)))
    [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) :
    IsArithFrobAt ℤ σ P ↔
      ∃ u : (ZMod (alpogeNativeHostN e q d))ˣ,
        (u : ZMod (alpogeNativeHostN e q d)).val ≡
          l [MOD ordCompl[l] (alpogeNativeHostN e q d)] ∧
        alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ = alpogeNativeRecMap e q d u := by
  refine ⟨fun hσ => ?_, fun ⟨u, hu, h⟩ =>
    alpogeNativeHostField_frob_of_modEq e q d hq2 hd2 hqd l P σ u hu h⟩
  let w := alpogeNativeFrobUnit (alpogeNativeHostN e q d) l
  let F := (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
    (alpogeNativeRecMap e q d w)
  have hF : IsArithFrobAt ℤ F P := alpogeNativeHostField_hostData_frob e q d hq2 hd2 hqd l P
  have hw : (w : ZMod (alpogeNativeHostN e q d)).val ≡
      l [MOD ordCompl[l] (alpogeNativeHostN e q d)] :=
    (alpogeNativeFrobUnit_modEq (Fact.out : l.Prime)).1
  have hFw : alpogeNativeHostGalEquiv e q d hq2 hd2 hqd F = alpogeNativeRecMap e q d w :=
    (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).apply_symm_apply _
  have hM := Nat.ordCompl_dvd (alpogeNativeHostN e q d) l
  rw [NativePrimeLift.frob_iff_inertia P F σ hF,
    alpogeNativeHostField_inertia_iff e q d hq2 hd2 hqd l P,
    map_mul, map_inv, hFw] at hσ
  obtain ⟨u, hu, h1⟩ := hσ
  refine ⟨u * w, ?_, ?_⟩
  · rw [val_modEq_one_iff hM] at hu
    rw [val_modEq_iff hM] at hw ⊢
    rw [map_mul, hu, one_mul, hw]
  · rw [map_mul, ← h1]
    exact (_root_.inv_mul_cancel_right
      (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ)
      (alpogeNativeRecMap e q d w)).symm

/-- The actual Frobenius coset is precisely the additive coset already
used in the native arithmetic source, with its existing CRT representative. -/
theorem alpogeNativeHostField_frob_iff_hostData
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (l : ℕ) [Fact l.Prime]
    (P : Ideal (𝓞 (alpogeNativeHostField e q d)))
    [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) :
    IsArithFrobAt ℤ σ P ↔
      (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ).toAdd -
        (alpogeNativeHostData e q d).frob l ∈ (alpogeNativeHostData e q d).inertia l := by
  let F := (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
    (Multiplicative.ofAdd ((alpogeNativeHostData e q d).frob l))
  have hF : IsArithFrobAt ℤ F P := alpogeNativeHostField_hostData_frob e q d hq2 hd2 hqd l P
  rw [NativePrimeLift.frob_iff_inertia P F σ hF,
    alpogeNativeHostField_inertia_iff_hostData e q d hq2 hd2 hqd l P]
  simp only [map_mul, map_inv, F, MulEquiv.apply_symm_apply,
    toAdd_mul, toAdd_inv, toAdd_ofAdd]
  exact (congrArg
    (fun z : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
      z ∈ (alpogeNativeHostData e q d).inertia l)
    (_root_.sub_eq_add_neg
      (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ).toAdd
      ((alpogeNativeHostData e q d).frob l))).symm.to_iff

/-- Complex conjugation is outside the actual inertia group at every
rational prime. One of the two distinct quadratic signs is unramified. -/
theorem alpogeNativeHostConj_not_inertia
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3)
    (l : ℕ) [Fact l.Prime]
    (P : Ideal (𝓞 (alpogeNativeHostField e q d)))
    [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ¬ ∀ x : 𝓞 (alpogeNativeHostField e q d),
      alpogeNativeHostConj e q d • x - x ∈ P := by
  intro h
  obtain ⟨u, hu, hσ⟩ :=
    (alpogeNativeHostField_inertia_iff e q d hq2 hd2 hqd l P _).mp h
  rw [alpogeNativeHostGalEquiv_conj e q d hq2 hd2 hqd hq4 hd4] at hσ
  have hunit : ∀ (r : ℕ) (hr : r.Prime) (hrN : r ∣ alpogeNativeHostN e q d)
      (hlr : l ≠ r), ZMod.unitsMap hrN u = 1 := by
    intro r hr hrN hlr
    have hlnd : ¬ l ∣ r := fun hdiv =>
      hlr ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hr).mp hdiv)
    have hrM : r ∣ ordCompl[l] (alpogeNativeHostN e q d) :=
      Nat.dvd_ordCompl_of_dvd_not_dvd hrN hlnd
    exact (val_modEq_one_iff hrN u).mp (hu.of_dvd hrM)
  by_cases hld : l = d
  · have hq := hunit q (Fact.out : q.Prime) (alpogeNativeQ_dvd_hostN e q d)
      (by intro hlq; exact hqd (hlq.symm.trans hld))
    have hbit := congrArg (fun g : Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e) =>
      g.toAdd.1.2) hσ
    have hzero : (alpogeNativeRecMap e q d u).toAdd.1.2 = 0 := by
      change (alpogeNativeSign2 (alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d) u)).toAdd = 0
      simp only [alpogeNativeLegU, MonoidHom.comp_apply, hq, map_one, toAdd_one]
    change (1 : ZMod 2) = (alpogeNativeRecMap e q d u).toAdd.1.2 at hbit
    rw [hzero] at hbit
    exact one_ne_zero hbit
  · have hd := hunit d (Fact.out : d.Prime) (alpogeNativeD_dvd_hostN e q d) hld
    have hbit := congrArg (fun g : Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e) =>
      g.toAdd.1.1) hσ
    have hzero : (alpogeNativeRecMap e q d u).toAdd.1.1 = 0 := by
      change (alpogeNativeSign2 (alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u)).toAdd = 0
      simp only [alpogeNativeLegU, MonoidHom.comp_apply, hd, map_one, toAdd_one]
    change (1 : ZMod 2) = (alpogeNativeRecMap e q d u).toAdd.1.1 at hbit
    rw [hzero] at hbit
    exact one_ne_zero hbit

namespace NativePrimeLift

theorem exists_prime_liesOver {M : Type} [Field M] [NumberField M]
    (P : Ideal (𝓞 M)) [P.IsPrime] (h0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ P.LiesOver (span {(p : ℤ)}) := by
  have hne : Ideal.comap (algebraMap ℤ (𝓞 M)) P ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact Ideal.under_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.comap (algebraMap ℤ (𝓞 M)) P = Ideal.span {g} :=
    Submodule.IsPrincipal.principal (Ideal.comap (algebraMap ℤ (𝓞 M)) P)
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hne
    rw [hg, Ideal.span_singleton_eq_bot]
  have hpr : (Ideal.span {g}).IsPrime := by rw [← hg]; infer_instance
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp hpr
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, ⟨?_⟩⟩
  rw [Int.span_natAbs]
  exact hg.symm

end NativePrimeLift

/-- The original all-finite-prime `unramEF` conclusion is now proved for
the actual native fixed field and its actual complex conjugation. -/
theorem alpogeNativeHostConj_unramEF
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3)
    (P : Ideal (𝓞 (alpogeNativeHostField e q d))) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ¬ ∀ x : 𝓞 (alpogeNativeHostField e q d),
      alpogeNativeHostConj e q d • x - x ∈ P := by
  let : P.IsPrime := hP
  obtain ⟨l, hl, hPl⟩ := NativePrimeLift.exists_prime_liesOver P hP0
  let : Fact l.Prime := ⟨hl⟩
  let : P.LiesOver (span {(l : ℤ)}) := hPl
  exact alpogeNativeHostConj_not_inertia e q d hq2 hd2 hqd hq4 hd4 l P

end RHLean.Analysis

end
