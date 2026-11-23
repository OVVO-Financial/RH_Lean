import RHLean.Analysis.AlpogeThin.NativeDyadicHostRamifiedPrimes

/-!
# Exact prime-power class weights of the actual native host

The full native Frobenius/inertia census is identified with the odd-power
class sums used by Alpöge's local multiplicity argument.  The conductor
primes 2 and q contribute zero, and every power of d contributes with
coefficient one at its actual non-CM-type inertia-coset site.  The same
widths, cutoff, CRT Frobenius and inertia are retained throughout.

This is the arithmetic inlet to the finite-place gain estimate.  It does
not assert the local lattice inclusion, module length or multiplicity
inequality which produces that gain.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/GlobalSchurBounds/FrameCodeOfAdditive.lean`,
`right₃`, `inert_sum`, and
`src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean`,
`pb_atD`, `ASK_at`.  The proofs below use the existing native full census
and the actual modular-unit host instead of assuming a geometric datum.
The source archive/mirror states no license; attribution is retained
without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin

open Formalism.FrobeniusOrbits Formalism.HC NativeCyclotomicResidue

/-- The nontrivial d-inertia element in the native d,q coordinates. -/
def nativeDyadicDInvolution (e : ℕ) :
    AlpogeNativeE0 × AlpogeNativeDyadicH e := ((1, 0), 0)

theorem nativeDyadicDInvolution_ne_zero (e : ℕ) :
    nativeDyadicDInvolution e ≠ 0 := by
  intro h
  have := congrArg (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e => g.1.1) h
  norm_num [nativeDyadicDInvolution] at this

theorem nativeDyadicFullHostEquiv_dInvolution (e : ℕ) :
    nativeDyadicFullHostEquiv e (Multiplicative.ofAdd (nativeDyadicDInvolution e)) =
      (nativeDyadicFrame e).iod := by
  rw [nativeDyadicFullHostEquiv_apply]
  change ((nativeDyadicSignEquiv.symm (Multiplicative.ofAdd (0 : ZMod 2)),
    nativeDyadicSignEquiv.symm (Multiplicative.ofAdd (1 : ZMod 2))),
      Multiplicative.ofAdd ((nativeDyadicFrameEquiv e).symm 0)) = ((1, -1), 1)
  simp only [nativeDyadicSignEquiv_symm_zero, nativeDyadicSignEquiv_symm_one,
    map_zero, ofAdd_zero]

private theorem nativePrimePowerLegU_of_modEq
    {N p a : ℕ} [NeZero N] [Fact p.Prime] (hp : p ∣ N)
    (u : (ZMod N)ˣ) (hu : (u : ZMod N).val ≡ a [MOD p]) :
    ((alpogeNativeLegU N p hp u : ℤˣ) : ℤ) = jacobiSym (a : ℤ) p := by
  rw [NativeQuadraticRoot.legU_val,
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu,
    ← jacobiSym.legendreSym.to_jacobiSym]
  simp only [legendreSym, Int.cast_natCast]

private theorem nativePrimePowerRec_inPhi_of_modEq_one
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (u : (ZMod (alpogeNativeHostN e q d))ˣ)
    (hu : (u : ZMod (alpogeNativeHostN e q d)).val ≡ 1 [MOD d]) :
    alpogeNativeInPhi (alpogeNativeRecMap e q d u).toAdd := by
  have hmap : ZMod.unitsMap (alpogeNativeD_dvd_hostN e q d) u = 1 :=
    (val_modEq_one_iff (alpogeNativeD_dvd_hostN e q d) u).mp hu
  have hleg : alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u = 1 := by
    simp only [alpogeNativeLegU, MonoidHom.comp_apply, hmap, map_one]
  change (if alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) u = 1
    then (0 : ZMod 2) else 1) = 0
  simp only [hleg, ↓reduceIte]

/-- The actual unramified inertia subgroup is trivial. -/
theorem nativeDyadicHostData_inertia_unramified
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hp : p.Prime) (hpN : ¬ p ∣ alpogeNativeHostN e q d) :
    (alpogeNativeHostData e q d).inertia p = ⊥ := by
  simp [alpogeNativeHostData, alpogeNativeCftData,
    alpogeNativeLocalUnits_unramified _ p hp hpN]

/-- All elements of the literal native d-inertia subgroup, including both
directions of the membership characterization. -/
theorem nativeDyadicHostData_mem_inertia_d
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (g : AlpogeNativeE0 × AlpogeNativeDyadicH e) :
    g ∈ (alpogeNativeHostData e q d).inertia d ↔
      g = 0 ∨ g = nativeDyadicDInvolution e := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hd4 : d % 4 = 3 := by omega
  have hcompl := nativeDyadicOrdCompl_d e q d hd2 hqd
  change Multiplicative.ofAdd g ∈
    (alpogeNativeLocalUnits (alpogeNativeHostN e q d) d).map
      (alpogeNativeRecMap e q d) ↔ _
  constructor
  · rintro ⟨u, hu, hug⟩
    have hu' := (val_modEq_one_iff
      (Nat.ordCompl_dvd (alpogeNativeHostN e q d) d) u).mpr hu
    rw [hcompl] at hu'
    rcases nativeDyadicArt_d e q d u hu' with h | h
    · left
      apply Multiplicative.ofAdd.injective
      apply (nativeDyadicFullHostEquiv e).injective
      rw [← hug]
      change nativeDyadicArt e q d u = 1
      exact h
    · right
      apply Multiplicative.ofAdd.injective
      apply (nativeDyadicFullHostEquiv e).injective
      rw [nativeDyadicFullHostEquiv_dInvolution, ← hug]
      exact h
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · obtain ⟨u, hu, hi⟩ := nativeDyadicArt_exists_iod e q d hd2 hqd hd4
      refine ⟨u, ?_, ?_⟩
      · apply (val_modEq_one_iff
          (Nat.ordCompl_dvd (alpogeNativeHostN e q d) d) u).mp
        rwa [hcompl]
      · apply (nativeDyadicFullHostEquiv e).injective
        rw [nativeDyadicFullHostEquiv_dInvolution]
        exact hi

theorem nativeDyadicHostData_inertia_d_card
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hH : HostHyp q d) :
    (Finset.univ.filter (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
      g ∈ (alpogeNativeHostData e q d).inertia d)).card = 2 := by
  classical
  have hs : Finset.univ.filter (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
      g ∈ (alpogeNativeHostData e q d).inertia d) =
        {0, nativeDyadicDInvolution e} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      nativeDyadicHostData_mem_inertia_d e q d hH,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hs]
  simp only [Finset.card_insert_of_notMem
    (by simpa only [Finset.mem_singleton] using (nativeDyadicDInvolution_ne_zero e).symm),
    Finset.card_singleton]

/-- The existing CRT representative at d has trivial d-character.  This
fixes the representative of the exceptional non-CM-type coset exactly. -/
theorem nativeDyadicHostData_frob_d_inPhi
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hH : HostHyp q d) :
    alpogeNativeInPhi ((alpogeNativeHostData e q d).frob d) := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hcompl := nativeDyadicOrdCompl_d e q d hd2 hqd
  have hproj : ordProj[d] (alpogeNativeHostN e q d) = d := by
    have hmul := Nat.ordProj_mul_ordCompl_eq_self (alpogeNativeHostN e q d) d
    rw [hcompl] at hmul
    have hpos : 0 < 2 ^ (e + 2) * q :=
      mul_pos (pow_pos (by decide) _) (Fact.out : q.Prime).pos
    unfold alpogeNativeHostN at hmul ⊢
    nlinarith
  have hu := (alpogeNativeFrobUnit_modEq (N := alpogeNativeHostN e q d)
    (Fact.out : d.Prime)).2
  rw [hproj] at hu
  exact nativePrimePowerRec_inPhi_of_modEq_one e q d _ hu

private theorem nativePrimePowerJacobi_typeI
    {e q d p : ℕ} (hH : HostHyp q d) (hp : p.Prime)
    (hpA : p ∣ 2 ^ (e + 2) * q) : jacobiSym (p : ℤ) d = 1 := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have hd8 : d % 8 = 7 := by omega
  rcases hp.dvd_mul.mp hpA with hp2 | hpq
  · have hp2' : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hp2)
    subst p
    rw [Nat.cast_ofNat, jacobiSym.at_two (b := d) (Nat.odd_iff.mpr (by omega)),
      ZMod.χ₈_nat_eq_if_mod_eight]
    norm_num [hd8]
    omega
  · have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hH.1).mp hpq
    subst p
    have hs := hH.2.2.2.2
    rw [jacobiSym.neg _ (Nat.odd_iff.mpr (by omega)),
      ZMod.χ₄_nat_three_mod_four hq4, neg_one_mul] at hs
    rw [jacobiSym.quadratic_reciprocity_three_mod_four hq4 hd4]
    linarith

/-- At each conductor prime other than d, both actual inertia and the
actual Frobenius representative preserve the native CM type. -/
theorem nativeDyadicHostData_typeI
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (hp : p.Prime) (hpA : p ∣ 2 ^ (e + 2) * q) :
    (∀ g ∈ (alpogeNativeHostData e q d).inertia p, alpogeNativeInPhi g) ∧
      alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p) := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hc : (2 ^ (e + 2) * q).Coprime d :=
    (((Nat.coprime_primes Nat.prime_two (Fact.out : d.Prime)).mpr hd2.symm).pow_left _).mul_left
      ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : d.Prime)).mpr hqd)
  have hpnd : ¬ p ∣ d := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpA hc) h)
  have hdM : d ∣ ordCompl[p] (alpogeNativeHostN e q d) :=
    Nat.dvd_ordCompl_of_dvd_not_dvd (alpogeNativeD_dvd_hostN e q d) hpnd
  constructor
  · intro g hg
    obtain ⟨u, hu, hug⟩ := hg
    have hu' := (val_modEq_one_iff
      (Nat.ordCompl_dvd (alpogeNativeHostN e q d) p) u).mpr hu
    have h := nativePrimePowerRec_inPhi_of_modEq_one e q d u (hu'.of_dvd hdM)
    rw [hug] at h
    change alpogeNativeInPhi g at h
    exact h
  · have hu := (alpogeNativeFrobUnit_modEq (N := alpogeNativeHostN e q d) hp).1
    have hleg := nativePrimePowerLegU_of_modEq (alpogeNativeD_dvd_hostN e q d)
      (alpogeNativeFrobUnit (alpogeNativeHostN e q d) p) (hu.of_dvd hdM)
    rw [nativePrimePowerJacobi_typeI hH hp hpA] at hleg
    have hleg' : alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d)
        (alpogeNativeFrobUnit (alpogeNativeHostN e q d) p) = 1 := Units.ext hleg
    change (if alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d)
      (alpogeNativeFrobUnit (alpogeNativeHostN e q d) p) = 1
        then (0 : ZMod 2) else 1) = 0
    simp only [hleg', ↓reduceIte]

/-- The exact parity criterion holds for every exponent, not merely the
first prime occurrence. -/
theorem nativeDyadic_not_inPhi_nsmul
    (e : ℕ) (g : AlpogeNativeE0 × AlpogeNativeDyadicH e) (i : ℕ) :
    ¬ alpogeNativeInPhi (i • g) ↔ Odd i ∧ ¬ alpogeNativeInPhi g := by
  change i • g.1.1 ≠ 0 ↔ Odd i ∧ g.1.1 ≠ 0
  rw [nsmul_eq_mul, mul_ne_zero_iff, Ne, ZMod.natCast_eq_zero_iff_even,
    Nat.not_even_iff_odd]

private theorem nativePrimePowerJacobi_unramified {p d : ℕ}
    (hp : p % 2 = 1) (hd : d % 4 = 3) :
    jacobiSym (-(d : ℤ)) p = jacobiSym (p : ℤ) d := by
  rw [jacobiSym.neg _ (Nat.odd_iff.mpr hp)]
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h (Nat.odd_iff.mpr (by omega))]
  · rw [ZMod.χ₄_nat_three_mod_four h,
      jacobiSym.quadratic_reciprocity_three_mod_four hd h]
    ring

/-- The unramified native bit is the actual quadratic splitting sign. -/
theorem nativeDyadicHostData_frob_not_inPhi_iff
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (hp : p.Prime)
    (hpN : ¬ p ∣ alpogeNativeHostN e q d) :
    ¬ alpogeNativeInPhi ((alpogeNativeHostData e q d).frob p) ↔
      jacobiSym (-(d : ℤ)) p = -1 := by
  have hdmod := hH.2.2.2.1
  have hd4 : d % 4 = 3 := by omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpN ((dvd_pow_self 2 (by omega : e + 2 ≠ 0)).trans
      (alpogeNativeTwo_dvd_hostN e q d))
  have hcompl : ordCompl[p] (alpogeNativeHostN e q d) = alpogeNativeHostN e q d :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ hp).mpr (Or.inr hpN)
  have hu := (alpogeNativeFrobUnit_modEq (N := alpogeNativeHostN e q d) hp).1
  rw [hcompl] at hu
  have hleg := nativePrimePowerLegU_of_modEq (alpogeNativeD_dvd_hostN e q d)
    (alpogeNativeFrobUnit (alpogeNativeHostN e q d) p)
    (hu.of_dvd (alpogeNativeD_dvd_hostN e q d))
  rw [← nativePrimePowerJacobi_unramified (hp.eq_two_or_odd.resolve_left hp2) hd4] at hleg
  change (if alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d)
    (alpogeNativeFrobUnit (alpogeNativeHostN e q d) p) = 1
      then (0 : ZMod 2) else 1) ≠ 0 ↔ _
  rcases Int.units_eq_one_or (alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d)
    (alpogeNativeFrobUnit (alpogeNativeHostN e q d) p)) with h | h
  · rw [h] at hleg
    simp [h, ← hleg]
  · rw [h] at hleg
    simp [h, ← hleg]

/-- The actual class measure at one prime-power site, applied to any
site weight.  Its inertia normalization is inherited literally from the
native complete prime-power census. -/
def nativeDyadicHostPrimePowerWeight
    (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime]
    (F : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℂ) : ℂ := by
  classical
  exact ∑ g ∈ Finset.univ.filter
      (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e => ¬ alpogeNativeInPhi g),
    (if g - i • (alpogeNativeHostData e q d).frob p ∈
        (alpogeNativeHostData e q d).inertia p then
      (2 : ℂ) / ((Finset.univ.filter
        (fun u : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
          u ∈ (alpogeNativeHostData e q d).inertia p)).card : ℂ)
      else 0) * F g

/-- Exact coefficient two at every unramified inert odd power, zero at
every other unramified power.  The class may move with the exponent. -/
theorem nativeDyadicHostPrimePowerWeight_unramified
    (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (hp : p.Prime)
    (hpN : ¬ p ∣ alpogeNativeHostN e q d)
    (F : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℂ) :
    nativeDyadicHostPrimePowerWeight e q d p i F =
      if Odd i ∧ jacobiSym (-(d : ℤ)) p = -1 then
        2 * F (i • (alpogeNativeHostData e q d).frob p) else 0 := by
  classical
  have hI := nativeDyadicHostData_inertia_unramified e q d p hp hpN
  have hnon : ¬ alpogeNativeInPhi (i • (alpogeNativeHostData e q d).frob p) ↔
      Odd i ∧ jacobiSym (-(d : ℤ)) p = -1 := by
    rw [nativeDyadic_not_inPhi_nsmul,
      nativeDyadicHostData_frob_not_inPhi_iff e q d p hH hp hpN]
  have hmem (g : AlpogeNativeE0 × AlpogeNativeDyadicH e) :
      g - i • (alpogeNativeHostData e q d).frob p ∈
        (alpogeNativeHostData e q d).inertia p ↔
      g = i • (alpogeNativeHostData e q d).frob p := by
    rw [hI, AddSubgroup.mem_bot]
    exact sub_eq_zero
  have hc : (Finset.univ.filter (fun u : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
      u ∈ (alpogeNativeHostData e q d).inertia p)).card = 1 := by
    have hs : Finset.univ.filter
        (fun u : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
          u ∈ (alpogeNativeHostData e q d).inertia p) = {0} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hI,
        AddSubgroup.mem_bot, Finset.mem_singleton]
    rw [hs, Finset.card_singleton]
  unfold nativeDyadicHostPrimePowerWeight
  rw [hc]
  simp only [hmem, Nat.cast_one, div_one, ite_mul, zero_mul]
  by_cases h : Odd i ∧ jacobiSym (-(d : ℤ)) p = -1
  · rw [ite_eq_left h]
    have hm : i • (alpogeNativeHostData e q d).frob p ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e => ¬ alpogeNativeInPhi g) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnon.mpr h⟩
    rw [Finset.sum_eq_single (i • (alpogeNativeHostData e q d).frob p)]
    · simp
    · intro g _ hg
      simp only [hg, ↓reduceIte]
    · exact fun hn => (hn hm).elim
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro g hg
    have hne : g ≠ i • (alpogeNativeHostData e q d).frob p := by
      intro heq
      subst g
      exact h (hnon.mp (Finset.mem_filter.mp hg).2)
    simp only [hne, ↓reduceIte]

/-- No omitted ramified mass: at 2 and q the full inertia coset is in
the CM type, hence its contribution to this non-CM-type sum is zero. -/
theorem nativeDyadicHostPrimePowerWeight_typeI
    (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (hp : p.Prime) (hpA : p ∣ 2 ^ (e + 2) * q)
    (F : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℂ) :
    nativeDyadicHostPrimePowerWeight e q d p i F = 0 := by
  classical
  obtain ⟨hI, hF⟩ := nativeDyadicHostData_typeI e q d p hH hp hpA
  unfold nativeDyadicHostPrimePowerWeight
  apply Finset.sum_eq_zero
  intro g hg
  have hn := (Finset.mem_filter.mp hg).2
  have hmem : g - i • (alpogeNativeHostData e q d).frob p ∉
      (alpogeNativeHostData e q d).inertia p := by
    intro hm
    have h := hI _ hm
    change g.1.1 - i • ((alpogeNativeHostData e q d).frob p).1.1 = 0 at h
    change ((alpogeNativeHostData e q d).frob p).1.1 = 0 at hF
    rw [hF, smul_zero, sub_zero] at h
    exact hn h
  simp only [hmem, ↓reduceIte, zero_mul]

/-- Every d-power has coefficient one at the unique non-CM-type point
of its actual two-element inertia coset.  No parity restriction occurs. -/
theorem nativeDyadicHostPrimePowerWeight_d
    (e q d i : ℕ) [Fact q.Prime] [Fact d.Prime] (hH : HostHyp q d)
    (F : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℂ) :
    nativeDyadicHostPrimePowerWeight e q d d i F =
      F (nativeDyadicDInvolution e + i • (alpogeNativeHostData e q d).frob d) := by
  classical
  let g0 := i • (alpogeNativeHostData e q d).frob d
  let g1 := nativeDyadicDInvolution e + g0
  have hg0 : alpogeNativeInPhi g0 := by
    have h := nativeDyadicHostData_frob_d_inPhi e q d hH
    change ((alpogeNativeHostData e q d).frob d).1.1 = 0 at h
    change i • ((alpogeNativeHostData e q d).frob d).1.1 = 0
    rw [h, smul_zero]
  have hg1 : ¬ alpogeNativeInPhi g1 := by
    change (nativeDyadicDInvolution e).1.1 + g0.1.1 ≠ 0
    change g0.1.1 = 0 at hg0
    rw [hg0, add_zero]
    norm_num [nativeDyadicDInvolution]
  have hm (g : AlpogeNativeE0 × AlpogeNativeDyadicH e)
      (hg : ¬ alpogeNativeInPhi g) :
      g - g0 ∈ (alpogeNativeHostData e q d).inertia d ↔ g = g1 := by
    rw [nativeDyadicHostData_mem_inertia_d e q d hH]
    constructor
    · rintro (h | h)
      · have heq : g = g0 := sub_eq_zero.mp h
        subst g
        exact (hg hg0).elim
      · exact (sub_eq_iff_eq_add).mp h
    · intro h
      right
      exact (sub_eq_iff_eq_add).mpr h
  unfold nativeDyadicHostPrimePowerWeight
  rw [nativeDyadicHostData_inertia_d_card e q d hH]
  norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℂ) ≠ 0)]
  change (∑ g ∈ Finset.univ.filter
    (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e => ¬ alpogeNativeInPhi g),
    (if g - g0 ∈ (alpogeNativeHostData e q d).inertia d then 1 else 0) * F g) = F g1
  rw [Finset.sum_eq_single g1]
  · rw [ite_eq_left ((hm g1 hg1).mpr rfl), one_mul]
  · intro g hg hne
    rw [hm g (Finset.mem_filter.mp hg).2]
    simp only [hne, ↓reduceIte, zero_mul]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg1⟩)).elim

/-- The original inert classes, still tested by the actual quadratic
symbol and excluding precisely the original conductor primes. -/
def nativeDyadicInertPrimes (e q d N : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.range (N + 1)).filter Nat.Prime).filter
    (fun p => ¬ p ∣ alpogeNativeHostN e q d ∧ jacobiSym (-(d : ℤ)) p = -1)

/-- Every odd exponent at every actual unramified inert prime, with its
moving Frobenius class and the same sharp width. -/
def nativeDyadicOddClassASK
    (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) : ℂ :=
  ∑ p ∈ nativeDyadicInertPrimes e q d N,
    (2 * Real.log p : ℂ) * ∑ i ∈ (Finset.Icc 1 N).filter Odd,
      alpogeNativeSiteCut a w t (p ^ i)
        (i • (alpogeNativeHostData e q d).frob p)

/-- The complete exceptional d-prime correction, without an odd-exponent
restriction or an unramified coefficient two. -/
def nativeDyadicDPrimeASK
    (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) : ℂ :=
  (Real.log d : ℂ) * ∑ i ∈ Finset.Icc 1 N,
    alpogeNativeSiteCut a w t (d ^ i)
      (nativeDyadicDInvolution e + i • (alpogeNativeHostData e q d).frob d)

private theorem nativePrimePowerSiteCut_zero_above
    (e : ℕ) (N : ℕ) (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ))
    (n : ℕ) (g : AlpogeNativeE0 × AlpogeNativeDyadicH e)
    (hg : ¬ alpogeNativeInPhi g) (hn : N < n) :
    alpogeNativeSiteCut a w t n g = 0 := by
  have hg1 : g.1.1 = 1 := by
    have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact (hc g.1.1).resolve_left hg
  have hρ : alpogeNativeInPhi (alpogeNativePartner t g) := by
    change 1 + g.1.1 + 0 = (0 : ZMod 2)
    rw [hg1]
    decide
  have hw0 := hw _ hρ
  have hbound := (div_le_iff₀ hw0).mp (hN _ hρ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le N).trans_lt hn
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
  have hcut : a / (n : ℝ) ≤ w (alpogeNativePartner t g) := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  simp only [alpogeNativeSiteCut, max_eq_right (sub_nonpos.mpr hcut), Complex.ofReal_zero]

private theorem nativeDyadicDPrimeASK_zero_of_lt
    (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ)) (hNd : N < d) :
    nativeDyadicDPrimeASK e q d N a t w = 0 := by
  unfold nativeDyadicDPrimeASK
  have hs : (∑ i ∈ Finset.Icc 1 N,
      alpogeNativeSiteCut a w t (d ^ i)
        (nativeDyadicDInvolution e + i • (alpogeNativeHostData e q d).frob d)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply nativePrimePowerSiteCut_zero_above e N a t w hw hN
    · have hf := nativeDyadicHostData_frob_d_inPhi e q d hH
      change ((alpogeNativeHostData e q d).frob d).1.1 = 0 at hf
      change (nativeDyadicDInvolution e).1.1 +
        i • ((alpogeNativeHostData e q d).frob d).1.1 ≠ 0
      rw [hf, smul_zero, add_zero]
      norm_num [nativeDyadicDInvolution]
    · have hi0 : i ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      exact hNd.trans_le (Nat.le_self_pow hi0 d)
  rw [hs, mul_zero]

/-- The literal native full ASK is the sum of all original odd-power
class weights and the complete d-prime correction.  Every cutoff
endpoint is the existing `Icc 1 N`; positivity only removes terms
already proved zero above that cutoff. -/
theorem nativeDyadicHost_fullASK_eq_oddClassSums_add_dCorrection
    (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ)) :
    alpogeNativeFullKernelASK (alpogeNativeHostData e q d).inertia
      (alpogeNativeHostData e q d).frob N a t w =
        nativeDyadicOddClassASK e q d N a t w +
          nativeDyadicDPrimeASK e q d N a t w := by
  classical
  rw [alpogeNativeFullKernelASK_eq_primePowerCensus _ _ N a t w hw hN]
  let P := (Finset.range (N + 1)).filter Nat.Prime
  let A : ℕ → ℂ := fun p => (2 * Real.log p : ℂ) *
    ∑ i ∈ (Finset.Icc 1 N).filter Odd,
      alpogeNativeSiteCut a w t (p ^ i) (i • (alpogeNativeHostData e q d).frob p)
  have hlocal (p : ℕ) (hpP : p ∈ P) :
      (∑ i ∈ Finset.Icc 1 N, (Real.log p : ℂ) *
        nativeDyadicHostPrimePowerWeight e q d p i
          (alpogeNativeSiteCut a w t (p ^ i))) =
        (if ¬ p ∣ alpogeNativeHostN e q d ∧ jacobiSym (-(d : ℤ)) p = -1 then A p else 0) +
        (if p = d then nativeDyadicDPrimeASK e q d N a t w else 0) := by
    have hp : p.Prime := (Finset.mem_filter.mp hpP).2
    by_cases hpd : p = d
    · subst p
      have hdN := alpogeNativeD_dvd_hostN e q d
      simp only [hdN, not_true_eq_false, false_and, ↓reduceIte, zero_add]
      simp only [nativeDyadicHostPrimePowerWeight_d e q d _ hH]
      exact (Finset.mul_sum _ _ _).symm
    · rw [ite_eq_right hpd, add_zero]
      by_cases hpN : p ∣ alpogeNativeHostN e q d
      · have hpA : p ∣ 2 ^ (e + 2) * q := by
          rcases hp.dvd_mul.mp hpN with hpA | hpd'
          · exact hpA
          · exact (hpd ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : d.Prime)).mp hpd')).elim
        simp only [hpN, not_true_eq_false, false_and, ↓reduceIte,
          nativeDyadicHostPrimePowerWeight_typeI e q d p _ hH hp hpA,
          mul_zero, Finset.sum_const_zero]
      · simp only [hpN, not_false_eq_true, true_and]
        simp only [nativeDyadicHostPrimePowerWeight_unramified e q d p _ hH hp hpN]
        by_cases hJ : jacobiSym (-(d : ℤ)) p = -1
        · simp only [hJ, and_true, ↓reduceIte]
          unfold A
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          split_ifs <;> ring
        · simp only [hJ, and_false, ↓reduceIte, mul_zero, Finset.sum_const_zero]
  change (∑ p ∈ P, ∑ i ∈ Finset.Icc 1 N, (Real.log p : ℂ) *
    nativeDyadicHostPrimePowerWeight e q d p i
      (alpogeNativeSiteCut a w t (p ^ i))) = _
  rw [Finset.sum_congr rfl hlocal, Finset.sum_add_distrib]
  have hodd : (∑ p ∈ P,
      if ¬ p ∣ alpogeNativeHostN e q d ∧ jacobiSym (-(d : ℤ)) p = -1 then A p else 0) =
      nativeDyadicOddClassASK e q d N a t w := by
    exact (Finset.sum_filter (s := P)
      (fun p => ¬ p ∣ alpogeNativeHostN e q d ∧ jacobiSym (-(d : ℤ)) p = -1) A).symm
  rw [hodd]
  congr 1
  by_cases hdP : d ∈ P
  · rw [Finset.sum_eq_single d]
    · simp only [↓reduceIte]
    · intro p _ hpd
      simp only [hpd, ↓reduceIte]
    · exact fun h => (h hdP).elim
  · have hNd : N < d := by
      have hp : d.Prime := Fact.out
      simpa only [P, Finset.mem_filter, Finset.mem_range, hp, and_true,
        not_lt, Nat.add_one_le_iff] using hdP
    rw [nativeDyadicDPrimeASK_zero_of_lt e q d N hH a t w hw hN hNd]
    simp only [ite_self, Finset.sum_const_zero]

/-- Signed source fidelity: the same full `De`, including its original
ell-dependent principal and primitive-character corrections, is exactly
the local odd-power sums plus all d powers minus the original MAIN. -/
theorem nativeDyadicHost_De_eq_oddClassSums_add_dCorrection_sub_MAIN
    (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d)
    (ell : AddChar (AlpogeNativeE0 × AlpogeNativeDyadicH e) ℂ → ℂ)
    (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (ha : 0 < a)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ)) :
    alpogeNativeDe (alpogeNativeHostData e q d).inertia
      (alpogeNativeHostData e q d).frob ell a t w =
        nativeDyadicOddClassASK e q d N a t w +
          nativeDyadicDPrimeASK e q d N a t w - alpogeNativeMAIN ell a w := by
  rw [← alpogeNativeConcreteHostASK_sub_MAIN_eq_De e q d ell N a t w ha hw hN,
    nativeDyadicHost_fullASK_eq_oddClassSums_add_dCorrection e q d N hH a t w hw hN]

private theorem nativePrimePower_geom_positive
    (I : Finset ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hI : ∀ i ∈ I, 1 ≤ i) :
    ∑ i ∈ I, r ^ i ≤ r / (1 - r) := by
  have hsub : I ⊆ Finset.Ico 1 (I.sup id + 1) := by
    intro i hi
    have hisup : i ≤ I.sup id := Finset.le_sup (f := id) hi
    exact Finset.mem_Ico.mpr ⟨hI i hi, by omega⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => pow_nonneg hr0 i)
  have hgeom := geom_sum_Ico_le_of_lt_one
    (x := r) (m := 1) (n := I.sup id + 1) hr0 hr1
  rw [pow_one] at hgeom
  exact hsum.trans hgeom

/-- The full d-prime term is a nonnegative real number. -/
theorem nativeDyadicDPrimeASK_re_nonneg
    (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) :
    0 ≤ (nativeDyadicDPrimeASK e q d N a t w).re := by
  simp only [nativeDyadicDPrimeASK, alpogeNativeSiteCut, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Real.log_natCast_nonneg d)
    (Finset.sum_nonneg fun i _ => le_max_right _ _)

/-- A quantitative payment for all ramified d-powers on the SAME native
widths.  The exact geometric-series constant is `a * log d / (d - 1)`;
no prime power is discarded before estimating the nonnegative terms. -/
theorem nativeDyadicDPrimeASK_norm_le
    (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (a : ℝ) (t : AlpogeNativeDyadicH e)
    (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (ha : 0 ≤ a)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 ≤ w ρ) :
    ‖nativeDyadicDPrimeASK e q d N a t w‖ ≤
      a * Real.log d / ((d : ℝ) - 1) := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast (Fact.out : d.Prime).one_lt
  have hd0 : (0 : ℝ) < d := by linarith
  have hgeom := nativePrimePower_geom_positive (Finset.Icc 1 N) (1 / (d : ℝ))
    (by positivity) ((div_lt_one hd0).mpr hd1)
    (fun i hi => (Finset.mem_Icc.mp hi).1)
  have heq : (1 / (d : ℝ)) / (1 - 1 / (d : ℝ)) = 1 / ((d : ℝ) - 1) := by
    field_simp [hd0.ne', sub_ne_zero.mpr hd1.ne']
  rw [heq] at hgeom
  let W : ℕ → ℝ := fun i =>
    w (alpogeNativePartner t
      (nativeDyadicDInvolution e + i • (alpogeNativeHostData e q d).frob d))
  have hW : ∀ i, 0 ≤ W i := by
    intro i
    apply hw
    have hf := nativeDyadicHostData_frob_d_inPhi e q d hH
    change ((alpogeNativeHostData e q d).frob d).1.1 = 0 at hf
    change 1 + (1 + i • ((alpogeNativeHostData e q d).frob d).1.1) + 0 = (0 : ZMod 2)
    rw [hf, smul_zero]
    decide
  have hsum : (∑ i ∈ Finset.Icc 1 N, max (a / (d : ℝ) ^ i - W i) 0) ≤
      a / ((d : ℝ) - 1) := by
    calc
      _ ≤ a * ∑ i ∈ Finset.Icc 1 N, (1 / (d : ℝ)) ^ i := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have he : a * (1 / (d : ℝ)) ^ i = a / (d : ℝ) ^ i := by
          rw [one_div, inv_pow]
          rfl
        rw [he]
        exact max_le (sub_le_self _ (hW i)) (div_nonneg ha (pow_nonneg hd0.le _))
      _ ≤ a * (1 / ((d : ℝ) - 1)) := mul_le_mul_of_nonneg_left hgeom ha
      _ = _ := by ring
  have hreal : nativeDyadicDPrimeASK e q d N a t w =
      ((Real.log d * ∑ i ∈ Finset.Icc 1 N, max (a / (d : ℝ) ^ i - W i) 0 : ℝ) : ℂ) := by
    simp only [nativeDyadicDPrimeASK, alpogeNativeSiteCut, Nat.cast_pow,
      Complex.ofReal_mul, Complex.ofReal_sum, W]
  rw [hreal, Complex.norm_real, Real.norm_of_nonneg
    (mul_nonneg (Real.log_natCast_nonneg d) (Finset.sum_nonneg fun i _ => le_max_right _ _))]
  calc
    _ ≤ Real.log d * (a / ((d : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hsum (Real.log_natCast_nonneg d)
    _ = _ := by ring

/-- Summation retains the literal site widths and amplitudes.  The only
uniform amplitude used here is the supplied upper bound on those sites. -/
theorem nativeDyadicDPrimeASK_sum_norm_le
    {ι : Type*} (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (J : Finset ι) (T : Finset (AlpogeNativeDyadicH e))
    (a : AlpogeNativeDyadicH e → ℝ)
    (w : ι → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) (Amax : ℝ)
    (ha : ∀ t ∈ T, 0 ≤ a t ∧ a t ≤ Amax)
    (hw : ∀ j ∈ J, ∀ ρ, alpogeNativeInPhi ρ → 0 ≤ w j ρ) :
    ‖∑ j ∈ J, ∑ t ∈ T, nativeDyadicDPrimeASK e q d N (a t) t (w j)‖ ≤
      (J.card : ℝ) * (T.card : ℝ) * Amax * Real.log d / ((d : ℝ) - 1) := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast (Fact.out : d.Prime).one_lt
  have hsum : ‖∑ j ∈ J, ∑ t ∈ T, nativeDyadicDPrimeASK e q d N (a t) t (w j)‖ ≤
      ∑ j ∈ J, ∑ t ∈ T, Amax * Real.log d / ((d : ℝ) - 1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro t ht
    exact (nativeDyadicDPrimeASK_norm_le e q d N hH (a t) t (w j)
      (ha t ht).1 (hw j hj)).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ha t ht).2 (Real.log_natCast_nonneg d)) (by linarith))
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_div_assoc] using hsum

/-- Exact normalization by the already derived signal divisor
`|T| * |J| * b * Delta / 2`.  An amplitude window `a ≤ b(x+1)` pays the
complete ramified term by `2(x+1) log d / (Delta(d-1))`. -/
theorem nativeDyadicDPrimeASK_normalized_le
    {ι : Type*} (e q d N : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (J : Finset ι) (T : Finset (AlpogeNativeDyadicH e))
    (hJ : J.Nonempty) (hT : T.Nonempty)
    (a : AlpogeNativeDyadicH e → ℝ)
    (w : ι → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (x b Delta : ℝ) (hb : 0 < b) (hDelta : 0 < Delta)
    (ha : ∀ t ∈ T, 0 ≤ a t ∧ a t ≤ b * (x + 1))
    (hw : ∀ j ∈ J, ∀ ρ, alpogeNativeInPhi ρ → 0 ≤ w j ρ) :
    ‖∑ j ∈ J, ∑ t ∈ T, nativeDyadicDPrimeASK e q d N (a t) t (w j)‖ /
        ((T.card : ℝ) * (J.card : ℝ) * b * Delta / 2) ≤
      2 * (x + 1) * Real.log d / (Delta * ((d : ℝ) - 1)) := by
  have hJpos : (0 : ℝ) < J.card := by exact_mod_cast Finset.card_pos.mpr hJ
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hdpos : 0 < (d : ℝ) - 1 := by
    have hd1 : (1 : ℝ) < d := by exact_mod_cast (Fact.out : d.Prime).one_lt
    linarith
  have hbound := nativeDyadicDPrimeASK_sum_norm_le e q d N hH J T a w
    (b * (x + 1)) ha hw
  have hnorm : 0 < (T.card : ℝ) * (J.card : ℝ) * b * Delta / 2 := by positivity
  apply (div_le_div_of_nonneg_right hbound hnorm.le).trans_eq
  field_simp [hJpos.ne', hTpos.ne', hb.ne', hDelta.ne', hdpos.ne']

end RHLean.Analysis.AlpogeThin

end
