import «research.oai_434.VF919FiniteSlotReflectedGain»
import OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized

/-!
# Actual principal comparison at tilted physical scales

The residue and signal scale by exactly Z^(-8*tilt). This transports the
original finite-window estimate without changing its weights or normalizer.
The actual raw principal remainder is then divided by that same normalizer.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter MeasureTheory
namespace SevenEighths.ProbePrincipalResidueActual
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
open ProbeFiniteProductBounds ProbeEuler ProbeLocal HeckeSignal ProbePhysical Continuation
open ActualEisensteinCubic CompletedGauss

lemma tilted_cubic_scale (Z tilt : ℝ) (hZ : 0<Z) :
    ((Z^((17/48:ℝ)-24*tilt):ℝ):ℂ)^(1/3:ℂ)=
      ((Z^(-8*tilt):ℝ):ℂ)*((Z^(17/48:ℝ):ℝ):ℂ)^(1/3:ℂ) := by
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [←Complex.cpow_mul_ofReal_nonneg hZ.le (17/48-24*tilt) (1/3),
    ←Complex.cpow_mul_ofReal_nonneg hZ.le (17/48) (1/3),
    Complex.ofReal_cpow hZ.le,←Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring

lemma tilted_source_residue (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character)
    (a Y Z tilt : ℝ) (hZ : 0<Z) (H B : ℂ→ℂ→ℂ→ℂ) :
    sourceResidueIntegral W0 W1 M χ a (Z^((17/48:ℝ)-24*tilt)) Y Z H B=
      sourceResidueIntegral W0 W1 M χ a (Z^(17/48:ℝ)) Y Z H B*((Z^(-8*tilt):ℝ):ℂ) := by
  have hi (s : ℂ) :
      fixedPrincipalResidue M^2/6*
        sourceMultiplier W0 W1 (Z^((17/48:ℝ)-24*tilt)) Y Z χ s (H s) (B s) 1 (1/6)=
      (fixedPrincipalResidue M^2/6*
        sourceMultiplier W0 W1 (Z^(17/48:ℝ)) Y Z χ s (H s) (B s) 1 (1/6))*
        ((Z^(-8*tilt):ℝ):ℂ) := by
    rw [source_double_residue,source_double_residue,tilted_cubic_scale Z tilt hZ]
    ring
  unfold sourceResidueIntegral
  simp_rw [hi]
  exact PrincipalMellinResidues.verticalIntegral_mul_const _ _ _

lemma tilted_signal (χ : Character) (H : ℂ→ℂ) (Z tilt : ℝ) (hZ : 0<Z) :
    signal χ H (-11/16-8*tilt) Z=
      signal χ H (-11/16) Z*((Z^(-8*tilt):ℝ):ℂ) := by
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold signal
  rw [Complex.ofReal_cpow hZ.le]
  calc
    _=(Z:ℂ)^(((-11/16:ℝ):ℂ)+((-8*tilt:ℝ):ℂ))*
        mellinInv (-2) (fun s=>amplitude χ H (-s)) Z := by
      congr 2
      push_cast
      ring
    _=_ := by rw [Complex.cpow_add _ _ hz];ring


theorem normalized_actual_window_residue_tilted (tilt : ℝ) {κ : Type*}
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 7/8<a) (ha2 : a≤2) (hβ : HeckeZeroSupremum.beta<a) (S : Finset κ) :
    letI : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃D : ℝ, 0≤D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0<a0 → 0<a1 → Function.support W0⊆Set.Icc a0 b0 →
      Function.support W1⊆Set.Icc a1 b1 →
      (∀y,(W0 y).im=0) → (∀y,(W1 y).im=0) →
      (∀y,0≤(W0 y).re) → (∀y,0≤(W1 y).re) → W0≠0 → W1≠0 →
      ∀ (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480≤P → 1440*P^(-(7/8 : ℝ))≤1 →
      (∀j∈S,∀p∈T j,0≤W j ((Ideal.absNorm p.val : ℝ)/scale j)) →
      (∀j∈S,∀p∈T j,P≤(Ideal.absNorm p.val : ℝ)) →
      (∀j∈S,∀p∈T j,IsCoprime p.val η.modulus) →
      (∀j∈S,0<slotMass T (residueWeights W scale) j) → 1≤Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏p∈E,p) *
        (Probe.principalScalar S Z (1/6) (slotMass T (residueWeights W scale)) : ℂ)
      normer≠0 ∧
      ‖sourceResidueIntegral W0 W1 (∏p∈E,p) (η.excludePrimes E hE.prime)
          a (Z^((17/48:ℝ)-24*tilt)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16-8*tilt) Z‖ ≤
        D*Z^(a-11/16-8*tilt)*P^(-(7/8 : ℝ)) := by
  let : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D,hD,hbound⟩ := normalized_actual_window_residue E hE η ha ha2 hβ S
  refine ⟨D,hD,?_⟩
  intro W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W scale P Y Z hP hsmall hW hnorm hcop hmass hZ
  have hb := hbound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W scale P Y Z hP hsmall hW hnorm hcop hmass hZ
  dsimp only at hb ⊢
  refine ⟨hb.1,?_⟩
  have hz : 0<Z := zero_lt_one.trans_le hZ
  rw [tilted_source_residue W0 W1 _ _ _ Y Z tilt hz,
    tilted_signal _ _ Z tilt hz]
  rw [show ∀A N F q : ℂ,A*q/N-F*q=(A/N-F)*q from fun A N F q=>by ring,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hz _)]
  apply (mul_le_mul_of_nonneg_right hb.2.2 (Real.rpow_nonneg hz.le _)).trans_eq
  rw [show a-11/16-8*tilt=(a-11/16)+(-8*tilt) by ring,Real.rpow_add hz]
  ring

end SevenEighths.ProbePrincipalResidueActual
namespace SevenEighths.ProbePrincipalNormalized
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

theorem actual_ray_principal_comparison_tilted (tilt : ℝ) (htilt : 0≤tilt) {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hmin : 0<ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0<e) (hehi : e≤1/1000) (hnu : 0<nu)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16-8*tilt) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-11/16-8*tilt-17/48000+nu)+
        Z^(HeckeZeroSupremum.beta-11/16-8*tilt+e-(7/8)*ellMin)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := ProbePrincipalPhysical.physical_principal_residue_remainder_tilted
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := normalized_actual_window_residue_tilted tilt S hS η ha ha2 (by linarith) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(7/8:ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne ell (fun j=>hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=>c) (fun _=>d) ell (fun _=>hc) (fun _=>hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0<Z := by linarith
  let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
  let normer := cs*(Probe.principalScalar Finset.univ Z (1/6)
    (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=>Z^(ell j)) (c*Z^ellMin) (Z^((23/48:ℝ)+12*tilt)) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=>hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem tilt htilt ell hsum W hWbounds (fun j=>Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2
  have hpw : (c*Z^ellMin)^(-(7/8:ℝ))=c^(-(7/8:ℝ))*Z^(-(7/8:ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-11/16-8*tilt-17/48000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-11/16-8*tilt-17/48000+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-11/16-8*tilt)*(c*Z^ellMin)^(-(7/8:ℝ))=
      (D*c^(-(7/8:ℝ)))*Z^(HeckeZeroSupremum.beta-11/16-8*tilt+e-(7/8)*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-11/16-8*tilt+e-(7/8)*ellMin=
      (HeckeZeroSupremum.beta+e-11/16-8*tilt)+(-(7/8:ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖≤C := by
    dsimp [C]
    have : 0≤D*c^(-(7/8:ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(7/8:ℝ))≤C := by
    dsimp [C]
    have : 0≤C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C*Z^(HeckeZeroSupremum.beta-11/16-8*tilt-17/48000+nu)+
        C*Z^(HeckeZeroSupremum.beta-11/16-8*tilt+e-(7/8)*ellMin) := by gcongr
    _ = _ := by ring

#print axioms actual_ray_principal_comparison_tilted
end SevenEighths.ProbePrincipalNormalized
end
end OAI
