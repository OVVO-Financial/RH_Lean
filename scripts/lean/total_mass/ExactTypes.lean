import «research.oai_434.VF919TotalMassEndpoint»

/-!
# Exact public types for the total-mass LOW endpoint

Every assertion below spells out the expected quantified type. The terms
are the compiled public declarations; no expected conclusion is introduced
as a premise. This file and its source-type manifest are committed review
artifacts. CI compares them and elaborates this file; it never rewrites them.

The four unconditional endpoints construct one positive-minimum source.
The growth and signed-pair endpoints save m/4, while the fixed-power
endpoint saves m/8. The signed-pair type retains the actual diagonal.
-/

set_option autoImplicit false

-- Source: research/oai_434/VF919TotalMassLowEnergy.lean
section VF919TotalMassLowEnergyExactTypes

namespace OAI
noncomputable section
open scoped Classical ContDiff SchwartzMap BigOperators
open Filter MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

-- Expected public type: OAI.SevenEighths.ProbePhysical.totalMassAuxiliaryPhysicalExponents
example :
    LowPhysicalExponents :=
  @_root_.OAI.SevenEighths.ProbePhysical.totalMassAuxiliaryPhysicalExponents


-- Expected public type: OAI.SevenEighths.ProbePhysical.low_selected_nominal_energy_total_mass
example : ∀ (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (hsum : ∑ i, ell i ≤ 1/6)
    (hbudget : (3/2 : ℝ) * ((5/3 : ℝ) - 2*(phys.x+phys.y)) ≤ ∑ i, ell i)
    (Ck b ε : ℝ) (hCk : 0 < Ck) (hε : 0 < ε) (hε1 : ε ≤ 1),
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
      ∀ (T : Fin K → Finset PrimeIdeal),
        (∀ i P, P ∈ T i → Supported P.val) →
        (∀ i P, P ∈ T i → P.val ∉ S) →
        Pairwise (fun i j => Disjoint (T i) (T j)) →
        (∀ i P, P ∈ T i → (Ideal.absNorm P.val : ℝ) ≤ b*Z^(ell i)) →
      ∀ (J : Finset (Fin K)) (R : Finset O),
        (∀ z ∈ R, z ≠ 0 ∧
          elementNorm z ≤ Ck*Z^((phys.x+phys.y)-2*lowUnselectedLength ell J)) →
      ∀ X : ℝ, 0 < X →
        Z^(1+lowSelectedLength ell J-ε/2) ≤ X →
        X ≤ Z^(1+lowSelectedLength ell J+ε/2) →
      ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (Y : Fin K → ℝ) (t : ℝ) (σ : RayRing),
        (∑ z ∈ R, ‖lowSelectedInverseRow Finset.univ
          (lowSelectedWeight η (fun i => canonicalSlotSupport (T i)) J W Y t)
          η S hS (lowSelectedIdeal (fun i => canonicalSlotSupport (T i)) J)
          X t σ z‖^2) ≤
          C*(1+‖t‖)^degree*
            Z^((phys.x+phys.y)-lowUnselectedLength ell J+507*ε) :=
  @_root_.OAI.SevenEighths.ProbePhysical.low_selected_nominal_energy_total_mass

end SevenEighths.ProbePhysical
end
end OAI

end VF919TotalMassLowEnergyExactTypes

-- Source: research/oai_434/VF919TotalMassLowPhysical.lean
section VF919TotalMassLowPhysicalExactTypes

namespace OAI
noncomputable section
open scoped Classical ContDiff SchwartzMap BigOperators
open Filter MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance exactTypesUnitsFintype : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

-- Expected public type: OAI.SevenEighths.ProbePhysical.low_physical_inverse_normalized_total_mass
example : ∀ (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b aCut bCut ε : ℝ) (ha : 0<a) (haCut : 0<aCut) (hbCut : 0<bCut)
    (hε : 0<ε) (hε1 : ε≤1),
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J),
    ∀X : ℝ,0<X→Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L)
      ∀(hX0 : 0<Z^(phys.x:ℝ)/L)(hY0 : 0<Z^(phys.y:ℝ)/L),
      (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) aCut bCut haCut hbCut
          (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L) hX0 hY0
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W (fun i=>Z^(ell i)) t)
            η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t)≤
        C*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2) :=
  @_root_.OAI.SevenEighths.ProbePhysical.low_physical_inverse_normalized_total_mass


-- Expected public type: OAI.SevenEighths.ProbePhysical.low_central_compensated_tuple_total_mass
example : ∀ (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M),
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(X : ℝ),0<X→
      Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J
            (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) X t*
          selectedSlotFactor W (fun i=>Z^(ell i)) (fun i=>(p i).val) J t‖≤
        C*(1+‖t‖)^degree*Z^(((5*phys.x+phys.y)/12)+254*ε) :=
  @_root_.OAI.SevenEighths.ProbePhysical.low_central_compensated_tuple_total_mass


-- Expected public type: OAI.SevenEighths.ProbePhysical.low_central_gaussian_dyad_total_mass
example : ∀ (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M),
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(U : ℝ),0<U→
      Z^(1+lowSelectedLength ell J-ε/2)≤U→U≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
    ∀(V : SchwartzMap ℝ ℂ)(hV : HasCompactSupport (V:ℝ→ℂ)),
      ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
        W (fun i=>Z^(ell i)) J (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) U
          (Z^(1+lowSelectedLength ell J)) V hV‖≤
        C*Z^(((5*phys.x+phys.y)/12)+254*ε)*gaussianJointMoment V hV degree (U/Z^(1+lowSelectedLength ell J)) :=
  @_root_.OAI.SevenEighths.ProbePhysical.low_central_gaussian_dyad_total_mass


-- Expected public type: OAI.SevenEighths.ProbePhysical.low_central_gaussian_dyads_total_mass
example : ∀ (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M),
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(((5*phys.x+phys.y)/12)+256*ε) :=
  @_root_.OAI.SevenEighths.ProbePhysical.low_central_gaussian_dyads_total_mass


-- Expected public type: OAI.SevenEighths.ProbePhysical.low_all_gaussian_dyads_total_mass
example : ∀ (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1),
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV
      Summable f ∧ ‖∑'j : ℕ,f j‖≤C*Z^(((5*phys.x+phys.y)/12)+256*ε) :=
  @_root_.OAI.SevenEighths.ProbePhysical.low_all_gaussian_dyads_total_mass


-- Expected public type: OAI.SevenEighths.ProbePhysical.compensatedPhysicalProbe_low_total_mass
example : ∀ (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1),
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
      ‖compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
        (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i))
        (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) Z‖≤C*Z^(((5*phys.x+phys.y)/12)+256*ε) :=
  @_root_.OAI.SevenEighths.ProbePhysical.compensatedPhysicalProbe_low_total_mass


-- Expected public type: OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_total_mass
example : ∀ (phys : LowPhysicalExponents) (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i) (R : Set Id)
    (a b ε : ℝ) (ha : 0<a) (hab : a≤b) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1),
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) Z‖≤C*Z^(((5*phys.x+phys.y)/12)+256*ε) :=
  @_root_.OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_total_mass


-- Expected public type: OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_loss_total_mass
example : ∀ (phys : LowPhysicalExponents)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i) (R : Set Id)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1),
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) Z‖≤C*Z^(((5*phys.x+phys.y)/12)+loss) :=
  @_root_.OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_loss_total_mass


-- Expected public type: OAI.SevenEighths.ProbePhysical.original_normalized_compensatedPhysicalProbe_low_total_mass
example : ∀ (phys : LowPhysicalExponents) {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0),
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) Z/normer‖≤
        C*Z^(((5*phys.x+phys.y)/12)+loss) :=
  @_root_.OAI.SevenEighths.ProbePhysical.original_normalized_compensatedPhysicalProbe_low_total_mass

end SevenEighths.ProbePhysical
end
end OAI

end VF919TotalMassLowPhysicalExactTypes

-- Source: research/oai_434/VF919TotalMassEndpoint.lean
section VF919TotalMassEndpointExactTypes

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Asymptotics
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual RHLeanFiniteSlotGap

-- Expected public type: OAI.SevenEighths.ProbeFinalAssembly.SourceData.tiltedProbe_low_total_mass
example : ∀ {Delta : ℝ}
    {D : Parameters.HighData Delta} (F : SourceData D)
    (tilt : ℝ) (htilt : 0 ≤ tilt) (htilt1 : tilt < 1 / 960)
    (loss : ℝ) (hloss : 0 < loss) (eta : Character),
    F.tiltedProbe tilt eta =O[atTop]
      (fun Z : ℝ => Z ^ (3 / 16 - 9 * tilt + loss)) :=
  @_root_.OAI.SevenEighths.ProbeFinalAssembly.SourceData.tiltedProbe_low_total_mass

end SevenEighths.ProbeFinalAssembly
namespace SevenEighths.RHLeanNativeSevenEighthsReplay
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open ProbeFinalAssembly PrincipalSignalComparison RHLeanFiniteSlotGap
open RHLeanFullPhysicalTilt ProbeFinalAssemblyCertifiedBands
open CenteredMomentDetectorPlainMomentParameters

-- Expected public type: OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_fixed_total_mass_probe_bounds
example : ∀ (D : HighData (1 / 1000000 : ℝ))
    (tilt : ℝ) (htilt : 0 < tilt) (htilt1 : tilt < 1 / 960)
    (htail : 24 * tilt < D.t)
    (hfine : ∀ j, D.ell j ≤ detectorMesh (1 / 1000000) D.t / 200)
    (hepsilon : D.ε ≤ D.t / 2000) (he : D.e ≤ D.t / 2000)
    (heps : ((D.N : ℝ) + 8) * D.eps ≤ D.t) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t)
    (hbetalow : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta),
    ∀ chi : Character,
      (∀ loss : ℝ, 0 < loss →
        F.tiltedProbe tilt chi =O[atTop]
          (fun Z : ℝ => Z ^ (3 / 16 - 9 * tilt + loss))) ∧
      (fun Z => F.tiltedProbe tilt chi Z -
        HeckeSignal.signal (chi.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection chi F.S) (-11 / 16 - 8 * tilt) Z) =O[atTop]
        (fun Z : ℝ => Z ^ ((7 / 8 : ℝ) - 11 / 16 - 8 * tilt - D.sigma)) :=
  @_root_.OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_fixed_total_mass_probe_bounds


-- Expected public type: OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_total_mass_boundary
example : ∀ (D : HighData (1 / 1000000 : ℝ))
    (tilt : ℝ) (htilt : 0 < tilt) (htilt1 : tilt < 1 / 960)
    (htail : 24 * tilt < D.t)
    (hfine : ∀ j, D.ell j ≤ detectorMesh (1 / 1000000) D.t / 200)
    (hepsilon : D.ε ≤ D.t / 2000) (he : D.e ≤ D.t / 2000)
    (heps : ((D.N : ℝ) + 8) * D.eps ≤ D.t)
    (hreserve : tilt ≤ D.sigma) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t),
    HeckeZeroSupremum.beta ≤ 7 / 8 - tilt :=
  @_root_.OAI.SevenEighths.RHLeanNativeSevenEighthsReplay.native_beta_le_total_mass_boundary

end SevenEighths.RHLeanNativeSevenEighthsReplay
namespace SevenEighths.RHLeanActualSlotMin
open Parameters RHLeanFullPhysicalTilt RHLeanNativeSevenEighthsReplay
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands

-- Expected public type: OAI.SevenEighths.RHLeanActualSlotMin.recalibrated_sigma_eq_true_minimum_quarter
example : ∀ {Delta : ℝ}
    (D : HighData Delta),
    (slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)).sigma =
      actualSlotMinimum D / 4 :=
  @_root_.OAI.SevenEighths.RHLeanActualSlotMin.recalibrated_sigma_eq_true_minimum_quarter


-- Expected public type: OAI.SevenEighths.RHLeanActualSlotMin.total_mass_calibration_preserves_physical_geometry
example : ∀ {Delta : ℝ}
    (D : HighData Delta),
    let E := slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)
    E.t = D.t ∧ E.N = D.N ∧ E.ell = D.ell :=
  @_root_.OAI.SevenEighths.RHLeanActualSlotMin.total_mass_calibration_preserves_physical_geometry


-- Expected public type: OAI.SevenEighths.RHLeanActualSlotMin.recalibrated_total_mass_tilt_budget
example : ∀ {Delta : ℝ}
    (D : HighData Delta),
    let E := slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)
    0 < E.sigma ∧ E.sigma < 1 / 960 ∧ 24 * E.sigma < E.t :=
  @_root_.OAI.SevenEighths.RHLeanActualSlotMin.recalibrated_total_mass_tilt_budget


-- Expected public type: OAI.SevenEighths.RHLeanActualSlotMin.total_mass_boundary_strictly_improves_low_first
example : ∀ {Delta : ℝ}
    (D : HighData Delta),
    (7 / 8 : ℝ) - actualSlotMinimum D / 4 <
      7 / 8 - slotTiltLowFirst
        (slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)) :=
  @_root_.OAI.SevenEighths.RHLeanActualSlotMin.total_mass_boundary_strictly_improves_low_first


-- Expected public type: OAI.SevenEighths.RHLeanActualSlotMin.total_mass_fixed_power_strictly_improves_low_first
example : ∀ {Delta : ℝ}
    (D : HighData Delta),
    (7 / 8 : ℝ) - actualSlotMinimum D / 8 <
      7 / 8 - slotTiltLowFirst
        (slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)) :=
  @_root_.OAI.SevenEighths.RHLeanActualSlotMin.total_mass_fixed_power_strictly_improves_low_first


-- Expected public type: OAI.SevenEighths.RHLeanActualSlotMin.native_beta_le_true_physical_slot_minimum_total_mass_of_fine
example : ∀ (D : HighData (1 / 1000000 : ℝ))
    (hfine : ∀ i, D.ell i ≤ detectorMesh (1 / 1000000) D.t / 200),
    HeckeZeroSupremum.beta ≤ 7 / 8 - actualSlotMinimum D / 4 :=
  @_root_.OAI.SevenEighths.RHLeanActualSlotMin.native_beta_le_true_physical_slot_minimum_total_mass_of_fine


-- Expected public type: OAI.SevenEighths.RHLeanActualSlotMin.native_beta_le_true_physical_slot_minimum_total_mass
example :
    ∃ D : HighData (1 / 1000000 : ℝ),
      0 < actualSlotMinimum D ∧
      HeckeZeroSupremum.beta ≤ 7 / 8 - actualSlotMinimum D / 4 :=
  @_root_.OAI.SevenEighths.RHLeanActualSlotMin.native_beta_le_true_physical_slot_minimum_total_mass

end SevenEighths.RHLeanActualSlotMin
end
end OAI
namespace RHLean.Analysis
open MertensExponent OAI.SevenEighths
open RHLeanActualSlotMin RHLeanNativeSevenEighthsReplay

-- Expected public type: RHLean.Analysis.native_mertens_true_physical_slot_minimum_total_mass
example :
    ∃ D : Parameters.HighData (1 / 1000000 : ℝ),
      0 < actualSlotMinimum D ∧
      MertensGrowthAtMost (7 / 8 - actualSlotMinimum D / 4) :=
  @_root_.RHLean.Analysis.native_mertens_true_physical_slot_minimum_total_mass


-- Expected public type: RHLean.Analysis.native_mertens_fixed_true_physical_slot_minimum_total_mass
example :
    ∃ D : Parameters.HighData (1 / 1000000 : ℝ),
      0 < actualSlotMinimum D ∧
      MertensExponent.MertensPowerBound (7 / 8 - actualSlotMinimum D / 8) :=
  @_root_.RHLean.Analysis.native_mertens_fixed_true_physical_slot_minimum_total_mass


-- Expected public type: RHLean.Analysis.native_signed_pair_true_physical_slot_minimum_total_mass
example :
    ∃ D : Parameters.HighData (1 / 1000000 : ℝ),
      0 < actualSlotMinimum D ∧ ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x →
        2 * realMertensPositiveLagPairSum (x + 1) ≤
          (C * Real.rpow (x : ℝ)
            (7 / 8 - actualSlotMinimum D / 4 + eps)) ^ 2 -
            realMertensDiagonal (x + 1) :=
  @_root_.RHLean.Analysis.native_signed_pair_true_physical_slot_minimum_total_mass

end RHLean.Analysis

end VF919TotalMassEndpointExactTypes
