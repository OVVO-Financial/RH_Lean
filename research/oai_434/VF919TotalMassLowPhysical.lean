import «research.oai_434.VF919TotalMassLowEnergy»
import «research.oai_434.VF919OriginalLowTupleSignedGram»

/-!
# Complete reflected LOW from total unselected mass

The actual physical source, parent rows, prime pools, compensation subsets,
and principal normalizer are unchanged. The nominal-energy estimate spends
one unselected length. Its square-root cost is cancelled by the existing
moving inverse-square tuple mass at rho = 1/2, before summing the complete
compensation family. The remaining Gaussian and normalization steps reuse
the original proof at the same physical exponents.

Original comparison source: VF919TiltedLowPhysical.lean at main
cae99df1c3ea24ff4113063bf09f6fd07517ad93. No pointwise energy saving or
new cancellation premise is assumed.
-/

namespace OAI
noncomputable section
open scoped Classical ContDiff SchwartzMap BigOperators
open Filter MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem low_physical_inverse_normalized_total_mass (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b aCut bCut ε : ℝ) (ha : 0<a) (haCut : 0<aCut) (hbCut : 0<bCut)
    (hε : 0<ε) (hε1 : ε≤1) :
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
        C*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2) := by
  let q := elementNorm (calibrationForSet S hS).generator
  let c := (min 1 a)^K
  let B := (max 1 b)^K
  have hq : 0<q := calibration_elementNorm_pos _
  have hc : 0<c := by dsimp [c];positivity
  have hB : 0<B := by dsimp [B];positivity
  let Ck := 2*bCut*(q/c^2)
  have hCk : 0<Ck := by dsimp [Ck];positivity
  obtain ⟨degree,C,ZC,hbound⟩ := low_selected_nominal_energy_total_mass phys η S hS hbad ell hell hsum htotal Ck b ε hCk hε hε1
  let C0 := ((Fintype.card RayRing:ℝ)+1)*Real.sqrt (C*B^2/q)/(2*Real.pi)
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
  dsimp only
  let L := elementNorm (∏i : J,(p i).val)
  let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L)
  intro hX0 hY0
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hL : 0<L := lowUnselectedProduct_norm_pos _
    (fun i n hn=>canonicalSlotSupport_nonzero _ (hT i) n hn) J p
  have hnormE (i : Fin K) (n : O) (hn : n∈canonicalSlotSupport (T i)) :
      a*Z^(ell i)≤elementNorm n ∧ elementNorm n≤b*Z^(ell i) := by
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hLlo : c*Z^(lowUnselectedLength ell J)≤L :=
    lowUnselectedProduct_norm_lower ell a Z ha hz _ (fun i n hn=>(hnormE i n hn).1) J p
  have hLhi : L≤B*Z^(lowUnselectedLength ell J) :=
    lowUnselectedProduct_norm_upper_nominal ell b Z hz _ (fun i n hn=>(hnormE i n hn).2) J p
  have hQ : 0<Q := lowPhysicalScale_pos _ _ _ hX0 hY0
  let R := lowNumeratorRows aCut bCut haCut hbCut Q hQ
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W (fun i=>Z^(ell i)) t)
    η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t
  have hrows : ∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^((phys.x+phys.y)-2*lowUnselectedLength ell J) := by
    intro z hzR
    refine ⟨lowNumeratorRows_nonzero aCut bCut haCut hbCut Q hQ z hzR,?_⟩
    apply (lowNumeratorRows_norm_bound aCut bCut haCut hbCut Q hQ z hzR).trans
    have hh := mul_le_mul_of_nonneg_left
      (lowPhysicalScale_nominal_bound_tilted phys (calibrationForSet S hS) Z L c (lowUnselectedLength ell J) hz hc hLlo)
      (show 0≤2*bCut by positivity)
    simpa only [Ck,mul_assoc] using hh
  have he (σ : RayRing) : (∑z∈R,‖row σ z‖^2)≤
      C*(1+‖t‖)^degree*Z^((phys.x+phys.y)-lowUnselectedLength ell J+507*ε) :=
    hZ.2 T hT hout hdis (fun i P hP=>(hnorm i P hP).2) J R hrows X hX hXlo hXhi W hW (fun i=>Z^(ell i)) t σ
  have hn (σ : RayRing) : Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q≤
      Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2) := by
    dsimp only [Q]
    rw [lowPhysicalScale_source_tilted phys _ Z L hz]
    exact low_inverse_sqrt_normalized_tilted phys q C B Z L (lowUnselectedLength ell J) (lowUnselectedLength ell J+507*ε) (1+‖t‖)
      (∑z∈R,‖row σ z‖^2) degree hq ZC.le hB.le hz hL (le_add_of_nonneg_right (norm_nonneg t))
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
      (by
        simpa only [show (phys.x+phys.y)-2*lowUnselectedLength ell J+
            (lowUnselectedLength ell J+507*ε) =
            (phys.x+phys.y)-lowUnselectedLength ell J+507*ε by ring] using he σ) hLhi
  change (Real.sqrt Q)⁻¹/(2*Real.pi)*(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2))≤_
  calc
    _=(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q)/(2*Real.pi) := by
      rw [←Finset.sum_div]
      ring
    _≤(∑σ : RayRing,Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2))/(2*Real.pi) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _=>hn σ)) (by positivity)
    _≤_ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [C0]
      calc
        _=((Fintype.card RayRing:ℝ)*Real.sqrt (C*B^2/q)/(2*Real.pi))*(1+|t|)^degree*Z^((lowUnselectedLength ell J+507*ε)/2) := by ring
        _≤_ := by gcongr ; linarith

theorem low_central_compensated_tuple_total_mass (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
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
        C*(1+‖t‖)^degree*Z^(((5*phys.x+phys.y)/12)+254*ε) := by
  obtain ⟨Cg,hCg,hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree,Ci,hCi,hinverse⟩ := low_physical_inverse_normalized_total_mass phys η S hS hbad ell hell hsum htotal
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cm,hCm,hmass⟩ := lowUnselectedMass_moving_power_bound (1/2:ℝ) (by norm_num) (by norm_num)
  let Cu := (max 1 (Cm * a ^ ((1/2:ℝ)-1))) ^ K
  have hCu : 0<Cu := by dsimp [Cu];positivity
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0<q := calibration_elementNorm_pos _
  let C0 := Cg*Ci*Real.sqrt (3*q)*Cu
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hinverse,eventually_original_slot_scales_tilted phys (calibrationForSet S hS)
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=>canonicalSlotSupport (T i)
  let Yp := fun i=>Z^(ell i)
  have hz : 0<Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈slots i→elementNorm n ≤ max 1 b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^(((5*phys.x+phys.y)/12)+(phys.y/2)*ε:ℝ)
  let V := Ci*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2)
  have hGV : G*V≤Ci*(1+‖t‖)^degree*Z^(((5*phys.x+phys.y)/12)+254*ε+lowUnselectedLength ell J/2) := by
    dsimp only [G,V]
    calc
      _=Ci*(1+‖t‖)^degree*(Z^(((5*phys.x+phys.y)/12)+(phys.y/2)*ε:ℝ)*Z^((lowUnselectedLength ell J+507*ε)/2)) := by ring
      _≤_ := by
        rw [←Real.rpow_add hz]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by nlinarith [phys.y_le_one])
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L)
      ‖lowUnselectedWeight slots J W Yp p‖*((Real.sqrt Q)⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L) ε*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t)≤
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(((5*phys.x+phys.y)/12)+254*ε+lowUnselectedLength ell J/2))*
        (‖lowUnselectedWeight slots J W Yp p‖*L^(-(1/2:ℝ))) := by
    dsimp only
    let L := elementNorm (∏i : J,(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0≤lowGramFactor (calibrationForSet S hS) (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0≤V by dsimp [V];positivity)
    calc
      _=‖lowUnselectedWeight slots J W Yp p‖*
        lowGramFactor (calibrationForSet S hS) (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L) ε*
        (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L)
          (div_pos (by positivity) hL) (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) X t) := by ring
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*(G*V) := by
        have hh3 := hh.trans hh2
        simp only [G,V,div_eq_mul_inv,mul_assoc] at hh3 ⊢
        convert hh3 using 1 ; congr 7
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*
          (Ci*(1+‖t‖)^degree*Z^(((5*phys.x+phys.y)/12)+254*ε+lowUnselectedLength ell J/2)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _=_ := by rw [low_compensated_sqrt_factor q L hq.le hL];ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hm0 := hmass K T hT ell a Z 1 ha hz (by norm_num)
    (fun i P hP => (hnorm i P hP).1) J W Yp hW
  have hpow : (Cm * 1 * a ^ ((1/2:ℝ)-1)) ^ J.card ≤ Cu := by
    simp only [mul_one]
    apply (pow_le_pow_left₀ (by positivity)
      (le_max_right 1 (Cm * a ^ ((1/2:ℝ)-1))) J.card).trans
    exact pow_le_pow_right₀ (le_max_left _ _)
      (by simpa using Finset.card_le_card (Finset.subset_univ J))
  have hm :
      (∑p : LowUnselectedTuple slots J,
        ‖lowUnselectedWeight slots J W Yp p‖*
          elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ))) ≤
        Cu * Z ^ (-lowUnselectedLength ell J/2) := by
    have hm1 := hm0.trans (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hz.le _))
    have hexp : ((1/2:ℝ)-1)*(∑i∈J,ell i) = -lowUnselectedLength ell J/2 := by
      dsimp [lowUnselectedLength]
      ring
    simpa only [hexp] using hm1
  calc
    _≤Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*
        Z^(((5*phys.x+phys.y)/12)+254*ε+lowUnselectedLength ell J/2))*
        (Cu * Z ^ (-lowUnselectedLength ell J/2))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hm (by positivity)) hCg.le
    _=C0*(1+‖t‖)^degree*
        (Z^(((5*phys.x+phys.y)/12)+254*ε+lowUnselectedLength ell J/2)*
          Z^(-lowUnselectedLength ell J/2)) := by dsimp [C0];ring
    _=_ := by
      rw [←Real.rpow_add hz]
      congr 2
      ring

theorem low_central_gaussian_dyad_total_mass (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
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
        C*Z^(((5*phys.x+phys.y)/12)+254*ε)*gaussianJointMoment V hV degree (U/Z^(1+lowSelectedLength ell J)) := by
  obtain ⟨degree,C,hC,he⟩ := low_central_compensated_tuple_total_mass phys η S hS hbad ell hell hsum htotal
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J U hU hlo hhi W hW V hV
  apply lowCommonDyad_norm_of_bound
  intro t
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hZ.2 T hT hout hdis hnorm J U hU hlo hhi W hW t

theorem low_central_gaussian_dyads_total_mass (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(((5*phys.x+phys.y)/12)+256*ε) := by
  obtain ⟨degree,C,hC,he⟩ := low_central_gaussian_dyad_total_mass phys η S hS hbad ell hell hsum htotal
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  obtain ⟨Cm,hCm,hm⟩ := gaussianJointMoment_summed V hV degree ε hε
  refine ⟨C*Cm,mul_pos hC hCm,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  let R := Z^(1+lowSelectedLength ell J)
  let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
    ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
      W (fun i=>Z^(ell i)) J (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) ((2:ℝ)^j) R V hV‖
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  obtain ⟨hsm,hmb⟩ := hm R (by dsimp [R];positivity)
  have hb (j : ℕ) : f j≤(C*Z^(((5*phys.x+phys.y)/12)+254*ε))*
      (((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := by
    dsimp only [f]
    split_ifs with hj
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
    · obtain ⟨hlo,hhi⟩ := not_lowRemote_bounds Z (lowSelectedLength ell J) ε ((2:ℝ)^j) hz hj
      apply (hZ.2 T hT hout hdis hnorm J ((2:ℝ)^j) (by positivity) hlo hhi W hW V hV).trans
      have hp : 1≤((2:ℝ)^j)^ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp
  have hn (j : ℕ) : 0≤f j := by dsimp [f];split_ifs <;>positivity
  have hsumf := Summable.of_nonneg_of_le hn hb (hsm.mul_left (C*Z^(((5*phys.x+phys.y)/12)+254*ε)))
  refine ⟨hsumf,?_⟩
  calc
    _≤∑'j : ℕ,(C*Z^(((5*phys.x+phys.y)/12)+254*ε))*(((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) :=
      hsumf.tsum_le_tsum hb (hsm.mul_left _)
    _=(C*Z^(((5*phys.x+phys.y)/12)+254*ε))*(∑'j : ℕ,((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := tsum_mul_left
    _≤(C*Z^(((5*phys.x+phys.y)/12)+254*ε))*(Cm*R^ε) := mul_le_mul_of_nonneg_left hmb (by positivity)
    _≤_ := by
      dsimp only [R]
      rw [←Real.rpow_mul hz.le]
      calc
        _=(C*Cm)*(Z^(((5*phys.x+phys.y)/12)+254*ε)*Z^((1+lowSelectedLength ell J)*ε)) := by ring
        _≤_ := by
          rw [←Real.rpow_add hz]
          apply mul_le_mul_of_nonneg_left _ (mul_pos hC hCm).le
          have hh := lowLength_bounds ell hell hsum J
          exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by nlinarith)

theorem low_all_gaussian_dyads_total_mass (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV
      Summable f ∧ ‖∑'j : ℕ,f j‖≤C*Z^(((5*phys.x+phys.y)/12)+256*ε) := by
  obtain ⟨Cc,hCc,hcentral⟩ := low_central_gaussian_dyads_total_mass phys η S hS hbad ell hell hsum htotal
    a b ε ha hε hε1 V hV W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1 hW0 hW1 hW0s hW1s hWB1
  obtain ⟨Cr,hCr,hremote⟩ := low_remote_gaussian_dyads_tilted phys S hS ell hell hsum b ε hε V hV
    W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1 hW0 hW1 hWB0 hWB1
  refine ⟨Cc+Cr,add_pos hCc hCr,?_⟩
  filter_upwards [hcentral,hremote] with Z hc hr
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  have hc' := hc.2 T hT hout hdis hnorm J W hW
  have hr' := hr.2 η T hT (fun i P hP=>(hnorm i P hP).2) J W hW
  dsimp only at hc' hr' ⊢
  have hh := low_dyad_norm_split _ (fun j=>lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j)) hc'.1 hr'.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp : Z^(-1:ℝ)≤Z^(((5*phys.x+phys.y)/12)+256*ε) := Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith [phys.x_gt_slot,phys.x_lt_y])
  calc
    _≤Cc*Z^(((5*phys.x+phys.y)/12)+256*ε)+Cr*Z^(-1:ℝ) := add_le_add hc'.2 hr'.2
    _≤Cc*Z^(((5*phys.x+phys.y)/12)+256*ε)+Cr*Z^(((5*phys.x+phys.y)/12)+256*ε) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _=_ := by ring

theorem compensatedPhysicalProbe_low_total_mass (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (htotal : (3/2:ℝ)*((5/3:ℝ)-2*(phys.x+phys.y)) ≤ ∑i,ell i)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
      ‖compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
        (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i))
        (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) Z‖≤C*Z^(((5*phys.x+phys.y)/12)+256*ε) := by
  obtain ⟨V,hV,hbudget,hidentity⟩ := compensatedPhysicalProbe_common_gaussian W
    (fun _=>|Real.log a|+|Real.log b|) (fun _=>by positivity)
    (fun i=>low_window_log_support (W i) a b ha (hW i))
  choose C hC he using fun A : Finset (Fin K)=>low_all_gaussian_dyads_total_mass phys η S hS hbad ell hell hsum htotal
    a b ε ha hε hε1 (V A) (hV A) W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  let C0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,C A)+1
  have hC0 : 0<C0 := by
    have hn := Finset.sum_nonneg (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>(hC A).le)
    dsimp only [C0]
    linarith
  refine ⟨C0,hC0,?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with Z hZ
  have hz1 : 1<Z := (hZ ∅).1
  have hz : 0<Z := lt_trans zero_lt_one hz1
  refine ⟨hz1,?_⟩
  intro T hT hout hdis hnorm
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  rw [hidentity η (calibrationForSet S hS) W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    _ hslots (fun i=>Z^(ell i)) (fun i=>by positivity)
    (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) Z (by positivity) (by positivity) hz]
  apply (norm_sum_le _ _).trans
  have hterm (A : Finset (Fin K)) :
      ‖∑'j : ℕ,lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i)) W
        (fun i=>Z^(ell i)) A (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) ((2:ℝ)^j)
        (Z*∏i∈Finset.univ\A,Z^(ell i)) (V A) (hV A)‖≤C A*Z^(((5*phys.x+phys.y)/12)+256*ε) := by
    have hc : Z*(∏i∈Finset.univ\A,Z^(ell i))=Z^(1+lowSelectedLength ell A) := by
      rw [lowSelectedScale_product ell A Z hz,Real.rpow_add hz,Real.rpow_one]
    rw [hc]
    exact ((hZ A).2 T hT hout hdis hnorm A W hWnorm).2
  have hh := Finset.sum_le_sum (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>hterm A)
  apply hh.trans
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C0];linarith) (Real.rpow_nonneg hz.le _)

theorem original_ray_compensatedPhysicalProbe_low_total_mass (phys : LowPhysicalExponents) (η : HeckeFamily.Character)
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
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) Z‖≤C*Z^(((5*phys.x+phys.y)/12)+256*ε) := by
  obtain ⟨C,hC,he⟩ := compensatedPhysicalProbe_low_total_mass phys η S hmax hS.bad ell hell hsum htotal
    a b ε ha hε hε1 W hW hWnorm W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨C,hC,?_⟩
  filter_upwards [he,ProbeRaySlots.power_pools_eventually_disjoint R S (fun _=>a) (fun _=>b) ell
    (fun _=>ha) (fun _=>hab) hinj] with Z hZ hd
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  apply hZ.2 _ (fun i=>ProbeRaySlots.pool_supported R S hS a b (Z^(ell i)))
    (fun i P hP=>((ProbeRaySlots.mem_pool R S a b (Z^(ell i)) P).mp hP).2.2.2)
    (fun i j hij=>hd i j hij)
  intro i P hP
  have hh := ProbeRaySlots.pool_norm_bounds R S ha.le hab (Real.rpow_pos_of_pos hz _) P hP
  simpa only [mul_comm] using And.intro hh.1.le hh.2

theorem original_ray_compensatedPhysicalProbe_low_loss_total_mass (phys : LowPhysicalExponents)
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
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) Z‖≤C*Z^(((5*phys.x+phys.y)/12)+loss) := by
  let D := max 1 B
  have hD : 0<D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDc : (D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hD.ne'
  let Wn := fun i x=>W i x/(D:ℂ)
  have hWn : ∀i,Function.support (Wn i)⊆Set.Icc a b := by
    intro i x hx
    apply hW i
    intro hz
    exact hx (by dsimp [Wn];rw [hz,zero_div])
  have hn : ∀i x,‖Wn i x‖≤1 := by
    intro i x
    dsimp only [Wn]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
    exact (div_le_one hD).mpr ((hWnorm i x).trans (le_max_right _ _))
  have hscale : (fun i x=>(D:ℂ)*Wn i x)=W := by
    funext i x
    dsimp [Wn]
    field_simp
  let ε := min (loss/512) (1/2)
  have he : 0<ε := by dsimp [ε];positivity
  have he1 : ε<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heloss : 256*ε≤loss := by have hh := min_le_left (loss/512) (1/2:ℝ);dsimp only [ε];linarith
  intro η
  obtain ⟨C,hC,hbound⟩ := original_ray_compensatedPhysicalProbe_low_total_mass phys η S hS hmax ell hell hinj hsum htotal R
    a b ε ha hab he he1 Wn hWn hn W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨D^K*C,by positivity,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  have heq := compensatedPhysicalProbe_window_scale η (calibrationForSet S hmax) W0 W1
    (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) Wn (fun i=>Z^(ell i))
    (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) Z (D:ℂ)
  rw [hscale] at heq
  rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
  calc
    _≤D^K*(C*Z^(((5*phys.x+phys.y)/12)+256*ε)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _≤D^K*(C*Z^(((5*phys.x+phys.y)/12)+loss)) := by gcongr
    _=_ := by ring

theorem original_normalized_compensatedPhysicalProbe_low_total_mass (phys : LowPhysicalExponents) {K : ℕ}
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
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
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
        C*Z^(((5*phys.x+phys.y)/12)+loss) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1⊆Set.Icc a1 (max b1 (a1+1)) := by
    intro y hy
    exact ⟨(hW1 hy).1,(hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1 < max b1 (a1+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := ProbeHighRowFamily.actual_ray_normalizer_inverse M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ := original_ray_compensatedPhysicalProbe_low_loss_total_mass phys S hS hmax ell
    (fun j=>(hell j).le) hinj hsum.le htotal (RayQuotient.identityClass M H) a b B (loss/2)
    ha hab (by positivity) WC hWC hWCB W0 W1 a0 b0 a1 (max b1 (a1+1))
    (SchwartzMap.seminorm ℝ 0 0 W0) (SchwartzMap.seminorm ℝ 0 0 W1)
    ha0 ha1 hab1 (by positivity) (by positivity) hW0 hW1' (W0.smooth (⊤ : ℕ∞)) (W1.smooth (⊤ : ℕ∞))
    (SchwartzMap.norm_le_seminorm ℝ W0) (SchwartzMap.norm_le_seminorm ℝ W1) η
  refine ⟨Cp*Cn,by positivity,?_⟩
  filter_upwards [hprobe,hnorm,eventually_gt_atTop (0:ℝ)] with Z hp hn hZ
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(Cp*Z^(((5*phys.x+phys.y)/12)+loss/2))*(Cn*Z^(loss/2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _=(Cp*Cn)*Z^(((5*phys.x+phys.y)/12)+loss) := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2
      ring

#print axioms low_physical_inverse_normalized_total_mass
#print axioms low_central_compensated_tuple_total_mass
#print axioms original_normalized_compensatedPhysicalProbe_low_total_mass
end SevenEighths.ProbePhysical
end
end OAI
