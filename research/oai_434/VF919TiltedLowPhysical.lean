import «research.oai_434.VF919TiltedLowReflection»
import OAI.NumberTheory.DirichletL.Detector.LowNormalized

/-!
# Complete compensated LOW probe at admissible physical exponents

All source coefficients, prime pools, masks and compensation terms are the
original arithmetic source. The finite-slot gate is discharged from the
actual slot lengths. No energy estimate is assumed as an input.
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

/-- Only geometric scale conditions; this record contains no analytic estimate. -/
structure LowPhysicalExponents where
  x : ℝ
  y : ℝ
  sum_lo : (1/2:ℝ) ≤ x+y
  sum_hi : x+y ≤ (5/6:ℝ)
  x_gt_slot : (1/6:ℝ) < x
  x_lt_y : x < y
  gram_gap : (1/6:ℝ) < 2*x-y
  y_le_one : y ≤ 1



/-! Physical extension: Detector/LowNominalGeometry.lean. -/

lemma lowPhysicalScale_source_tilted (phys : LowPhysicalExponents) (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L)=
      elementNorm C.generator*Z^((phys.x+phys.y):ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(phys.x:ℝ)*Z^(phys.y:ℝ)=Z^((phys.x+phys.y):ℝ) := by rw [←Real.rpow_add hZ]
  rw [←he]
  ring

lemma lowPhysicalScale_nominal_bound_tilted (phys : LowPhysicalExponents) (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L)≤
      (elementNorm C.generator/c^2)*Z^((phys.x+phys.y)-2*d:ℝ) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source_tilted phys C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^((phys.x+phys.y):ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ]
      ring


/-! Physical extension: Detector/LowGramScale.lean. -/

lemma source_gram_power_tilted (phys : LowPhysicalExponents) (Z δ : ℝ) (hZ : 0<Z) :
    Z^(phys.x:ℝ)*(Z^((phys.y-phys.x):ℝ))^(1/6:ℝ)*(Z^(phys.y:ℝ))^δ=
      Z^(((5*phys.x+phys.y)/6)+(phys.y)*δ:ℝ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma source_gram_sqrt_power_tilted (phys : LowPhysicalExponents) (Z δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^(((5*phys.x+phys.y)/6)+(phys.y)*δ:ℝ))=Z^(((5*phys.x+phys.y)/12)+(phys.y/2)*δ:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring


/-! Physical extension: Detector/LowSourceScales.lean. -/

lemma source_scale_ratio_tilted (phys : LowPhysicalExponents) (Z : ℝ) (hZ : 0<Z) :
    Z^(phys.y:ℝ)/Z^(phys.x:ℝ)=Z^((phys.y-phys.x):ℝ) := by
  rw [←Real.rpow_sub hZ]

lemma source_scale_square_tilted (phys : LowPhysicalExponents) (Z : ℝ) (hZ : 0<Z) :
    Z^((2*phys.x-phys.y):ℝ)*Z^(phys.y:ℝ)=(Z^(phys.x:ℝ))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1 <;> ring

lemma source_compensated_scale_admissible_tilted (phys : LowPhysicalExponents) (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^((phys.y-phys.x):ℝ)) (hLl : L≤Z^((2*phys.x-phys.y):ℝ)) :
    1≤Z^(phys.y:ℝ)/L ∧
    q*Z^(phys.x:ℝ)≤Z^(phys.y:ℝ) ∧
    L*Z^(phys.y:ℝ)≤q^2*(Z^(phys.x:ℝ))^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show ((2*phys.x-phys.y):ℝ)≤phys.y by linarith [phys.x_lt_y]))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (phys.x))).mp
    rwa [source_scale_ratio_tilted phys Z hz]
  · calc
      _≤Z^((2*phys.x-phys.y):ℝ)*Z^(phys.y:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(phys.x:ℝ))^2 := source_scale_square_tilted phys Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_compensated_gram_scale_tilted (phys : LowPhysicalExponents) (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^((phys.y-phys.x):ℝ)) (hLl : L≤Z^((2*phys.x-phys.y):ℝ)) (hδ : 0≤δ) :
    (q*(Z^(phys.x:ℝ)/L)*(Z^(phys.y:ℝ)/L)/(Z^(phys.y:ℝ)/L))*
      (1+((Z^(phys.y:ℝ)/L)^2/(q*(Z^(phys.x:ℝ)/L)*(Z^(phys.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(phys.y:ℝ)/L)^2/(q*(Z^(phys.x:ℝ)/L)*(Z^(phys.y:ℝ)/L)))^2/(Z^(phys.y:ℝ)/L))*
      (Z^(phys.y:ℝ)/L)^δ ≤
        (3*q/L)*Z^(((5*phys.x+phys.y)/6)+(phys.y)*δ:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible_tilted phys q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(phys.y:ℝ)/(q*Z^(phys.x:ℝ))≤Z^((phys.y-phys.x):ℝ) := by
    rw [←source_scale_ratio_tilted phys Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(phys.y:ℝ)/(q*Z^(phys.x:ℝ))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(phys.x:ℝ)/L)*(Z^((phys.y-phys.x):ℝ))^(1/6:ℝ)*(Z^(phys.y:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(phys.x:ℝ)*(Z^((phys.y-phys.x):ℝ))^(1/6:ℝ)*(Z^(phys.y:ℝ))^δ) := by ring
    _=_ := by rw [source_gram_power_tilted phys Z δ hz]

lemma source_compensated_gram_sqrt_tilted (phys : LowPhysicalExponents) (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^((phys.y-phys.x):ℝ)) (hLl : L≤Z^((2*phys.x-phys.y):ℝ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(phys.x:ℝ)/L)*(Z^(phys.y:ℝ)/L)/(Z^(phys.y:ℝ)/L))*
      (1+((Z^(phys.y:ℝ)/L)^2/(q*(Z^(phys.x:ℝ)/L)*(Z^(phys.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(phys.y:ℝ)/L)^2/(q*(Z^(phys.x:ℝ)/L)*(Z^(phys.y:ℝ)/L)))^2/(Z^(phys.y:ℝ)/L))*
      (Z^(phys.y:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^(((5*phys.x+phys.y)/12)+(phys.y/2)*δ:ℝ) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale_tilted phys q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power_tilted phys Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma lowGramFactor_source_bound_tilted (phys : LowPhysicalExponents) (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^((phys.y-phys.x):ℝ))
    (hLl : L≤Z^((2*phys.x-phys.y):ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(((5*phys.x+phys.y)/12)+(phys.y/2)*δ:ℝ) :=
  source_compensated_gram_sqrt_tilted phys _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma eventually_compensated_source_scales_tilted (phys : LowPhysicalExponents) (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^((phys.y-phys.x):ℝ) ∧
      ∀L : ℝ,1≤L→L≤B*Z^(1/6:ℝ)→
        1≤Z^(phys.y:ℝ)/L ∧
        1≤(Z^(phys.y:ℝ)/L)^2/lowPhysicalScale C (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^(((5*phys.x+phys.y)/12)+(phys.y/2)*δ:ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0<((phys.y-phys.x):ℝ) by linarith [phys.x_lt_y])).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<((2*phys.x-phys.y-1/6):ℝ) by linarith [phys.gram_gap])).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^((2*phys.x-phys.y):ℝ) := calc
    L≤B*Z^(1/6:ℝ) := hLB
    _≤Z^((2*phys.x-phys.y-1/6):ℝ)*Z^(1/6:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^((2*phys.x-phys.y):ℝ) := by rw [←Real.rpow_add hz];congr 1;ring
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible_tilted phys _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound_tilted phys C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)


/-! Physical extension: Detector/LowSlotScales.lean. -/

theorem eventually_original_slot_scales_tilted (phys : LowPhysicalExponents) {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6) (b : ℝ) (hb : 1≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤Z^(phys.y:ℝ)/L ∧
      1≤(Z^(phys.y:ℝ)/L)^2/lowPhysicalScale C (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(phys.x:ℝ)/L) (Z^(phys.y:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^(((5*phys.x+phys.y)/12)+(phys.y/2)*δ:ℝ) := by
  filter_upwards [eventually_compensated_source_scales_tilted phys C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ.1 slots hnorm J a)


/-! Physical extension: Detector/LowInverseNormalize.lean. -/

lemma low_inverse_power_cancel_tilted (phys : LowPhysicalExponents) (Z d α : ℝ) (hZ : 0<Z) :
    Z^((phys.x+phys.y)-2*d+α)*(Z^d)^2/Z^((phys.x+phys.y):ℝ)=Z^α := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  ring

lemma low_inverse_sqrt_normalized_tilted (phys : LowPhysicalExponents) (q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0<q) (hC : 0≤C) (_hB : 0≤B) (hZ : 0<Z) (hL : 0<L) (hH : 1≤H)
    (hE : 0≤E) (hEL : E≤C*H^n*Z^((phys.x+phys.y)-2*d+α)) (hLB : L≤B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^((phys.x+phys.y):ℝ)/L^2)≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^((phys.x+phys.y):ℝ)/L^2)≤(C*B^2/q)*H^n*Z^α := by
    calc
      _≤(C*H^n*Z^((phys.x+phys.y)-2*d+α))/(q*Z^((phys.x+phys.y):ℝ)/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _=(C*H^n*Z^((phys.x+phys.y)-2*d+α))*L^2/(q*Z^((phys.x+phys.y):ℝ)) := by field_simp
      _≤(C*H^n*Z^((phys.x+phys.y)-2*d+α))*(B*Z^d)^2/(q*Z^((phys.x+phys.y):ℝ)) := by
        gcongr
      _=(C*B^2/q)*H^n*(Z^((phys.x+phys.y)-2*d+α)*(Z^d)^2/Z^((phys.x+phys.y):ℝ)) := by ring
      _=_ := by rw [low_inverse_power_cancel_tilted phys Z d α hZ]
  rw [←Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^α)=Z^(α/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity)) (by positivity)


/-! Physical extension: Detector/LowSelectedBound.lean. -/

theorem low_selected_physical_energy_tilted (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (K : ℕ) (Ck ε : ℝ) (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
    ∀(Z d ell0 shift : ℝ),Z₀≤Z→0≤d→d≤1/6→0≤ell0→ell0≤1/6-d+ε→|shift|≤ε→
    ∀(R : Finset O),(∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^((phys.x+phys.y)-2*d))→
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
    ∀(J : Finset (Fin K))(H : SelectedSlot J→ℝ),
      (IsEmpty (SelectedSlot J) ∨ (5/3:ℝ)-2*(phys.x+phys.y)≤ell0)→
      (∀i,1≤H i)→(∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i)→(∏i,H i)≤Z^ell0→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) (Z^(1+ell0+shift)) t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^(((phys.x+phys.y)-2*d)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := InverseReflectedPhase.low_original_completed_energy_tilted (phys.x+phys.y) phys.sum_lo phys.sum_hi
    (lowReflectionPeriod η S hS) (lowReflectionPeriod_ne_zero η S hS)
    (1:Id) squarefree_one (lowReflectionMask η S hS) (lowReflectionMask_ne_zero η S hS)
    (lowReflectionMask_bad η S hS hbad).1 (lowReflectionMask_bad η S hS hbad).2
    (lowReflectionMask_period η S hS) (lowReflectionMask_bad_ideals η S hS hbad)
    (1/2) 2 (by norm_num) gaussianFixedWindow gaussianFixedWindow_support gaussianFixedWindow_contDiff
    Ck ε hCk hε hε1 K
  let C0 := (lowCorrectionEnergy+1)*((Fintype.card RayCharacter:ℝ)+1)*6*C
  have hC0 : 0<C0 := by have hh := lowCorrectionEnergy_nonneg;dsimp [C0];positivity
  refine ⟨degree,C0,Z₀,hC0,hZ₀,?_⟩
  intro Z d ell0 shift hZ hd hd1 hell hellcap hshift R hR T hT hout hdis J H hgate hH1 hH hprod W hW Y t σ
  let L := fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val))
  have hLP (i : SelectedSlot J) : lowPeriodPrimeList η S hS (T i.val)⊆T i.val := Finset.filter_subset _ _
  have hLS (i : SelectedSlot J) : ∀P∈lowPeriodPrimeList η S hS (T i.val),Supported P.val :=
    fun P hP=>hT i.val P (hLP i hP)
  have hlists : Pairwise (fun i j=>Disjoint (L i) (L j)) :=
    lowPrimeIdealList_disjoint _ (lowPeriodPrimeList_disjoint η S hS _
      (fun i j hij=>hdis (fun h=>hij (Subtype.ext h))))
  have hparents : ∀I∈lowIdealRows R,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^((phys.x+phys.y)-2*d) :=
    fun I hI=>⟨lowIdealRows_nonzero R (fun z hz=>(hR z hz).1) I hI,
      lowIdealRows_norm_bound R _ (fun z hz=>(hR z hz).2) I hI⟩
  have hcard : Fintype.card (SelectedSlot J)≤K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  have hrow (χ : RayCharacter) (u : Oˣ) :
      (∑I∈lowIdealRows R,‖lowActualIdealPolynomial L
        (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) (Z^(1+ell0+shift))‖^2)≤
          C*(1+‖t‖)^degree*Z^(((phys.x+phys.y)-2*d)+507*ε) := by
    convert he Z d ell0 shift hZ hd hd1 hell hellcap hshift hgate (lowIdealRows R) hparents hcard L H
      hlists (fun i=>lowPrimeIdealList_maximal _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).1)
      (fun i=>lowPrimeIdealList_prime _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).2)
      hH1 (fun i=>lowPrimeIdealList_norm _ _ (fun P hP=>hH i P (hLP i hP))) hprod
      (physicalRayPeriodicBase η S hS σ χ) (lowReflectionPeriod_actual η S hS σ χ).2
      (lowReflectionPeriod_actual η S hS σ χ).1 u t
      (fun i P=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator P.val))
      (fun i P=>low_actual_ideal_weight_bound η (W i.val) (hW i.val) (Y i.val) t P.val) using 1
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    unfold lowActualIdealPolynomial
    congr 1
    ext p
    simp
  apply (lowSelectedInverseRow_actual_reflected_energy η S hS hbad T hT hout hdis J W Y
    (Z^(1+ell0+shift)) t σ R (fun z hz=>(hR z hz).1)).trans
  have hh := Finset.sum_le_sum (fun χ (_ : χ∈(Finset.univ:Finset RayCharacter))=>
    Finset.sum_le_sum (fun u (_ : u∈(Finset.univ:Finset Oˣ))=>hrow χ u))
  have hm := mul_le_mul_of_nonneg_left hh lowCorrectionEnergy_nonneg
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,low_unit_card] at hm
  simp only [Nat.cast_ofNat,Real.norm_eq_abs] at hm ⊢
  apply hm.trans
  dsimp [C0]
  have hc0 := lowCorrectionEnergy_nonneg
  have hcount : 0≤(Fintype.card RayCharacter:ℝ) := Nat.cast_nonneg _
  have hzpos : 0≤Z^(((phys.x+phys.y)-2*d)+507*ε) := Real.rpow_nonneg (le_trans zero_le_one (hZ₀.le.trans hZ)) _
  have htpos : 0≤(1+|t|)^degree := by positivity
  calc
    _=(lowCorrectionEnergy*(Fintype.card RayCharacter:ℝ)*6*C)*(1+|t|)^degree*
        Z^(((phys.x+phys.y)-2*d)+507*ε) := by ring
    _≤_ := by gcongr <;> linarith


/-! Physical extension: Detector/LowNominalEnergy.lean. -/

theorem low_selected_nominal_energy_tilted (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (hgap : ∀ i, (5/3:ℝ)-2*(phys.x+phys.y) ≤ ell i)
    (Ck b ε : ℝ) (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(R : Finset O),
      (∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^((phys.x+phys.y)-2*lowUnselectedLength ell J))→
    ∀X : ℝ,0<X→Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^(((phys.x+phys.y)-2*lowUnselectedLength ell J)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_selected_physical_energy_tilted phys η S hS hbad K Ck ε hCk hε hε1
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [eventually_low_selected_caps ell hell b ε hε,Filter.eventually_ge_atTop Z₀] with Z hc hZ
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J R hR X hX hXlo hXhi W hW Y t σ
  obtain ⟨hd,hd1,hs,hscap⟩ := lowLength_bounds ell hell hsum J
  have hscale := lowCentralShift_scale Z X (lowSelectedLength ell J+ε/2) hc.1 hX
  rw [←hscale]
  have hgate : IsEmpty (SelectedSlot J) ∨
      (5/3:ℝ)-2*(phys.x+phys.y) ≤ lowSelectedLength ell J+ε/2 := by
    by_cases hn : (Finset.univ\J).Nonempty
    · obtain ⟨i,hi⟩ := hn
      have hsingle : ell i ≤ lowSelectedLength ell J := by
        rw [lowSelectedLength,Finset.sum_coe_sort]
        exact Finset.single_le_sum (fun j _ => hell j) hi
      exact Or.inr (by linarith [hgap i])
    · exact Or.inl ⟨fun i => hn ⟨i.val,i.property⟩⟩
  apply he Z (lowUnselectedLength ell J) (lowSelectedLength ell J+ε/2)
    (lowCentralShift Z X (lowSelectedLength ell J+ε/2)) hZ hd hd1 (by linarith) (by linarith)
    (lowCentralShift_bound Z X (lowSelectedLength ell J) ε hc.1 hX hε.le hXlo hXhi)
    R hR T hT hout hdis J (fun i=>max 1 (b*Z^(ell i.val))) hgate
    (fun i=>le_max_left _ _)
    (fun i P hP=>(hnorm i.val P hP).trans (le_max_right _ _)) (hc.2 J) W hW Y t σ


/-! Physical extension: Detector/LowPhysicalInverseBound.lean. -/

theorem low_physical_inverse_normalized_tilted (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (hgap : ∀ i, (5/3:ℝ)-2*(phys.x+phys.y) ≤ ell i)
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
        C*(1+‖t‖)^degree*Z^(507*ε/2) := by
  let q := elementNorm (calibrationForSet S hS).generator
  let c := (min 1 a)^K
  let B := (max 1 b)^K
  have hq : 0<q := calibration_elementNorm_pos _
  have hc : 0<c := by dsimp [c];positivity
  have hB : 0<B := by dsimp [B];positivity
  let Ck := 2*bCut*(q/c^2)
  have hCk : 0<Ck := by dsimp [Ck];positivity
  obtain ⟨degree,C,ZC,hbound⟩ := low_selected_nominal_energy_tilted phys η S hS hbad ell hell hsum hgap Ck b ε hCk hε hε1
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
      C*(1+‖t‖)^degree*Z^((phys.x+phys.y)-2*lowUnselectedLength ell J+507*ε) :=
    hZ.2 T hT hout hdis (fun i P hP=>(hnorm i P hP).2) J R hrows X hX hXlo hXhi W hW (fun i=>Z^(ell i)) t σ
  have hn (σ : RayRing) : Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q≤
      Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^(507*ε/2) := by
    dsimp only [Q]
    rw [lowPhysicalScale_source_tilted phys _ Z L hz]
    exact low_inverse_sqrt_normalized_tilted phys q C B Z L (lowUnselectedLength ell J) (507*ε) (1+‖t‖)
      (∑z∈R,‖row σ z‖^2) degree hq ZC.le hB.le hz hL (le_add_of_nonneg_right (norm_nonneg t))
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (he σ) hLhi
  change (Real.sqrt Q)⁻¹/(2*Real.pi)*(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2))≤_
  calc
    _=(∑σ : RayRing,Real.sqrt (∑z∈R,‖row σ z‖^2)/Real.sqrt Q)/(2*Real.pi) := by
      rw [←Finset.sum_div]
      ring
    _≤(∑σ : RayRing,Real.sqrt (C*B^2/q)*(1+‖t‖)^degree*Z^(507*ε/2))/(2*Real.pi) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _=>hn σ)) (by positivity)
    _≤_ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [C0]
      calc
        _=((Fintype.card RayRing:ℝ)*Real.sqrt (C*B^2/q)/(2*Real.pi))*(1+|t|)^degree*Z^(507*ε/2) := by ring
        _≤_ := by gcongr ; linarith


/-! Physical extension: Detector/LowCentralTuple.lean. -/

theorem low_central_compensated_tuple_tilted (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (hgap : ∀ i, (5/3:ℝ)-2*(phys.x+phys.y) ≤ ell i)
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
  obtain ⟨degree,Ci,hCi,hinverse⟩ := low_physical_inverse_normalized_tilted phys η S hS hbad ell hell hsum hgap
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu,hCu,hmass⟩ := lowUnselectedMass_bound K 1 (by norm_num)
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
  have hnormE : ∀i n,n∈slots i→elementNorm n≤max 1 b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^(((5*phys.x+phys.y)/12)+(phys.y/2)*ε:ℝ)
  let V := Ci*(1+‖t‖)^degree*Z^(507*ε/2)
  have hGV : G*V≤Ci*(1+‖t‖)^degree*Z^(((5*phys.x+phys.y)/12)+254*ε) := by
    dsimp only [G,V]
    calc
      _=Ci*(1+‖t‖)^degree*(Z^(((5*phys.x+phys.y)/12)+(phys.y/2)*ε:ℝ)*Z^(507*ε/2)) := by ring
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
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(((5*phys.x+phys.y)/12)+254*ε))*
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
          (Ci*(1+‖t‖)^degree*Z^(((5*phys.x+phys.y)/12)+254*ε)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _=_ := by rw [low_compensated_sqrt_factor q L hq.le hL];ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hm := hmass T hT J W Yp hW
  calc
    _≤Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(((5*phys.x+phys.y)/12)+254*ε))*Cu) := by gcongr
    _=_ := by dsimp [C0];ring


/-! Physical extension: Detector/LowRemoteMass.lean. -/

lemma compensation_scale_mass_bound_tilted (phys : LowPhysicalExponents) {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b Z : ℝ) (hZ : 1≤Z) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=>compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=>Z^(phys.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Z^(phys.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C (Z^(phys.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(phys.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^((phys.x+phys.y):ℝ) := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=>norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun (i : SelectedSlot J) _=>hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [lowPhysicalScale_source_tilted phys C Z _ hz]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=>hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0≤elementNorm C.generator*Z^((phys.x+phys.y):ℝ) by unfold elementNorm;positivity)
  apply hc.trans
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*(Z^(1/6:ℝ)*Z^((phys.x+phys.y):ℝ)) := by ring
    _≤_ := by
      rw [←Real.rpow_add hz]
      have hp : Z^((1/6:ℝ)+(phys.x+phys.y)) ≤ Z := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hZ (show (1/6:ℝ)+(phys.x+phys.y)≤1 by linarith [phys.sum_hi])
      exact mul_le_mul_of_nonneg_left hp (by unfold elementNorm;positivity)


/-! Physical extension: Detector/LowGaussianDyad.lean. -/

theorem low_central_gaussian_dyad_tilted (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (hgap : ∀ i, (5/3:ℝ)-2*(phys.x+phys.y) ≤ ell i)
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
  obtain ⟨degree,C,hC,he⟩ := low_central_compensated_tuple_tilted phys η S hS hbad ell hell hsum hgap
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J U hU hlo hhi W hW V hV
  apply lowCommonDyad_norm_of_bound
  intro t
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hZ.2 T hT hout hdis hnorm J U hU hlo hhi W hW t


/-! Physical extension: Detector/LowGaussianRemote.lean. -/

lemma eventually_low_physical_scales_tilted (phys : LowPhysicalExponents) {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (b : ℝ) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
      ∀(slots : Fin K→Finset O),(∀i x,x∈slots i→x≠0)→
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(p : ∀i,slots i),
      1≤Z^(phys.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) ∧
      1≤Z^(phys.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<((phys.x-1/6):ℝ) by linarith [phys.x_gt_slot])).eventually
      (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro slots hn hnorm J p
  have hl : 0<elementNorm (slotProduct (fun i=>(p i).val) J) :=
    slotProduct_norm_pos _ (fun i=>hn i _ (p i).property) J
  have hb := lowUnselectedProduct_norm_bound ell hell hsum (max 1 b) Z (le_max_left _ _) hZ.le
    slots (fun i n hm=>(hnorm i n hm).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    J (fun i=>p i.val)
  rw [←slotProduct_subtype (fun i=>(p i).val) J] at hb
  have hLX : elementNorm (slotProduct (fun i=>(p i).val) J)≤Z^(phys.x:ℝ) := by
    apply hb.trans
    calc
      _≤Z^((phys.x-1/6):ℝ)*Z^(1/6:ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];congr 1;ring
  constructor
  · exact (one_le_div hl).mpr hLX
  · exact (one_le_div hl).mpr (hLX.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [phys.x_lt_y])))

theorem low_remote_gaussian_dyads_tilted (phys : LowPhysicalExponents) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b ε : ℝ) (hε : 0<ε) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(η : HeckeFamily.Character)(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(phys.x:ℝ)) (Z^(phys.y:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖ else 0
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(-1:ℝ) := by
  have hep : 0<ε/2 := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt ((13/3:ℝ)/(ε/2))
  have hN' : (13/3:ℝ)≤(ε/2)*(N:ℝ) := by
    have hh := (div_lt_iff₀ hep).mp hN
    nlinarith
  obtain ⟨Cg,hCg,he⟩ := gaussianPhysicalFamily_remote_polynomial V hV N
    a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg*(q*(128*max 1 b)^K)
  have hq : 0<q := calibration_elementNorm_pos _
  refine ⟨C0,by dsimp [C0];positivity,?_⟩
  filter_upwards [eventually_low_physical_scales_tilted phys ell hell hsum b] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro η T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈canonicalSlotSupport (T i)→elementNorm n≤b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hs := hZ.2 _ hslots hnormE J
  have hh := he η S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1 (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
    (fun p=>compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
    (fun p=>Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
    (fun p=>Z^(phys.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p=>Z^(phys.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p _=>(hs p).1) (fun p _=>(hs p).2)
    (fun i : SelectedSlot J=>W i.val) (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))
    (Z^(1+lowSelectedLength ell J)) (Z^(ε/2)) (by positivity) (Real.one_le_rpow hZ.1.le hep.le)
  simp only [←lowCommonDyad_eq_family] at hh
  refine ⟨?_,?_⟩
  · convert hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only [ite_true, ite_false]
  · have hhFinal := hh.2.trans (show _≤C0*Z^(-1:ℝ) from by
      have hm := compensation_scale_mass_bound_tilted phys η (calibrationForSet S hS) ell hell hsum b Z hZ.1.le T hT hnorm J W hW
      calc
        _≤Cg*((q*(128*max 1 b)^K)*Z)*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N := by gcongr
        _=C0*(Z*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N) := by dsimp [C0];ring
        _≤_ := mul_le_mul_of_nonneg_left (low_remote_power Z (lowSelectedLength ell J) ε N hZ.1.le
          (by have hb := lowLength_bounds ell hell hsum J;linarith) hN') (by dsimp [C0];positivity))
    convert hhFinal using 1
    apply tsum_congr
    intro j
    split_ifs with h <;> simp_all only [ite_true, ite_false]


/-! Physical extension: Detector/LowGaussianCentral.lean. -/

theorem low_central_gaussian_dyads_tilted (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (hgap : ∀ i, (5/3:ℝ)-2*(phys.x+phys.y) ≤ ell i)
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
  obtain ⟨degree,C,hC,he⟩ := low_central_gaussian_dyad_tilted phys η S hS hbad ell hell hsum hgap
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


/-! Physical extension: Detector/LowGaussianSum.lean. -/

theorem low_all_gaussian_dyads_tilted (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (hgap : ∀ i, (5/3:ℝ)-2*(phys.x+phys.y) ≤ ell i)
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
  obtain ⟨Cc,hCc,hcentral⟩ := low_central_gaussian_dyads_tilted phys η S hS hbad ell hell hsum hgap
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


/-! Physical extension: Detector/LowCommonBound.lean. -/

theorem compensatedPhysicalProbe_low_tilted (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (hgap : ∀ i, (5/3:ℝ)-2*(phys.x+phys.y) ≤ ell i)
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
  choose C hC he using fun A : Finset (Fin K)=>low_all_gaussian_dyads_tilted phys η S hS hbad ell hell hsum hgap
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

theorem original_ray_compensatedPhysicalProbe_low_tilted (phys : LowPhysicalExponents) (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6)
    (hgap : ∀ i, (5/3:ℝ)-2*(phys.x+phys.y) ≤ ell i) (R : Set Id)
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
  obtain ⟨C,hC,he⟩ := compensatedPhysicalProbe_low_tilted phys η S hmax hS.bad ell hell hsum hgap
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


/-! Physical extension: Detector/LowWindowBound.lean. -/

theorem original_ray_compensatedPhysicalProbe_low_loss_tilted (phys : LowPhysicalExponents)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6)
    (hgap : ∀ i, (5/3:ℝ)-2*(phys.x+phys.y) ≤ ell i) (R : Set Id)
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
  obtain ⟨C,hC,hbound⟩ := original_ray_compensatedPhysicalProbe_low_tilted phys η S hS hmax ell hell hinj hsum hgap R
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


/-! Physical extension: Detector/LowNormalized.lean. -/

theorem original_normalized_compensatedPhysicalProbe_low_tilted (phys : LowPhysicalExponents) {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (hgap : ∀ i, (5/3:ℝ)-2*(phys.x+phys.y) ≤ ell i)
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
  have hab1 : a1<max b1 (a1+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := ProbeHighRowFamily.actual_ray_normalizer_inverse M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ := original_ray_compensatedPhysicalProbe_low_loss_tilted phys S hS hmax ell
    (fun j=>(hell j).le) hinj hsum.le hgap (RayQuotient.identityClass M H) a b B (loss/2)
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


#print axioms original_normalized_compensatedPhysicalProbe_low_tilted
end SevenEighths.ProbePhysical
end
end OAI
