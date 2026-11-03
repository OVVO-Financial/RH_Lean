import «research.oai_434.VF919FiniteSlotReflectedGain»
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyHigh

/-!
# Tilted physical tails and complete canonical decomposition

The absolute Mellin weights satisfy an exact scale identity. The original
signed rows, source coefficients, dyadic cutoff, bins and character families
are retained. The large contour pays its explicit 24*tilt charge.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O

lemma tilted_scale_product (Z : ℝ) (hZ : 0<Z) (tilt σ υ r : ℝ) :
    (Z^((17/48:ℝ)-24*tilt))^(1/2-r)*Z^(σ+r-1)*
      (Z^((23/48:ℝ)+12*tilt))^(υ-1)=
    Z^(tilt*(24*r+12*υ-24))*
      ((Z^(17/48:ℝ))^(1/2-r)*Z^(σ+r-1)*(Z^(23/48:ℝ))^(υ-1)) := by
  simp_rw [←Real.rpow_mul hZ.le]
  simp_rw [←Real.rpow_add hZ]
  congr 1
  ring

lemma tilted_sourceMellinWeight_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (Z tilt : ℝ) (hZ : 0<Z) (s w z : ℂ) :
    ‖sourceMellinWeight W0 W1 (Z^((17/48:ℝ)-24*tilt))
      (Z^((23/48:ℝ)+12*tilt)) Z s w z‖=
    Z^(tilt*(24*z.re+12*w.re-24))*
      ‖sourceMellinWeight W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z s w z‖ := by
  rw [sourceMellinWeight_eq_scale,sourceMellinWeight_eq_scale,norm_mul,norm_mul,
    sourceScale_norm _ _ _ (by positivity) (by positivity) hZ,
    sourceScale_norm _ _ _ (by positivity) (by positivity) hZ,
    tilted_scale_product Z hZ tilt s.re w.re z.re]
  ring

lemma tilted_absolutePhysicalDyadIntegral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (Z tilt σ υ r : ℝ) (hZ : 0<Z) :
    absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1
      (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z σ υ r=
    Z^(tilt*(24*r+12*υ-24))*
      absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z σ υ r := by
  unfold absolutePhysicalDyadIntegral
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [tilted_sourceMellinWeight_norm W0 W1 Z tilt hZ]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  ring

lemma tilted_central_power_bound (Z tilt a e : ℝ) (hZ : 1≤Z)
    (htilt : 0≤tilt) (ha : 51/100≤a) (he : 0≤e) :
    (Z^((17/48:ℝ)-24*tilt))^(4/25:ℝ)*Z^(a+16*e-33/50)*
      (Z^((23/48:ℝ)+12*tilt))^(-a-6*e)≤
      Z^((25/48)*a-181/300+(105/8)*e-8*tilt) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  simp_rw [←Real.rpow_mul hz.le]
  rw [←Real.rpow_add hz,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have ht := RHLeanFiniteSlotGap.tilted_central_prefactor_margin tilt a e htilt ha he
  nlinarith



/-! Physical extension: PrimeRows/SmallTail.lean. -/

theorem small_physical_dyads_sum_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50))
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_physical_dyads_sum K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hbnd := hmain η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hscale (n : ℕ) := tilted_absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W
    (fun i=>Z^(length i)) W0 W1 Z tilt (HeckeZeroSupremum.beta+8*e) (1/2) (17/50) hz
  simp_rw [hscale]
  rw [←Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg hz.le _)).trans
  calc
    _=C*(η.modulus.absNorm:ℝ)^δ*
      (Z^(tilt*(24*(17/50:ℝ)+12*(1/2:ℝ)-24))*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)) := by ring
    _≤_ := by
      rw [←Real.rpow_add hz]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)


/-! Physical extension: PrimeRows/LargeSaving.lean. -/

theorem large_physical_tail_arbitrary_saving_tilted (tilt : ℝ) (_htilt : 0≤tilt) (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ) (htiltCut : 24*tilt<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃r C : ℝ,(17/50:ℝ)≤r ∧ 0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((13/16:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving-8*tilt) := by
  obtain ⟨r,hr,hr',hpower⟩ := exists_large_tail_line (ζ-24*tilt) δ
    (saving+8*tilt+24*tilt*(8/5+δ)) (by linarith)
  obtain ⟨C,hC,hmain⟩ := large_physical_dyads_summable K δ a b B r ζ hδ hδ' hr hr' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨r,C,hr,hC,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hs,hbnd⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hscale (n : ℕ) := tilted_absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W
    (fun i=>Z^(length i)) W0 W1 Z tilt 2 2 r hz
  simp_rw [hscale]
  refine ⟨hs.mul_left _,?_⟩
  rw [tsum_mul_left]
  apply (mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg hz.le _)).trans
  calc
    _=C*(η.modulus.absNorm:ℝ)^δ*
      (Z^(tilt*(24*r+12*2-24))*Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r)) := by ring
    _≤_ := by
      rw [←Real.rpow_add hz]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith only [hpower])


/-! Physical extension: PrimeRows/PhysicalSmallTail.lean. -/

theorem small_original_physical_tail_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_physical_dyads_sum_tilted tilt htilt K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hmain' := hmain η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
  have hbnd (n : ℕ) (hn : n∈F) :
      ‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z‖≤N*g n := norm_finitePhysicalRows_le_absolute
    e (HeckeZeroSupremum.beta+8*e) (1/2) (17/50) he he' (by linarith) le_rfl
    (by linarith [HeckeZeroSupremum.beta_le_one]) le_rfl (by norm_num) le_rfl
    S hS hmax hfirst η (R n) (fun u hu=>(hR n hn u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  calc
    _ ≤ ∑n∈F,N*g n := Finset.sum_le_sum hbnd
    _ = N*∑n∈F,g n := (Finset.mul_sum _ _ _).symm
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e)) :=
      mul_le_mul_of_nonneg_left hmain' hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring


/-! Physical extension: PrimeRows/PhysicalLargeTail.lean. -/

theorem large_original_physical_tail_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ) (htiltCut : 24*tilt<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((13/16:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving-8*tilt) := by
  obtain ⟨r,C,hr,hC,hmain⟩ := large_physical_tail_arbitrary_saving_tilted tilt htilt K δ a b B ζ saving hδ hδ' hζ htiltCut ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hgs,hgb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℂ := fun n=>finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
    (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z 2 2 r
  have hbnd (n : ℕ) : ‖f n‖≤N*g n := norm_finitePhysicalRows_le_absolute
    (1/2000) 2 2 r (by norm_num) (by norm_num) (by norm_num)
    (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num) (by norm_num) (by norm_num) hr
    S hS hmax hfirst η (R n) (fun u hu=>(hR n u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  have hns : Summable (fun n=>‖f n‖) := Summable.of_nonneg_of_le (fun n=>norm_nonneg _) hbnd (hgs.mul_left N)
  refine ⟨hns.of_norm,?_⟩
  calc
    (∑'n,‖f n‖) ≤ ∑'n,N*g n := hns.tsum_le_tsum hbnd (hgs.mul_left N)
    _ = N*(∑'n,g n) := tsum_mul_left
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving-8*tilt)) := mul_le_mul_of_nonneg_left hgb hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving-8*tilt)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring


/-! Physical extension: PrimeRows/CanonicalTails.lean. -/

theorem canonical_small_original_tail_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z‖
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_original_physical_tail_tilted tilt htilt K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  let L := Z^(1/100:ℝ)
  have hrows (n : ℕ) (hn : n∈smallDyadicIndices L) (u : FreeRow) (hu : u∈smallDyadicRows L n) :
      u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n := by
    have hh := mem_dyadicRows.mp (mem_smallDyadicRows.mp hu).1
    exact ⟨hh.1,by simpa only [one_mul,rowNorm] using hh.2.1,by simpa only [one_mul,rowNorm] using hh.2.2.le⟩
  have hbnd := hmain η Z hZ (smallDyadicIndices L) (fun n hn=>mem_smallDyadicIndices.mp hn)
    (smallDyadicRows L) hrows T hT hdis length hl0 hl W hWS hWB
  have heq := sum_small_dyadicRows L (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
    (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z)
  change finitePhysicalRows S hmax η (rowBand 1 L) T W (fun i=>Z^(length i)) W0 W1
    (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z=
    ∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i=>Z^(length i)) W0 W1
      (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z at heq
  rw [heq]
  exact (norm_sum_le _ _).trans hbnd

theorem canonical_large_original_tail_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ) (htiltCut : 24*tilt<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (dyadicRows (Z^((13/16:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (dyadicRows (Z^((13/16:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving-8*tilt) := by
  obtain ⟨C,hC,hmain⟩ := large_original_physical_tail_tilted tilt htilt K δ a b B ζ saving hδ hδ' hζ htiltCut ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  apply hmain η Z hZ (dyadicRows (Z^((13/16:ℝ)+ζ))) _ T hT hdis length hl0 hl W hWS hWB
  intro n u hu
  have hh := mem_dyadicRows.mp hu
  exact ⟨hh.1,hh.2.1,hh.2.2.le⟩


/-! Physical extension: PrimeRows/CanonicalReduction.lean. -/

theorem canonical_probe_minus_central_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (e δ a b B ζ saving : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (htiltCut : 24*tilt<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T W (fun i=>Z^(length i))
          W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z‖≤
        C*(η.modulus.absNorm:ℝ)^δ*(Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e)+Z^(-saving-8*tilt)) := by
  obtain ⟨Cs,hCs,hs⟩ := canonical_small_original_tail_tilted tilt htilt K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cl,hCl,hl⟩ := canonical_large_original_tail_tilted tilt htilt K δ a b B ζ saving hδ (by linarith) hζ htiltCut ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cs+Cl,add_pos hCs hCl,?_⟩
  intro η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hdec := canonical_physical_probe_partition S hS hmax η T
    (fun i P hP=>outside_prime_supported S hS.bad P (hT i P hP)) W (fun i=>Z^(length i)) W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z
    (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  have hs' := hs η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hl' := hl η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hsmall : (∑n∈smallDyadicIndices (Z^(1/100:ℝ)),finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n)
      T W (fun i=>Z^(length i)) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z)=
      finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z :=
    (sum_small_dyadicRows (Z^(1/100:ℝ)) (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
      (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z)).symm
  rw [hsmall] at hdec
  rw [hdec]
  have heq : principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Z^(length i)))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z := rfl
  rw [←heq,add_sub_cancel_left]
  rw [show ∀a b c : ℂ,a+b+c-b=a+c from fun a b c=>by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs' ((norm_tsum_le_tsum_norm hl'.1.norm).trans hl'.2)).trans
  calc
    _ ≤ (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e)+
        (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(-saving-8*tilt) := by gcongr <;> linarith
    _ = _ := by ring


/-! Physical extension: PrimeRows/CentralErrorSaving.lean. -/

lemma central_source_crude_scale_tilted (tilt : ℝ) (htilt : 0≤tilt) {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^((17/48:ℝ)-24*tilt))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^((23/48:ℝ)+12*tilt))^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  rw [tilted_scale_product Z hz tilt 2 (1-a-6*e) (17/50)]
  have hp : Z^(tilt*(24*(17/50:ℝ)+12*(1-a-6*e)-24))≤1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hZ
    exact mul_nonpos_of_nonneg_of_nonpos htilt (by linarith)
  exact (mul_le_of_le_one_left (by positivity) hp).trans (central_source_crude_scale hZ ha he)

variable {ι : Type*} [Fintype ι]


/-! Physical extension: PrimeRows/CubeErrorSaving.lean. -/

theorem original_row_cube_arbitrary_saving_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→HeckeInverseAmplification.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving-8*tilt) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((17/2:ℝ)+saving+8*tilt)/τ)
  have hN' : (17/2:ℝ)+saving+8*tilt<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := central_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := central_source_crude_scale_tilted tilt htilt hZ (by linarith : 0≤a) he.le
  have hden : Z^(τ*N)≤height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(17/2:ℝ)/Z^(τ*N)≤Z^(-saving-8*tilt) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(13/2:ℝ))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/height H^N) := by
      have hh : Z^(13/2:ℝ)*Z^(2:ℝ)=Z^(17/2:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)


/-! Physical extension: PrimeRows/CubeFiniteError.lean. -/

theorem finite_cube_arbitrary_saving_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48) (hA : 0≤A)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ)) →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=>Z^(length j)) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        finiteCentralCubeRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z e a H‖≤C*(η.modulus.absNorm:ℝ)^2*Z^(-saving-8*tilt) := by
  obtain ⟨C,hC,hrow⟩ := original_row_cube_arbitrary_saving_tilted tilt htilt (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^((13/16:ℝ)+ζ)≤Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (13/16:ℝ)+ζ≤1 by linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (central_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (1/6:ℝ)≤1 by norm_num)) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2)-8*tilt)
  have hE : 0≤E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z u-
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z (a u) e (H u)‖≤E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=>hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=>hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralCubeRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z (a u) e (H u)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^K*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^K*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^K*Z)*(A^K*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2)-8*tilt)=Z^(-saving-8*tilt) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^K*A^K*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2)-8*tilt)) := by ring
        _ = _ := by rw [hz]


/-! Physical extension: PrimeRows/CanonicalCubeReduction.lean. -/

theorem canonical_probe_minus_cube_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (htiltCut : 24*tilt<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(alpha base H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (51/100:ℝ)≤alpha u ∧ alpha u≤1 ∧ 2<base u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*base u)<alpha u+2*e) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e)+Z^(-saving-8*tilt)) := by
  obtain ⟨C0,hC0,h0⟩ := canonical_probe_minus_central_tilted tilt htilt K e δ a b B ζ saving he he' hδ hδ' hζ htiltCut ha hb hB hβ
    S hS hmax (hfirst.mono_parameter (by linarith)) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨C1,hC1,h1⟩ := finite_cube_arbitrary_saving_tilted tilt htilt (ι:=ι) K τ saving b ζ B hτ hb hζ' hB e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C0+C1,add_pos_of_pos_of_nonneg hC0 hC1,?_⟩
  intro η Z hZ T hT hdis length hl0 hl hpool W hWS hWB alpha base H idx ψ hbin
  have h0' := h0 η Z hZ T hT hdis length hl0 hl W hWS hWB
  let R := rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))
  have hR (u : FreeRow) (hu : u∈R) : u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ) :=
    ⟨(mem_rowBand.mp hu).1,(mem_rowBand.mp hu).2.2.le⟩
  have h1' := h1 η Z hZ R hR T hT hdis length hl hpool W hWB alpha base H idx ψ hbin
  have hQ := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hQδ : (η.modulus.absNorm:ℝ)^δ≤(η.modulus.absNorm:ℝ)^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  let E := Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e)+Z^(-saving-8*tilt)
  have hE : 0≤E := by dsimp [E];positivity
  have hsave : Z^(-saving-8*tilt)≤E := by dsimp [E];have : 0≤Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e) := Real.rpow_nonneg (by linarith) _;linarith
  have h0'' : ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z‖≤
      C0*(η.modulus.absNorm:ℝ)^2*E :=
    h0'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQδ hC0.le) hE)
  have h1'' := h1'.trans (mul_le_mul_of_nonneg_left hsave (mul_nonneg hC1 (sq_nonneg (η.modulus.absNorm:ℝ))))
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z) _).trans
  exact (add_le_add h0'' h1'').trans_eq (by dsimp [E];ring)


/-! Physical extension: PrimeRows/CanonicalCubeChoice.lean. -/

theorem canonical_probe_exists_cube_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (htiltCut : 24*tilt<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∃n : ℕ,0<n ∧ ∀(η : Character) (Z : ℝ),1≤Z → 2<Z^τ →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀ψ : FreeRow→ι→Character,∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (ψ u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (ψ u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e)+Z^(-saving-8*tilt)) := by
  obtain ⟨C,hC,hbound⟩ := canonical_probe_minus_cube_tilted tilt htilt (ι:=ι) K e δ a b B ζ saving τ
    he he' hδ hδ' hζ htiltCut hζ' hτ ha hb hB hβ S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨n,hn,hwidth⟩ := exists_source_cube_bin_number e he
  refine ⟨C,hC,n,hn,?_⟩
  intro η Z hZ hZT T hT hdis length hl0 hl hpool W hWS hWB ψ
  obtain ⟨idx,grid,hbins⟩ := exists_source_cube_bins e (Z^τ) he hZT n hn hwidth S hS.prime η ψ
  refine ⟨idx,grid,?_,?_,?_⟩
  · intro u
    exact ⟨(hbins u).1,(hbins u).2.1,(hbins u).2.2.1,(hbins u).2.2.2.2.2.2.1⟩
  · intro u
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    exact ⟨ha0,ha1,hlo,hhi,hnext,hzero⟩
  · apply hbound η Z hZ T hT hdis length hl0 hl hpool W hWS hWB
      (fun u=>51/100+e*grid u) (fun _=>Z^τ) (fun u=>(3*idx u+1:ℕ)*Z^τ) idx ψ
    intro u hu
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    refine ⟨ha0,ha1,hZT,hBH,?_,hnext⟩
    have : 0≤Z^τ := Real.rpow_nonneg (by linarith) _
    linarith

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


/-! Physical extension: PrimeRows/CanonicalRayCube.lean. -/

theorem canonical_probe_exists_ray_cube_tilted (tilt : ℝ) (htilt : 0≤tilt) (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (htiltCut : 24*tilt<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∃n : ℕ,0<n ∧ ∀ᶠ Z : ℝ in atTop,∀η : Character,
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^((17/48:ℝ)-24*tilt)) (Z^((23/48:ℝ)+12*tilt)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-8*tilt-63/800+8*e)+Z^(-saving-8*tilt)) := by
  obtain ⟨C,hC,n,hn,hchoice⟩ := canonical_probe_exists_cube_tilted tilt htilt (ι:=RayQuotient.Characters M H)
    K e δ a b B ζ saving τ he he' hδ hδ' hζ htiltCut hζ' hτ ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,n,hn,?_⟩
  filter_upwards [source_cube_height_eventually τ hτ,
    ProbeRayCharacterFamily.large_supported_twists_eventually M (1/100) (by norm_num)]
    with Z hZ hlarge
  intro η T hT hdis length hl0 hl hpool W hWS hWB
  obtain ⟨idx,grid,hlabel,hbins,herror⟩ := hchoice η Z hZ.1 hZ.2 T hT hdis length hl0 hl hpool W hWS hWB
    (rayCubeFamily M H hH)
  refine ⟨idx,grid,hlabel,hbins,?_,herror⟩
  intro u hu hcal
  have hs := calibration_nonzero_supported S hmax hS.bad u.val hcal
  have hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1 :=
    hlarge u (mem_rowBand.mp hu).2.1 hs H hH
  refine ⟨hnp,?_,?_⟩
  · exact ProbeRayCharacterFamily.raw_twisted_conductor M H hH u
  · intro hnp'
    exact (ProbeRayCharacterFamily.source_nonprincipal_maximum_dominates S hS.prime η u
      (rayCubeFamily M H hH u) hnp' _).trans_lt (hbins u).2.2.2.2.1


#print axioms canonical_probe_exists_ray_cube_tilted
end SevenEighths.ProbeHighRowFamily
end
end OAI
