import «research.NativeSignedWidthSweep»
import «research.NativeAnchoredSlotMetric»
import RHLean.Analysis.AlpogeThin.NativeScalarSupplierPayment
import RHLean.Analysis.AlpogeThin.Formalism.ZeroFreeRegion.LogDerivRegion

/-! The centered thick response on the actual translated widths and its own MAIN.
The temporary common outside width below only compares thick coordinates. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ArithmeticFunction.vonMangoldt
open Filter

namespace RHLean.Analysis.AlpogeThin.SlotProjector

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

private theorem thick_congr (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T : Finset H) (u t : H) (a : ℝ) {v w : AlpogeNativeE0 × H → ℝ}
    (eq : ∀ ρ ∈ alpogeNativeThickPositiveSites T u, v ρ = w ρ) :
    alpogeNativeProjectionActualThick F T a u t v = alpogeNativeProjectionActualThick F T a u t w := by
  unfold alpogeNativeProjectionActualThick
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  simp only [alpogeNativeProjectionColourTerm, alpogeNativeProjectionThick_partner,
    eq _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)]

private theorem ask_antitone (I : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (f : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H) {v w : AlpogeNativeE0 × H → ℝ} (ord : ∀ ρ, v ρ ≤ w ρ) :
    (alpogeNativeFullKernelASK I f N a t w).re ≤ (alpogeNativeFullKernelASK I f N a t v).re := by
  simp only [alpogeNativeFullKernelASK_re_eq_weighted]
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
    mul_le_mul_of_nonneg_left (max_le_max (sub_le_sub_left (ord _) _) le_rfl) (alpogeNativeASKRealWeight_nonneg ..)

/-- Count each eligible thick colour on exactly its original translates before
bounding the complete prime-power mass. -/
private theorem translated_mass_le (I : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (f : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a l R : ℝ) (t : H) (T : Finset H) (w : H → AlpogeNativeE0 × H → ℝ) (hlR : l ≤ R) :
    (∑ u : H, WidthSweep.mass I f N a t (alpogeNativeFreezeThick T u l (w u))
      (alpogeNativeFreezeThick T u R (w u))) ≤ T.card*(2*(R-l)*nativePsi N) := by
  classical
  rw [WidthSweep.frozen_mass_translate]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  unfold nativePsi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  let W := alpogeNativeASKRealWeight I f n
  let E := Finset.univ.image (alpogeNativeProjectionE1 (H := H))
  have sub : E ⊆ Finset.univ.filter (fun g : AlpogeNativeE0 × H => ¬alpogeNativeInPhi g) := by
    intro g hg
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change ¬(1:ZMod 2)=0; decide⟩
  have gross : (∑ h : H, W (alpogeNativeProjectionE1 h)) ≤ 2*Λ n := calc
    _ = ∑ g ∈ E, W g := (Finset.sum_image (fun _ _ _ _ heq => congrArg Prod.snd heq)).symm
    _ ≤ _ := (Finset.sum_le_sum_of_subset_of_nonneg sub (fun g _ _ => alpogeNativeASKRealWeight_nonneg I f n g)).trans
      (alpogeNativeASKRealWeight_sum_le_two_lambda I f n)
  calc
    _ ≤ (∑ h : H, W (alpogeNativeProjectionE1 h))*(R-l) := mul_le_mul_of_nonneg_left (min_le_right _ _)
      (Finset.sum_nonneg fun h _ => alpogeNativeASKRealWeight_nonneg I f n _)
    _ ≤ (2*Λ n)*(R-l) := mul_le_mul_of_nonneg_right gross (sub_nonneg.mpr hlR)
    _ = _ := by ring

/-- The centered thick width displacement at one top and lift, summed over
all translates. Its bill has the same mask cardinality as the earned divisor. -/
theorem centered_thick_translate (I : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (f : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ) (T : Finset H) (t : H) (a l b R : ℝ)
    (w : H → AlpogeNativeE0 × H → ℝ) (ha : 0 < a) (hl : 0 < l) (hlb : l ≤ b) (hbR : b ≤ R)
    (hw : ∀ u ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u ρ ∈ Set.Icc l R) :
    let F := alpogeNativeFrobInertiaGPsi I f ell
    |∑ u : H, ((alpogeNativeProjectionActualThick F T a u t (w u)).re -
      (alpogeNativeFrozenThick F T b (a/b) u t).re)| ≤
      T.card*(2*(R-l)*nativePsi ⌈a/l⌉₊ + a/2*Real.log (R/l)) := by
  classical
  intro F
  let N := ⌈a/l⌉₊
  let v := fun (u : H) ρ => if ρ ∈ alpogeNativeThickPositiveSites T u then w u ρ else l
  let fr := fun (s : ℝ) (u : H) => alpogeNativeFreezeThick T u s (v u)
  let bill := fun u => WidthSweep.mass I f N a t (fr l u) (fr R u)
  let logBill := a*((1/((alpogeNativePhiSet H).card:ℝ))*((T.card:ℝ)*Real.log (R/l)))
  let X := fun v' => (alpogeNativeFullKernelASK I f N a t v').re
  let M := fun v' => (alpogeNativeMAIN ell a v').re
  have span (u : H) ρ : v u ρ ∈ Set.Icc l R := by
    by_cases hρ : ρ ∈ alpogeNativeThickPositiveSites T u
    · simpa only [v,ite_eq_left hρ] using hw u ρ hρ
    · simp only [v,ite_eq_right hρ,Set.mem_Icc]; exact ⟨le_rfl,hlb.trans hbR⟩
  have frlo (u : H) ρ : fr l u ρ = l := by
    simp only [fr, alpogeNativeFreezeThick, v]; split <;> rfl
  have sandwich (s : ℝ) (hs : s ∈ Set.Icc l R) (u : H) ρ :
      fr l u ρ ≤ fr s u ρ ∧ fr s u ρ ≤ fr R u ρ := by
    dsimp only [fr, alpogeNativeFreezeThick]; split <;> first | exact hs | exact ⟨le_rfl,le_rfl⟩
  have mid (u : H) ρ : fr l u ρ ≤ v u ρ ∧ v u ρ ≤ fr R u ρ := by
    dsimp only [fr,alpogeNativeFreezeThick]; split
    · exact span u ρ
    · exact ⟨le_rfl,le_rfl⟩
  have full (u : H) (v' : AlpogeNativeE0 × H → ℝ) (hv : ∀ ρ, l ≤ v' ρ) :
      X v'-M v' = (alpogeNativeProjectionActualThick F T a u t v').re +
        (alpogeNativeProjectionThinReturn F T a u t v').re := by
    change (alpogeNativeFullKernelASK I f N a t v' - alpogeNativeMAIN ell a v').re = _
    rw [alpogeNativeFullASK_sub_MAIN_eq_De I f ell N a t v' ha (fun ρ _ => hl.trans_le (hv ρ))
      (fun ρ _ => (div_le_div_of_nonneg_left ha.le hl (hv ρ)).trans (Nat.le_ceil _)),
      ← alpogeNativeProjectionFullSource_eq_nativeDe I f ell,alpogeNativeProjectionFull_eq_thick_add_thin _ T a u t v',
      Complex.add_re]
  have row (u : H) : |(alpogeNativeProjectionActualThick F T a u t (w u)).re -
      (alpogeNativeFrozenThick F T b (a/b) u t).re| ≤ bill u+logBill := by
    have mb := sandwich b ⟨hlb,hbR⟩ u
    have cover : ∀ ρ, 0 < fr l u ρ := fun ρ => (frlo u ρ).symm ▸ hl
    have price := WidthSweep.signed_row_eq I f ell N a t (fr l u) (fr R u)
      (fun ρ _ => ⟨cover ρ,(mid u ρ).1.trans (mid u ρ).2⟩)
    rw [show (∑ ρ ∈ alpogeNativePhiSet H, Real.log (fr R u ρ/fr l u ρ)) = _ from
      WidthSweep.frozen_log_sum T u l R (v u) (fun ρ _ => hl.trans_le (span u ρ).1)] at price
    have drop : X (fr l u)-X (fr R u) = bill u := WidthSweep.ask_drop_eq_mass I f N a t _ _
      (fun ρ _ => (mid u ρ).1.trans (mid u ρ).2)
    change X (fr R u)-M (fr R u) = (X (fr l u)-M (fr l u))+logBill-bill u at price
    have spread : M (fr l u)-M (fr R u) = logBill := by linarith only [price,drop]
    have bounds (v' : AlpogeNativeE0 × H → ℝ) (h : ∀ ρ, fr l u ρ ≤ v' ρ ∧ v' ρ ≤ fr R u ρ) :
        X (fr R u) ≤ X v' ∧ X v' ≤ X (fr l u) ∧ M (fr R u) ≤ M v' ∧ M v' ≤ M (fr l u) :=
      ⟨ask_antitone I f N a t (fun ρ => (h ρ).2), ask_antitone I f N a t (fun ρ => (h ρ).1),
       alpogeNativeMAIN_re_antitone_width ell a ha.le _ _ (fun ρ _ => (cover ρ).trans_le (h ρ).1) (fun ρ _ => (h ρ).2),
       alpogeNativeMAIN_re_antitone_width ell a ha.le _ _ (fun ρ _ => cover ρ) (fun ρ _ => (h ρ).1)⟩
    have V := bounds (v u) (mid u)
    have B := bounds (fr b u) mb
    have whole := full u (v u) (fun ρ => (span u ρ).1)
    have frozen := full u (fr b u) (fun ρ => (frlo u ρ) ▸ (mb ρ).1)
    rw [show fr b u = alpogeNativeFreezeThick T u b (v u) from rfl,
      alpogeNativeProjectionActualThick_freeze,alpogeNativeProjectionThinReturn_freeze] at frozen
    rw [thick_congr F T u t a (v := w u) (w := v u) (fun ρ hρ => by simp [v,hρ])]
    apply abs_le.mpr
    constructor <;> linarith only [V.1,V.2.1,V.2.2.1,V.2.2.2,B.1,B.2.1,B.2.2.1,B.2.2.2,whole,frozen,spread,drop]
  have W := translated_mass_le I f N a l R t T v (hlb.trans hbR)
  have card : (Fintype.card H:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ _ := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => row u)
    _ = (∑ u, bill u)+(Fintype.card H:ℝ)*logBill := by simp [Finset.sum_add_distrib]
    _ ≤ T.card*(2*(R-l)*nativePsi N)+(Fintype.card H:ℝ)*logBill := add_le_add_right W _
    _ = _ := by dsimp only [logBill]; rw [alpogeNativeProjectionPhi_card, Nat.cast_mul, Nat.cast_ofNat]; field_simp [card] <;> ring

end RHLean.Analysis.AlpogeThin.SlotProjector
