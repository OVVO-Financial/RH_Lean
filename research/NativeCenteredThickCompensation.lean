import «research.NativeSignedWidthSweep»
import «research.NativeAnchoredSlotMetric»
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
    _ ≤ T.card*(2*(R-l)*nativePsi N)+(Fintype.card H:ℝ)*logBill := add_le_add W le_rfl
    _ = _ := by dsimp only [logBill]; rw [alpogeNativeProjectionPhi_card, Nat.cast_mul, Nat.cast_ofNat]; field_simp [card]; ring

/-- The literal centered thick numerator with the original top, row and host weights. -/
def centeredThick (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ) (TT T : Finset H) {n : ℕ}
    (a : H → ℝ) (v : H → Fin n → AlpogeNativeE0 × H → ℝ) : ℝ :=
  (1/(Fintype.card (⊤ : AddSubgroup H):ℝ))*∑ u : (⊤ : AddSubgroup H), ∑ t ∈ TT, ∑ j : Fin n,
    (alpogeNativeProjectionActualThick F T (a t) u t (v u j)).re

/-- Normalized price of moving every centered thick reading to its common
width. Both terms have been averaged before the mask density cancels. -/
theorem centered_thick_width_price (I : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (f : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ) (TT T : Finset H) {n : ℕ} (a : H → ℝ) (A l b R : ℝ)
    (v : H → Fin n → AlpogeNativeE0 × H → ℝ) (htt : TT.Nonempty) (ht : T.Nonempty) (hn : 0 < n)
    (ha : ∀ t ∈ TT, 0 < a t ∧ a t ≤ A) (hl : 0 < l) (hlb : l ≤ b) (hbR : b ≤ R)
    (hv : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → v u j ρ ∈ Set.Icc l R) :
    let F := alpogeNativeFrobInertiaGPsi I f ell
    |centeredThick F TT T a v/alpogeNativeProjectionDivisor TT T n b - alpogeNativeProjectedSignal ⊤ F TT a b| ≤
      (4*(R-l)*(Real.log 4+2)*(A/l+1)+A*Real.log (R/l))/b := by
  classical
  intro F
  let Q := alpogeNativeProjectionDivisor TT T n b
  let J := (⊤ : AddSubgroup H)
  let B := 2*(R-l)*(Real.log 4+2)*(A/l+1)+A/2*Real.log (R/l)
  let d := fun (u t : H) (j : Fin n) => (alpogeNativeProjectionActualThick F T (a t) u t (v u j)).re -
    (alpogeNativeFrozenThick F T b (a t/b) u t).re
  have hQ : 0 < Q := alpogeNativeProjectionDivisor_pos TT T htt ht n hn b (hl.trans_le hlb)
  have hc : 0 ≤ Real.log 4+2 := by positivity
  have hR := sub_nonneg.mpr (hlb.trans hbR)
  have hlog := Real.log_nonneg ((one_le_div hl).2 (hlb.trans hbR))
  have per (t) (h : t ∈ TT) (j : Fin n) : |∑ u, d u t j| ≤ T.card*B := by
    apply (centered_thick_translate I f ell T t (a t) l b R (fun u => v u j) (ha t h).1 hl hlb hbR
      (fun u ρ => hv u j ρ)).trans
    have ps : nativePsi ⌈a t/l⌉₊ ≤ (Real.log 4+2)*(A/l+1) := (nativePsi_le_const_mul _).trans <|
      mul_le_mul_of_nonneg_left ((Nat.ceil_lt_add_one (div_nonneg (ha t h).1.le hl.le)).le.trans
        (add_le_add (div_le_div_of_nonneg_right (ha t h).2 hl.le) le_rfl)) hc
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    dsimp only [B]
    have p := mul_le_mul_of_nonneg_left ps (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hR)
    linarith only [p,mul_le_mul_of_nonneg_right (ha t h).2 hlog]
  have total : |∑ t ∈ TT, ∑ j : Fin n, ∑ u : H, d u t j| ≤ (TT.card:ℝ)*(n*(T.card*B)) := calc
    _ ≤ ∑ t ∈ TT, ∑ j : Fin n, T.card*B := (Finset.abs_sum_le_sum_abs _ _).trans <|
      Finset.sum_le_sum fun t h => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => per t h j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  let eqv : J ≃ H := AddSubgroup.topEquiv.toEquiv
  have identity : centeredThick F TT T a v - Q*alpogeNativeProjectedSignal J F TT a b =
      (1/(Fintype.card H:ℝ))*∑ t ∈ TT, ∑ j : Fin n, ∑ u : H, d u t j := by
    have join : (∑ u : J, ∑ t ∈ TT, ∑ j : Fin n, d (u:H) t j) =
        (∑ u : J, ∑ t ∈ TT, ∑ j : Fin n, (alpogeNativeProjectionActualThick F T (a t) u t (v u j)).re) -
          ∑ u : J, ∑ t ∈ TT, ∑ _j : Fin n, (alpogeNativeFrozenThick F T b (a t/b) u t).re := by
      simp only [d,Finset.sum_sub_distrib]
    have swap : (∑ u : J, ∑ t ∈ TT, ∑ j : Fin n, d (u:H) t j) = ∑ t ∈ TT, ∑ j : Fin n, ∑ u : H, d u t j := calc
      _ = ∑ u : H, ∑ t ∈ TT, ∑ j : Fin n, d u t j := eqv.sum_comp (fun u => ∑ t ∈ TT, ∑ j : Fin n, d u t j)
      _ = _ := by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun t _ => Finset.sum_comm
    rw [← swap,← Fintype.card_congr eqv,join,mul_sub,
      alpogeNativeFrozenThick_average_eq_signal J F TT T htt (fun _ _ => trivial) n a b]
    all_goals rfl
  have hH : (Fintype.card H:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hb := hl.trans_le hlb
  change |centeredThick F TT T a v/Q - _| ≤ _
  rw [show centeredThick F TT T a v/Q-alpogeNativeProjectedSignal J F TT a b =
    (centeredThick F TT T a v-Q*alpogeNativeProjectedSignal J F TT a b)/Q by field_simp, identity,
    abs_div,abs_of_pos hQ,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(Fintype.card H:ℝ))]
  apply (div_le_iff₀ hQ).2
  calc
    _ ≤ (1/(Fintype.card H:ℝ))*((TT.card:ℝ)*(n*(T.card*B))) := mul_le_mul_of_nonneg_left total (by positivity)
    _ = _ := by dsimp only [B,Q,alpogeNativeProjectionDivisor,alpogeNativeProjectionDensity]; field_simp [hH,hb.ne']; all_goals ring

private theorem grid_collar (w b x η : ℝ) (hb : 0 < b) (hη : 0 < η) (hη2 : η ≤ 1/2)
    (hw : w ∈ Set.Icc b (b*(1+1/x))) :
    alpogeNativeLowerLogWidth η w ∈ Set.Icc (b*(1-η)) (b*(1+1/x)) := by
  have hw0 := hb.trans_le hw.1
  have hi := (le_div_iff₀ hη).mp (Int.floor_le (Real.log w/η))
  have lo := (div_lt_iff₀ hη).mp (Int.lt_floor_add_one (Real.log w/η))
  have e := Real.add_one_le_exp (-η)
  constructor
  · calc
      _ ≤ w*(1-η) := mul_le_mul_of_nonneg_right hw.1 (by linarith)
      _ ≤ w*Real.exp (-η) := mul_le_mul_of_nonneg_left (by linarith only [e]) hw0.le
      _ = Real.exp (Real.log w-η) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hw0]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [lo])
  · exact ((Real.exp_le_exp.mpr hi).trans (Real.exp_log hw0).le).trans hw.2

private theorem collar_price (x b η : ℝ) (hx : 4 ≤ x) (hb : 0 < b) (hη : 0 < η) (grid : η ≤ 1/Real.sqrt x) :
    let A := (x+1)*b
    let l := b*(1-η)
    let R := b*(1+1/x)
    (4*(R-l)*(Real.log 4+2)*(A/l+1)+A*Real.log (R/l))/b ≤ 32*(Real.log 4+3)*Real.sqrt x := by
  intro A l R
  have hx0 : 0 < x := by linarith
  have hr : 2 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).2 (by linarith)
  have hr0 : 0 < Real.sqrt x := by linarith
  have hhalf : η ≤ 1/2 := grid.trans ((div_le_div_iff₀ hr0 (by norm_num : (0:ℝ)<2)).2 (by linarith))
  have hl : 0 < l := mul_pos hb (by linarith)
  have hl2 : b ≤ 2*l := by dsimp [l]; nlinarith only [mul_le_mul_of_nonneg_left hhalf hb.le]
  let s := η+1/x
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hR : R-l = b*s := by dsimp [R,l,s]; ring
  have hRl := sub_nonneg.mp (hR.symm ▸ mul_nonneg hb.le hs)
  have logprice : Real.log (R/l) ≤ 2*s := calc
    _ ≤ R/l-1 := Real.log_le_sub_one_of_pos (div_pos (hl.trans_le hRl) hl)
    _ ≤ _ := by apply (sub_le_iff_le_add).2; apply (div_le_iff₀ hl).2; nlinarith only [hR,mul_le_mul_of_nonneg_right hl2 hs]
  have size : A/l+1 ≤ 3*x := by
    have h : A/l ≤ 2*(x+1) := (div_le_iff₀ hl).2 (by dsimp [A]; nlinarith only [mul_le_mul_of_nonneg_left hl2 (by linarith : 0 ≤ x+1)])
    linarith
  have cs : 0 ≤ Real.log 4+2 := by positivity
  have hL : 0 ≤ Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  have t := (Real.sqrt_le_self_iff.mpr (Or.inr (by linarith : 1 ≤ x)))
  have sm : s ≤ 2/Real.sqrt x := calc
    _ ≤ 1/Real.sqrt x + 1/Real.sqrt x := add_le_add grid (one_div_le_one_div_of_le hr0 t)
    _ = _ := by ring
  have xs : x*s ≤ 2*Real.sqrt x := calc
    _ ≤ x*(2/Real.sqrt x) := mul_le_mul_of_nonneg_left sm hx0.le
    _ = _ := by field_simp [hr0.ne']; nlinarith only [Real.mul_self_sqrt hx0.le]
  have logp := mul_le_mul_of_nonneg_left logprice (by dsimp [A]; positivity : 0 ≤ A)
  have p := mul_le_mul_of_nonneg_left size (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (sub_nonneg.mpr hRl)) cs)
  rw [hR] at p ⊢
  apply (div_le_iff₀ hb).2
  have t1 := mul_le_mul_of_nonneg_left xs (mul_nonneg (by norm_num : (0:ℝ) ≤ 12) cs)
  have t2 := mul_le_mul_of_nonneg_right (show 2*(x+1) ≤ 3*x by linarith) hs
  dsimp only [A] at logp p ⊢
  nlinarith only [p,logp,mul_le_mul_of_nonneg_right t1 hb.le,mul_le_mul_of_nonneg_left t2 hb.le,
    mul_le_mul_of_nonneg_left xs hb.le, mul_nonneg hb.le (mul_nonneg hr0.le hL), mul_nonneg hb.le hr0.le]

/-- The complete rounded centered thick source differs from the original
principal arithmetic value by a root-scale price on the selected pair. -/
theorem centered_thick_principal (e q d n : ℕ) [Fact q.Prime] [Fact d.Prime] {ε Y Z x : ℝ}
    (pair : UpperTheory.Top.PairGood 1 ε Y Z q d) (he : 0 ≤ ε) (hx : 4 ≤ x)
    (TT T : Finset (AlpogeNativeDyadicH e)) (a : AlpogeNativeDyadicH e → ℝ) (b η : ℝ)
    (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (htt : TT.Nonempty) (ht : T.Nonempty) (hn : 0 < n) (hb : 0 < b) (hη : 0 < η) (grid : η ≤ 1/Real.sqrt x)
    (ha : ∀ t ∈ TT, a t ∈ Set.Icc (x*b) ((x+1)*b)) (win : ∀ t ∈ TT, a t/b ∈ Set.Icc Y Z)
    (hw : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u j ρ ∈ Set.Icc b (b*(1+1/x))) :
    let D := alpogeNativeHostData e q d
    let F := alpogeNativeFrobInertiaGPsi D.inertia D.frob (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d))
    let v := fun u j ρ => alpogeNativeLowerLogWidth η (w u j ρ)
    |centeredThick F TT T a v/alpogeNativeProjectionDivisor TT T n b - alpogeNativeGzArithmetic x| ≤
      32*(Real.log 4+3)*Real.sqrt x + (3*(x+1)^((1:ℝ)/2+ε/2)+alpogeNativeMoveConstant) := by
  classical
  intro D F v
  let l := b*(1-η)
  let R := b*(1+1/x)
  let A := (x+1)*b
  have hx0 : 0 < x := by linarith
  have hr : 2 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).2 (by linarith)
  have hhalf : η ≤ 1/2 := grid.trans ((div_le_div_iff₀ (Real.sqrt_pos.2 hx0) (by norm_num : (0:ℝ)<2)).2 (by linarith))
  have hl : 0 < l := mul_pos hb (by linarith)
  have hlb : l ≤ b := by dsimp [l]; nlinarith only [mul_nonneg hb.le hη.le]
  have hbR : b ≤ R := le_mul_of_one_le_right hb.le (by linarith only [one_div_pos.mpr hx0])
  have width := (centered_thick_width_price D.inertia D.frob (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d))
    TT T a A l b R v htt ht hn (fun t h => ⟨(mul_pos hx0 hb).trans_le (ha t h).1,(ha t h).2⟩)
    hl hlb hbR (fun u j ρ hρ => grid_collar _ b x η hb hη hhalf (hw u j ρ hρ))).trans (collar_price x b η hx hb hη grid)
  let S := alpogeNativeFrobInertiaGsig D.inertia D.frob (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d))
    (alpogeNativeChC (AlpogeNativeDyadicH e)) (alpogeNativePsC (AlpogeNativeDyadicH e))
  let γ := (1:ℝ)/2+ε/2
  let E := 3*(x+1)^γ+alpogeNativeMoveConstant
  have point t (h : t ∈ TT) : |(S (a t/b)).re-alpogeNativeGzArithmetic x| ≤ E := by
    let y := a t/b
    have lo : x ≤ y := (le_div_iff₀ hb).2 (ha t h).1
    have hi : y ≤ x+1 := (div_le_iff₀ hb).2 (ha t h).2
    have twist := (Complex.abs_re_le_norm _).trans (nativePairGood_dyadicGsig_sub_Gz_norm_le e q d pair
      y (win t h).1 (win t h).2)
    change |(S y).re-alpogeNativeGzArithmetic y| ≤ 3*y^γ at twist
    have mov := alpogeNativeGzArithmetic_sub_abs_le_of_le y x (by linarith) lo hi
    have pow := Real.rpow_le_rpow (hx0.le.trans lo) hi (show 0 ≤ γ by dsimp [γ]; linarith)
    calc
      _ ≤ |(S y).re-alpogeNativeGzArithmetic y| + |alpogeNativeGzArithmetic y-alpogeNativeGzArithmetic x| := abs_sub_le ..
      _ ≤ E := by dsimp only [E]; linarith only [twist,mov,pow,
        mul_le_mul_of_nonneg_left (show y-x ≤ 1 by linarith only [hi]) alpogeNativeMoveConstant_nonneg]
  have hc : (0:ℝ) < TT.card := by exact_mod_cast htt.card_pos
  have sig : |alpogeNativeProjectedSignal ⊤ F TT a b-alpogeNativeGzArithmetic x| ≤ E := by
    rw [alpogeNativeProjectedSignal_top_eq_Gsig]
    change |1/(TT.card:ℝ)*(∑ t ∈ TT, (S (a t/b)).re) - _| ≤ E
    have id : 1/(TT.card:ℝ)*(∑ t ∈ TT, ((S (a t/b)).re-alpogeNativeGzArithmetic x)) =
        1/(TT.card:ℝ)*(∑ t ∈ TT, (S (a t/b)).re)-alpogeNativeGzArithmetic x := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; field_simp [hc.ne']
    rw [← id, abs_mul, abs_of_pos (one_div_pos.mpr hc)]
    calc
      _ ≤ 1/(TT.card:ℝ)*(∑ _t ∈ TT, E) := mul_le_mul_of_nonneg_left
        ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum point)) (by positivity)
      _ = E := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp [hc.ne']
  exact (abs_sub_le _ (alpogeNativeProjectedSignal ⊤ F TT a b) _).trans (add_le_add width sig)

/-- Negative complementary log-volume in the independently measured counting metric. -/
def highComplement (e q d n : ℕ) [Fact q.Prime] [Fact d.Prime] (TT T : Finset (AlpogeNativeDyadicH e))
    (a : AlpogeNativeDyadicH e → ℝ) (x : ℝ)
    (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ) : ℝ :=
  let c := ⌊Real.sqrt x⌋₊
  let P := highThickPrimes e q d x
  let g := fun p => ((alpogeNativeHostData e q d).frob p).2
  let V := occupied TT P g
  let p := primeAt TT P g
  let r := fun s : ↥V => (partnerPrimes TT P g s.val).card-1
  let D := fun (s : ↥V) (i : Fin (r s+1)) => p s i ^ (⌊(c:ℝ)*x⌋₊/p s i-c)
  let S := fun (s : ↥V) (j : ↥(siteRows T n s.val)) => bands (fun i => a (s.val-g (p s i))/(p s i:ℝ))
    (w j.val.1 j.val.2 ((0,1),s.val))
  4*(∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), complementaryLog (S s j) (D s))/((c:ℝ)*((T.card*n:ℕ):ℝ)*TT.card)

private theorem centered_root_price (x ε : ℝ) (hx : 1 ≤ x) (he : 0 ≤ ε) (he1 : ε ≤ 1) :
    32*(Real.log 4+3)*Real.sqrt x + (3*(x+1)^((1:ℝ)/2+ε/2)+alpogeNativeMoveConstant) +
      (20*Real.log 4*Real.sqrt x+(8/ε)*x^((1:ℝ)/2+9*ε/8)) ≤
      (53*Real.log 4+106+8/ε)*x^((1:ℝ)/2+9*ε/8) := by
  let α := (1:ℝ)/2+ε/2
  let β := (1:ℝ)/2+9*ε/8
  have hx0 := zero_le_one.trans hx
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have root : Real.sqrt x ≤ x^β := by
    rw [Real.sqrt_eq_rpow]; apply Real.rpow_le_rpow_of_exponent_le hx; dsimp [β]; linarith
  have power : (x+1)^α ≤ 2*x^β := calc
    _ ≤ (2*x)^α := Real.rpow_le_rpow (by linarith) (by linarith) hα
    _ = (2:ℝ)^α*x^α := Real.mul_rpow (by norm_num) hx0
    _ ≤ 2*x^α := mul_le_mul_of_nonneg_right (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (show α ≤ 1 by dsimp [α]; linarith)) (Real.rpow_nonneg hx0 _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (show α ≤ β by dsimp [α,β]; linarith)) (by norm_num)
  have unit : 1 ≤ x^β := Real.one_le_rpow hx hβ
  change 32*(Real.log 4+3)*Real.sqrt x + (3*(x+1)^α+(Real.log 4+4)) +
    (20*Real.log 4*Real.sqrt x+(8/ε)*x^β) ≤ (53*Real.log 4+106+8/ε)*x^β
  linarith only [power,mul_le_mul_of_nonneg_left root (by positivity : 0 ≤ 32*(Real.log 4+3)),
    mul_le_mul_of_nonneg_left root (by positivity : 0 ≤ 20*Real.log 4),
    mul_le_mul_of_nonneg_left unit (by positivity : 0 ≤ Real.log 4+4)]

/-- Two-sided identification of the centered thick deficit after subtracting
the actual high reads and measured negative complement. A classical bound
on the surviving principal component gives an unconditional sublinear price. -/
theorem centered_thick_measured (ε : ℝ) (he : 0 < ε) (he1 : ε ≤ 1) :
    ∃ κ K : ℝ, 0 < κ ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop, ∀ (e q d n : ℕ) [Fact q.Prime] [Fact d.Prime]
      {Y Z : ℝ} (_pair : UpperTheory.Top.PairGood 1 ε Y Z q d) (TT T : Finset (AlpogeNativeDyadicH e))
      (a : AlpogeNativeDyadicH e → ℝ) (η : ℝ)
      (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
      let b := Real.exp (x^ε)
      let D := alpogeNativeHostData e q d
      let F := alpogeNativeFrobInertiaGPsi D.inertia D.frob (alpogeNativeCanonicalHostEll (alpogeNativeRecMap e q d))
      let v := fun u j ρ => alpogeNativeLowerLogWidth η (w u j ρ)
      let Hc := centeredThick F TT T a v/alpogeNativeProjectionDivisor TT T n b
      let high := roundedHighASK e q d n TT T a b x η w
      let C := highComplement e q d n TT T a x w
      let E := 32*(Real.log 4+3)*Real.sqrt x + (3*(x+1)^((1:ℝ)/2+ε/2)+alpogeNativeMoveConstant) +
        (20*Real.log 4*Real.sqrt x+(8/ε)*x^((1:ℝ)/2+9*ε/8))
      TT.Nonempty → T.Nonempty → 0 < n → 0 < η → η ≤ 1/Real.sqrt x →
      x^(-(ε/8))*(Fintype.card (AlpogeNativeDyadicH e):ℝ)/2 ≤ TT.card →
      (∀ t ∈ TT, a t ∈ Set.Icc (x*b) ((x+1)*b)) → (∀ t ∈ TT, a t/b ∈ Set.Icc Y Z) →
      (∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T u → w u j ρ ∈ Set.Icc b (b*(1+1/x))) →
      |(Hc-high-C)-alpogeNativeGzArithmetic x| ≤ E ∧
      Hc-high ≤ C+K*x*Real.exp (-κ*Real.sqrt (Real.log x))+(53*Real.log 4+106+8/ε)*x^((1:ℝ)/2+9*ε/8) := by
  classical
  obtain ⟨κ,K,hκ,hK⟩ := Formalism.ZF.gzPNT
  refine ⟨κ,max 1 K,hκ,zero_lt_one.trans_le (le_max_left _ _),?_⟩
  filter_upwards [highThick_frame ε he he1,eventually_ge_atTop (10:ℝ)] with x frame hx
  intro e q d n _ _ Y Z pair TT T a η w b D F v Hc high C E htt ht hn hη grid density ha win hw
  have principal := centered_thick_principal e q d n pair he.le (by linarith : 4 ≤ x) TT T a b η w htt ht hn
    (Real.exp_pos _) hη grid ha win hw
  obtain ⟨hS,_,_,_,_,_,_,pay⟩ := frame e q d n 1 TT T a w Nat.zero_lt_one ha hw
  let c := ⌊Real.sqrt x⌋₊
  let P := highThickPrimes e q d x
  let g := fun l => ((alpogeNativeHostData e q d).frob l).2
  let V := occupied TT P g
  let p := primeAt TT P g
  let r := fun s : ↥V => (partnerPrimes TT P g s.val).card-1
  let pow := fun (s : ↥V) (i : Fin (r s+1)) => p s i^(⌊(c:ℝ)*x⌋₊/p s i-c)
  let S := fun (s : ↥V) (j : ↥(siteRows T n s.val)) => bands (fun i => a (s.val-g (p s i))/(p s i:ℝ))
    (w j.val.1 j.val.2 ((0,1),s.val))
  have pos (s : ↥V) (i : Fin (r s+1)) : 0 < pow s i := pow_pos (highThick_primeAt e q d x TT s i).1.pos _
  have opp : C = -(4*(∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), logVolume (S s j) (pow s))/
      ((c:ℝ)*((T.card*n:ℕ):ℝ)*TT.card)) := by
    change 4*(∑ s : ↥V, ∑ j : ↥(siteRows T n s.val), complementaryLog (S s j) (pow s))/_ = _
    simp_rw [fun s j => complementaryLog_eq (S s j) (pow s) (hS s j) (pos s),Finset.sum_neg_distrib]
    ring
  have hp : |high+C| ≤ 20*Real.log 4*Real.sqrt x+(8/ε)*x^((1:ℝ)/2+9*ε/8) := by
    rw [opp, ← sub_eq_add_neg]; exact pay η hη grid htt ht hn density
  have gap : |(Hc-high-C)-alpogeNativeGzArithmetic x| ≤ E := by
    rw [show (Hc-high-C)-alpogeNativeGzArithmetic x = (Hc-alpogeNativeGzArithmetic x)-(high+C) by ring]
    exact (abs_sub _ _).trans (add_le_add principal hp)
  refine ⟨gap,?_⟩
  have classicalBound := hK x (by linarith)
  change |AlpogeNativeBoundHandoff.statementOCGz x| ≤ _ at classicalBound
  rw [AlpogeNativeBoundHandoff.statementOCGz_eq_native] at classicalBound
  have positive := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) K) (by linarith : 0 ≤ x))
    (Real.exp_pos (-κ*Real.sqrt (Real.log x))).le
  have paid : E ≤ (53*Real.log 4+106+8/ε)*x^((1:ℝ)/2+9*ε/8) := centered_root_price x ε (by linarith) he.le he1
  linarith only [(abs_le.mp gap).2, le_abs_self (alpogeNativeGzArithmetic x),classicalBound,positive,paid]

/-- At the original finite cutoff the centered thin term has its own MAIN.
The bound is simultaneous in every cutoff. Host size and conductor are
supplied at this anchor by the original PageN and the selected pair. -/
theorem original_cutoff_centered_thick (ε : ℝ) (he : 0 < ε) (h52 : ε < 1/52) :
    ∀ᶠ x : ℝ in atTop, ∀ (e q d n N : ℕ) [Fact q.Prime] [Fact d.Prime] {Y Z : ℝ}
      (_pair : UpperTheory.Top.PairGood 1 ε Y Z q d), 1 ≤ Y → Y ≤ x → UpperTheory.Top.PageN ε x e →
      ∀ (TT T : Finset (AlpogeNativeDyadicH e)) (a : AlpogeNativeDyadicH e → ℝ) (η : ℝ)
      (w : AlpogeNativeDyadicH e → Fin n → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
      let b := Real.exp (x^ε)
      let D := alpogeNativeHostData e q d
      let ell := alpogeNativeCanonicalHostEll (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
      let F := alpogeNativeFrobInertiaGPsi D.inertia D.frob ell
      let v := fun u j ρ => alpogeNativeLowerLogWidth η (w u j ρ)
      let Q := alpogeNativeProjectionDivisor TT T n b
      TT.Nonempty → T.Nonempty → 0 < n → 0 < η → x^(-ε) ≤ alpogeNativeProjectionDensity T →
      (∀ t ∈ TT, a t ∈ Set.Icc (x*b) ((x+1)*b)) →
      (∀ u j t, t ∈ TT → ∀ g ∈ (Finset.univ.filter (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
          ¬alpogeNativeInPhi g)) \ alpogeNativeProjectionThickColours T u t,
        0 < w u j (alpogeNativePartner t g) ∧ Real.exp (x^(ε/3))/3 ≤ a t/w u j (alpogeNativePartner t g)) →
      alpogeNativePhysicalSubgroupTopExcess ⊤ D.inertia D.frob ell N TT a v/Q ≤
        centeredThick F TT T a v/Q+2*x^(ε-1) := by
  classical
  obtain ⟨x₁,source⟩ := nativeLedger_pairGood_roundedASK_le_thick ε he
  obtain ⟨x₂,host⟩ := nativePageN_host_size_eventually ε h52
  obtain ⟨x₃,cond⟩ := nativePageN_conductor_eventually ε he h52
  filter_upwards [eventually_ge_atTop x₁,eventually_ge_atTop x₂,eventually_ge_atTop x₃,
    nativeDyadicCostWindows_eventually ε 3 he,eventually_ge_atTop (2:ℝ)] with x hx₁ hx₂ hx₃ cost hx
  intro e q d n N _ _ Y Z pair hY hy page TT T a η w b D ell F v Q htt ht hn hη density ha thin
  let J := (⊤ : AddSubgroup (AlpogeNativeDyadicH e))
  let m := (Fintype.card (AlpogeNativeDyadicH e):ℝ)
  let θ := Real.exp (-(x^(ε/8)))
  let δ := alpogeNativeProjectionDensity T
  have hθ : 0 ≤ θ := (Real.exp_pos _).le
  have hm : 0 < m := by
    change 0 < (Fintype.card (AlpogeNativeDyadicH e):ℝ)
    exact_mod_cast Fintype.card_pos
  have hx0 : 0 < x := by linarith
  have hb : 0 < b := Real.exp_pos _
  have hQ : 0 < Q := alpogeNativeProjectionDivisor_pos TT T htt ht n hn b hb
  have hδ : 0 < δ := (Real.rpow_pos_of_pos hx0 _).trans_le density
  have poly : (2:ℝ)^e ≤ x^(3:ℝ) := by simpa only [alpogeNativeDyadicH_card,Nat.cast_pow,Nat.cast_ofNat] using host x hx₂ e page
  have cheap := (cost e poly b 0 le_rfl le_rfl (by positivity)).1
  have mEq : m = (2:ℝ)^e := by simp only [m,alpogeNativeDyadicH_card,Nat.cast_pow,Nat.cast_ofNat]
  change 4*(2:ℝ)^e*(x+1)*θ ≤ 1/x at cheap
  rw [← mEq] at cheap
  have row (u t : AlpogeNativeDyadicH e) (h : t ∈ TT) j :
      (alpogeNativeFullKernelASK D.inertia D.frob N (a t) t (v u j)-alpogeNativeMAIN ell (a t) (v u j)).re ≤
        (alpogeNativeProjectionActualThick F T (a t) u t (v u j)).re+b/x := by
    have ha0 := (mul_pos hx0 hb).trans_le (ha t h).1
    have s := source x hx₁ Y Z q d e N pair T u t (a t) η (w u j) ha0 hη
      (cond x hx₃ Y q d e hY hy pair.pair page) (thin u j t h)
    rw [alpogeNativeProjectionPhi_card,Nat.cast_mul,Nat.cast_ofNat] at s
    apply s.trans (add_le_add le_rfl _)
    change (2*m-(T.card:ℝ))/(2*m)*(4*m*a t*θ) ≤ b/x
    calc
      _ ≤ 4*m*a t*θ := mul_le_of_le_one_left (by positivity) ((div_le_one (by positivity)).2 (sub_le_self _ (by positivity)))
      _ ≤ 4*m*((x+1)*b)*θ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha t h).2 (by positivity)) hθ
      _ = b*(4*m*(x+1)*θ) := by ring
      _ ≤ b/x := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left cheap hb.le
  have hJ : (Fintype.card J:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have cap : alpogeNativePhysicalSubgroupTopExcess (⊤ : AddSubgroup (AlpogeNativeDyadicH e)) D.inertia D.frob ell N TT a v ≤
      centeredThick F TT T a v+(TT.card:ℝ)*n*(b/x) := by
    unfold alpogeNativePhysicalSubgroupTopExcess centeredThick
    calc
      _ ≤ (1/(Fintype.card (⊤ : AddSubgroup (AlpogeNativeDyadicH e)):ℝ))*
          ∑ u : (⊤ : AddSubgroup (AlpogeNativeDyadicH e)), ∑ t ∈ TT, ∑ j : Fin n,
            ((alpogeNativeProjectionActualThick F T (a t) u t (v u j)).re+b/x) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun t h =>
          Finset.sum_le_sum fun j _ => row (u:AlpogeNativeDyadicH e) t h j) (by positivity)
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_add]
        refine congrArg₂ (· + ·) ?_ ?_
        · first | rfl | congr!
        · field_simp [hJ]; all_goals ring
  have norm : ((TT.card:ℝ)*n*(b/x))/Q = 2/(δ*x) := by
    dsimp only [Q,δ,alpogeNativeProjectionDivisor]; field_simp [hb.ne',hx0.ne',hδ.ne',
      (show ((TT.card:ℝ)) ≠ 0 by exact_mod_cast htt.card_pos.ne'), (show (n:ℝ) ≠ 0 by exact_mod_cast hn.ne')]; all_goals ring
  have inv : 1/δ ≤ x^ε := by
    have orig : x^(-ε) ≤ δ := density
    rw [Real.rpow_neg hx0.le, ← one_div] at orig
    exact (one_div_le_one_div_of_le (one_div_pos.mpr (Real.rpow_pos_of_pos hx0 ε)) orig).trans_eq (by rw [one_div_one_div])
  have pay : 2/(δ*x) ≤ 2*x^(ε-1) := calc
    _ = (2/x)*(1/δ) := by ring
    _ ≤ (2/x)*x^ε := mul_le_mul_of_nonneg_left inv (by positivity)
    _ = _ := by rw [Real.rpow_sub hx0,Real.rpow_one]; ring
  calc
    _ ≤ (centeredThick F TT T a v+(TT.card:ℝ)*n*(b/x))/Q := div_le_div_of_nonneg_right cap hQ.le
    _ ≤ _ := by rw [add_div,norm]; exact add_le_add le_rfl pay

end RHLean.Analysis.AlpogeThin.SlotProjector
