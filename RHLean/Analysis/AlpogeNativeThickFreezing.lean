import Mathlib
import RHLean.Analysis.AlpogeNativeSubgroupProjection
import RHLean.Analysis.AlpogeNativeSignedWidthPayment
import RHLean.Analysis.AlpogeSquareClockSharpCollar
import RHLean.Analysis.NativePNTChebyshev

/-!
# Complete-character thick freezing with a paid, host-independent cost

Lower only the thick widths to b, leaving every complementary width intact.
After character inversion the physical weights are nonnegative and their
entire non-Phi mass at each prime power is at most two.  Consequently the
one-sided freezing charge is at most 2*h*psi(floor(a/b)), independently of
the number of host characters.  The logarithmic MAIN has the favorable sign.

No L'/L bound, thin-source bound, or root-size complete-source estimate is
assumed. The later subgroup application keeps the original signed thin
return, and derives its original normalizing divisor from the companion
projection theorem.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators Classical

namespace RHLean.Analysis

section

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The mass-two budget holds for the actual Lambda-weighted kernel at
every integer. Non-prime-powers contribute exactly zero. -/
theorem alpogeNativeASKRealWeight_sum_le_two_lambda
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H) (n : ℕ) :
    (∑ g ∈ Finset.univ.filter
      (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
      alpogeNativeASKRealWeight inertia frob n g) ≤ 2 * Λ n := by
  classical
  by_cases hn : Λ n = 0
  · simp [alpogeNativeASKRealWeight, hn]
  · rw [ArithmeticFunction.vonMangoldt_ne_zero_iff,
      isPrimePow_nat_iff] at hn
    obtain ⟨p, k, hp, hk, rfl⟩ := hn
    have hreal : ∀ g : AlpogeNativeE0 × H,
        (alpogeNativeColourKernel inertia frob (p ^ k) g).re =
          if g - k • frob p ∈ inertia p then
            2 / ((alpogeSquareInertiaCarrier (inertia p)).card : ℝ) else 0 := by
      intro g
      rw [alpogeNativeColourKernel_primePower inertia frob p k hp hk g]
      split_ifs
      · have heq :
            (2 / (((Finset.univ.filter
              (fun u : AlpogeNativeE0 × H => u ∈ inertia p)).card : ℕ) : ℂ)) =
            (((2 : ℝ) / ((alpogeSquareInertiaCarrier (inertia p)).card : ℝ)) : ℂ) := by
          unfold alpogeSquareInertiaCarrier
          push_cast
          rfl
        rw [heq, Complex.ofReal_re]
      · simp
    have hmass :
        (∑ g ∈ Finset.univ.filter
          (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
          (alpogeNativeColourKernel inertia frob (p ^ k) g).re) =
          alpogeSquareColourCosetMass (inertia p) (k • frob p) := by
      simp_rw [hreal]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      unfold alpogeSquareColourCosetMass alpogeSquareColourSupport
      ring
    unfold alpogeNativeASKRealWeight
    rw [← Finset.mul_sum, hmass]
    have h := mul_le_mul_of_nonneg_left
      (alpogeSquareColourCosetMass_nonneg_le_two (inertia p) (k • frob p)).2
      (show 0 ≤ Λ (p ^ k) from ArithmeticFunction.vonMangoldt_nonneg)
    simpa [mul_comm] using h

omit [Fintype H] [DecidableEq H] in
/-- Every original non-Phi colour maps to a positive site. -/
theorem alpogeNativeFreezing_partner_inPhi (t : H) (g : AlpogeNativeE0 × H)
    (hg : ¬ alpogeNativeInPhi g) :
    alpogeNativeInPhi (alpogeNativePartner t g) := by
  have hbit : g.1.1 = (1 : ZMod 2) := by
    have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hcases g.1.1 with hz | hz
    · exact False.elim (hg hz)
    · exact hz
  change (1 : ZMod 2) + g.1.1 + 0 = 0
  simpa only [hbit] using (show (1 : ZMod 2) + 1 + 0 = 0 by decide)

/-- A lower-to-upper width change costs at most its displacement, and
vanishes above the original lower-width cutoff. -/
theorem alpogeNativeFreezing_cut_difference_le
    (a b h u v : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hn : 1 ≤ n) (huv : u ≤ v) (hd : v - u ≤ h)
    (hactive : u = v ∨ b ≤ u) :
    alpogeASKPos (a / (n : ℝ)) u - alpogeASKPos (a / (n : ℝ)) v ≤
      if n ≤ ⌊a / b⌋₊ then h else 0 := by
  have hdiff : alpogeASKPos (a / (n : ℝ)) u -
      alpogeASKPos (a / (n : ℝ)) v ≤ v - u := by
    unfold alpogeASKPos
    apply (sub_le_iff_le_add).2
    apply max_le
    · linarith [le_max_left (a / (n : ℝ) - v) 0]
    · linarith [le_max_right (a / (n : ℝ) - v) 0]
  split_ifs with hcut
  · exact hdiff.trans hd
  · rcases hactive with heq | hbu
    · simp [heq]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hfloor : a / b < (n : ℝ) :=
        (Nat.floor_lt (by positivity : 0 ≤ a / b)).1 (not_le.1 hcut)
      have haz : a / (n : ℝ) < b := by
        rw [div_lt_iff₀ hb] at hfloor
        apply (div_lt_iff₀ hn0).2
        nlinarith
      unfold alpogeASKPos
      rw [max_eq_right (by linarith : a / (n : ℝ) - u ≤ 0),
        max_eq_right (by linarith : a / (n : ℝ) - v ≤ 0)]
      simp

/-- Complete ASK transport with mass two. Only changed widths must be at
least b; unchanged thin widths can be arbitrarily small and remain exact. -/
theorem alpogeNativeFullASK_lower_width_le
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a b h : ℝ) (t : H)
    (w₀ w₁ : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hh : 0 ≤ h)
    (horder : ∀ ρ, alpogeNativeInPhi ρ → w₀ ρ ≤ w₁ ρ)
    (hdisp : ∀ ρ, alpogeNativeInPhi ρ → w₁ ρ - w₀ ρ ≤ h)
    (hactive : ∀ ρ, alpogeNativeInPhi ρ → w₀ ρ = w₁ ρ ∨ b ≤ w₀ ρ) :
    (alpogeNativeFullKernelASK inertia frob N a t w₀).re -
        (alpogeNativeFullKernelASK inertia frob N a t w₁).re ≤
      2 * h * nativePsi ⌊a / b⌋₊ := by
  classical
  rw [alpogeNativeFullKernelASK_re_eq_weighted,
    alpogeNativeFullKernelASK_re_eq_weighted, ← Finset.sum_sub_distrib]
  have hpoint : ∀ n ∈ Finset.Icc 1 N,
      (∑ g ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
        alpogeNativeASKRealWeight inertia frob n g *
          alpogeASKPos (a / (n : ℝ)) (w₀ (alpogeNativePartner t g))) -
      (∑ g ∈ Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
        alpogeNativeASKRealWeight inertia frob n g *
          alpogeASKPos (a / (n : ℝ)) (w₁ (alpogeNativePartner t g))) ≤
      if n ≤ ⌊a / b⌋₊ then 2 * h * Λ n else 0 := by
    intro n hn
    rw [← Finset.sum_sub_distrib]
    have hsum :
        (∑ g ∈ Finset.univ.filter
          (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
          (alpogeNativeASKRealWeight inertia frob n g *
            alpogeASKPos (a / (n : ℝ)) (w₀ (alpogeNativePartner t g)) -
           alpogeNativeASKRealWeight inertia frob n g *
            alpogeASKPos (a / (n : ℝ)) (w₁ (alpogeNativePartner t g)))) ≤
        (∑ g ∈ Finset.univ.filter
          (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
          alpogeNativeASKRealWeight inertia frob n g) *
            (if n ≤ ⌊a / b⌋₊ then h else 0) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro g hg
      have hp := alpogeNativeFreezing_partner_inPhi t g (Finset.mem_filter.mp hg).2
      have hs := alpogeNativeFreezing_cut_difference_le a b h
        (w₀ (alpogeNativePartner t g)) (w₁ (alpogeNativePartner t g)) n
        ha hb (Finset.mem_Icc.mp hn).1
        (horder _ hp) (hdisp _ hp) (hactive _ hp)
      simpa [mul_sub] using mul_le_mul_of_nonneg_left hs
        (alpogeNativeASKRealWeight_nonneg inertia frob n g)
    by_cases hc : n ≤ ⌊a / b⌋₊
    · rw [if_pos hc] at hsum ⊢
      have hm := mul_le_mul_of_nonneg_right
        (alpogeNativeASKRealWeight_sum_le_two_lambda inertia frob n) hh
      nlinarith
    · simpa [hc] using hsum
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        if n ≤ ⌊a / b⌋₊ then 2 * h * Λ n else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≤ ⌊a / b⌋₊),
        2 * h * Λ n := by rw [Finset.sum_filter]
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊a / b⌋₊, 2 * h * Λ n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1,
            (Finset.mem_filter.mp hn).2⟩
      · intro n _hn _hnot
        exact mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg
    _ = 2 * h * nativePsi ⌊a / b⌋₊ := by
      unfold nativePsi
      rw [Finset.mul_sum]

/-- Lowering widths increases MAIN. This preserves the favorable sign of
the complete logarithmic counterterm, including its authentic ell term. -/
theorem alpogeNativeMAIN_re_antitone_width
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a : ℝ) (ha : 0 ≤ a) (w₀ w₁ : AlpogeNativeE0 × H → ℝ)
    (hpos : ∀ ρ, alpogeNativeInPhi ρ → 0 < w₀ ρ)
    (horder : ∀ ρ, alpogeNativeInPhi ρ → w₀ ρ ≤ w₁ ρ) :
    (alpogeNativeMAIN ell a w₁).re ≤ (alpogeNativeMAIN ell a w₀).re := by
  classical
  have hlogs : (∑ ρ ∈ alpogeNativePhiSet H, Real.log (w₀ ρ)) ≤
      ∑ ρ ∈ alpogeNativePhiSet H, Real.log (w₁ ρ) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    have hp : alpogeNativeInPhi ρ := (Finset.mem_filter.mp hρ).2
    exact Real.log_le_log (hpos ρ hp) (horder ρ hp)
  have hscaled := mul_le_mul_of_nonneg_left hlogs
    (show 0 ≤ a * (1 / ((alpogeNativePhiSet H).card : ℝ)) by positivity)
  unfold alpogeNativeMAIN
  simp only [Complex.mul_re, Complex.add_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith

/-- Paid movement of the COMPLETE signed source. No characterwise norm is
taken, and unchanged thin widths do not enter the freezing cost. -/
theorem alpogeNativeSignedWidthSource_lower_width_le
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a b h : ℝ) (t : H)
    (w₀ w₁ : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hh : 0 ≤ h)
    (hpos : ∀ ρ, alpogeNativeInPhi ρ → 0 < w₀ ρ)
    (horder : ∀ ρ, alpogeNativeInPhi ρ → w₀ ρ ≤ w₁ ρ)
    (hdisp : ∀ ρ, alpogeNativeInPhi ρ → w₁ ρ - w₀ ρ ≤ h)
    (hactive : ∀ ρ, alpogeNativeInPhi ρ → w₀ ρ = w₁ ρ ∨ b ≤ w₀ ρ) :
    alpogeNativeSignedWidthSource inertia frob ell N a t w₀ ≤
      alpogeNativeSignedWidthSource inertia frob ell N a t w₁ +
        2 * h * nativePsi ⌊a / b⌋₊ := by
  have hA := alpogeNativeFullASK_lower_width_le inertia frob N a b h t w₀ w₁
    ha hb hh horder hdisp hactive
  have hM := alpogeNativeMAIN_re_antitone_width ell a ha.le w₀ w₁ hpos horder
  unfold alpogeNativeSignedWidthSource
  simp only [Complex.sub_re]
  linarith

/-- Elementary numerical payment: no PNT or critical source estimate.
The constant is the already proved native Chebyshev constant log 4 + 2. -/
theorem alpogeNativeFreezing_cost_le
    (a b h : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hh : 0 ≤ h) :
    2 * h * nativePsi ⌊a / b⌋₊ ≤
      2 * h * (Real.log 4 + 2) * (a / b) := by
  have hc : 0 ≤ Real.log 4 + 2 := by
    have : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hfloor := Nat.floor_le (div_nonneg ha hb.le)
  have hp := (nativePsi_le_const_mul ⌊a / b⌋₊).trans
    (mul_le_mul_of_nonneg_left hfloor hc)
  have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * h by positivity)
  nlinarith

/-- Actual positive thick sites, before applying the t-dependent partner. -/
def alpogeNativeThickPositiveSites (T2 : Finset H) (u : H) :
    Finset (AlpogeNativeE0 × H) :=
  T2.image (fun s => (((0, 1) : AlpogeNativeE0), s + u))

/-- Freeze exactly the selected thick sites; every thin width is unchanged. -/
def alpogeNativeFreezeThick (T2 : Finset H) (u : H) (b : ℝ)
    (w : AlpogeNativeE0 × H → ℝ) : AlpogeNativeE0 × H → ℝ :=
  fun ρ => if ρ ∈ alpogeNativeThickPositiveSites T2 u then b else w ρ

theorem alpogeNativeFreezing_partner_mem_iff
    (T2 : Finset H) (u t : H) (g : AlpogeNativeE0 × H) :
    alpogeNativePartner t g ∈ alpogeNativeThickPositiveSites T2 u ↔
      g ∈ alpogeNativeProjectionThickColours T2 u t := by
  classical
  have hinj : Function.Injective (alpogeNativePartner (H := H) t) := by
    intro g g' h
    unfold alpogeNativePartner at h
    exact add_left_cancel (add_right_cancel h)
  constructor
  · intro h
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp h
    apply Finset.mem_image.mpr
    refine ⟨s, hs, hinj ?_⟩
    rw [alpogeNativeProjectionThick_partner]
    exact heq
  · intro h
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
    rw [alpogeNativeProjectionThick_partner]
    exact Finset.mem_image.mpr ⟨s, hs, rfl⟩

theorem alpogeNativeProjectionActualThick_freeze
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (a b : ℝ) (u t : H)
    (w : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeProjectionActualThick F T2 a u t
        (alpogeNativeFreezeThick T2 u b w) =
      alpogeNativeFrozenThick F T2 b (a / b) u t := by
  classical
  unfold alpogeNativeProjectionActualThick alpogeNativeFrozenThick
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hmem : (((0, 1) : AlpogeNativeE0), s + u) ∈
      alpogeNativeThickPositiveSites T2 u := Finset.mem_image.mpr ⟨s, hs, rfl⟩
  simp only [alpogeNativeProjectionColourTerm,
    alpogeNativeProjectionThick_partner, alpogeNativeFreezeThick, if_pos hmem]

/-- Exact preservation of the complete signed thin return. -/
theorem alpogeNativeProjectionThinReturn_freeze
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (a b : ℝ) (u t : H)
    (w : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeProjectionThinReturn F T2 a u t
        (alpogeNativeFreezeThick T2 u b w) =
      alpogeNativeProjectionThinReturn F T2 a u t w := by
  classical
  unfold alpogeNativeProjectionThinReturn
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  have hnot : alpogeNativePartner t g ∉ alpogeNativeThickPositiveSites T2 u := by
    rw [alpogeNativeFreezing_partner_mem_iff]
    exact (Finset.mem_sdiff.mp hg).2
  simp only [alpogeNativeProjectionColourTerm, alpogeNativeFreezeThick, if_neg hnot]

theorem alpogeNativeProjectionFullSource_freeze
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (a b : ℝ) (u t : H)
    (w : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeProjectionFullSource F a t (alpogeNativeFreezeThick T2 u b w) =
      alpogeNativeFrozenThick F T2 b (a / b) u t +
        alpogeNativeProjectionThinReturn F T2 a u t w := by
  rw [alpogeNativeProjectionFull_eq_thick_add_thin F T2 a u t,
    alpogeNativeProjectionActualThick_freeze, alpogeNativeProjectionThinReturn_freeze]

/-- Complete-character thick freezing.  Its only charged arithmetic mass
is the actual prefix up to floor(a/b); all complementary sites stay signed. -/
theorem alpogeNativeThickFreezing_paid
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (T2 : Finset H) (a b h : ℝ) (u t : H)
    (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hh : 0 ≤ h)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hthick : ∀ ρ ∈ alpogeNativeThickPositiveSites T2 u,
      b ≤ w ρ ∧ w ρ ≤ b + h)
    (hN : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (N : ℝ))
    (hNb : a / b ≤ (N : ℝ)) :
    (alpogeNativeFrozenThick (alpogeNativeFrobInertiaGPsi inertia frob ell)
      T2 b (a / b) u t).re +
      (alpogeNativeProjectionThinReturn (alpogeNativeFrobInertiaGPsi inertia frob ell)
        T2 a u t w).re ≤
      alpogeNativeSignedWidthSource inertia frob ell N a t w +
        2 * h * nativePsi ⌊a / b⌋₊ := by
  classical
  let w₀ := alpogeNativeFreezeThick T2 u b w
  have hp : ∀ ρ, alpogeNativeInPhi ρ → 0 < w₀ ρ := by
    intro ρ hρ
    dsimp [w₀, alpogeNativeFreezeThick]
    split_ifs
    · exact hb
    · exact hw ρ hρ
  have ho : ∀ ρ, alpogeNativeInPhi ρ → w₀ ρ ≤ w ρ := by
    intro ρ _hρ
    dsimp [w₀, alpogeNativeFreezeThick]
    split_ifs with hs
    · exact (hthick ρ hs).1
    · exact le_rfl
  have hd : ∀ ρ, alpogeNativeInPhi ρ → w ρ - w₀ ρ ≤ h := by
    intro ρ _hρ
    dsimp [w₀, alpogeNativeFreezeThick]
    split_ifs with hs
    · linarith [(hthick ρ hs).2]
    · simpa using hh
  have hac : ∀ ρ, alpogeNativeInPhi ρ → w₀ ρ = w ρ ∨ b ≤ w₀ ρ := by
    intro ρ _hρ
    dsimp [w₀, alpogeNativeFreezeThick]
    split_ifs
    · exact Or.inr le_rfl
    · exact Or.inl rfl
  have hcut : ∀ ρ, alpogeNativeInPhi ρ → a / w₀ ρ ≤ (N : ℝ) := by
    intro ρ hρ
    dsimp [w₀, alpogeNativeFreezeThick]
    split_ifs
    · exact hNb
    · exact hN ρ hρ
  have hpaid := alpogeNativeSignedWidthSource_lower_width_le
    inertia frob ell N a b h t w₀ w ha hb hh hp ho hd hac
  have heq : alpogeNativeSignedWidthSource inertia frob ell N a t w₀ =
      (alpogeNativeFrozenThick (alpogeNativeFrobInertiaGPsi inertia frob ell)
        T2 b (a / b) u t).re +
      (alpogeNativeProjectionThinReturn (alpogeNativeFrobInertiaGPsi inertia frob ell)
        T2 a u t w).re := by
    unfold alpogeNativeSignedWidthSource
    rw [alpogeNativeFullASK_sub_MAIN_eq_De inertia frob ell N a t w₀ ha hp hcut,
      ← alpogeNativeProjectionFullSource_eq_nativeDe inertia frob ell]
    change (alpogeNativeProjectionFullSource _ a t
      (alpogeNativeFreezeThick T2 u b w)).re = _
    rw [alpogeNativeProjectionFullSource_freeze, Complex.add_re]
  rwa [heq] at hpaid

/-- The literal signed thin average, preserving the same subgroup, all
lifted rows, all top heights, and each original width. -/
def alpogeNativeProjectionThinAverage
    (A0 : AddSubgroup H)
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (TT T2 : Finset H) {m : ℕ} (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card A0 : ℝ)) * ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
    (alpogeNativeProjectionThinReturn F T2 (a t) u t (w u j)).re

/-- Derived Q plus a fully paid freezing error. The complete signed thin
source stays on the LHS and can be combined with the same geometric bill. -/
theorem alpogeNativePhysicalSubgroup_freezing_paid
    (A0 : AddSubgroup H)
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT T2 : Finset H) (hTT : TT.Nonempty)
    (hT2 : ∀ s ∈ T2, s ∈ A0) (a : H → ℝ) (b h : ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (hb : 0 < b) (hh : 0 ≤ h) (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ)
    (hthick : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
      b ≤ w u j ρ ∧ w u j ρ ≤ b + h)
    (hN : ∀ u j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ → a t / w u j ρ ≤ (N : ℝ))
    (hNb : ∀ t ∈ TT, a t / b ≤ (N : ℝ)) :
    alpogeNativeProjectionDivisor TT T2 m b *
      alpogeNativeProjectedSignal A0 (alpogeNativeFrobInertiaGPsi inertia frob ell) TT a b +
      alpogeNativeProjectionThinAverage A0 (alpogeNativeFrobInertiaGPsi inertia frob ell)
        TT T2 a w ≤
      alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w +
        2 * h * m * ∑ t ∈ TT, nativePsi ⌊a t / b⌋₊ := by
  classical
  let F := alpogeNativeFrobInertiaGPsi inertia frob ell
  have hs :
      (∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
        ((alpogeNativeFrozenThick F T2 b (a t / b) u t).re +
          (alpogeNativeProjectionThinReturn F T2 (a t) u t (w u j)).re)) ≤
      ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
        (alpogeNativeSignedWidthSource inertia frob ell N (a t) t (w u j) +
          2 * h * nativePsi ⌊a t / b⌋₊) := by
    apply Finset.sum_le_sum
    intro u _hu
    apply Finset.sum_le_sum
    intro t ht
    apply Finset.sum_le_sum
    intro j _hj
    exact alpogeNativeThickFreezing_paid inertia frob ell N T2 (a t) b h u t (w u j)
      (ha t ht) hb hh (hw u j) (hthick u j) (hN u j t ht) (hNb t ht)
  have hcost : (1 / (Fintype.card A0 : ℝ)) *
      (∑ _u : A0, ∑ t ∈ TT, ∑ _j : Fin m, 2 * h * nativePsi ⌊a t / b⌋₊) =
      2 * h * m * ∑ t ∈ TT, nativePsi ⌊a t / b⌋₊ := by
    have hu : (Fintype.card A0 : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    field_simp [hu]
  have hscaled := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 1 / (Fintype.card A0 : ℝ) by positivity)
  simp only [Finset.sum_add_distrib] at hscaled
  rw [mul_add, mul_add,
    alpogeNativeFrozenThick_average_eq_signal A0 F TT T2 hTT hT2 m a b,
    hcost] at hscaled
  exact hscaled

/-- The complete retained-character inequality, with BOTH excluded
characters and the signed thin source still explicit. The thick movement
has been paid from actual arithmetic, not assumed as a small error. -/
theorem alpogeNativeRetained_freezing_paid
    (A0 : AddSubgroup H)
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) {m : ℕ} (TT T2 : Finset H) (hTT : TT.Nonempty)
    (hT2 : ∀ s ∈ T2, s ∈ A0) (a : H → ℝ) (b h : ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (Kp : Finset (AddChar (AlpogeNativeE0 × H) ℂ))
    (hKp : Kp ⊆ alpogeNativeProjectionChars A0)
    (hb : 0 < b) (hh : 0 ≤ h) (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ)
    (hthick : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
      b ≤ w u j ρ ∧ w u j ρ ≤ b + h)
    (hN : ∀ u j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ → a t / w u j ρ ≤ (N : ℝ))
    (hNb : ∀ t ∈ TT, a t / b ≤ (N : ℝ)) :
    alpogeNativeProjectionDivisor TT T2 m b *
      (alpogeNativeRetainedSignal (alpogeNativeFrobInertiaGPsi inertia frob ell) Kp TT a b -
        alpogeNativeExcludedCharacterMass A0 (alpogeNativeFrobInertiaGPsi inertia frob ell)
          Kp TT a b) +
      alpogeNativeProjectionThinAverage A0 (alpogeNativeFrobInertiaGPsi inertia frob ell)
        TT T2 a w ≤
      alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w +
        2 * h * m * ∑ t ∈ TT, nativePsi ⌊a t / b⌋₊ := by
  have hchar := alpogeNativeRetained_sub_excluded_le_projected A0
    (alpogeNativeFrobInertiaGPsi inertia frob ell) Kp hKp TT a b
  have hQ : 0 ≤ alpogeNativeProjectionDivisor TT T2 m b := by
    unfold alpogeNativeProjectionDivisor alpogeNativeProjectionDensity
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hchar hQ
  exact (add_le_add hscaled le_rfl).trans
    (alpogeNativePhysicalSubgroup_freezing_paid A0 inertia frob ell N TT T2 hTT hT2
      a b h w hb hh ha hw hthick hN hNb)

omit [DecidableEq H] in
/-- The original divisor cancels the actual top and row multiplicities.
If a_t/b <= X, the entire normalized freezing bill is at most
4*h*(log 4+2)*X/(b*Delta). No host cardinal remains except the actual density. -/
theorem alpogeNativeFreezing_normalized_cost_le
    (TT T2 : Finset H) (hTT : TT.Nonempty) (hT2 : T2.Nonempty)
    (m : ℕ) (hm : 0 < m) (a : H → ℝ) (b h X : ℝ)
    (hb : 0 < b) (hh : 0 ≤ h)
    (ha : ∀ t ∈ TT, 0 ≤ a t)
    (hX : ∀ t ∈ TT, a t / b ≤ X) :
    (2 * h * m * ∑ t ∈ TT, nativePsi ⌊a t / b⌋₊) /
        alpogeNativeProjectionDivisor TT T2 m b ≤
      4 * h * (Real.log 4 + 2) * X /
        (b * alpogeNativeProjectionDensity T2) := by
  classical
  have hc : 0 ≤ Real.log 4 + 2 := by
    have : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hsum : (∑ t ∈ TT, nativePsi ⌊a t / b⌋₊) ≤
      (TT.card : ℝ) * (Real.log 4 + 2) * X := by
    calc
      _ ≤ ∑ _t ∈ TT, (Real.log 4 + 2) * X := by
        apply Finset.sum_le_sum
        intro t ht
        have hfloor : (⌊a t / b⌋₊ : ℝ) ≤ X :=
          (Nat.floor_le (div_nonneg (ha t ht) hb.le)).trans (hX t ht)
        exact (nativePsi_le_const_mul ⌊a t / b⌋₊).trans
          (mul_le_mul_of_nonneg_left hfloor hc)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hQ := alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm b hb
  have ht : (TT.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hTT).ne'
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hd : alpogeNativeProjectionDensity T2 ≠ 0 := by
    unfold alpogeNativeProjectionDensity
    apply div_ne_zero
    · exact_mod_cast (Finset.card_pos.mpr hT2).ne'
    · exact_mod_cast Fintype.card_ne_zero
  have hnum := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 2 * h * (m : ℝ) by positivity)
  calc
    _ ≤ (2 * h * m * ((TT.card : ℝ) * (Real.log 4 + 2) * X)) /
        alpogeNativeProjectionDivisor TT T2 m b :=
      div_le_div_of_nonneg_right hnum hQ.le
    _ = _ := by
      unfold alpogeNativeProjectionDivisor
      field_simp [ht, hmr, hb.ne', hd]

end

end RHLean.Analysis
