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
  · have hpow : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
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
            Complex.ofReal ((2 : ℝ) /
              ((alpogeSquareInertiaCarrier (inertia p)).card : ℝ)) := by
          simp only [alpogeSquareInertiaCarrier, Complex.ofReal_div,
            Complex.ofReal_ofNat, Complex.ofReal_natCast]
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
    · rw [ite_eq_left hc] at hsum ⊢
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

/-- Increasing the physical widths decreases every real ASK summand.
The remaining price for the signed source is exactly the MAIN log change
as an upper bound. The two profiles use the same height, host and cutoff. -/
theorem alpogeNativeSignedWidthSource_upper_width_le
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a : ℝ) (t : H) (w₀ w : AlpogeNativeE0 × H → ℝ)
    (horder : ∀ ρ, alpogeNativeInPhi ρ → w₀ ρ ≤ w ρ) :
    alpogeNativeSignedWidthSource inertia frob ell N a t w ≤
      alpogeNativeSignedWidthSource inertia frob ell N a t w₀ +
        a * ((1 / ((alpogeNativePhiSet H).card : ℝ)) *
          ∑ ρ ∈ alpogeNativePhiSet H, (Real.log (w ρ) - Real.log (w₀ ρ))) := by
  classical
  have hAsk : (alpogeNativeFullKernelASK inertia frob N a t w).re ≤
      (alpogeNativeFullKernelASK inertia frob N a t w₀).re := by
    rw [alpogeNativeFullKernelASK_re_eq_weighted, alpogeNativeFullKernelASK_re_eq_weighted]
    apply Finset.sum_le_sum
    intro n _
    apply Finset.sum_le_sum
    intro g hg
    apply mul_le_mul_of_nonneg_left _ (alpogeNativeASKRealWeight_nonneg inertia frob n g)
    exact max_le_max (sub_le_sub_left (horder _
      (alpogeNativeFreezing_partner_inPhi t g (Finset.mem_filter.mp hg).2)) _) le_rfl
  unfold alpogeNativeSignedWidthSource alpogeNativeMAIN
  simp only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Finset.sum_sub_distrib]
  linarith only [hAsk]

/-- Compl3-style cancellation on the actual complete signed row: every
height and character term common to the two profiles disappears. The
ASK difference is retained with its sign, not bounded by its absolute
value. No geometric comparison is needed for this identity. -/
theorem alpogeNativeSignedWidthSource_sub_eq
    (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N : ℕ) (a : ℝ) (t : H) (w v : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeSignedWidthSource inertia frob ell N a t w -
        alpogeNativeSignedWidthSource inertia frob ell N a t v =
      (alpogeNativeFullKernelASK inertia frob N a t w).re -
        (alpogeNativeFullKernelASK inertia frob N a t v).re +
      a * ((1 / ((alpogeNativePhiSet H).card : ℝ)) *
        ∑ ρ ∈ alpogeNativePhiSet H, (Real.log (w ρ) - Real.log (v ρ))) := by
  classical
  unfold alpogeNativeSignedWidthSource alpogeNativeMAIN
  simp only [Complex.sub_re, Complex.mul_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.sum_sub_distrib]
  ring

/-- Upper width enclosures on the original top excess. A bound on the mean
log-width distortion on each row suffices. The subgroup mean, top count and
row count cancel against the original divisor, leaving its density visible. -/
theorem alpogeNativePhysicalSubgroupTopExcess_upper_width_le
    (A0 : AddSubgroup H) (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (A b η : ℝ)
    (w₀ w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m) (hb : 0 < b)
    (hη : 0 ≤ η) (ha : ∀ t ∈ TT, 0 ≤ a t ∧ a t ≤ A)
    (horder : ∀ (u : A0) j ρ, alpogeNativeInPhi ρ → w₀ u j ρ ≤ w u j ρ)
    (hlog : ∀ (u : A0) j, (1 / ((alpogeNativePhiSet H).card : ℝ)) *
      ∑ ρ ∈ alpogeNativePhiSet H, (Real.log (w u j ρ) - Real.log (w₀ u j ρ)) ≤ η) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w /
        alpogeNativeProjectionDivisor TT T2 m b ≤
      alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w₀ /
        alpogeNativeProjectionDivisor TT T2 m b +
      2 * A * η / (b * alpogeNativeProjectionDensity T2) := by
  classical
  let S (v : H → Fin m → AlpogeNativeE0 × H → ℝ) (u : A0) (t : H) (j : Fin m) :=
    alpogeNativeSignedWidthSource inertia frob ell N (a t) t (v u j)
  have hsum : (∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m, S w u t j) ≤
      ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m, (S w₀ u t j + A * η) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro t ht
    apply Finset.sum_le_sum
    intro j _
    have hrow := alpogeNativeSignedWidthSource_upper_width_le inertia frob ell
      N (a t) t (w₀ u j) (w u j) (horder u j)
    exact hrow.trans (add_le_add le_rfl
      ((mul_le_mul_of_nonneg_left (hlog u j) (ha t ht).1).trans
        (mul_le_mul_of_nonneg_right (ha t ht).2 hη)))
  have hu : (Fintype.card A0 : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hQ := alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm b hb
  have hδ : 0 < alpogeNativeProjectionDensity T2 := by
    unfold alpogeNativeProjectionDensity
    exact div_pos (by exact_mod_cast hT2.card_pos) (by exact_mod_cast Fintype.card_pos)
  have hT : (TT.card : ℝ) ≠ 0 := by exact_mod_cast hTT.card_pos.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmean := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 1 / (Fintype.card A0 : ℝ) by positivity)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_add] at hmean
  change alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w ≤
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w₀ +
      (1 / (Fintype.card A0 : ℝ)) * ((Fintype.card A0 : ℝ) *
        ((TT.card : ℝ) * ((m : ℝ) * (A * η)))) at hmean
  have hdiv := div_le_div_of_nonneg_right hmean hQ.le
  rw [add_div] at hdiv
  calc
    _ ≤ _ := hdiv
    _ = _ := by
      congr 1
      unfold alpogeNativeProjectionDivisor
      field_simp [hu, hT, hm', hb.ne', hδ.ne']

/-- Lower endpoint of the logarithmic cell containing a positive width. -/
def alpogeNativeLowerLogWidth (η v : ℝ) : ℝ :=
  Real.exp ((⌊Real.log v / η⌋ : ℤ) * η)

private theorem lowerLogWidth_bounds {η v : ℝ} (hη : 0 < η) (hv : 0 < v) :
    alpogeNativeLowerLogWidth η v ≤ v ∧
      Real.log v - Real.log (alpogeNativeLowerLogWidth η v) ≤ η := by
  let k : ℤ := ⌊Real.log v / η⌋
  have hlo : (k : ℝ) * η ≤ Real.log v :=
    (le_div_iff₀ hη).mp (Int.floor_le _)
  have hhi : Real.log v < ((k : ℝ) + 1) * η :=
    (div_lt_iff₀ hη).mp (Int.lt_floor_add_one _)
  change Real.exp ((k : ℝ) * η) ≤ v ∧ Real.log v - Real.log (Real.exp ((k : ℝ) * η)) ≤ η
  rw [Real.log_exp]
  exact ⟨(Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log hv), by linarith only [hhi]⟩

/-- The coarsened width profile is constructed from the physical widths.
Its one-sided transfer price after the actual projection is at most
2 A η / (b Δ), uniformly in the subgroup, the top count and the row count. -/
theorem alpogeNativePhysicalSubgroupTopExcess_logGrid_le
    (A0 : AddSubgroup H) (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (A b η : ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m) (hb : 0 < b)
    (hη : 0 < η) (ha : ∀ t ∈ TT, 0 ≤ a t ∧ a t ≤ A)
    (hw : ∀ (u : A0) j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w /
        alpogeNativeProjectionDivisor TT T2 m b ≤
      alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a
          (fun u j ρ => alpogeNativeLowerLogWidth η (w u j ρ)) /
        alpogeNativeProjectionDivisor TT T2 m b +
      2 * A * η / (b * alpogeNativeProjectionDensity T2) := by
  apply alpogeNativePhysicalSubgroupTopExcess_upper_width_le A0 inertia frob ell
    N m TT T2 a A b η _ w hTT hT2 hm hb hη.le ha
  · exact fun u j ρ hρ => (lowerLogWidth_bounds hη (hw u j ρ hρ)).1
  · intro u j
    have hsum := Finset.sum_le_sum (s := alpogeNativePhiSet H)
      (fun ρ hρ => (lowerLogWidth_bounds hη (hw u j ρ (Finset.mem_filter.mp hρ).2)).2)
    have hcard : (0 : ℝ) < (alpogeNativePhiSet H).card := by
      exact_mod_cast Finset.card_pos.mpr
        (show (alpogeNativePhiSet H).Nonempty from
          ⟨0, by simp [alpogeNativePhiSet, alpogeNativeInPhi]⟩)
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    rw [one_div, ← div_eq_inv_mul]
    exact (div_le_iff₀ hcard).2 (hsum.trans_eq (mul_comm _ _))

/-- On the full native host a fixed first-coset colour is charged once
for each thick site. This is the density earned in the signed ASK saving. -/
theorem alpogeNativeThickColour_translate_count (T2 : Finset H) (t h : H) :
    (Finset.univ.filter (fun u : H =>
      alpogeNativeProjectionE1 h ∈ alpogeNativeProjectionThickColours T2 u t)).card =
      T2.card := by
  classical
  have hset : Finset.univ.filter (fun u : H =>
      alpogeNativeProjectionE1 h ∈ alpogeNativeProjectionThickColours T2 u t) =
      T2.image (fun s => h + t - s) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      alpogeNativeProjectionThickColours, Finset.mem_image]
    constructor
    · rintro ⟨s, hs, heq⟩
      have hx : s + u - t = h := congrArg Prod.snd heq
      exact ⟨s, hs, by rw [← hx]; abel⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, congrArg alpogeNativeProjectionE1 (by abel)⟩
  rw [hset]
  exact Finset.card_image_of_injective _ (fun _ _ hxy => sub_right_injective hxy)

/-- The rounded widths still pay the physical thick cutoff. For each
selected colour the saving is the difference of two sharp cuts. -/
theorem alpogeNativeLowerLogWidth_cut_le (η z c w : ℝ)
    (hη : 0 < η) (hw : 0 < w) (hc : c ≤ w) :
    alpogeASKPos z (alpogeNativeLowerLogWidth η w) ≤
      alpogeASKPos z (c * Real.exp (-η)) := by
  have hlog := (lowerLogWidth_bounds hη hw).2
  have hle : Real.log w - η ≤ Real.log (alpogeNativeLowerLogWidth η w) := by linarith
  have hw' : 0 < alpogeNativeLowerLogWidth η w := Real.exp_pos _
  have hbound := Real.exp_le_exp.mpr hle
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hw, Real.exp_log hw'] at hbound
  apply max_le_max _ le_rfl
  exact sub_le_sub_left ((mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans hbound) z

/-- Independent upper estimate on the comparison source. Every positive-part cut
is at most its height divided by the prime power. The full signed MAIN is
retained, and the mass-two estimate uses the given inertia and Frobenius. -/
theorem alpogeNativePhysicalSubgroupTopExcess_mass_bound
    (A0 : AddSubgroup H) (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N m : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (ha : ∀ t ∈ TT, 0 ≤ a t)
    (hw : ∀ (u : A0) j ρ, alpogeNativeInPhi ρ → 0 ≤ w u j ρ) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w ≤
      (1 / (Fintype.card A0 : ℝ)) * ∑ u : A0, ∑ t ∈ TT, ∑ j : Fin m,
        ((∑ n ∈ Finset.Icc 1 N, (2 * Λ n) * (a t / (n : ℝ))) -
          (alpogeNativeMAIN ell (a t) (w u j)).re) := by
  classical
  unfold alpogeNativePhysicalSubgroupTopExcess
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro t ht
  apply Finset.sum_le_sum
  intro j _
  rw [Complex.sub_re]
  apply sub_le_sub_right
  rw [alpogeNativeFullKernelASK_re_eq_weighted]
  apply Finset.sum_le_sum
  intro n _
  have hz : 0 ≤ a t / (n : ℝ) := div_nonneg (ha t ht) (Nat.cast_nonneg n)
  apply le_trans _ (mul_le_mul_of_nonneg_right
    (alpogeNativeASKRealWeight_sum_le_two_lambda inertia frob n) hz)
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro g hg
  apply mul_le_mul_of_nonneg_left _ (alpogeNativeASKRealWeight_nonneg inertia frob n g)
  exact max_le (sub_le_self _ (hw u j _ (alpogeNativeFreezing_partner_inPhi t g
    (Finset.mem_filter.mp hg).2))) hz

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

omit [Fintype H] in
/-- Exactly the actual thick sites, not all positive host coordinates,
can change under freezing. Translation is injective. -/
theorem alpogeNativeThickPositiveSites_card (T2 : Finset H) (u : H) :
    (alpogeNativeThickPositiveSites T2 u).card = T2.card := by
  unfold alpogeNativeThickPositiveSites
  exact Finset.card_image_of_injective _ (fun _ _ heq =>
    add_right_cancel (congrArg Prod.snd heq))

/-- The native supported-coordinate estimate: unchanged thin coordinates
contribute zero, and each actual thick coordinate costs at most h/b in
log width. The Phi normalization pays the exact fraction Delta/2. -/
theorem alpogeNativeFreezeThick_logMean_le
    (T2 : Finset H) (u : H) (b h : ℝ) (hb : 0 < b)
    (w : AlpogeNativeE0 × H → ℝ)
    (hthick : ∀ ρ ∈ alpogeNativeThickPositiveSites T2 u,
      b ≤ w ρ ∧ w ρ ≤ b + h) :
    (1 / ((alpogeNativePhiSet H).card : ℝ)) *
      ∑ ρ ∈ alpogeNativePhiSet H,
        (Real.log (w ρ) - Real.log (alpogeNativeFreezeThick T2 u b w ρ)) ≤
      (alpogeNativeProjectionDensity T2 / 2) * (h / b) := by
  classical
  have hsub : alpogeNativeThickPositiveSites T2 u ⊆ alpogeNativePhiSet H := by
    intro ρ hρ
    obtain ⟨s, _hs, rfl⟩ := Finset.mem_image.mp hρ
    simp [alpogeNativePhiSet, alpogeNativeInPhi]
  have hset : (alpogeNativePhiSet H).filter
      (fun ρ => ρ ∈ alpogeNativeThickPositiveSites T2 u) =
      alpogeNativeThickPositiveSites T2 u := by
    ext ρ
    simp only [Finset.mem_filter]
    exact ⟨fun hρ => hρ.2, fun hρ => ⟨hsub hρ, hρ⟩⟩
  have hsum : (∑ ρ ∈ alpogeNativePhiSet H,
      (Real.log (w ρ) - Real.log (alpogeNativeFreezeThick T2 u b w ρ))) ≤
      (T2.card : ℝ) * (h / b) := by
    calc
      _ ≤ ∑ ρ ∈ alpogeNativePhiSet H,
          (if ρ ∈ alpogeNativeThickPositiveSites T2 u then h / b else 0) := by
        apply Finset.sum_le_sum
        intro ρ _hρ
        by_cases hs : ρ ∈ alpogeNativeThickPositiveSites T2 u
        · have hw := hthick ρ hs
          have hp := hb.trans_le hw.1
          have hlog := Real.log_le_sub_one_of_pos (div_pos hp hb)
          rw [Real.log_div hp.ne' hb.ne'] at hlog
          have hratio := div_le_div_of_nonneg_right hw.2 hb.le
          rw [add_div, div_self hb.ne'] at hratio
          simp only [alpogeNativeFreezeThick, if_pos hs]
          linarith
        · simp [alpogeNativeFreezeThick, hs]
      _ = _ := by
        rw [← Finset.sum_filter, hset, Finset.sum_const, nsmul_eq_mul,
          alpogeNativeThickPositiveSites_card]
  have hH : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (1 / ((alpogeNativePhiSet H).card : ℝ)) *
        ((T2.card : ℝ) * (h / b)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [alpogeNativeProjectionPhi_card, Nat.cast_mul]
      unfold alpogeNativeProjectionDensity
      push_cast
      field_simp [hH, hb.ne'] <;> ring

/-- Apply the supported-coordinate budget to the existing signed consumer.
The favorable ASK change is not charged. The thick density cancels against
the actual Q, and no thin width is modified. -/
theorem alpogeNativePhysicalSubgroupTopExcess_freezeThick_upper_le
    (A0 : AddSubgroup H) (inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H))
    (frob : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (A b h : ℝ)
    (w : H → Fin m → AlpogeNativeE0 × H → ℝ)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m) (hb : 0 < b)
    (hh : 0 ≤ h) (ha : ∀ t ∈ TT, 0 ≤ a t ∧ a t ≤ A)
    (hthick : ∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
      b ≤ w u j ρ ∧ w u j ρ ≤ b + h) :
    alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a w /
        alpogeNativeProjectionDivisor TT T2 m b ≤
      alpogeNativePhysicalSubgroupTopExcess A0 inertia frob ell N TT a
        (fun u j => alpogeNativeFreezeThick T2 u b (w u j)) /
        alpogeNativeProjectionDivisor TT T2 m b + (A / b) * (h / b) := by
  classical
  have hδ : 0 < alpogeNativeProjectionDensity T2 := by
    unfold alpogeNativeProjectionDensity
    exact div_pos (by exact_mod_cast hT2.card_pos) (by exact_mod_cast Fintype.card_pos)
  have hη : 0 ≤ (alpogeNativeProjectionDensity T2 / 2) * (h / b) := by positivity
  have horder : ∀ (u : A0) (j : Fin m) ρ, alpogeNativeInPhi ρ →
      alpogeNativeFreezeThick T2 u b (w u j) ρ ≤ w u j ρ := by
    intro u j ρ _hρ
    unfold alpogeNativeFreezeThick
    split_ifs with hs
    · exact (hthick u j ρ hs).1
    · exact le_rfl
  have hcmp := alpogeNativePhysicalSubgroupTopExcess_upper_width_le
    A0 inertia frob ell N m TT T2 a A b
    ((alpogeNativeProjectionDensity T2 / 2) * (h / b))
    (fun u j => alpogeNativeFreezeThick T2 u b (w u j)) w
    hTT hT2 hm hb hη ha horder
    (fun u j => alpogeNativeFreezeThick_logMean_le T2 u b h hb (w u j) (hthick u j))
  have hprice : 2 * A * ((alpogeNativeProjectionDensity T2 / 2) * (h / b)) /
      (b * alpogeNativeProjectionDensity T2) = (A / b) * (h / b) := by
    field_simp [hb.ne', hδ.ne'] <;> ring
  rwa [hprice] at hcmp

omit [Fintype H] in
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

/-- For an actual first-coset colour, the entire translate sum of rounded
sharp cuts earns the full thick saving. All thin widths may vary with u. -/
theorem alpogeNativeLowerLogWidth_thick_translate_cuts_le
    (T2 : Finset H) (t h : H) (η z beta b : ℝ) (w : H → ℝ)
    (hη : 0 < η) (hbeta : 0 < beta) (hw : ∀ u, beta ≤ w u)
    (hthick : ∀ u, alpogeNativeProjectionE1 h ∈ alpogeNativeProjectionThickColours T2 u t →
      b ≤ w u) :
    let P := fun c : ℝ => alpogeASKPos z (c * Real.exp (-η))
    (∑ u : H, alpogeASKPos z (alpogeNativeLowerLogWidth η (w u))) ≤
      (Fintype.card H : ℝ) * P beta - (T2.card : ℝ) * (P beta - P b) := by
  classical
  let P := fun c : ℝ => alpogeASKPos z (c * Real.exp (-η))
  let selected := fun u => alpogeNativeProjectionE1 h ∈ alpogeNativeProjectionThickColours T2 u t
  have hpay : (∑ u : H, if selected u then P beta - P b else 0) =
      (T2.card : ℝ) * (P beta - P b) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [show (Finset.univ.filter selected).card = T2.card from
      alpogeNativeThickColour_translate_count T2 t h]
  change _ ≤ (Fintype.card H : ℝ) * P beta - (T2.card : ℝ) * (P beta - P b)
  calc
    _ ≤ ∑ u : H, (P beta - (if selected u then P beta - P b else 0)) := by
      apply Finset.sum_le_sum
      intro u _
      have hw0 := hbeta.trans_le (hw u)
      by_cases hu : selected u
      · rw [ite_eq_left hu, sub_sub_cancel]
        exact alpogeNativeLowerLogWidth_cut_le η z b (w u) hη hw0 (hthick u hu)
      · rw [ite_eq_right hu, sub_zero]
        exact alpogeNativeLowerLogWidth_cut_le η z beta (w u) hη hw0 (hw u)
    _ = _ := by
      rw [Finset.sum_sub_distrib, hpay, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

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
    alpogeNativeProjectionThick_partner, alpogeNativeFreezeThick, ite_eq_left hmem]

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
  simp only [alpogeNativeProjectionColourTerm, alpogeNativeFreezeThick, ite_eq_right hnot]

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
      ring

end

end RHLean.Analysis
