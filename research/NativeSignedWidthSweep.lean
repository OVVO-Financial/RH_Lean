import RHLean.Analysis.AlpogeThin.NativeExistingRecoveryPayment
import «research.STABLE_FAR_PERRON_REAL_GRAM_COSINE»

/-! A finite comparison with an all-thin reference, on the original selected
host and cutoff. Its price is independent of the prime-power counts in the
sweep. Both profiles have the same height and canonical character term. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin.WidthSweep

private theorem cut_sub {z lo hi : ℝ} (h : lo ≤ hi) :
    alpogeASKPos z lo - alpogeASKPos z hi = min (alpogeASKPos z lo) (hi-lo) := by
  unfold alpogeASKPos
  rcases le_total z lo with hz | hz
  · rw [max_eq_right (by linarith : z-lo ≤ 0), max_eq_right (by linarith : z-hi ≤ 0),
      min_eq_left (by linarith : 0 ≤ hi-lo), sub_zero]
  · rw [max_eq_left (sub_nonneg.mpr hz)]
    rcases le_total z hi with hz' | hz'
    · rw [max_eq_right (sub_nonpos.mpr hz'), sub_zero, min_eq_left (by linarith)]
    · rw [max_eq_left (sub_nonneg.mpr hz'), min_eq_right (by linarith)]
      ring

/-- On the log-width coordinate the signed MAIN uses ordinary length and the
crossed part of a prime-power cut uses the integral of exp on the same interval. -/
theorem log_interval_cost (lo hi z : ℝ) (hlo : 0 < lo) (h : lo ≤ hi) :
    Real.log (hi/lo) = (∫ _ : ℝ in Real.log lo..Real.log hi, (1:ℝ)) ∧
    min (alpogeASKPos z lo) (hi-lo) =
      ∫ u : ℝ in Real.log lo..Real.log (max lo (min hi z)), Real.exp u := by
  constructor
  · simp [Real.log_div (hlo.trans_le h).ne' hlo.ne']
  · rw [integral_exp, Real.exp_log (hlo.trans_le (le_max_left _ _)), Real.exp_log hlo]
    unfold alpogeASKPos
    rcases le_total z lo with hz | hz
    · rw [max_eq_right (sub_nonpos.mpr hz), min_eq_left (sub_nonneg.mpr h),
        min_eq_right (hz.trans h), max_eq_left hz, sub_self]
    · rw [max_eq_left (sub_nonneg.mpr hz), max_eq_right (le_min h hz)]
      rcases le_total z hi with hh | hh
      · rw [min_eq_left (by linarith : z-lo ≤ hi-lo), min_eq_right hh]
      · rw [min_eq_right (by linarith : hi-lo ≤ z-lo), min_eq_left hh]

/-- The Fourier phase at the measured endpoint a/p is the project's actual
Perron multiplier, with the height phase and the reciprocal amplitude restored. -/
theorem firstPrime_endpoint_phase (a τ : ℝ) (p : ℕ) (ha : 0 < a) (hp : 0 < p) :
    RHLean.Proof.stableFarLogFrequencyMode (2*τ) (Real.log (a/p)) =
      RHLean.Proof.stableFarLogFrequencyMode (2*τ) (Real.log a) *
        ((p:ℂ) * RHLean.Proof.stableFarCriticalQ2LogMultiplier τ p) := by
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [RHLean.Proof.stableFarCriticalQ2LogMultiplier_eq_reciprocal_phase τ hp,
    ← mul_assoc (p:ℂ), mul_one_div_cancel hp0, one_mul]
  unfold RHLean.Proof.stableFarQ2LogFrequencyMultiplier RHLean.Proof.stableFarLogFrequencyMode
  rw [Real.log_div ha.ne' (Nat.cast_ne_zero.mpr hp.ne'), ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Mass of the parts of the original cuts crossed by the width increase.
Every prime power retains its real inertia/Frobenius weight. -/
def mass (I : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (F : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a : ℝ) (t : H) (lo hi : AlpogeNativeE0 × H → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ g ∈ Finset.univ.filter (fun g : AlpogeNativeE0 × H =>
    ¬ alpogeNativeInPhi g), alpogeNativeASKRealWeight I F n g *
      min (alpogeASKPos (a / (n:ℝ)) (lo (alpogeNativePartner t g)))
        (hi (alpogeNativePartner t g) - lo (alpogeNativePartner t g))

/-- The height and character constants cancel in the original signed MAIN.
Only the logarithmic width integral survives, with positive sign; the finite
prime-power mass has negative sign. -/
theorem signed_row_eq (I : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (F : ℕ → AlpogeNativeE0 × H)
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ) (N : ℕ) (a : ℝ) (t : H)
    (lo hi : AlpogeNativeE0 × H → ℝ)
    (h : ∀ ρ, alpogeNativeInPhi ρ → 0 < lo ρ ∧ lo ρ ≤ hi ρ) :
    alpogeNativeSignedWidthSource I F ell N a t hi =
      alpogeNativeSignedWidthSource I F ell N a t lo +
        a * ((1 / ((alpogeNativePhiSet H).card:ℝ)) *
          ∑ ρ ∈ alpogeNativePhiSet H, Real.log (hi ρ / lo ρ)) - mass I F N a t lo hi := by
  classical
  have paid : (alpogeNativeFullKernelASK I F N a t lo).re -
      (alpogeNativeFullKernelASK I F N a t hi).re = mass I F N a t lo hi := by
    simp only [alpogeNativeFullKernelASK_re_eq_weighted, mass, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun g hg => ?_
    rw [← mul_sub, cut_sub (h _ (alpogeNativeFreezing_partner_inPhi t g
      (Finset.mem_filter.mp hg).2)).2]
  have logs : (∑ ρ ∈ alpogeNativePhiSet H, (Real.log (hi ρ) - Real.log (lo ρ))) =
      ∑ ρ ∈ alpogeNativePhiSet H, Real.log (hi ρ / lo ρ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hw := h ρ (Finset.mem_filter.mp hρ).2
    exact (Real.log_div (hw.1.trans_le hw.2).ne' hw.1.ne').symm
  have rel := alpogeNativeSignedWidthSource_sub_eq I F ell N a t hi lo
  rw [logs] at rel
  linarith only [rel, paid]

/-- Summing a swept E1-colour over all physical translates gives the exact
thick multiplicity even when the other widths vary between translates. -/
theorem frozen_colour_mass (T2 : Finset H) (t h : H) (z l r : ℝ)
    (w : H → AlpogeNativeE0 × H → ℝ) :
    let site := alpogeNativePartner t (alpogeNativeProjectionE1 h)
    let lo := fun u => alpogeNativeFreezeThick T2 u l (w u) site
    let hi := fun u => alpogeNativeFreezeThick T2 u r (w u) site
    (∑ u : H, min (alpogeASKPos z (lo u)) (hi u - lo u)) =
      (T2.card:ℝ) * min (alpogeASKPos z l) (r-l) := by
  classical
  dsimp only
  let selected := fun u => alpogeNativeProjectionE1 h ∈ alpogeNativeProjectionThickColours T2 u t
  calc
    _ = ∑ u : H, if selected u then min (alpogeASKPos z l) (r-l) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : selected u
      · have hm := (alpogeNativeFreezing_partner_mem_iff T2 u t _).2 hu
        simp only [alpogeNativeFreezeThick, hm, hu, if_true]
      · have hm := (alpogeNativeFreezing_partner_mem_iff T2 u t _).not.mpr hu
        simp only [alpogeNativeFreezeThick, hm, hu, if_false, sub_self]
        exact min_eq_right (le_max_right _ _)
    _ = _ := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [show (Finset.univ.filter selected).card = T2.card from
        alpogeNativeThickColour_translate_count T2 t h]

/-- Exactly the same thick multiplicity multiplies the logarithm in MAIN. -/
theorem frozen_log_sum (T2 : Finset H) (u : H) (l r : ℝ)
    (w : AlpogeNativeE0 × H → ℝ) (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ) :
    (∑ ρ ∈ alpogeNativePhiSet H,
      Real.log (alpogeNativeFreezeThick T2 u r w ρ / alpogeNativeFreezeThick T2 u l w ρ)) =
      (T2.card:ℝ) * Real.log (r/l) := by
  classical
  let mask := alpogeNativeThickPositiveSites T2 u
  have sub : mask ⊆ alpogeNativePhiSet H := by
    intro ρ hρ
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hρ
    simp [alpogeNativePhiSet, alpogeNativeInPhi]
  calc
    _ = ∑ ρ ∈ mask, Real.log (alpogeNativeFreezeThick T2 u r w ρ /
        alpogeNativeFreezeThick T2 u l w ρ) := by
      symm
      apply Finset.sum_subset sub
      intro ρ hρ hout
      have h0 := (hw ρ (Finset.mem_filter.mp hρ).2).ne'
      change ρ ∉ alpogeNativeThickPositiveSites T2 u at hout
      simp [alpogeNativeFreezeThick, hout, h0]
    _ = ∑ _ρ ∈ mask, Real.log (r/l) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      change ρ ∈ alpogeNativeThickPositiveSites T2 u at hρ
      simp [alpogeNativeFreezeThick, hρ]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, alpogeNativeThickPositiveSites_card]

/-- The native thick-class two-cutoff remainder. The additive centering
constant cancels in a difference; the same finite N is used at both arguments. -/
def colourRemainder (I : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (F : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 N, (2 * ∑ h : H, alpogeNativeASKRealWeight I F n (alpogeNativeProjectionE1 h)) *
    max (1/(n:ℝ) - 1/y) 0) - Real.log y

/-- The normalized thick height numerator is exactly the small-cutoff
remainder minus the far-cutoff remainder on the native moving colour. -/
theorem two_cutoff_eq (I : ℕ → AddSubgroup (AlpogeNativeE0 × H)) (F : ℕ → AlpogeNativeE0 × H)
    (N : ℕ) (a l r : ℝ) (ha : 0 < a) (hl : 0 < l) (hlr : l ≤ r) :
    a * (colourRemainder I F N (a/r) - colourRemainder I F N (a/l)) =
      a * Real.log (r/l) -
        ∑ n ∈ Finset.Icc 1 N, (2 * ∑ h : H, alpogeNativeASKRealWeight I F n
          (alpogeNativeProjectionE1 h)) * min (alpogeASKPos (a/(n:ℝ)) l) (r-l) := by
  classical
  let W := fun n => 2 * ∑ h : H, alpogeNativeASKRealWeight I F n (alpogeNativeProjectionE1 h)
  have scaled (v : ℝ) (hv : 0 < v) :
      a * colourRemainder I F N (a/v) =
        (∑ n ∈ Finset.Icc 1 N, W n * alpogeASKPos (a/(n:ℝ)) v) - a * Real.log (a/v) := by
    unfold colourRemainder
    rw [mul_sub, Finset.mul_sum]
    apply congrArg (· - a * Real.log (a/v))
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have step : a * max (1/(n:ℝ)-1/(a/v)) 0 = alpogeASKPos (a/(n:ℝ)) v := by
      rw [mul_max_of_nonneg _ _ ha.le, mul_zero]
      unfold alpogeASKPos
      congr 1
      field [ha.ne', hv.ne', hn0.ne']
    change a * (W n * _) = _
    rw [mul_left_comm, step]
  have diff : (∑ n ∈ Finset.Icc 1 N, W n * alpogeASKPos (a/(n:ℝ)) l) -
      (∑ n ∈ Finset.Icc 1 N, W n * alpogeASKPos (a/(n:ℝ)) r) =
      ∑ n ∈ Finset.Icc 1 N, W n * min (alpogeASKPos (a/(n:ℝ)) l) (r-l) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [← mul_sub, cut_sub hlr]
  rw [mul_sub, scaled r (hl.trans_le hlr), scaled l hl,
    Real.log_div ha.ne' (hl.trans_le hlr).ne', Real.log_div ha.ne' hl.ne',
    Real.log_div (hl.trans_le hlr).ne' hl.ne']
  change _ = a * _ - ∑ n ∈ Finset.Icc 1 N, W n * _
  rw [← diff]
  ring

/-- Cap the measured widths at a common raw width s before rounding. On the
selected native pair the reference lies in the all-thin range. The right
hand side uses the same finite cutoff as the measured row, which can be any N. -/
theorem pairGood_row_le (eps : ℝ) (he : 0 < eps) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (Y Z : ℝ) (q d e N : ℕ)
      (hG : UpperTheory.Top.PairGood 1 eps Y Z q d),
      letI : Fact q.Prime := ⟨hG.pair.q_prime⟩
      letI : Fact d.Prime := ⟨hG.pair.d_prime⟩
      ∀ (t : AlpogeNativeDyadicH e) (a η s : ℝ)
        (w : AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
        0 < a → 0 < η → 0 < s → Real.exp (x ^ (eps/3))/3 ≤ a/s →
        Real.log (alpogeNativeHostN e q d) ≤ 2*x^(eps/5)*Real.log x^2 →
        (∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ) →
        let D := alpogeNativeHostData e q d
        let ell := alpogeNativeCanonicalHostEll (H := AlpogeNativeDyadicH e) (alpogeNativeRecMap e q d)
        let lo := fun ρ => alpogeNativeLowerLogWidth η (min (w ρ) s)
        let hi := fun ρ => alpogeNativeLowerLogWidth η (w ρ)
        alpogeNativeSignedWidthSource D.inertia D.frob ell N a t hi ≤
          4 * (Fintype.card (AlpogeNativeDyadicH e):ℝ) * a * Real.exp (-(x ^ (eps/8))) +
          a * ((1 / ((alpogeNativePhiSet (AlpogeNativeDyadicH e)).card:ℝ)) *
            ∑ ρ ∈ alpogeNativePhiSet (AlpogeNativeDyadicH e), Real.log (hi ρ / lo ρ)) -
          mass D.inertia D.frob N a t lo hi := by
  classical
  obtain ⟨x₀, h₀⟩ := nativeLedger_pairGood_roundedASK_le_thick eps he
  refine ⟨x₀, ?_⟩
  intro x hx Y Z q d e N hG
  letI : Fact q.Prime := ⟨hG.pair.q_prime⟩
  letI : Fact d.Prime := ⟨hG.pair.d_prime⟩
  dsimp only
  intro t a η s w ha hη hs hthin hlog hw
  let raw := fun ρ => min (w ρ) s
  let lo := fun ρ => alpogeNativeLowerLogWidth η (raw ρ)
  let hi := fun ρ => alpogeNativeLowerLogWidth η (w ρ)
  have hraw ρ (hρ : alpogeNativeInPhi ρ) : 0 < raw ρ := lt_min (hw ρ hρ) hs
  have budget := h₀ x hx Y Z q d e N hG ∅ 0 t a η raw ha hη hlog (by
    intro g hg
    have hg' : ¬alpogeNativeInPhi g := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hg).1).2
    have hρ := alpogeNativeFreezing_partner_inPhi t g hg'
    exact ⟨hraw _ hρ, hthin.trans (div_le_div_of_nonneg_left ha.le (hraw _ hρ) (min_le_right _ _))⟩)
  have hcard : (Fintype.card (AlpogeNativeDyadicH e):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [alpogeNativeProjectionActualThick, Finset.sum_empty, mul_zero, Complex.zero_re,
    zero_add, Finset.card_empty, Nat.cast_zero, sub_zero, alpogeNativeProjectionPhi_card,
    Nat.cast_mul, Nat.cast_ofNat, div_self (mul_ne_zero two_ne_zero hcard), one_mul] at budget
  have order (ρ) (hρ : alpogeNativeInPhi ρ) : 0 < lo ρ ∧ lo ρ ≤ hi ρ := by
    refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hη.le)⟩
    exact_mod_cast Int.floor_le_floor (div_le_div_of_nonneg_right
      (Real.log_le_log (hraw ρ hρ) (min_le_left _ _)) hη.le)
  rw [signed_row_eq _ _ _ N a t lo hi order]
  exact sub_le_sub_right (add_le_add_right budget _) _

end RHLean.Analysis.AlpogeThin.WidthSweep
