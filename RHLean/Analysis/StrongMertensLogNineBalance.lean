import RHLean.Analysis.StrongMertensLogNineBalanceCore

noncomputable section

open Filter Asymptotics Set

namespace RHLean.Analysis

/-- Balanced smoothed Mobius transform with subexponential decay. -/
theorem nativeSmoothedMobius_logNine_subexp_eventually
    (corridor : StrongMertensLogNineCorridor)
    {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ᶠ X : ℝ in atTop,
      ‖nativeSmoothedMobius f (strongMertensBalanceEps corridor X) X‖ ≤
        C * X * Real.exp (-strongMertensFinalDecay corridor * strongMertensScale X) := by
  obtain ⟨C0, hC0, henv⟩ :=
    nativeSmoothedMobius_logNine_envelope_for corridor hsupp hnonneg hmass hdiff
  refine ⟨5 * C0, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (3 : ℝ),
    strongMertensScale_tendsto_atTop.eventually_gt_atTop (Real.log 3),
    strongMertens_balanced_envelopes_eventually corridor] with X hX hr3 hbal
  have heps : strongMertensBalanceEps corridor X ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨strongMertensBalanceEps_pos corridor X,
      strongMertensBalanceEps_lt_one corridor (by linarith)⟩
  have hT : 3 < strongMertensBalanceHeight X := by
    rw [strongMertensBalanceHeight, ← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_lt_exp.mpr hr3
  have h := henv heps hX hT
  exact h.trans <| by
    have hC0nn : 0 ≤ C0 := hC0.le
    calc
      C0 * (strongMertensFarEnvelope (strongMertensBalanceEps corridor X) X
              (strongMertensBalanceHeight X) +
            strongMertensHorizontalEnvelope (strongMertensBalanceEps corridor X) X
              (strongMertensBalanceHeight X) +
            strongMertensVerticalEnvelope corridor (strongMertensBalanceEps corridor X) X
              (strongMertensBalanceHeight X))
        ≤ C0 * (5 * X * Real.exp
            (-strongMertensFinalDecay corridor * strongMertensScale X)) :=
          mul_le_mul_of_nonneg_left hbal hC0nn
      _ = 5 * C0 * X * Real.exp
          (-strongMertensFinalDecay corridor * strongMertensScale X) := by ring

/-- Transfer the balanced smoothed estimate to the sharp real Mertens sum. -/
theorem nativeMertensSharpReal_logNine_subexp_eventually_for
    (corridor : StrongMertensLogNineCorridor)
    {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ f x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), f x / x = 1)
    (hdiff : ContDiff ℝ 1 f) :
    ∃ C > 0, ∀ᶠ X : ℝ in atTop,
      |nativeMertensSharpReal X| ≤
        C * X * Real.exp (-strongMertensFinalDecay corridor * strongMertensScale X) := by
  obtain ⟨Cs, hCs, hsmooth⟩ :=
    nativeSmoothedMobius_logNine_subexp_eventually corridor hsupp hnonneg hmass hdiff
  obtain ⟨Cc, hCc, hclose⟩ := strongMertens_smoothed_close_eps hdiff hsupp hnonneg hmass
  refine ⟨Cc + Cs, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (3 : ℝ),
    strongMertensScale_tendsto_atTop.eventually_ge_atTop (0 : ℝ),
    strongMertens_two_lt_X_mul_balanceEps corridor,
    hsmooth] with X hX hr0 hXeps hs
  let eps := strongMertensBalanceEps corridor X
  have heps0 : 0 < eps := strongMertensBalanceEps_pos corridor X
  have heps1 : eps < 1 := strongMertensBalanceEps_lt_one corridor (by linarith)
  have hc := hclose X hX eps heps0 heps1 hXeps
  let c := strongMertensFinalDecay corridor
  have hcA : c ≤ corridor.A / 8 := by
    dsimp [c, strongMertensFinalDecay]
    exact min_le_left _ _
  have heps_le : eps ≤ Real.exp (-c * strongMertensScale X) := by
    dsimp [eps, strongMertensBalanceEps]
    apply Real.exp_le_exp.mpr
    have hA := corridor.A_mem.1
    nlinarith
  have hclose' :
      ‖nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ)‖ ≤
        Cc * X * Real.exp (-c * strongMertensScale X) := by
    calc
      _ ≤ Cc * eps * X := hc
      _ ≤ Cc * Real.exp (-c * strongMertensScale X) * X := by gcongr
      _ = Cc * X * Real.exp (-c * strongMertensScale X) := by ring
  have htri : ‖(nativeMertensSharpReal X : ℂ)‖ ≤
      ‖nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ)‖ +
        ‖nativeSmoothedMobius f eps X‖ := by
    rw [show (nativeMertensSharpReal X : ℂ) =
      nativeSmoothedMobius f eps X -
        (nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ)) by ring]
    exact norm_sub_le _ _
  have hfinal : ‖(nativeMertensSharpReal X : ℂ)‖ ≤
      (Cc + Cs) * X * Real.exp (-c * strongMertensScale X) :=
    htri.trans <| by
      calc
        ‖nativeSmoothedMobius f eps X - (nativeMertensSharpReal X : ℂ)‖ +
            ‖nativeSmoothedMobius f eps X‖
          ≤ Cc * X * Real.exp (-c * strongMertensScale X) +
            Cs * X * Real.exp (-c * strongMertensScale X) := add_le_add hclose' hs
        _ = (Cc + Cs) * X * Real.exp (-c * strongMertensScale X) := by ring
  simpa [c, Complex.norm_real, Real.norm_eq_abs] using hfinal

end RHLean.Analysis