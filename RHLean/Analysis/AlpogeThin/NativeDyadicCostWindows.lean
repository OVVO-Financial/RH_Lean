import RHLean.Analysis.AlpogeThin.NativeDyadicGzPayment

/-!
# Pay the analytic remainder in the original polynomial size regime

Numerical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean`,
`ModelText.ev_rpow_le_exp`, `cost1`, and `cost2`.
The source cost windows are defined in `SizeWindowBrackets/SChain.lean`.

Only the numerical arguments are reconstructed here. The source's separate
`ModelText.family` consistency model is not used as a geometric witness.
The host is RH_Lean's actual dyadic quotient. Its polynomial cardinal bound,
actual positive heights, density and width regime remain explicit. From
those original conditions, both cost windows and the complete normalized
thin, freezing and three-character charges are proved small. No top-excess
bound, final Gz bound, or completed theta-cover witness is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter
open scoped BigOperators Classical Topology

namespace RHLean.Analysis.AlpogeThin

private theorem dyadic_rpow_le_exp_eventually (c δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, x ^ c ≤ Real.exp (x ^ δ) := by
  have hc : 0 < (|c| + 1)⁻¹ := by positivity
  have hb := (isLittleO_log_rpow_atTop hδ).bound hc
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.norm_of_nonneg (Real.log_nonneg hx1)] at hx
  have hxpos : 0 < x := by linarith
  have h1 : (|c| + 1) * Real.log x ≤ x ^ δ := by
    have h2 : (|c| + 1) * Real.log x ≤
        (|c| + 1) * ((|c| + 1)⁻¹ * x ^ δ) := by gcongr
    rwa [mul_inv_cancel_left₀ (by positivity)] at h2
  rw [Real.rpow_def_of_pos hxpos]
  apply Real.exp_le_exp.2
  have hlog0 := Real.log_nonneg hx1
  have h2 : Real.log x * c ≤ Real.log x * |c| := by
    gcongr
    exact le_abs_self c
  nlinarith [abs_nonneg c]

private theorem dyadic_rpow_add_three (x K : ℝ) (hx : 0 < x) :
    x ^ (K + 3) = x ^ K * x * x * x := by
  rw [show K + 3 = K + 1 + 1 + 1 by ring,
    Real.rpow_add hx, Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one]

/-- Both original cost windows follow uniformly from the genuine host's
polynomial size and the source exponential width scales. -/
theorem nativeDyadicCostWindows_eventually
    (eps K : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ e : ℕ, (2 : ℝ) ^ e ≤ x ^ K →
      ∀ b h : ℝ, Real.exp (x ^ eps) ≤ b → 0 ≤ h →
        h ≤ Real.exp (x ^ (eps / 4)) + 1 →
        4 * (2 : ℝ) ^ e * (x + 1) * Real.exp (-(x ^ (eps / 8))) ≤ 1 / x ∧
        12 * (2 : ℝ) ^ e * (x + 1) * h ≤ b / x := by
  have e1 := dyadic_rpow_le_exp_eventually (K + 3) (eps / 8) (by positivity)
  have e2 := dyadic_rpow_le_exp_eventually (K + 3) (eps / 4) (by positivity)
  have e3 : ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ x ^ (3 * eps / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  filter_upwards [e1, e2, e3, eventually_ge_atTop (48 : ℝ)] with x h1 h2 h3 hx
  intro e hn b h hb _hh hheight
  have hxpos : 0 < x := by linarith
  have hnpos : 0 < (2 : ℝ) ^ e := by positivity
  have hpK : 0 < x ^ K := Real.rpow_pos_of_pos hxpos _
  have hpoly4 : 4 * (2 : ℝ) ^ e * (x + 1) * x ≤ x ^ (K + 3) := by
    rw [dyadic_rpow_add_three x K hxpos]
    have hquad : 4 * (x + 1) ≤ x * x := by nlinarith
    calc
      _ ≤ 4 * x ^ K * (x + 1) * x := by gcongr
      _ = (x ^ K * x) * (4 * (x + 1)) := by ring
      _ ≤ (x ^ K * x) * (x * x) := by gcongr
      _ = _ := by ring
  have hpoly24 : 24 * (2 : ℝ) ^ e * (x + 1) * x ≤ x ^ (K + 3) := by
    rw [dyadic_rpow_add_three x K hxpos]
    have hquad : 24 * (x + 1) ≤ x * x := by nlinarith
    calc
      _ ≤ 24 * x ^ K * (x + 1) * x := by gcongr
      _ = (x ^ K * x) * (24 * (x + 1)) := by ring
      _ ≤ (x ^ K * x) * (x * x) := by gcongr
      _ = _ := by ring
  constructor
  · rw [Real.exp_neg, le_div_iff₀ hxpos]
    calc
      _ = (4 * (2 : ℝ) ^ e * (x + 1) * x) *
          (Real.exp (x ^ (eps / 8)))⁻¹ := by ring
      _ ≤ Real.exp (x ^ (eps / 8)) * (Real.exp (x ^ (eps / 8)))⁻¹ := by
        gcongr
        exact hpoly4.trans h1
      _ = 1 := mul_inv_cancel₀ (Real.exp_pos _).ne'
  · rw [le_div_iff₀ hxpos]
    have hE1 : 1 ≤ Real.exp (x ^ (eps / 4)) :=
      Real.one_le_exp (Real.rpow_nonneg hxpos.le _)
    have hEE : Real.exp (x ^ (eps / 4)) * Real.exp (x ^ (eps / 4)) ≤
        Real.exp (x ^ eps) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have hp : x ^ eps = x ^ (3 * eps / 4) * x ^ (eps / 4) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
      rw [hp]
      nlinarith [Real.rpow_nonneg hxpos.le (eps / 4)]
    calc
      _ ≤ 12 * (2 : ℝ) ^ e * (x + 1) *
          (2 * Real.exp (x ^ (eps / 4))) * x := by
        gcongr
        linarith
      _ = (24 * (2 : ℝ) ^ e * (x + 1) * x) *
          Real.exp (x ^ (eps / 4)) := by ring
      _ ≤ Real.exp (x ^ (eps / 4)) * Real.exp (x ^ (eps / 4)) := by
        gcongr
        exact hpoly24.trans h2
      _ ≤ b := hEE.trans hb

/-- A pointwise form of the original normalized cost payment. The two
cost windows pay the thin and freezing terms by `4/(Delta*x)` in total;
the three actual thick characters cost at most `6*x^(1/2+eps/2)`. -/
theorem nativeDyadicAnalyticRemainder_le_of_costWindows
    (e : ℕ) (TT T2 : Finset (AlpogeNativeDyadicH e))
    (a : AlpogeNativeDyadicH e → ℝ) (b h Amax x eps θ : ℝ)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty)
    (hx : 1 ≤ x) (he : 0 ≤ eps) (he1 : eps ≤ 1)
    (hb : 0 < b) (hh : 0 ≤ h) (hθ : 0 ≤ θ)
    (ha : ∀ t ∈ TT, 0 ≤ a t)
    (hheight : ∀ t ∈ TT, a t / b ≤ x + 1)
    (hmax : Amax / b ≤ x + 1)
    (hthin : 4 * (2 : ℝ) ^ e * (x + 1) * θ ≤ 1 / x)
    (hwidth : 12 * (2 : ℝ) ^ e * (x + 1) * h ≤ b / x) :
    (8 * (2 : ℝ) ^ e - 4 * T2.card) * θ *
        ((∑ t ∈ TT, a t) / TT.card) / (b * (T2.card / (2 : ℝ) ^ e)) +
      4 * h * (Real.log 4 + 2) * (Amax / b) /
        (b * alpogeNativeProjectionDensity T2) +
      (3 / (TT.card : ℝ)) * ∑ t ∈ TT,
        (a t / b) ^ ((1 : ℝ) / 2 + eps / 2) ≤
      4 / (alpogeNativeProjectionDensity T2 * x) +
        6 * x ^ ((1 : ℝ) / 2 + eps / 2) := by
  let n : ℝ := (2 : ℝ) ^ e
  let δ : ℝ := (T2.card : ℝ) / n
  let μ : ℝ := (∑ t ∈ TT, a t) / TT.card
  let α : ℝ := (1 : ℝ) / 2 + eps / 2
  have hn1 : (1 : ℝ) ≤ n := by
    dsimp [n]
    exact one_le_pow₀ (by norm_num)
  have hn : 0 < n := by linarith
  have hT : (0 : ℝ) < TT.card := by exact_mod_cast hTT.card_pos
  have hS : (0 : ℝ) < T2.card := by exact_mod_cast hT2.card_pos
  have hδ : 0 < δ := div_pos hS hn
  have hx0 : 0 < x := by linarith
  have hα0 : 0 ≤ α := by dsimp [α]; linarith
  have hα1 : α ≤ 1 := by dsimp [α]; linarith
  have hdensity : alpogeNativeProjectionDensity T2 = δ := by
    simp only [δ, n, alpogeNativeProjectionDensity, alpogeNativeDyadicH_card,
      Nat.cast_pow, Nat.cast_ofNat]
  have hμ0 : 0 ≤ μ := div_nonneg (Finset.sum_nonneg ha) hT.le
  have hμ : μ ≤ b * (x + 1) := by
    apply (div_le_iff₀ hT).2
    calc
      ∑ t ∈ TT, a t ≤ ∑ _t ∈ TT, b * (x + 1) := by
        apply Finset.sum_le_sum
        intro t ht
        simpa only [mul_comm] using (div_le_iff₀ hb).1 (hheight t ht)
      _ = (b * (x + 1)) * TT.card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hthinNum : (8 * n - 4 * T2.card) * θ * μ ≤ 2 * b / x := by
    calc
      _ ≤ 8 * n * θ * μ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) hθ) hμ0
      _ ≤ 8 * n * θ * (b * (x + 1)) := by gcongr
      _ = 2 * b * (4 * n * (x + 1) * θ) := by ring
      _ ≤ 2 * b * (1 / x) :=
        mul_le_mul_of_nonneg_left hthin (by positivity)
      _ = 2 * b / x := by ring
  have hthinPaid : (8 * n - 4 * T2.card) * θ * μ / (b * δ) ≤
      2 / (δ * x) := by
    calc
      _ ≤ (2 * b / x) / (b * δ) :=
        div_le_div_of_nonneg_right hthinNum (mul_pos hb hδ).le
      _ = _ := by field_simp [hb.ne', hδ.ne', hx0.ne']; ring
  have hC0 : 0 ≤ Real.log 4 + 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  have hC : Real.log 4 + 2 ≤ 6 * n := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hwidthNum : 4 * h * (Real.log 4 + 2) * (Amax / b) ≤ 2 * b / x := by
    calc
      _ ≤ 4 * h * (Real.log 4 + 2) * (x + 1) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
      _ ≤ 4 * h * (6 * n) * (x + 1) := by gcongr
      _ = 2 * (12 * n * (x + 1) * h) := by ring
      _ ≤ 2 * (b / x) := mul_le_mul_of_nonneg_left hwidth (by norm_num)
      _ = 2 * b / x := by ring
  have hwidthPaid : 4 * h * (Real.log 4 + 2) * (Amax / b) / (b * δ) ≤
      2 / (δ * x) := by
    calc
      _ ≤ (2 * b / x) / (b * δ) :=
        div_le_div_of_nonneg_right hwidthNum (mul_pos hb hδ).le
      _ = _ := by field_simp [hb.ne', hδ.ne', hx0.ne']; ring
  have htwice : (2 : ℝ) ^ α ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1
  have hpoint : ∀ t ∈ TT, (a t / b) ^ α ≤ 2 * x ^ α := by
    intro t ht
    calc
      _ ≤ (2 * x) ^ α := Real.rpow_le_rpow (div_nonneg (ha t ht) hb.le)
        (by have := hheight t ht; linarith) hα0
      _ = (2 : ℝ) ^ α * x ^ α := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 2 * x ^ α := mul_le_mul_of_nonneg_right htwice (Real.rpow_nonneg hx0.le _)
  have hthickPaid : (3 / (TT.card : ℝ)) * ∑ t ∈ TT, (a t / b) ^ α ≤ 6 * x ^ α := by
    calc
      _ ≤ (3 / (TT.card : ℝ)) * ∑ _t ∈ TT, 2 * x ^ α :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (by positivity)
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp [hT.ne'] <;> ring
  rw [hdensity]
  change (8 * n - 4 * T2.card) * θ * μ / (b * δ) +
      4 * h * (Real.log 4 + 2) * (Amax / b) / (b * δ) +
      (3 / (TT.card : ℝ)) * ∑ t ∈ TT, (a t / b) ^ α ≤
    4 / (δ * x) + 6 * x ^ α
  linarith

/-- The complete analytic remainder is paid at the critical scale from
the original polynomial host, width and density regime. All quantifiers
are uniform in the actual dyadic exponent and the finite height family. -/
theorem nativeDyadicAnalyticRemainder_eventually
    (eps K : ℝ) (he : 0 < eps) (he1 : eps ≤ 1) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (e : ℕ) (TT T2 : Finset (AlpogeNativeDyadicH e))
        (a : AlpogeNativeDyadicH e → ℝ) (b h Amax : ℝ),
        TT.Nonempty → T2.Nonempty → (2 : ℝ) ^ e ≤ x ^ K →
        Real.exp (x ^ eps) ≤ b → 0 ≤ h → h ≤ Real.exp (x ^ (eps / 4)) + 1 →
        (∀ t ∈ TT, 0 ≤ a t) → (∀ t ∈ TT, a t / b ≤ x + 1) →
        Amax / b ≤ x + 1 → x ^ (-eps) ≤ alpogeNativeProjectionDensity T2 →
        (8 * (2 : ℝ) ^ e - 4 * T2.card) * Real.exp (-(x ^ (eps / 8))) *
            ((∑ t ∈ TT, a t) / TT.card) / (b * (T2.card / (2 : ℝ) ^ e)) +
          4 * h * (Real.log 4 + 2) * (Amax / b) /
            (b * alpogeNativeProjectionDensity T2) +
          (3 / (TT.card : ℝ)) * ∑ t ∈ TT,
            (a t / b) ^ ((1 : ℝ) / 2 + eps / 2) ≤
          x ^ ((1 : ℝ) / 2 + eps) := by
  have hcost := nativeDyadicCostWindows_eventually eps K he
  have hgrow : ∀ᶠ x : ℝ in atTop, (10 : ℝ) ≤ x ^ (eps / 2) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  filter_upwards [hcost, hgrow, eventually_ge_atTop (1 : ℝ)] with x hcost hgrow hx
  intro e TT T2 a b h Amax hTT hT2 hn hb hh hupper ha hheight hmax hdensity
  have hb0 : 0 < b := (Real.exp_pos _).trans_le hb
  have hx0 : 0 < x := by linarith
  obtain ⟨hthin, hwidth⟩ := hcost e hn b h hb hh hupper
  have hpaid := nativeDyadicAnalyticRemainder_le_of_costWindows e TT T2 a b h Amax
    x eps (Real.exp (-(x ^ (eps / 8)))) hTT hT2 hx he.le he1 hb0 hh
    (Real.exp_pos _).le ha hheight hmax hthin hwidth
  have hinv : 1 / x ≤ alpogeNativeProjectionDensity T2 := by
    calc
      _ = x ^ (-1 : ℝ) := by simp only [Real.rpow_neg_one, one_div]
      _ ≤ x ^ (-eps) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ ≤ _ := hdensity
  have hden : 1 ≤ alpogeNativeProjectionDensity T2 * x := (div_le_iff₀ hx0).1 hinv
  have hfour : 4 / (alpogeNativeProjectionDensity T2 * x) ≤ (4 : ℝ) :=
    div_le_self (by norm_num) hden
  have hpow : 1 ≤ x ^ ((1 : ℝ) / 2 + eps / 2) :=
    Real.one_le_rpow hx (by positivity)
  calc
    _ ≤ 4 / (alpogeNativeProjectionDensity T2 * x) +
        6 * x ^ ((1 : ℝ) / 2 + eps / 2) := hpaid
    _ ≤ 10 * x ^ ((1 : ℝ) / 2 + eps / 2) := by linarith
    _ ≤ x ^ (eps / 2) * x ^ ((1 : ℝ) / 2 + eps / 2) :=
      mul_le_mul_of_nonneg_right hgrow (Real.rpow_nonneg hx0.le _)
    _ = x ^ ((1 : ℝ) / 2 + eps) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring

/-- The original size regime pays every analytic scalar term on the same
selected prime pair. The literal complete physical top excess is now the
only unbounded source term in this inequality. Its genuine geometric
construction, and the realization of these size conditions by that same
family, remain separate obligations. -/
theorem nativeSelectedDyadicGzPayment_of_size_regime
    (eps A K : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) (hA : 1 ≤ A) :
    ∃ Y₀ x₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∃ (q d : ℕ) (hG : UpperTheory.Top.PairGood 1 eps Y (Y ^ A) q d),
        letI : Fact q.Prime := ⟨hG.pair.q_prime⟩
        letI : Fact d.Prime := ⟨hG.pair.d_prime⟩
        ∀ x : ℝ, x₀ ≤ x → ∀ e : ℕ,
          (2 : ℝ) ^ e ≤ x ^ K →
          Real.log (alpogeNativeHostN e q d) ≤
            2 * x ^ (eps / 5) * Real.log x ^ 2 →
          let r := alpogeNativeRecMap e q d
          let D := alpogeNativeHostData e q d
          let ell := alpogeNativeCanonicalHostEll r
          ∀ (m : ℕ) (TT T2 : Finset (AlpogeNativeDyadicH e)),
            TT.Nonempty → T2.Nonempty → 0 < m →
            ∀ (a : AlpogeNativeDyadicH e → ℝ) (b h Amax beta : ℝ)
              (w : AlpogeNativeDyadicH e → Fin m →
                AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
              0 < beta → beta ≤ b → 0 ≤ h →
              Real.exp (x ^ eps) ≤ b → h ≤ Real.exp (x ^ (eps / 4)) + 1 →
              (∀ t ∈ TT, 0 < a t) → (∀ t ∈ TT, a t ≤ Amax) →
              Amax / b ≤ x + 1 →
              x ^ (-eps) ≤ alpogeNativeProjectionDensity T2 →
              (∀ u j ρ, alpogeNativeInPhi ρ → beta ≤ w u j ρ) →
              (∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
                b ≤ w u j ρ ∧ w u j ρ ≤ b + h) →
              (∀ (u : (⊤ : AddSubgroup (AlpogeNativeDyadicH e))) t,
                t ∈ TT → ∀ (j : Fin m) g,
                g ∈ (Finset.univ.filter
                    (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
                      ¬ alpogeNativeInPhi g)) \
                      alpogeNativeProjectionThickColours T2 u t →
                  Real.exp (x ^ (eps / 3)) / 3 ≤
                    a t / w u j (alpogeNativePartner t g)) →
              (∀ t ∈ TT, a t / b ∈ Set.Icc Y (Y ^ A)) →
              (1 / (TT.card : ℝ)) * ∑ t ∈ TT,
                  alpogeNativeGzArithmetic (a t / b) ≤
                alpogeNativePhysicalSubgroupTopExcess
                    (⊤ : AddSubgroup (AlpogeNativeDyadicH e))
                    D.inertia D.frob ell (Nat.ceil (Amax / beta)) TT a w /
                  alpogeNativeProjectionDivisor TT T2 m b +
                x ^ ((1 : ℝ) / 2 + eps) := by
  obtain ⟨Y₀, x₀, hpair⟩ := nativeSelectedDyadicGzPayment eps A he he52 hA
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1
    (nativeDyadicAnalyticRemainder_eventually eps K he (by linarith))
  refine ⟨Y₀, max x₀ x₁, fun Y hY => ?_⟩
  obtain ⟨q, d, hG, hpaid⟩ := hpair Y hY
  refine ⟨q, d, hG, ?_⟩
  let : Fact q.Prime := ⟨hG.pair.q_prime⟩
  let : Fact d.Prime := ⟨hG.pair.d_prime⟩
  intro x hx e hn hlog
  dsimp only
  intro m TT T2 hTT hT2 hm a b h Amax beta w
    hbeta hbetab hh hb hupper ha hAmax hmax hdensity hwbeta hwthick hwthin hwindow
  have hb0 : 0 < b := hbeta.trans_le hbetab
  have hheight : ∀ t ∈ TT, a t / b ≤ x + 1 := fun t ht =>
    (div_le_div_of_nonneg_right (hAmax t ht) hb0.le).trans hmax
  have hnum := hx₁ x ((le_max_right _ _).trans hx) e TT T2 a b h Amax
    hTT hT2 hn hb hh hupper (fun t ht => (ha t ht).le) hheight hmax hdensity
  have hsource := hpaid x ((le_max_left _ _).trans hx) e hlog m TT T2 hTT hT2 hm
    a b h Amax beta w hbeta hbetab hh ha hAmax hwbeta hwthick hwthin hwindow
  linarith only [hsource, hnum]

end RHLean.Analysis.AlpogeThin
