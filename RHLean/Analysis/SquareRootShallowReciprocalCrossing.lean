import Mathlib
import RHLean.Analysis.NativePNTTransfer
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Proof.LargePrimeTerminalFlipLayers

/-!
# An eventual shallow reciprocal-depth crossing

The truncated upper-middle packet has a stronger crossing property than the
initial logarithmic target suggests.  Its fixed-depth PNT coefficient has an
exact negative rational certificate at depth `18800`.  Consequently the packet
itself is eventually positive at that fixed depth, while its first layer is
always negative.

Taking the first nonnegative depth therefore gives a genuine sign crossing at
some `K ≤ 18800`.  Since every fixed constant is eventually bounded by
`log R`, this implies the requested `O(log R)` crossing theorem.

The numerical ingredient below is a proposition checked by `native_decide`.
It unfolds the ordinary Möbius function and rational arithmetic, so no decimal
approximation or externally generated data enters the proof.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Analysis

/-! ## Exact finite coefficient certificate -/

/-- Rational Abel-boundary form of the fixed-depth reciprocal coefficient.

This form is computationally linear in the depth, unlike recomputing every
Mertens prefix in the weighted-sum form. -/
def squareRootPacketReciprocalBoundaryRat (K : ℕ) : ℚ :=
  (∑ d ∈ Finset.Icc 1 K, ((μ d : ℤ) : ℚ) / (d : ℚ)) -
    (squareRootMertensInt K : ℚ) / ((K + 1 : ℕ) : ℚ)

/-- Integer Mertens prefixes advance by the next Möbius value. -/
theorem squareRootMertensInt_succ (K : ℕ) :
    squareRootMertensInt (K + 1) =
      squareRootMertensInt K + μ (K + 1) := by
  unfold squareRootMertensInt
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]

/-- Rational summation by parts identifies the weighted reciprocal coefficient
with its efficient Möbius-boundary form. -/
theorem squareRootPacketReciprocalWeightRat_eq_boundary (K : ℕ) :
    (∑ d ∈ Finset.Icc 1 K,
        (squareRootMertensInt d : ℚ) *
          ((1 : ℚ) / (d : ℚ) - (1 : ℚ) / ((d + 1 : ℕ) : ℚ))) =
      squareRootPacketReciprocalBoundaryRat K := by
  unfold squareRootPacketReciprocalBoundaryRat
  induction K with
  | zero => simp [squareRootMertensInt]
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih,
        squareRootMertensInt_succ]
      push_cast
      ring

/-- Exact certificate: the fixed-depth coefficient at `18800` is negative. -/
theorem squareRootPacketReciprocalBoundaryRat_18800_neg :
    squareRootPacketReciprocalBoundaryRat 18800 < 0 := by
  native_decide

/-- Real form of the certified sign, ready for the PNT limit. -/
theorem squareRootPacketReciprocalWeightReal_18800_neg :
    (∑ d ∈ Finset.Icc 1 18800,
        (squareRootMertensInt d : ℝ) *
          ((1 : ℝ) / (d : ℝ) - (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) < 0 := by
  have hcast : (squareRootPacketReciprocalBoundaryRat 18800 : ℝ) < 0 := by
    exact_mod_cast squareRootPacketReciprocalBoundaryRat_18800_neg
  rw [← squareRootPacketReciprocalWeightRat_eq_boundary] at hcast
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_sub, Rat.cast_div,
    Rat.cast_one, Rat.cast_intCast, Rat.cast_natCast] using hcast

/-! ## Fixed-dilation consequences of the native PNT -/

/-- The square endpoint `R^2 - 1` tends to infinity. -/
theorem squareRootEndpoint_tendsto_atTop :
    Tendsto squareRootEndpoint atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  filter_upwards [eventually_ge_atTop (max 2 B)] with R hR
  have hR2 : 2 ≤ R := le_trans (le_max_left 2 B) hR
  have hBR : B ≤ R := le_trans (le_max_right 2 B) hR
  have hsq : R + 1 ≤ R ^ 2 := by
    calc
      R + 1 ≤ R + R := Nat.add_le_add_left (by omega : 1 ≤ R) R
      _ = 2 * R := by omega
      _ ≤ R * R := Nat.mul_le_mul_right R hR2
      _ = R ^ 2 := by ring
  unfold squareRootEndpoint
  omega

/-- Natural division by a fixed positive denominator has the expected real
ratio. -/
theorem natDiv_cast_div_cast_tendsto
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop
      (𝓝 ((1 : ℝ) / (d : ℝ))) := by
  have hscaled : Tendsto (fun N : ℕ => (N : ℝ) / (d : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_div_const (by exact_mod_cast hd))
  have hequiv := Asymptotics.isEquivalent_nat_floor.comp_tendsto hscaled
  have hequiv' : Asymptotics.IsEquivalent atTop
      (fun N : ℕ => ((N / d : ℕ) : ℝ))
      (fun N : ℕ => (N : ℝ) / (d : ℝ)) := by
    simpa [Function.comp_def, Nat.floor_div_eq_div] using hequiv
  have hden : ∀ᶠ N : ℕ in atTop, (N : ℝ) / (d : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    positivity
  have hratio :
      Tendsto
        (fun N : ℕ =>
          ((N / d : ℕ) : ℝ) / ((N : ℝ) / (d : ℝ)))
        atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hden).1 hequiv'
  have hmul := hratio.mul_const ((1 : ℝ) / (d : ℝ))
  have heq :
      (fun N : ℕ =>
        ((N / d : ℕ) : ℝ) / ((N : ℝ) / (d : ℝ)) *
          ((1 : ℝ) / (d : ℝ))) =ᶠ[atTop]
        (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  simpa using hmul.congr' heq

/-- The logarithms of `N/d` and `N` are asymptotically equal for fixed `d`. -/
theorem log_natDiv_div_log_tendsto_one
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun N : ℕ =>
        Real.log ((N / d : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  have hratio := natDiv_cast_div_cast_tendsto d hd
  have hc : (0 : ℝ) < (1 : ℝ) / (d : ℝ) := by positivity
  have hlogRatio :
      Tendsto
        (fun N : ℕ =>
          Real.log (((N / d : ℕ) : ℝ) / (N : ℝ)))
        atTop (𝓝 (Real.log ((1 : ℝ) / (d : ℝ)))) :=
    (Real.continuousAt_log hc.ne').tendsto.comp hratio
  have hdiff :
      Tendsto
        (fun N : ℕ =>
          Real.log ((N / d : ℕ) : ℝ) - Real.log (N : ℝ))
        atTop (𝓝 (Real.log ((1 : ℝ) / (d : ℝ)))) := by
    apply hlogRatio.congr'
    filter_upwards [eventually_ge_atTop (2 * d)] with N hN
    have hNpos : 0 < N := by omega
    have hdivpos : 0 < N / d :=
      (Nat.one_le_div_iff hd).2 (by omega)
    rw [Real.log_div (by positivity) (by positivity)]
  have hlogTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := hdiff.div_atTop hlogTop
  have hadd := hsmall.add_const 1
  have heq :
      (fun N : ℕ =>
        (Real.log ((N / d : ℕ) : ℝ) - Real.log (N : ℝ)) /
            Real.log (N : ℝ) + 1) =ᶠ[atTop]
        (fun N : ℕ =>
          Real.log ((N / d : ℕ) : ℝ) / Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog0 : Real.log (N : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast hN))
    field_simp
    ring
  simpa using hadd.congr' heq

/-- Native PNT at a fixed reciprocal dilation, normalized at the undilated
endpoint. -/
theorem nativePrimeCounting_natDiv_mul_log_div_tendsto
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun N : ℕ =>
        (Nat.primeCounting (N / d) : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 ((1 : ℝ) / (d : ℝ))) := by
  have hdivTop : Tendsto (fun N : ℕ => N / d) atTop atTop :=
    Nat.tendsto_div_const_atTop hd.ne'
  have hpnt := nativePrimeNumberTheorem.comp hdivTop
  have hratio := natDiv_cast_div_cast_tendsto d hd
  have hlog := log_natDiv_div_log_tendsto_one d hd
  have hlogInv := hlog.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hprod := (hpnt.mul hratio).mul hlogInv
  have heq :
      (fun N : ℕ =>
        (((Nat.primeCounting (N / d) : ℝ) *
              Real.log ((N / d : ℕ) : ℝ) /
                ((N / d : ℕ) : ℝ)) *
            (((N / d : ℕ) : ℝ) / (N : ℝ))) *
          (Real.log ((N / d : ℕ) : ℝ) /
            Real.log (N : ℝ))⁻¹) =ᶠ[atTop]
        (fun N : ℕ =>
          (Nat.primeCounting (N / d) : ℝ) * Real.log (N : ℝ) /
            (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop (max 2 (2 * d))] with N hN
    have hN2 : 2 ≤ N := (le_max_left 2 (2 * d)).trans hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hdiv2 : 2 ≤ N / d := by
      apply (Nat.le_div_iff_mul_le hd).2
      omega
    have hdiv0 : ((N / d : ℕ) : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log ((N / d : ℕ) : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast hdiv2))
    field_simp
  simpa [Function.comp_def] using hprod.congr' heq

/-- The same fixed-dilation PNT limit along the square endpoints. -/
theorem nativePrimeCounting_squareRootEndpoint_div_mul_log_div_tendsto
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun R : ℕ =>
        (Nat.primeCounting (squareRootEndpoint R / d) : ℝ) *
          Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ))
      atTop (𝓝 ((1 : ℝ) / (d : ℝ))) := by
  simpa [Function.comp_def] using
    (nativePrimeCounting_natDiv_mul_log_div_tendsto d hd).comp
      squareRootEndpoint_tendsto_atTop

/-! ## Reciprocal layers and the fixed packet -/

/-- At a fixed depth below the root, a reciprocal layer is exactly the
difference of the two ordinary prime counts at its reciprocal endpoints. -/
theorem squareRootReciprocalPrimeLayerCard_add_primeCounting
    {R d : ℕ} (hR : 1 ≤ R) (hd : 1 ≤ d) (hdR : d + 1 < R) :
    squareRootReciprocalPrimeLayerCard R d +
        Nat.primeCounting (squareRootEndpoint R / (d + 1)) =
      Nat.primeCounting (squareRootEndpoint R / d) := by
  have htop : squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R hR
  have hdSupport :
      d + 1 ∈ primeSieveQuotientSupport R (squareRootEndpoint R) := by
    unfold primeSieveQuotientSupport
    rw [htop]
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hRle : R ≤ squareRootEndpoint R / (d + 1) :=
    (lt_div_of_mem_primeSieveQuotientSupport hdSupport).le
  have hmono :
      squareRootEndpoint R / (d + 1) ≤ squareRootEndpoint R / d :=
    Nat.div_le_div_left (by omega) (by omega)
  unfold squareRootReciprocalPrimeLayerCard primeSieveReciprocalInterval
    primeSieveReciprocalLower primeSieveReciprocalUpper
  rw [max_eq_right hRle]
  exact primeCard_Ioc_add_primeCounting_eq hmono

/-- One fixed reciprocal layer has limiting density `1/d - 1/(d+1)` under
the square-endpoint PNT normalization. -/
theorem squareRootReciprocalPrimeLayerCard_mul_log_div_tendsto
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun R : ℕ =>
        (squareRootReciprocalPrimeLayerCard R d : ℝ) *
          Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ))
      atTop
      (𝓝 ((1 : ℝ) / (d : ℝ) -
        (1 : ℝ) / ((d + 1 : ℕ) : ℝ))) := by
  have hu := nativePrimeCounting_squareRootEndpoint_div_mul_log_div_tendsto d hd
  have hl := nativePrimeCounting_squareRootEndpoint_div_mul_log_div_tendsto
    (d + 1) (by omega)
  have hdiff := hu.sub hl
  apply hdiff.congr'
  filter_upwards [eventually_ge_atTop (d + 2)] with R hR
  have hadd := squareRootReciprocalPrimeLayerCard_add_primeCounting
    (R := R) (d := d) (by omega) (by omega) (by omega)
  have hreal :
      (squareRootReciprocalPrimeLayerCard R d : ℝ) +
          (Nat.primeCounting (squareRootEndpoint R / (d + 1)) : ℝ) =
        (Nat.primeCounting (squareRootEndpoint R / d) : ℝ) := by
    exact_mod_cast hadd
  rw [← hreal]
  ring

/-- For every fixed `K`, the normalized packet tends to the negative of its
reciprocal Mertens coefficient. -/
theorem squareRootTruncatedUpperMiddlePacketInt_mul_log_div_tendsto
    (K : ℕ) :
    Tendsto
      (fun R : ℕ =>
        (squareRootTruncatedUpperMiddlePacketInt R K : ℝ) *
          Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ))
      atTop
      (𝓝 (-∑ d ∈ Finset.Icc 1 K,
        (squareRootMertensInt d : ℝ) *
          ((1 : ℝ) / (d : ℝ) -
            (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
  have hsum :
      Tendsto
        (fun R : ℕ => ∑ d ∈ Finset.Icc 1 K,
          (-(squareRootMertensInt d : ℝ)) *
            ((squareRootReciprocalPrimeLayerCard R d : ℝ) *
              Real.log (squareRootEndpoint R : ℝ) /
                (squareRootEndpoint R : ℝ)))
        atTop
        (𝓝 (∑ d ∈ Finset.Icc 1 K,
          (-(squareRootMertensInt d : ℝ)) *
            ((1 : ℝ) / (d : ℝ) -
              (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
    apply tendsto_finset_sum
    intro d hdMem
    have hd : 0 < d := (Finset.mem_Icc.mp hdMem).1
    exact tendsto_const_nhds.mul
      (squareRootReciprocalPrimeLayerCard_mul_log_div_tendsto d hd)
  have hsum' :
      Tendsto
        (fun R : ℕ => ∑ d ∈ Finset.Icc 1 K,
          (-(squareRootMertensInt d : ℝ)) *
            ((squareRootReciprocalPrimeLayerCard R d : ℝ) *
              Real.log (squareRootEndpoint R : ℝ) /
                (squareRootEndpoint R : ℝ)))
        atTop
        (𝓝 (-∑ d ∈ Finset.Icc 1 K,
          (squareRootMertensInt d : ℝ) *
            ((1 : ℝ) / (d : ℝ) -
              (1 : ℝ) / ((d + 1 : ℕ) : ℝ)))) := by
    simpa only [neg_mul, Finset.sum_neg_distrib] using hsum
  refine hsum'.congr' ?_
  filter_upwards with R
  unfold squareRootTruncatedUpperMiddlePacketInt
  push_cast
  calc
    (∑ d ∈ Finset.Icc 1 K,
        -(squareRootMertensInt d : ℝ) *
          ((squareRootReciprocalPrimeLayerCard R d : ℝ) *
            Real.log (squareRootEndpoint R : ℝ) /
              (squareRootEndpoint R : ℝ))) =
        ∑ d ∈ Finset.Icc 1 K,
          (Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ)) *
              (-((squareRootReciprocalPrimeLayerCard R d : ℝ) *
                (squareRootMertensInt d : ℝ))) := by
          apply Finset.sum_congr rfl
          intro d _hd
          ring
    _ = (Real.log (squareRootEndpoint R : ℝ) /
          (squareRootEndpoint R : ℝ)) *
        ∑ d ∈ Finset.Icc 1 K,
          (-((squareRootReciprocalPrimeLayerCard R d : ℝ) *
            (squareRootMertensInt d : ℝ))) := by
          rw [Finset.mul_sum]
    _ = (-∑ d ∈ Finset.Icc 1 K,
          (squareRootReciprocalPrimeLayerCard R d : ℝ) *
            (squareRootMertensInt d : ℝ)) *
        Real.log (squareRootEndpoint R : ℝ) /
          (squareRootEndpoint R : ℝ) := by
          rw [Finset.sum_neg_distrib]
          ring

/-- The exact negative coefficient at depth `18800` forces the packet to be
strictly positive there for every sufficiently large square endpoint. -/
theorem eventually_squareRootTruncatedUpperMiddlePacketInt_18800_pos :
    ∀ᶠ R : ℕ in atTop,
      0 < squareRootTruncatedUpperMiddlePacketInt R 18800 := by
  let S : ℝ :=
    ∑ d ∈ Finset.Icc 1 18800,
      (squareRootMertensInt d : ℝ) *
        ((1 : ℝ) / (d : ℝ) -
          (1 : ℝ) / ((d + 1 : ℕ) : ℝ))
  have hS : S < 0 := by
    simpa [S] using squareRootPacketReciprocalWeightReal_18800_neg
  have hlimit :
      Tendsto
        (fun R : ℕ =>
          (squareRootTruncatedUpperMiddlePacketInt R 18800 : ℝ) *
            Real.log (squareRootEndpoint R : ℝ) /
              (squareRootEndpoint R : ℝ))
        atTop (𝓝 (-S)) := by
    simpa [S] using
      squareRootTruncatedUpperMiddlePacketInt_mul_log_div_tendsto 18800
  have hnormPos :
      ∀ᶠ R : ℕ in atTop,
        0 < (squareRootTruncatedUpperMiddlePacketInt R 18800 : ℝ) *
          Real.log (squareRootEndpoint R : ℝ) /
            (squareRootEndpoint R : ℝ) :=
    (tendsto_order.1 hlimit).1 0 (by linarith)
  filter_upwards [eventually_ge_atTop 3, hnormPos] with R hR hpos
  have hX : 1 < squareRootEndpoint R := by
    have h9 : 9 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  have hlog : 0 < Real.log (squareRootEndpoint R : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hXreal : 0 < (squareRootEndpoint R : ℝ) := by positivity
  have hmul :
      0 < (squareRootTruncatedUpperMiddlePacketInt R 18800 : ℝ) *
        Real.log (squareRootEndpoint R : ℝ) :=
    ((div_pos_iff.mp hpos).resolve_right
      (fun hneg => (not_lt_of_ge hXreal.le) hneg.2)).1
  have hcast : 0 < (squareRootTruncatedUpperMiddlePacketInt R 18800 : ℝ) := by
    exact ((mul_pos_iff.mp hmul).resolve_right
      (fun hneg => (not_lt_of_ge hlog.le) hneg.2)).1
  exact_mod_cast hcast

/-! ## First-crossing extraction -/

/-- The first reciprocal layer is the nonempty same-sign top block, hence the
integer packet is strictly negative there. -/
theorem squareRootTruncatedUpperMiddlePacketInt_one_neg
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTruncatedUpperMiddlePacketInt R 1 < 0 := by
  have hpow : R ^ 2 = R * R := by ring
  have hge : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
  have hhalf : R ≤ squareRootEndpoint R / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    unfold squareRootEndpoint
    omega
  have hcard :
      squareRootReciprocalPrimeLayerCard R 1 =
        (squareRootTopFibrePrimes R).card := by
    simp [squareRootReciprocalPrimeLayerCard, primeSieveReciprocalInterval,
      primeSieveReciprocalLower, primeSieveReciprocalUpper,
      squareRootTopFibrePrimes, hhalf]
  have hnonempty := one_le_card_squareRootTopFibrePrimes R (by omega)
  have hM1 : squareRootMertensInt 1 = 1 := by
    simp [squareRootMertensInt]
  unfold squareRootTruncatedUpperMiddlePacketInt
  rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide]
  simp [hM1, hcard]
  exact Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hnonempty)

/-- Eventually the packet has a genuine crossing at a depth bounded by the
absolute constant `18800`. -/
theorem eventually_exists_squareRootPacketCrossesAt_le_18800 :
    ∀ᶠ R : ℕ in atTop,
      ∃ K : ℕ, K ≤ 18800 ∧ SquareRootPacketCrossesAt R K := by
  filter_upwards [eventually_ge_atTop 3,
    eventually_squareRootTruncatedUpperMiddlePacketInt_18800_pos]
      with R hR htop
  let P : ℕ → Prop := fun K =>
    1 ≤ K ∧ K ≤ 18800 ∧
      0 ≤ squareRootTruncatedUpperMiddlePacketInt R K
  have hex : ∃ K, P K := ⟨18800, by norm_num, le_rfl, htop.le⟩
  let K := Nat.find hex
  have hK : P K := Nat.find_spec hex
  have hKgt : 1 < K := by
    by_contra hnot
    have hK1 : K = 1 := by omega
    have hbad := hK.2.2
    rw [hK1] at hbad
    linarith [squareRootTruncatedUpperMiddlePacketInt_one_neg R hR]
  have hprev : squareRootTruncatedUpperMiddlePacketInt R (K - 1) < 0 := by
    by_contra hnot
    have hprevNonneg :
        0 ≤ squareRootTruncatedUpperMiddlePacketInt R (K - 1) :=
      le_of_not_gt hnot
    have hpredP : P (K - 1) := ⟨by omega, (Nat.sub_le K 1).trans hK.2.1,
      hprevNonneg⟩
    have hmin := Nat.find_min' hex hpredP
    have : K ≤ K - 1 := by simpa [K] using hmin
    omega
  exact ⟨K, hK.2.1, hK.1, hprev, hK.2.2⟩

/-- The exact eventual theorem requested by the shallow-depth architecture.
The proof actually supplies a constant-depth crossing. -/
theorem squareRootPacket_eventual_log_crossing :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ R : ℕ, R₀ ≤ R →
        ∃ K : ℕ,
          K < R ∧
          (K : ℝ) ≤ C * Real.log (R : ℝ) ∧
          squareRootTruncatedUpperMiddlePacketInt R (K - 1) < 0 ∧
          0 ≤ squareRootTruncatedUpperMiddlePacketInt R K := by
  have hlogTop : Tendsto (fun R : ℕ => Real.log (R : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ R : ℕ in atTop, (18800 : ℝ) ≤ Real.log (R : ℝ) :=
    hlogTop.eventually_ge_atTop 18800
  have hcross : ∀ᶠ R : ℕ in atTop,
      ∃ K : ℕ, K ≤ 18800 ∧ SquareRootPacketCrossesAt R K :=
    eventually_exists_squareRootPacketCrossesAt_le_18800
  have hall : ∀ᶠ R : ℕ in atTop,
      18800 < R ∧ (18800 : ℝ) ≤ Real.log (R : ℝ) ∧
        ∃ K : ℕ, K ≤ 18800 ∧ SquareRootPacketCrossesAt R K := by
    filter_upwards [eventually_gt_atTop 18800, hlogLarge, hcross]
      with R hR hlog hK
    exact ⟨hR, hlog, hK⟩
  rw [eventually_atTop] at hall
  rcases hall with ⟨R₀, hR₀⟩
  refine ⟨1, by norm_num, R₀, ?_⟩
  intro R hR
  rcases hR₀ R hR with ⟨h18800R, hlog, K, hK18800, hcrossK⟩
  have hKreal : (K : ℝ) ≤ 18800 := by exact_mod_cast hK18800
  have hKlog : (K : ℝ) ≤ Real.log (R : ℝ) := hKreal.trans hlog
  exact ⟨K, hK18800.trans_lt h18800R,
    by simpa using hKlog,
    hcrossK.2.1, hcrossK.2.2⟩

end RHLean.Proof
