import RHLean.Analysis.AlpogeNativeZetaBalance

/-!
# The zeta window witness and its consumer

`AlpogeNativeZetaWindowWitness ε x C` is the minimum-cut interface at one
scale `x`: finite host data (field 1) with the full host as averaging
subgroup, eight arithmetic fields (2-9), and one geometric field (10) bounding
the full-host mean of the physical ASK minus MAIN by
`x ^ (C * ε) * alpogeNativeErrorBracket`. The consumer
`alpogeNativeGz_le_of_witness` turns a witness at a large scale into
`alpogeNativeGzArithmetic x ≤ x ^ (1 / 2 + (C + 3) * ε)`.

Status of the fields. This file constructs no witness.

* Field 10 (`top`) is the open geometric estimate.
* Field 9 (`excluded`) asks square-root size for the at most three
  nonprincipal characters trivial on the host. For a physical host this is of
  the strength of the Riemann hypothesis for those three characters at the
  single scale `x`.
* Field 6 (`thin`) is a prime number theorem with remainder for every
  character of the host beyond `X' / 3`.
* Fields 2-5, 7 and 8 are size relations between the chosen parameters.

Alpoge's `HostFactsS` and the identification of `ell` with a logarithmic
derivative are not fields: the native identity `ASK - MAIN = De` and the
movement bound hold for every Frobenius/inertia assignment and every `ell`.
They constrain a supplier of fields 6, 9 and 10, not this consumer. There is
no `SizeData₂` ledger.

Differences from the source interface: the thick cost window is the native
Chebyshev freezing bill `4 * h * (log 4 + 2) * (x + 1) ≤ b / x` (no host
factor), the cutoff also asks `x + 1 ≤ N`, the `ell` bound is `x ^ ε`, and
the movement constant is the explicit `alpogeNativeMoveConstant`.

Blueprint: CocoSgt/riemann-hypothesis-lean at
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Formalism/SizeWindowBrackets/{GrowthBoundGivesRiemannHypothesis, SChain,
ErrorFormsWeakWindowsFalse}.lean and
Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean.
-/

noncomputable section
open scoped BigOperators Classical

namespace RHLean.Analysis

section ErrorBracket

/-- Native copy of Alpoge's `errorBracketSizeWindows`. -/
def alpogeNativeErrorBracket (x ε : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : ℝ :=
  (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k) +
    m * ((2 * n) * m * b * x ^ ε +
      nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))

/-- The bracket is the geometric error bracket at `e = x ^ ε`. -/
theorem alpogeNativeErrorBracket_eq_geometric
    (x ε : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) (hx : 0 ≤ x) :
    alpogeNativeErrorBracket x ε n nT nT2 m b k aE =
      alpogeNativeGeometricErrorBracket nT nT2 n m b k aE (x ^ ε) := by
  unfold alpogeNativeErrorBracket alpogeNativeGeometricErrorBracket
  rw [Real.rpow_neg hx, ← div_eq_mul_inv]

/-- The exact `E / Q` identity for the bracket under the earned divisor. -/
theorem alpogeNativeErrorBracket_div_projectionDivisor
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (TT T2 : Finset H) (m : ℕ) (b k aE x ε : ℝ)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m)
    (hb : 0 < b) (hx : 0 ≤ x) :
    alpogeNativeErrorBracket x ε (Fintype.card H) TT.card T2.card m b k aE /
        alpogeNativeProjectionDivisor TT T2 m b =
      alpogeNativeNormalizedGeometricCosts
        TT.card (alpogeNativeProjectionDensity T2) (Fintype.card H) m b k aE
        (x ^ ε) := by
  rw [alpogeNativeErrorBracket_eq_geometric x ε _ _ _ _ b k aE hx]
  exact alpogeNativeGeometricErrorBracket_div_projectionDivisor TT T2 m b k aE
    (x ^ ε) hTT hT2 hm hb

end ErrorBracket

section SizeAbsorption

/-- Native `RestSize` together with the two multiplicity relations that
Alpoge's `SizeWindows` adds. All are relations between chosen parameters. -/
structure AlpogeNativeRestSize (ε x : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) :
    Prop where
  b_pos : 0 < b
  aE_le : aE ≤ 2 * x * b
  top_count : x ^ (-(ε / 8)) * n / 2 ≤ nT
  thick_density : x ^ (-ε) ≤ (nT2 : ℝ) / n
  mult_lower : x ^ ((1 : ℝ) / 2 - ε) ≤ m
  mult_upper : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)
  k_lower : x * m ≤ k
  k_upper : k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)

theorem alpogeNativeSize_topCount {x ε n nT : ℝ} (hx0 : 0 < x)
    (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) :
    n ≤ 2 * nT * x ^ (ε / 8) := by
  have h8 : 0 < x ^ (ε / 8) := Real.rpow_pos_of_pos hx0 _
  have hinv : x ^ (-(ε / 8)) * x ^ (ε / 8) = 1 := by
    rw [← Real.rpow_add hx0]
    simp
  have h := mul_le_mul_of_nonneg_right hnT h8.le
  have e : x ^ (-(ε / 8)) * n / 2 * x ^ (ε / 8) = n / 2 := by
    calc
      x ^ (-(ε / 8)) * n / 2 * x ^ (ε / 8) =
          (x ^ (-(ε / 8)) * x ^ (ε / 8)) * n / 2 := by ring
      _ = n / 2 := by rw [hinv]; ring
  linarith

/-- First bracket term: `T * aE ≤ 2 * Y * (T * m * b)`. -/
theorem alpogeNativeSize_term1 {x X Y m nT aE b : ℝ}
    (hxX : x ≤ X * m) (hXY : X ≤ Y) (hnT0 : 0 ≤ nT) (hm0 : 0 ≤ m)
    (hb : 0 ≤ b) (haE : aE ≤ 2 * x * b) :
    nT * aE ≤ 2 * Y * (nT * m * b) := by
  have h1 : nT * aE ≤ nT * (2 * x * b) := mul_le_mul_of_nonneg_left haE hnT0
  have hxY : x ≤ Y * m := hxX.trans (mul_le_mul_of_nonneg_right hXY hm0)
  have h2 : 2 * x * b ≤ 2 * (Y * m) * b := by nlinarith
  have h3 : nT * (2 * x * b) ≤ nT * (2 * (Y * m) * b) :=
    mul_le_mul_of_nonneg_left h2 hnT0
  calc
    nT * aE ≤ nT * (2 * (Y * m) * b) := h1.trans h3
    _ = 2 * Y * (nT * m * b) := by ring

/-- Second bracket term: `T * aE * (m ^ 2 / k) ≤ 2 * Y * (T * m * b)`. -/
theorem alpogeNativeSize_term2 {x Y m nT aE b k : ℝ}
    (hx0 : 0 < x) (hY1 : 1 ≤ Y) (hnT0 : 0 ≤ nT) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hk0 : 0 < k) (hk1 : x * m ≤ k) (haE : aE ≤ 2 * x * b) :
    nT * aE * (m ^ 2 / k) ≤ 2 * Y * (nT * m * b) := by
  have hmk : m ^ 2 / k ≤ m / x := by
    rw [div_le_div_iff₀ hk0 hx0]
    nlinarith
  have h1 : nT * aE * (m ^ 2 / k) ≤ nT * (2 * x * b) * (m / x) :=
    mul_le_mul (mul_le_mul_of_nonneg_left haE hnT0) hmk (by positivity)
      (by positivity)
  have h2 : nT * (2 * x * b) * (m / x) = 2 * (nT * m * b) := by field_simp
  have hQ : 0 ≤ nT * m * b := by positivity
  have h3 : 2 * (nT * m * b) ≤ 2 * Y * (nT * m * b) := by nlinarith
  linarith

/-- Third bracket term, the `2 * n * m * b * x ^ ε` congruence cost. -/
theorem alpogeNativeSize_term3 {x ε Y m n nT b : ℝ}
    (hx0 : 0 < x) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8))
    (hm2 : m ≤ x ^ ((1 : ℝ) / 2 + ε / 2))
    (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 ≤ n) :
    m * ((2 * n) * m * b * x ^ ε) ≤ 4 * Y * (nT * m * b) := by
  have pe := Real.rpow_pos_of_pos hx0 ε
  have p8 := Real.rpow_pos_of_pos hx0 (ε / 8)
  have hY' : x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε * x ^ (ε / 8) = Y := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, hY]
    ring_nf
  have hmY : m * x ^ ε * x ^ (ε / 8) ≤ Y := by
    rw [← hY']
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hm2 pe.le) p8.le
  have hnT' := alpogeNativeSize_topCount hx0 hnT
  have hnT0 : 0 ≤ nT := by
    have : 0 ≤ x ^ (-(ε / 8)) * n / 2 := by
      have := Real.rpow_pos_of_pos hx0 (-(ε / 8))
      positivity
    linarith
  have hme : 0 ≤ m * x ^ ε := by positivity
  have key : 2 * n * m * x ^ ε ≤ 4 * Y * nT := by
    calc
      2 * n * m * x ^ ε = 2 * n * (m * x ^ ε) := by ring
      _ ≤ 2 * (2 * nT * x ^ (ε / 8)) * (m * x ^ ε) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnT' (by norm_num)) hme
      _ = 4 * nT * (m * x ^ ε * x ^ (ε / 8)) := by ring
      _ ≤ 4 * nT * Y := mul_le_mul_of_nonneg_left hmY (by positivity)
      _ = 4 * Y * nT := by ring
  have hmb : 0 ≤ m * b := by positivity
  calc
    m * ((2 * n) * m * b * x ^ ε) = (2 * n * m * x ^ ε) * (m * b) := by ring
    _ ≤ (4 * Y * nT) * (m * b) := mul_le_mul_of_nonneg_right key hmb
    _ = 4 * Y * (nT * m * b) := by ring

/-- Fourth bracket term, the thin count cost. -/
theorem alpogeNativeSize_term4 {x ε Y m n nT nT2 b k : ℝ}
    (hx0 : 0 < x) (hx1 : 1 ≤ x) (hm0 : 0 ≤ m) (hb : 0 ≤ b) (hε : 0 < ε)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8))
    (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 < n) (hnT2 : nT2 ≤ n)
    (hk0 : 0 ≤ k) (hk2 : k ≤ n ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) :
    m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))) ≤
      2 * Y * (nT * m * b) := by
  have pe := Real.rpow_pos_of_pos hx0 ε
  have pne := Real.rpow_pos_of_pos hx0 (-ε)
  have p8 := Real.rpow_pos_of_pos hx0 (ε / 8)
  have hneg : x ^ (-ε) * x ^ ε = 1 := by
    rw [← Real.rpow_add hx0]
    simp
  have he : m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))) =
      (m * b) * (nT2 * k * (x ^ ε * x ^ ε) / n ^ 2) := by
    have h2 : x ^ (-ε) = 1 / x ^ ε := by
      rw [eq_div_iff pe.ne']
      exact hneg
    rw [h2]
    field_simp
  rw [he]
  have hA : nT2 * k * (x ^ ε * x ^ ε) / n ^ 2 ≤
      n * x ^ ((1 : ℝ) / 2 + ε) := by
    rw [div_le_iff₀ (by positivity)]
    have hxe : 0 ≤ x ^ ε * x ^ ε := by positivity
    have e2 : n * x ^ ((1 : ℝ) / 2 + ε) * n ^ 2 =
        n * (n ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) * (x ^ ε * x ^ ε) := by
      rw [show (1 : ℝ) / 2 + ε = ((1 : ℝ) / 2 - ε) + ε + ε by ring,
        Real.rpow_add hx0, Real.rpow_add hx0]
      ring
    rw [e2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hnT2 hk2 hk0 hn.le) hxe
  have hnT' := alpogeNativeSize_topCount hx0 hnT
  have hnT0 : 0 ≤ nT := by
    have : 0 ≤ x ^ (-(ε / 8)) * n / 2 := by positivity
    linarith
  have hXe : x ^ ((1 : ℝ) / 2 + ε) * x ^ (ε / 8) ≤ Y := by
    rw [← Real.rpow_add hx0, hY]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hB : n * x ^ ((1 : ℝ) / 2 + ε) ≤ 2 * Y * nT := by
    have hp := Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 2 + ε)
    calc
      n * x ^ ((1 : ℝ) / 2 + ε) ≤
          (2 * nT * x ^ (ε / 8)) * x ^ ((1 : ℝ) / 2 + ε) :=
        mul_le_mul_of_nonneg_right hnT' hp.le
      _ = 2 * nT * (x ^ ((1 : ℝ) / 2 + ε) * x ^ (ε / 8)) := by ring
      _ ≤ 2 * nT * Y := mul_le_mul_of_nonneg_left hXe (by positivity)
      _ = 2 * Y * nT := by ring
  have hmb : 0 ≤ m * b := by positivity
  calc
    (m * b) * (nT2 * k * (x ^ ε * x ^ ε) / n ^ 2) ≤
        (m * b) * (n * x ^ ((1 : ℝ) / 2 + ε)) :=
      mul_le_mul_of_nonneg_left hA hmb
    _ ≤ (m * b) * (2 * Y * nT) := mul_le_mul_of_nonneg_left hB hmb
    _ = 2 * Y * (nT * m * b) := by ring

/-- Size and budget absorption (native `GrowthSizeBound`). If the earned
divisor times `Gx - 4 * x ^ (1 / 2 + ε)` is at most a quantity `Err` below
`x ^ (C * ε)` times the bracket, plus the transport term `2 * T * m * b / x`,
then `Gx ≤ x ^ (1 / 2 + (C + 3) * ε)`. The bracket costs `10 * x ^ (13 ε / 8)`
divisors, the density costs `x ^ ε`, and `26 ≤ x ^ (3 ε / 8)` absorbs the
constant. -/
theorem alpogeNativeSizeWindow_absorb
    {C ε x : ℝ} {n nT nT2 m : ℕ} {b k aE Err Gx : ℝ}
    (hx3 : 3 ≤ x) (hε : 0 < ε) (hC : 0 ≤ C)
    (hbig : 26 ≤ x ^ (3 * ε / 8))
    (hn : 0 < n) (hnT2 : nT2 ≤ n)
    (hS : AlpogeNativeRestSize ε x n nT nT2 m b k aE)
    (hErr : Err ≤ x ^ (C * ε) * alpogeNativeErrorBracket x ε n nT nT2 m b k aE)
    (hT : (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) *
        (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤
      Err + 2 * (nT : ℝ) * m * b / x) :
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
  obtain ⟨hb, haE, hnT, hd2, hm1, hm2, hk1, hk2⟩ := hS
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have pos : ∀ u : ℝ, 0 < x ^ u := fun u => Real.rpow_pos_of_pos hx0 u
  have mono : ∀ u v : ℝ, u ≤ v → x ^ u ≤ x ^ v :=
    fun u v h => Real.rpow_le_rpow_of_exponent_le hx1 h
  have hP1 : 1 ≤ x ^ (C * ε) := Real.one_le_rpow hx1 (by positivity)
  have hY1 : 1 ≤ x ^ ((1 : ℝ) / 2 + 13 * ε / 8) :=
    Real.one_le_rpow hx1 (by linarith)
  have hXY : x ^ ((1 : ℝ) / 2 + ε) ≤ x ^ ((1 : ℝ) / 2 + 13 * ε / 8) :=
    mono _ _ (by linarith)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (pos _) hm1
  have hnT0 : (0 : ℝ) < nT := by
    refine lt_of_lt_of_le ?_ hnT
    have := pos (-(ε / 8))
    positivity
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk1
  have hQ : 0 < (nT : ℝ) * m * b := by positivity
  have hxX : x ≤ x ^ ((1 : ℝ) / 2 + ε) * m := by
    have e : x ^ ((1 : ℝ) / 2 + ε) * x ^ ((1 : ℝ) / 2 - ε) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    calc
      x = x ^ ((1 : ℝ) / 2 + ε) * x ^ ((1 : ℝ) / 2 - ε) := e.symm
      _ ≤ x ^ ((1 : ℝ) / 2 + ε) * m :=
        mul_le_mul_of_nonneg_left hm1 (pos _).le
  have h1 := alpogeNativeSize_term1 hxX hXY hnT0.le hm0.le hb.le haE
  have h2 := alpogeNativeSize_term2 hx0 hY1 hnT0.le hm0.le hb.le hk0 hk1 haE
  have h3 := alpogeNativeSize_term3 (ε := ε) (n := (n : ℝ)) hx0 hm0.le hb.le
    rfl hm2 hnT hnR.le
  have h4 := alpogeNativeSize_term4 (nT2 := (nT2 : ℝ)) hx0 hx1 hm0.le hb.le hε
    rfl hnT hnR (by exact_mod_cast hnT2) hk0.le hk2
  have hErr' : Err ≤ 10 * x ^ (C * ε) *
      x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by
    refine hErr.trans ?_
    have hsum : alpogeNativeErrorBracket x ε n nT nT2 m b k aE ≤
        10 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by
      have e : alpogeNativeErrorBracket x ε n nT nT2 m b k aE =
          (nT : ℝ) * aE + (nT : ℝ) * aE * ((m : ℝ) ^ 2 / k) +
            (m : ℝ) * ((2 * n) * m * b * x ^ ε) +
            (m : ℝ) * ((nT2 : ℝ) * k * b * x ^ ε /
              (n * (n * x ^ (-ε)))) := by
        unfold alpogeNativeErrorBracket
        ring
      rw [e]
      linarith
    calc
      x ^ (C * ε) * alpogeNativeErrorBracket x ε n nT nT2 m b k aE ≤
          x ^ (C * ε) *
            (10 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b)) :=
        mul_le_mul_of_nonneg_left hsum (pos _).le
      _ = _ := by ring
  have hxδ : 1 ≤ x ^ ε * ((nT2 : ℝ) / n) := by
    have h := mul_le_mul_of_nonneg_left hd2 (pos ε).le
    have e : x ^ ε * x ^ (-ε) = 1 := by
      rw [← Real.rpow_add hx0]
      simp
    linarith
  have hδ0 : 0 < (nT2 : ℝ) / n := lt_of_lt_of_le (pos _) hd2
  have h2x : 2 / x ≤ 1 := by
    rw [div_le_one hx0]
    linarith
  set P : ℝ := x ^ (C * ε) with hPd
  set Y : ℝ := x ^ ((1 : ℝ) / 2 + 13 * ε / 8) with hYd
  set X : ℝ := x ^ ((1 : ℝ) / 2 + ε) with hXd
  set Q : ℝ := (nT : ℝ) * m * b with hQd
  set δ : ℝ := (nT2 : ℝ) / n with hδd
  have hPY : 1 ≤ P * Y := one_le_mul_of_one_le_of_one_le hP1 hY1
  have hmain : δ * (Gx - 4 * X) ≤ 22 * (P * Y) := by
    have ha : Q * (δ / 2 * (Gx - 4 * X)) ≤ Q * (10 * (P * Y) + 2 / x) := by
      have e1 : Q * (δ / 2 * (Gx - 4 * X)) = Q * (δ / 2) * (Gx - 4 * X) := by
        ring
      have e2 : Q * (10 * (P * Y) + 2 / x) = 10 * P * Y * Q + 2 * Q / x := by
        ring
      have e3 : 2 * Q / x = 2 * (nT : ℝ) * m * b / x := by
        rw [hQd]
        ring
      rw [e1, e2, e3]
      linarith
    have hb2 := le_of_mul_le_mul_left ha hQ
    linarith
  have hG : Gx - 4 * X ≤ 22 * (P * Y) * x ^ ε := by
    by_cases hc : Gx - 4 * X ≤ 0
    · have : 0 ≤ 22 * (P * Y) * x ^ ε := by
        have := pos ε
        positivity
      linarith
    · have hc' : 0 < Gx - 4 * X := lt_of_not_ge hc
      calc
        Gx - 4 * X ≤ (x ^ ε * δ) * (Gx - 4 * X) :=
          le_mul_of_one_le_left hc'.le hxδ
        _ = x ^ ε * (δ * (Gx - 4 * X)) := by ring
        _ ≤ x ^ ε * (22 * (P * Y)) :=
          mul_le_mul_of_nonneg_left hmain (pos ε).le
        _ = 22 * (P * Y) * x ^ ε := by ring
  have hZ : P * Y * x ^ ε = x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    rw [hPd, hYd, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    ring_nf
  have hXZ : X ≤ x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    rw [hXd]
    exact mono _ _ (by nlinarith [mul_nonneg hC hε.le])
  have hfin : x ^ (3 * ε / 8) * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) =
      x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  have hZ0 := pos ((1 : ℝ) / 2 + (C + 21 / 8) * ε)
  have hG26 : Gx ≤ 26 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    have e : 22 * (P * Y) * x ^ ε =
        22 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
      rw [mul_assoc, hZ]
    linarith
  rw [← hfin]
  exact hG26.trans (mul_le_mul_of_nonneg_right hbig hZ0.le)

end SizeAbsorption

section LargeScale

/-- The explicit movement charge at scale `x`, with `ell` bounded by `x ^ ε`. -/
def alpogeNativeZetaMoveCost (x ε : ℝ) : ℝ :=
  alpogeNativeMoveConstant +
    3 * (Real.log (x + 1) + alpogeNativeMoveConstant + x ^ ε)

/-- Elementary largeness of `x` in terms of `ε`; `C` only has to be
nonnegative. No arithmetic input. -/
def alpogeNativeLargeX (ε C x : ℝ) : Prop :=
  0 < ε ∧ 0 ≤ C ∧ 3 ≤ x ∧ 26 ≤ x ^ (3 * ε / 8) ∧
    alpogeNativeZetaMoveCost x ε ≤ x ^ ((1 : ℝ) / 2 + ε)

/-- An explicit threshold for `alpogeNativeLargeX`. -/
def alpogeNativeLargeXThreshold (ε : ℝ) : ℝ :=
  max 3 (max ((26 : ℝ) ^ (8 / (3 * ε)))
    ((4 * alpogeNativeMoveConstant + 18) ^ 4))

theorem alpogeNativeLargeX_of_threshold_le {ε C x : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hx : alpogeNativeLargeXThreshold ε ≤ x) :
    alpogeNativeLargeX ε C x := by
  have hCd := alpogeNativeMoveConstant_nonneg
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have h26x : (26 : ℝ) ^ (8 / (3 * ε)) ≤ x :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hAx : (4 * alpogeNativeMoveConstant + 18) ^ 4 ≤ x :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  refine ⟨hε, hC, hx3, ?_, ?_⟩
  · have h3 := Real.rpow_le_rpow (by positivity) h26x
      (by positivity : 0 ≤ 3 * ε / 8)
    rw [← Real.rpow_mul (by norm_num)] at h3
    have h4 : 8 / (3 * ε) * (3 * ε / 8) = 1 := by field_simp
    rwa [h4, Real.rpow_one] at h3
  · have hA0 : 0 ≤ 4 * alpogeNativeMoveConstant + 18 := by linarith
    have hs1 : 1 ≤ x ^ ((1 : ℝ) / 4) := Real.one_le_rpow hx1 (by norm_num)
    have he1 : 1 ≤ x ^ ε := Real.one_le_rpow hx1 hε.le
    have hX : x ^ ((1 : ℝ) / 2 + ε) =
        x ^ ((1 : ℝ) / 4) * (x ^ ((1 : ℝ) / 4) * x ^ ε) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 1
      ring
    have hlogx : Real.log x ≤ 4 * x ^ ((1 : ℝ) / 4) := by
      have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
      linarith
    have hlog1 : Real.log (x + 1) ≤ 1 + 4 * x ^ ((1 : ℝ) / 4) := by
      have h1 : Real.log (x + 1) ≤ Real.log (2 * x) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hx0.ne'] at h1
      have h2 := Real.log_two_lt_d9
      linarith
    have hAs : 4 * alpogeNativeMoveConstant + 18 ≤ x ^ ((1 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow (by positivity) hAx
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have hroot := Real.pow_rpow_inv_natCast hA0 (by norm_num : (4 : ℕ) ≠ 0)
      have h4 : (((4 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 4 := by norm_num
      rw [h4] at hroot
      rwa [hroot] at h
    set s : ℝ := x ^ ((1 : ℝ) / 4) with hs
    set e : ℝ := x ^ ε with he
    have hse1 : 1 ≤ s * e := one_le_mul_of_one_le_of_one_le hs1 he1
    have hse : s ≤ s * e := le_mul_of_one_le_right (by linarith) he1
    have hes : e ≤ s * e := le_mul_of_one_le_left (by linarith) hs1
    have hCdse : alpogeNativeMoveConstant ≤ alpogeNativeMoveConstant * (s * e) :=
      le_mul_of_one_le_right hCd hse1
    have hfinal : (4 * alpogeNativeMoveConstant + 18) * (s * e) ≤ s * (s * e) :=
      mul_le_mul_of_nonneg_right hAs (by linarith)
    unfold alpogeNativeZetaMoveCost
    rw [hX]
    nlinarith

/-- `alpogeNativeLargeX` holds from an explicit point on. -/
theorem exists_alpogeNativeLargeX {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → alpogeNativeLargeX ε C x :=
  ⟨alpogeNativeLargeXThreshold ε,
    fun _ hx => alpogeNativeLargeX_of_threshold_le hε hC hx⟩

end LargeScale

section Witness

/-- Native cost windows. The first is Alpoge's thin window with `f = 2 * |H|`.
The second pays the Chebyshev freezing bill of thick widths in `[b, b + h]`
and replaces the source's `6 * f * (x + 1) * (η + 1) ≤ b / x`. -/
def AlpogeNativeCostWindows (x f b h θ : ℝ) : Prop :=
  2 * f * (x + 1) * θ ≤ 1 / x ∧
    4 * h * (Real.log 4 + 2) * (x + 1) ≤ b / x

/-- The minimum-cut witness at one scale, for the zeta-only level: averaging
subgroup `⊤` and retained set `{0}`. See the module docstring for the status
of each field. This raw interface admits arbitrary host data and includes
the entire quantitative `top` premise. Its construction is not an independent
supplier unless physical host identification and the top bound are proved
without assuming an RH-strength input. See the window RH bridge. -/
structure AlpogeNativeZetaWindowWitness (ε x C : ℝ) where
  /-- Field 1: the finite host and its physical data. -/
  H : Type
  [addCommGroup : AddCommGroup H]
  [fintype : Fintype H]
  [decidableEq : DecidableEq H]
  inertia : ℕ → AddSubgroup (AlpogeNativeE0 × H)
  frob : ℕ → AlpogeNativeE0 × H
  ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ
  N : ℕ
  m : ℕ
  TT : Finset H
  T2 : Finset H
  a : H → ℝ
  w : H → Fin m → AlpogeNativeE0 × H → ℝ
  b : ℝ
  b' : ℝ
  h : ℝ
  X' : ℝ
  θ : ℝ
  k : ℝ
  aE : ℝ
  /-- Field 2: scalar sizes. -/
  scales : 0 ≤ h ∧ 0 < X' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ
  /-- Field 3: every top height sits within one of `x * b`. -/
  heights : ∀ t ∈ TT, |a t / b - x| ≤ 1
  /-- Field 4: positive widths, thick widths in `[b, b + h]`, thin widths at
  most `2 * b'`. -/
  widths :
    (∀ u j ρ, alpogeNativeInPhi ρ → 0 < w u j ρ) ∧
    (∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
      b ≤ w u j ρ ∧ w u j ρ ≤ b + h) ∧
    (∀ u j ρ, alpogeNativeInPhi ρ →
      ρ ∉ alpogeNativeThickPositiveSites T2 u → w u j ρ ≤ 2 * b')
  /-- Field 5: one cutoff covers every original profile and the frozen one. -/
  cutoff :
    (∀ u j t, t ∈ TT →
      ∀ ρ, alpogeNativeInPhi ρ → a t / w u j ρ ≤ (N : ℝ)) ∧
    x + 1 ≤ (N : ℝ)
  /-- Field 6: thin scales for every character of the host. -/
  thin : AlpogeNativeThinScales
    (alpogeNativeFrobInertiaGPsi inertia frob ell) X' θ
  /-- Field 7: the two cost windows. -/
  costs : AlpogeNativeCostWindows x (alpogeNativePhiCard H) b h θ
  /-- Field 8: host, top, thick, multiplicity and lattice sizes. -/
  sizes : AlpogeNativeRestSize ε x (Fintype.card H) TT.card T2.card m b k aE
  /-- Field 9: the nonprincipal characters trivial on the host have `ell` at
  most `x ^ ε` and response at most `x ^ (1 / 2 + ε)` at `x`. -/
  excluded : ∀ ψ ∈ alpogeNativeProjectionChars (⊤ : AddSubgroup H), ψ ≠ 0 →
    ‖alpogeNativeFrobInertiaGPsi inertia frob ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε) ∧
      ‖ell ψ‖ ≤ x ^ ε
  /-- Field 10: the full-host mean of the physical ASK minus MAIN. -/
  top : alpogeNativePhysicalSubgroupTopExcess ⊤ inertia frob ell N TT a w ≤
    x ^ (C * ε) *
      alpogeNativeErrorBracket x ε (Fintype.card H) TT.card T2.card m b k aE

attribute [instance] AlpogeNativeZetaWindowWitness.addCommGroup
  AlpogeNativeZetaWindowWitness.fintype
  AlpogeNativeZetaWindowWitness.decidableEq

/-- The witness inequality before size absorption: the earned divisor times
`Gz x - 4 * x ^ (1 / 2 + ε)` is at most the physical top excess plus
`2 * T * m * b / x`. Fields 2-9 are consumed; field 10 is not. -/
theorem alpogeNativeZetaWindowWitness_divisor_mul_le {ε x C : ℝ}
    (W : AlpogeNativeZetaWindowWitness ε x C)
    (hx : alpogeNativeLargeX ε C x) :
    (W.TT.card : ℝ) * W.m * W.b * (((W.T2.card : ℝ) / Fintype.card W.H) / 2) *
        (alpogeNativeGzArithmetic x - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤
      alpogeNativePhysicalSubgroupTopExcess ⊤ W.inertia W.frob W.ell W.N
          W.TT W.a W.w +
        2 * (W.TT.card : ℝ) * W.m * W.b / x := by
  obtain ⟨_hε, _hC, hx3, _h26, hmove⟩ := hx
  have hx0 : 0 < x := by linarith
  have hS := W.sizes
  have hnR : (0 : ℝ) < Fintype.card W.H := by exact_mod_cast Fintype.card_pos
  have hTT : W.TT.Nonempty := by
    rw [← Finset.card_pos]
    have hp : 0 < x ^ (-(ε / 8)) * (Fintype.card W.H : ℝ) / 2 := by
      have := Real.rpow_pos_of_pos hx0 (-(ε / 8))
      positivity
    have h : (0 : ℝ) < W.TT.card := lt_of_lt_of_le hp hS.top_count
    exact_mod_cast h
  have hT2 : W.T2.Nonempty := by
    rw [← Finset.card_pos]
    have hp : 0 < (W.T2.card : ℝ) / Fintype.card W.H :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hS.thick_density
    have h : (0 : ℝ) < W.T2.card := (div_pos_iff_of_pos_right hnR).mp hp
    exact_mod_cast h
  have hm : 0 < W.m := by
    have h : (0 : ℝ) < W.m :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hS.mult_lower
    exact_mod_cast h
  have hbal := alpogeNativeGz_balance_le W.inertia W.frob W.ell W.N W.TT W.T2
    hTT hT2 hm W.a W.w (x := x) (b := W.b) (b' := W.b') (h := W.h)
    (X' := W.X') (θ := W.θ) (Cd := alpogeNativeMoveConstant)
    (B := x ^ ((1 : ℝ) / 2 + ε)) (L := x ^ ε)
    hx3 hS.b_pos W.scales.1 W.scales.2.1 W.scales.2.2.1 W.scales.2.2.2
    (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hx0.le _)
    W.heights W.widths.1 W.widths.2.1 W.widths.2.2 W.cutoff.1 W.cutoff.2
    (alpogeNativeDerivInt_moveConstant W.inertia W.frob W.ell)
    W.excluded W.thin W.costs.1 W.costs.2
  have hQ := alpogeNativeProjectionDivisor_pos W.TT W.T2 hTT hT2 W.m hm W.b
    hS.b_pos
  have hΔ : 0 < alpogeNativeProjectionDensity W.T2 := by
    unfold alpogeNativeProjectionDensity
    have h1 : (0 : ℝ) < W.T2.card := by
      exact_mod_cast Finset.card_pos.mpr hT2
    positivity
  have hG : alpogeNativeGzArithmetic x - 4 * x ^ ((1 : ℝ) / 2 + ε) ≤
      alpogeNativePhysicalSubgroupTopExcess ⊤ W.inertia W.frob W.ell W.N
          W.TT W.a W.w / alpogeNativeProjectionDivisor W.TT W.T2 W.m W.b +
        3 / (alpogeNativeProjectionDensity W.T2 * x) := by
    unfold alpogeNativeZetaMoveCost at hmove
    linarith
  have hmul := mul_le_mul_of_nonneg_left hG hQ.le
  have hTop : alpogeNativeProjectionDivisor W.TT W.T2 W.m W.b *
      (alpogeNativePhysicalSubgroupTopExcess ⊤ W.inertia W.frob W.ell W.N
        W.TT W.a W.w / alpogeNativeProjectionDivisor W.TT W.T2 W.m W.b) =
      alpogeNativePhysicalSubgroupTopExcess ⊤ W.inertia W.frob W.ell W.N
        W.TT W.a W.w := by
    field_simp
  have hcost : alpogeNativeProjectionDivisor W.TT W.T2 W.m W.b *
      (3 / (alpogeNativeProjectionDensity W.T2 * x)) =
      3 / 2 * ((W.TT.card : ℝ) * W.m * W.b / x) := by
    unfold alpogeNativeProjectionDivisor
    field_simp
  have hTmb : 0 ≤ (W.TT.card : ℝ) * W.m * W.b / x := by
    have := hS.b_pos
    positivity
  have hdiv : (W.TT.card : ℝ) * W.m * W.b *
      (((W.T2.card : ℝ) / Fintype.card W.H) / 2) =
      alpogeNativeProjectionDivisor W.TT W.T2 W.m W.b := by
    unfold alpogeNativeProjectionDivisor alpogeNativeProjectionDensity
    ring
  rw [mul_add, hTop, hcost] at hmul
  rw [hdiv]
  have hsplit : 2 * (W.TT.card : ℝ) * W.m * W.b / x =
      2 * ((W.TT.card : ℝ) * W.m * W.b / x) := by ring
  rw [hsplit]
  linarith

/-- Minimum-cut consumer: a witness at a large scale bounds the native `Gz`.
This is a conditional statement in the ten fields of the witness. -/
theorem alpogeNativeGz_le_of_witness {ε x C : ℝ}
    (W : AlpogeNativeZetaWindowWitness ε x C)
    (hx : alpogeNativeLargeX ε C x) :
    alpogeNativeGzArithmetic x ≤ x ^ (1 / 2 + (C + 3) * ε) := by
  have hmul := alpogeNativeZetaWindowWitness_divisor_mul_le W hx
  obtain ⟨hε, hC, hx3, h26, _hmove⟩ := hx
  exact alpogeNativeSizeWindow_absorb hx3 hε hC h26 Fintype.card_pos
    (Finset.card_le_univ W.T2) W.sizes W.top hmul

/-- Witnesses on arbitrarily late windows `[Y, Y ^ (1 + δ)]`, for every small
`ε`, with one exponent constant `C`. -/
def AlpogeNativeZetaWindowWitnessesOnWindows (δ C ε₁ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
    ∀ x ∈ Set.Icc Y (Y ^ (1 + δ)),
      Nonempty (AlpogeNativeZetaWindowWitness ε x C)

/-- Witnesses on windows give the one-sided window bounds on the native `Gz`
at every exponent above one half, with constant one. This is the hypothesis
shape of a window Landau theorem. -/
theorem alpogeNativeGz_windows_of_witnesses {δ C ε₁ : ℝ}
    (hC : 0 ≤ C) (hε₁ : 0 < ε₁)
    (h : AlpogeNativeZetaWindowWitnessesOnWindows δ C ε₁) :
    ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
      ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
        alpogeNativeGzArithmetic y ≤ K * y ^ (1 / 2 + η) := by
  intro η hη
  refine ⟨1, fun Y₀ => ?_⟩
  have hC3 : 0 < C + 3 := by linarith
  set ε : ℝ := min (η / (C + 3)) (ε₁ / 2) with hεd
  have hε : 0 < ε := lt_min (div_pos hη hC3) (by linarith)
  have hεlt : ε < ε₁ := (min_le_right _ _).trans_lt (by linarith)
  have hεη : (C + 3) * ε ≤ η := by
    have h1 : ε ≤ η / (C + 3) := min_le_left _ _
    have h2 := mul_le_mul_of_nonneg_left h1 hC3.le
    rwa [mul_div_cancel₀ _ hC3.ne'] at h2
  obtain ⟨Y, hY, hw⟩ := h ε hε hεlt (max Y₀ (alpogeNativeLargeXThreshold ε))
  refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
  obtain ⟨W⟩ := hw y hy
  have hthr : alpogeNativeLargeXThreshold ε ≤ y :=
    ((le_max_right _ _).trans hY).trans hy.1
  have hL := alpogeNativeLargeX_of_threshold_le hε hC hthr
  have hy1 : 1 ≤ y := by linarith [hL.2.2.1]
  rw [one_mul]
  exact (alpogeNativeGz_le_of_witness W hL).trans
    (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith))

end Witness

end RHLean.Analysis
