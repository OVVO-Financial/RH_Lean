import Mathlib
import RHLean.Analysis.AlpogeNativeCostNormalization

/-!
# Pay the complete normalized geometric bracket in the original size windows

Finite numerical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean`,
`SizeWindows` and `GrowthSizeBound`, and
`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean`,
`SZ.rp`, `SZ.nT_bound`, `SZ.T1`--`SZ.T4`, and `proposition_size_bound`.
Only these real-arithmetic declarations are reconstructed; no terminal RH
consumer or arithmetic signal estimate is imported from that source.
The source mirror states no license; attribution is retained without assigning one.

The final theorem uses the actual native character divisor and its complete
three-cost identity. Its error is the explicit bracket itself, so the source
error-budget premise is reflexive. All original nontrivial size windows remain
visible, including the TT cardinal, actual T2 density, theta multiplicity,
rank/width parameter, error scale and eventual threshold 26. This is a scalar
payment theorem; it does not construct the geometric witnesses or their windows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows

def SizeWindows (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ) : Prop :=
  3 ≤ x ∧ 0 < ε ∧ 0 ≤ C ∧ 0 < n ∧ 0 < b ∧ 0 ≤ aE ∧ aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧ nT2 ≤ n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) ∧
  x * m ≤ k ∧ k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) ∧
  Err ≤ x ^ (C * ε) * ((nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
    + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))) ∧
  26 ≤ x ^ (3 * ε / 8)

def GrowthSizeBound : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε)

namespace SZ

lemma rp {x : ℝ} (hx0 : 0 < x) (u v : ℝ) : x ^ (u + v) = x ^ u * x ^ v := Real.rpow_add hx0 u v

lemma nT_bound {x ε : ℝ} {n nT : ℝ} (hx0 : 0 < x) (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) :
    n ≤ 2 * nT * x ^ (ε / 8) := by
  have h8 : 0 < x ^ (ε / 8) := Real.rpow_pos_of_pos hx0 _
  have hinv : x ^ (-(ε / 8)) * x ^ (ε / 8) = 1 := by rw [← rp hx0]; simp
  have := mul_le_mul_of_nonneg_right hnT h8.le
  have e : x ^ (-(ε / 8)) * n / 2 * x ^ (ε / 8) = n / 2 := by
    calc x ^ (-(ε / 8)) * n / 2 * x ^ (ε / 8) = (x ^ (-(ε / 8)) * x ^ (ε / 8)) * n / 2 := by ring
      _ = n / 2 := by rw [hinv]; ring
  linarith

lemma T1 {x X Y m nT aE b : ℝ} (hxX : x ≤ X * m) (hXY : X ≤ Y) (hnT0 : 0 ≤ nT) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (haE : aE ≤ 2 * x * b) : nT * aE ≤ 2 * Y * (nT * m * b) := by
  have h1 : nT * aE ≤ nT * (2 * x * b) := mul_le_mul_of_nonneg_left haE hnT0
  have h2 : 2 * x * b ≤ 2 * (Y * m) * b := by
    have : x ≤ Y * m := le_trans hxX (mul_le_mul_of_nonneg_right hXY hm0)
    nlinarith
  have h3 : nT * (2 * x * b) ≤ nT * (2 * (Y * m) * b) := mul_le_mul_of_nonneg_left h2 hnT0
  calc nT * aE ≤ nT * (2 * (Y * m) * b) := le_trans h1 h3
    _ = 2 * Y * (nT * m * b) := by ring

lemma T2 {x Y m nT aE b k : ℝ} (hx0 : 0 < x) (hY1 : 1 ≤ Y) (hnT0 : 0 ≤ nT) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hk0 : 0 < k) (hk1 : x * m ≤ k) (haE : aE ≤ 2 * x * b) :
    nT * aE * (m ^ 2 / k) ≤ 2 * Y * (nT * m * b) := by
  have hmk : m ^ 2 / k ≤ m / x := by
    rw [div_le_div_iff₀ hk0 hx0]; nlinarith
  have h1 : nT * aE * (m ^ 2 / k) ≤ nT * (2 * x * b) * (m / x) :=
    mul_le_mul (mul_le_mul_of_nonneg_left haE hnT0) hmk (by positivity) (by positivity)
  have h2 : nT * (2 * x * b) * (m / x) = 2 * (nT * m * b) := by field_simp
  have hQ : 0 ≤ nT * m * b := by positivity
  have h3 : 2 * (nT * m * b) ≤ 2 * Y * (nT * m * b) := by nlinarith
  linarith

lemma T3 {x ε Y m n nT b : ℝ} (hx0 : 0 < x) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) (hm2 : m ≤ x ^ ((1 : ℝ) / 2 + ε / 2))
    (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 ≤ n) :
    m * ((2 * n) * m * b * x ^ ε) ≤ 4 * Y * (nT * m * b) := by
  have pe := Real.rpow_pos_of_pos hx0 ε
  have p8 := Real.rpow_pos_of_pos hx0 (ε / 8)
  have hY' : x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ ε * x ^ (ε / 8) = Y := by
    rw [← rp hx0, ← rp hx0, hY]; ring_nf
  have hmY : m * x ^ ε * x ^ (ε / 8) ≤ Y := by
    rw [← hY']; gcongr
  have hnT' := nT_bound hx0 hnT
  have key : 2 * n * m * x ^ ε ≤ 4 * Y * nT := by
    have hme : 0 ≤ m * x ^ ε := by positivity
    have hnT0 : 0 ≤ nT := by nlinarith
    calc 2 * n * m * x ^ ε = 2 * n * (m * x ^ ε) := by ring
      _ ≤ 2 * (2 * nT * x ^ (ε / 8)) * (m * x ^ ε) := by gcongr
      _ = 4 * nT * (m * x ^ ε * x ^ (ε / 8)) := by ring
      _ ≤ 4 * nT * Y := by gcongr
      _ = 4 * Y * nT := by ring
  have hmb : 0 ≤ m * b := by positivity
  calc m * ((2 * n) * m * b * x ^ ε) = (2 * n * m * x ^ ε) * (m * b) := by ring
    _ ≤ (4 * Y * nT) * (m * b) := mul_le_mul_of_nonneg_right key hmb
    _ = 4 * Y * (nT * m * b) := by ring

lemma T4 {x ε Y m n nT nT2 b k : ℝ} (hx0 : 0 < x) (hx1 : 1 ≤ x) (hm0 : 0 ≤ m) (hb : 0 ≤ b) (hε : 0 < ε)
    (hY : Y = x ^ ((1 : ℝ) / 2 + 13 * ε / 8)) (hnT : x ^ (-(ε / 8)) * n / 2 ≤ nT) (hn : 0 < n)
    (hnT2 : nT2 ≤ n) (hk0 : 0 ≤ k) (hk2 : k ≤ n ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) :
    m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))) ≤ 2 * Y * (nT * m * b) := by
  have pe := Real.rpow_pos_of_pos hx0 ε
  have pne := Real.rpow_pos_of_pos hx0 (-ε)
  have p8 := Real.rpow_pos_of_pos hx0 (ε / 8)
  have hneg : x ^ (-ε) * x ^ ε = 1 := by rw [← rp hx0]; simp
  have he : m * (nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
      = (m * b) * (nT2 * k * (x ^ ε * x ^ ε) / n ^ 2) := by
    have h2 : x ^ ε = 1 / x ^ (-ε) := by rw [eq_div_iff pne.ne', mul_comm, hneg]
    rw [h2]; field_simp
  rw [he]
  have hA : nT2 * k * (x ^ ε * x ^ ε) / n ^ 2 ≤ n * x ^ ((1 : ℝ) / 2 + ε) := by
    rw [div_le_iff₀ (by positivity)]
    have hxe : 0 ≤ x ^ ε * x ^ ε := by positivity
    have e2 : n * x ^ ((1 : ℝ) / 2 + ε) * n ^ 2 = n * (n ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) * (x ^ ε * x ^ ε) := by
      rw [show (1 : ℝ) / 2 + ε = ((1 : ℝ) / 2 - ε) + ε + ε by ring, rp hx0, rp hx0]; ring
    rw [e2]
    have := mul_le_mul hnT2 hk2 hk0 hn.le
    exact mul_le_mul_of_nonneg_right this hxe
  have hnT' := nT_bound hx0 hnT
  have hXe : x ^ ((1 : ℝ) / 2 + ε) * x ^ (ε / 8) ≤ Y := by
    rw [← rp hx0, hY]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hB : n * x ^ ((1 : ℝ) / 2 + ε) ≤ 2 * Y * nT := by
    have hp := Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 2 + ε)
    have hnT0 : 0 ≤ nT := by nlinarith
    calc n * x ^ ((1 : ℝ) / 2 + ε) ≤ (2 * nT * x ^ (ε / 8)) * x ^ ((1 : ℝ) / 2 + ε) :=
          mul_le_mul_of_nonneg_right hnT' hp.le
      _ = 2 * nT * (x ^ ((1 : ℝ) / 2 + ε) * x ^ (ε / 8)) := by ring
      _ ≤ 2 * nT * Y := by gcongr
      _ = 2 * Y * nT := by ring
  have hmb : 0 ≤ m * b := by positivity
  calc (m * b) * (nT2 * k * (x ^ ε * x ^ ε) / n ^ 2) ≤ (m * b) * (n * x ^ ((1 : ℝ) / 2 + ε)) :=
        mul_le_mul_of_nonneg_left hA hmb
    _ ≤ (m * b) * (2 * Y * nT) := mul_le_mul_of_nonneg_left hB hmb
    _ = 2 * Y * (nT * m * b) := by ring

end SZ

theorem proposition_size_bound : GrowthSizeBound := by
  intro C ε x n nT nT2 m b k aE Err Gx hW hT
  obtain ⟨hx3, hε, hC, hn, hb, haE0, haE, hnT, hd2, hnT2, hm1, hm2, hk1, hk2, hErr, hbig⟩ := hW
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have pos : ∀ u : ℝ, 0 < x ^ u := fun u => Real.rpow_pos_of_pos hx0 u
  have mono : ∀ u v : ℝ, u ≤ v → x ^ u ≤ x ^ v := fun u v h => Real.rpow_le_rpow_of_exponent_le hx1 h
  have hP1 : 1 ≤ x ^ (C * ε) := Real.one_le_rpow hx1 (by positivity)
  have hY1 : 1 ≤ x ^ ((1 : ℝ) / 2 + 13 * ε / 8) := Real.one_le_rpow hx1 (by linarith)
  have hXY : x ^ ((1 : ℝ) / 2 + ε) ≤ x ^ ((1 : ℝ) / 2 + 13 * ε / 8) := mono _ _ (by linarith)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (pos _) hm1
  have hnT0 : (0 : ℝ) < nT := lt_of_lt_of_le (by have := pos (-(ε / 8)); positivity) hnT
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk1
  have hQ : 0 < (nT : ℝ) * m * b := by positivity
  have hxX : x ≤ x ^ ((1 : ℝ) / 2 + ε) * m := by
    have e : x ^ ((1 : ℝ) / 2 + ε) * x ^ ((1 : ℝ) / 2 - ε) = x := by
      rw [← SZ.rp hx0]; norm_num
    calc x = x ^ ((1 : ℝ) / 2 + ε) * x ^ ((1 : ℝ) / 2 - ε) := e.symm
      _ ≤ x ^ ((1 : ℝ) / 2 + ε) * m := mul_le_mul_of_nonneg_left hm1 (pos _).le
  have h1 := SZ.T1 hxX hXY hnT0.le hm0.le hb.le haE
  have h2 := SZ.T2 hx0 hY1 hnT0.le hm0.le hb.le hk0 hk1 haE
  have h3 := SZ.T3 (ε := ε) (n := (n : ℝ)) hx0 hm0.le hb.le rfl hm2 hnT hnR.le
  have h4 := SZ.T4 (nT2 := (nT2 : ℝ)) hx0 hx1 hm0.le hb.le hε rfl hnT hnR (by exact_mod_cast hnT2) hk0.le hk2
  have hErr' : Err ≤ 10 * x ^ (C * ε) * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by
    refine le_trans hErr ?_
    have hsum : (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
        + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
        ≤ 10 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by
      have e : (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
          + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))
          = (nT : ℝ) * aE + (nT : ℝ) * aE * ((m : ℝ) ^ 2 / k) + (m : ℝ) * ((2 * n) * m * b * x ^ ε)
            + (m : ℝ) * ((nT2 : ℝ) * k * b * x ^ ε / (n * (n * x ^ (-ε)))) := by ring
      rw [e]; linarith
    have hP0 : 0 ≤ x ^ (C * ε) := (pos _).le
    calc x ^ (C * ε) * ((nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
        + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε)))))
        ≤ x ^ (C * ε) * (10 * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b)) :=
          mul_le_mul_of_nonneg_left hsum hP0
      _ = 10 * x ^ (C * ε) * x ^ ((1 : ℝ) / 2 + 13 * ε / 8) * ((nT : ℝ) * m * b) := by ring
  generalize hPd : x ^ (C * ε) = P at hErr' hP1
  generalize hYd : x ^ ((1 : ℝ) / 2 + 13 * ε / 8) = Y at hErr' hY1 hXY
  generalize hXd : x ^ ((1 : ℝ) / 2 + ε) = X at hT hXY
  generalize hQd : (nT : ℝ) * m * b = Q at hErr' hQ
  have hT' : Q * ((nT2 : ℝ) / n / 2) * (Gx - 4 * X) ≤ Err + 2 * Q / x := by
    rw [← hQd]; simpa [mul_assoc] using hT
  generalize hδd : ((nT2 : ℝ) / n) = δ at hT' hd2
  have hδ0 : 0 < δ := lt_of_lt_of_le (pos _) hd2
  have hxδ : 1 ≤ x ^ ε * δ := by
    have := mul_le_mul_of_nonneg_left hd2 (pos ε).le
    have e : x ^ ε * x ^ (-ε) = 1 := by rw [← SZ.rp hx0]; simp
    linarith
  have h2x : 2 / x ≤ 1 := by rw [div_le_one hx0]; linarith
  have hPY : 1 ≤ P * Y := by nlinarith
  have hmain : δ * (Gx - 4 * X) ≤ 22 * (P * Y) := by
    have h1 : Q * (δ / 2 * (Gx - 4 * X)) ≤ Q * (10 * P * Y + 2 / x) := by
      have e1 : Q * (δ / 2 * (Gx - 4 * X)) = Q * (δ / 2) * (Gx - 4 * X) := by ring
      have e2 : Q * (10 * P * Y + 2 / x) = 10 * P * Y * Q + 2 * Q / x := by ring
      rw [e1, e2]; linarith
    have h2 := le_of_mul_le_mul_left h1 hQ
    have e3 : δ * (Gx - 4 * X) = 2 * (δ / 2 * (Gx - 4 * X)) := by ring
    have e4 : 10 * P * Y = 10 * (P * Y) := by ring
    rw [e3]; rw [e4] at h2; linarith
  have hG : Gx - 4 * X ≤ 22 * (P * Y) * x ^ ε := by
    by_cases hc : Gx - 4 * X ≤ 0
    · have : 0 ≤ 22 * (P * Y) * x ^ ε := by have := pos ε; positivity
      linarith
    · have hc' : 0 < Gx - 4 * X := lt_of_not_ge hc
      have hxe := pos ε
      calc Gx - 4 * X ≤ (x ^ ε * δ) * (Gx - 4 * X) := le_mul_of_one_le_left hc'.le hxδ
        _ = x ^ ε * (δ * (Gx - 4 * X)) := by ring
        _ ≤ x ^ ε * (22 * (P * Y)) := mul_le_mul_of_nonneg_left hmain hxe.le
        _ = 22 * (P * Y) * x ^ ε := by ring
  have hZ : P * Y * x ^ ε = x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    rw [← hPd, ← hYd, ← SZ.rp hx0, ← SZ.rp hx0]; ring_nf
  have hXZ : X ≤ x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    rw [← hXd]; exact mono _ _ (by have := mul_nonneg hC hε.le; linarith)
  have hfin : x ^ (3 * ε / 8) * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) = x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
    rw [← SZ.rp hx0]; ring_nf
  have hZ0 := pos ((1 : ℝ) / 2 + (C + 21 / 8) * ε)
  have hG26 : Gx ≤ 26 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by
    have : 22 * (P * Y) * x ^ ε = 22 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := by rw [mul_assoc, hZ]
    linarith
  rw [← hfin]
  calc Gx ≤ 26 * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := hG26
    _ ≤ x ^ (3 * ε / 8) * x ^ ((1 : ℝ) / 2 + (C + 21 / 8) * ε) := mul_le_mul_of_nonneg_right hbig hZ0.le


/-- The original scalar windows with the error set to its explicit bracket.
This lists every nontrivial conjunct of `SizeWindows`, without asking for an
independent bound on a geometric or arithmetic target. -/
def GeometricSizeWindows (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : Prop :=
  3 ≤ x ∧ 0 < ε ∧ 0 ≤ C ∧ 0 < n ∧ 0 < b ∧ 0 ≤ aE ∧ aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧ nT2 ≤ n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) ∧
  x * m ≤ k ∧ k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) ∧
  26 ≤ x ^ (3 * ε / 8)

/-- The exact source bracket before division by the earned character divisor. -/
def sourceErrorBracket (ε x : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : ℝ :=
  (nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k) +
    m * ((2 * n) * m * b * x ^ ε +
      nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))

/-- The error premise in the original size theorem is paid by reflexivity
when its error is the explicit bracket. -/
theorem GeometricSizeWindows.sizeWindows
    {C ε x : ℝ} {n nT nT2 m : ℕ} {b k aE : ℝ}
    (hW : GeometricSizeWindows C ε x n nT nT2 m b k aE) :
    SizeWindows C ε x n nT nT2 m b k aE
      (x ^ (C * ε) * sourceErrorBracket ε x n nT nT2 m b k aE) := by
  obtain ⟨hx, hε, hC, hn, hb, haE0, haE, hnT, hd, hnT2, hm1, hm2, hk1, hk2, hbig⟩ := hW
  exact ⟨hx, hε, hC, hn, hb, haE0, haE, hnT, hd, hnT2, hm1, hm2, hk1, hk2,
    le_rfl, hbig⟩

/-- Match the original reciprocal-power denominator to the existing native
three-term bracket; no term or normalization is changed. -/
theorem sourceErrorBracket_eq_native
    (ε x : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) (hx : 0 ≤ x) :
    sourceErrorBracket ε x n nT nT2 m b k aE =
      alpogeNativeGeometricErrorBracket nT nT2 n m b k aE (x ^ ε) := by
  unfold sourceErrorBracket alpogeNativeGeometricErrorBracket
  rw [Real.rpow_neg hx]
  simp only [div_eq_mul_inv]

/-- The complete three geometric costs and the already-paid analytic
remainder fit the original `(C + 3) * epsilon` exponent. The normalization
uses the same finite TT and T2 and their actual native character divisor. -/
theorem normalizedCosts_add_analytic_le
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (C ε x : ℝ) (TT T2 : Finset H) (m : ℕ) (b k aE : ℝ)
    (hW : GeometricSizeWindows C ε x (Fintype.card H) TT.card T2.card m b k aE) :
    x ^ (C * ε) * alpogeNativeNormalizedGeometricCosts TT.card
        (alpogeNativeProjectionDensity T2) (Fintype.card H) m b k aE (x ^ ε) +
        x ^ ((1 : ℝ) / 2 + ε) ≤
      x ^ ((1 : ℝ) / 2 + (C + 3) * ε) := by
  have hsource := hW.sizeWindows
  obtain ⟨hx3, _hε, _hC, hn, hb, _haE0, _haE, hnT, hd, _hnT2,
    hm1, _hm2, _hk1, _hk2, _hbig⟩ := hW
  have hx0 : 0 < x := by linarith
  have hnR : (0 : ℝ) < Fintype.card H := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m :=
    (Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 2 - ε)).trans_le hm1
  have hTTR : (0 : ℝ) < TT.card := by
    have hp := Real.rpow_pos_of_pos hx0 (-(ε / 8))
    exact lt_of_lt_of_le (by positivity) hnT
  have hT2R : (0 : ℝ) < T2.card :=
    (div_pos_iff_of_pos_right hnR).mp
      ((Real.rpow_pos_of_pos hx0 (-ε)).trans_le hd)
  have hTT : TT.Nonempty := Finset.card_pos.mp (by exact_mod_cast hTTR)
  have hT2 : T2.Nonempty := Finset.card_pos.mp (by exact_mod_cast hT2R)
  have hm : 0 < m := by exact_mod_cast hmR
  let Q := alpogeNativeProjectionDivisor TT T2 m b
  let E := x ^ (C * ε) * sourceErrorBracket ε x (Fintype.card H) TT.card T2.card m b k aE
  let V := x ^ (C * ε) * alpogeNativeNormalizedGeometricCosts TT.card
    (alpogeNativeProjectionDensity T2) (Fintype.card H) m b k aE (x ^ ε)
  have hQ : 0 < Q := alpogeNativeProjectionDivisor_pos TT T2 hTT hT2 m hm b hb
  have hEV : E / Q = V := by
    dsimp only [E, Q, V]
    rw [mul_div_assoc, sourceErrorBracket_eq_native ε x _ _ _ _ _ _ _ hx0.le]
    exact congrArg (fun v : ℝ => x ^ (C * ε) * v)
      (alpogeNativeGeometricErrorBracket_div_projectionDivisor TT T2 m b k aE
        (x ^ ε) hTT hT2 hm hb)
  have hpaid : Q * V = E := by
    rw [← hEV]
    exact mul_div_cancel₀ E hQ.ne'
  have hQeq : (TT.card : ℝ) * m * b * (((T2.card : ℝ) / Fintype.card H) / 2) = Q := by
    dsimp [Q, alpogeNativeProjectionDivisor, alpogeNativeProjectionDensity]
    ring
  have hX0 : 0 ≤ x ^ ((1 : ℝ) / 2 + ε) := Real.rpow_nonneg hx0.le _
  have htransport : 0 ≤ 2 * (TT.card : ℝ) * m * b / x := by positivity
  have hT : (TT.card : ℝ) * m * b * (((T2.card : ℝ) / Fintype.card H) / 2) *
      (V + x ^ ((1 : ℝ) / 2 + ε) - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤
        E + 2 * (TT.card : ℝ) * m * b / x := by
    rw [hQeq]
    nlinarith [mul_nonneg hQ.le hX0]
  exact proposition_size_bound C ε x (Fintype.card H) TT.card T2.card m b k aE
    E (V + x ^ ((1 : ℝ) / 2 + ε)) hsource hT

end RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows

end
