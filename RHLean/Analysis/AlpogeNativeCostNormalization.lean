import RHLean.Analysis.AlpogeNativeSubgroupProjection
import RHLean.Analysis.AlpogeNativeAffineFamilyPayment

/-!
# The complete geometric error bracket under the earned character divisor

This file records finite algebra on the actual three-term error bracket in
Alpoge's `ChTop` / `ChCore` interface. It proves the normalization; it does not
assume or supply a bound of the physical ASK-MAIN by that bracket.

`e` stands for `x^epsilon`, `aE` is the geometric error scale, and `h` is the
cardinal of the thick set. The theta multiplicity `m`, host size `n`, and height
scale `b` remain distinct. No factor of `m` is inserted into the source.
-/

noncomputable section

namespace RHLean.Analysis

/-- The family-width denominator is the character divisor when supplied its
actual density. This identifies the two previously derived normalizations. -/
theorem alpogeNativeHCNormalizer_eq_projectionDivisor
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (TT T2 : Finset H) (m : ℕ) (b : ℝ) :
    alpogeNativeHCNormalizer TT m b (alpogeNativeProjectionDensity T2) =
      alpogeNativeProjectionDivisor TT T2 m b := rfl

/-- Original finite geometric error bracket, with `e = x^epsilon`. -/
def alpogeNativeGeometricErrorBracket (T h n m b k aE e : ℝ) : ℝ :=
  T * aE * (1 + m ^ 2 / k) +
    m * (2 * n * m * b * e + h * k * b * e / (n * (n / e)))

/-- The three original costs after division by the earned divisor. -/
def alpogeNativeNormalizedGeometricCosts (T Δ n m b k aE e : ℝ) : ℝ :=
  2 * aE / (m * b * Δ) * (1 + m ^ 2 / k) +
    4 * n * m * e / (T * Δ) + 2 * k * e ^ 2 / (n * T)

/-- Exact normalization: all three original geometric costs remain visible.
The density is the actual thick cardinal divided by the host cardinal. -/
theorem alpogeNativeGeometricErrorBracket_div_eq
    (T h n m b k aE e : ℝ)
    (hT : T ≠ 0) (hh : h ≠ 0) (hn : n ≠ 0)
    (hm : m ≠ 0) (hb : b ≠ 0) :
    alpogeNativeGeometricErrorBracket T h n m b k aE e /
        (T * m * b * (h / n) / 2) =
      alpogeNativeNormalizedGeometricCosts T (h / n) n m b k aE e := by
  unfold alpogeNativeGeometricErrorBracket alpogeNativeNormalizedGeometricCosts
  by_cases hk : k = 0
  · subst k
    simp only [div_zero, add_zero, mul_zero]
    field_simp [hT, hh, hn, hm, hb]; ring
  · field_simp [hT, hh, hn, hm, hb, hk]; ring

/-- Attach the normalization to the divisor already derived by character
orthogonality, rather than defining an unrelated scalar denominator. -/
theorem alpogeNativeGeometricErrorBracket_div_projectionDivisor
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (TT T2 : Finset H) (m : ℕ) (b k aE e : ℝ)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m)
    (hb : 0 < b) :
    alpogeNativeGeometricErrorBracket
        TT.card T2.card (Fintype.card H) m b k aE e /
        alpogeNativeProjectionDivisor TT T2 m b =
      alpogeNativeNormalizedGeometricCosts
        TT.card (alpogeNativeProjectionDensity T2) (Fintype.card H) m b k aE e := by
  have hT : (TT.card : ℝ) ≠ 0 := by exact_mod_cast hTT.card_pos.ne'
  have hh : (T2.card : ℝ) ≠ 0 := by exact_mod_cast hT2.card_pos.ne'
  have hn : (Fintype.card H : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H).ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  exact alpogeNativeGeometricErrorBracket_div_eq _ _ _ _ _ _ _ _
    hT hh hn hm' hb.ne'

/-- The original additive transport cost is also normalized explicitly.
The factor `T*m*b` cancels, while the density cost survives. -/
theorem alpogeNativeTransportCost_div_projectionDivisor
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (TT T2 : Finset H) (m : ℕ) (b x : ℝ)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m)
    (hb : 0 < b) :
    (2 * (TT.card : ℝ) * (m : ℝ) * b / x) /
        alpogeNativeProjectionDivisor TT T2 m b =
      4 / (alpogeNativeProjectionDensity T2 * x) := by
  have hT : (TT.card : ℝ) ≠ 0 := by exact_mod_cast hTT.card_pos.ne'
  have hh : (T2.card : ℝ) ≠ 0 := by exact_mod_cast hT2.card_pos.ne'
  have hn : (Fintype.card H : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H).ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold alpogeNativeProjectionDivisor alpogeNativeProjectionDensity
  by_cases hx : x = 0
  · simp [hx]
  · field_simp [hT, hh, hn, hm', hb.ne', hx]; ring

end RHLean.Analysis
