import «research.NYMAN_WITNESS_CLIP»

/-! TWO-WITNESS: rational relations and clipping fibres for the actual two-band residual. -/
set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace RHLean.Analysis

private def massQ (a b : ℕ) : ℚ := ∑ k ∈ Ioc a b, 1/(k:ℚ)
private theorem castMass (a b : ℕ) : (massQ a b : ℝ) = nymanRidgeS a b := by
  simp [massQ, nymanRidgeS]

/-- Distinct prime coordinates force rational independence of the physical repair amplitudes. -/
theorem nyman_witness_two_amplitudes (K H p q : ℕ) (hH : 0 < H) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (lp : max (3*K) H < p) (up : p < 6*K)
    (lq : max (3*K) H < q) (uq : q < 6*K) (x y : ℚ) :
    (x:ℝ)*nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) +
      (y:ℝ)*nymanRidgeRight K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) = 0 ↔
      x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hk : 0 < K := by omega
    have hkq : (K:ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    have hkr : (K:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hd := (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/12) (nyman_ridge_gap K hk)).ne'
    let s := massQ (3*K) (4*K)
    let t := massQ (5*K) (6*K)
    let D : ℚ := (y*s-x*t)/K
    have eqn : ((x-y:ℚ):ℝ)*nymanFlatMoment (6*K) H + (D:ℝ)*nymanRidgeV K H = 0 := by
      dsimp only [D, s, t]
      push_cast
      rw [castMass, castMass]
      calc
        _ = ((x:ℝ)*nymanRidgeLeft K (nymanFlatMoment (6*K) H) (nymanRidgeV K H) +
            (y:ℝ)*nymanRidgeRight K (nymanFlatMoment (6*K) H) (nymanRidgeV K H)) * nymanRidgeGap K := by
          unfold nymanRidgeLeft nymanRidgeRight
          field_simp [hkr, hd]
          ring
        _ = 0 := by rw [h, zero_mul]
    have pr := nyman_witness_relation_coordinate K H p hp (by omega) up hH (by omega) (x-y) D eqn
    have qr := nyman_witness_relation_coordinate K H q hq (by omega) uq hH (by omega) (x-y) D eqn
    have diff : ((p:ℚ)-q)*D = 0 := by linear_combination pr - qr
    have hpq' : (p:ℚ) ≠ q := by exact_mod_cast hpq
    have hD := (mul_eq_zero.mp diff).resolve_left (sub_ne_zero.mpr hpq')
    have hxy : x = y := sub_eq_zero.mp (by simpa [hD] using pr)
    have hnum : y*s-x*t = 0 := (div_eq_zero_iff.mp (show (y*s-x*t)/(K:ℚ) = 0 from hD)).resolve_right hkq
    have hs : s ≠ t := by
      intro he
      have hc := congrArg (fun w : ℚ => (w:ℝ)) he
      change (massQ (3*K) (4*K):ℝ) = (massQ (5*K) (6*K):ℝ) at hc
      rw [castMass, castMass] at hc
      exact hd (sub_eq_zero.mpr hc)
    have hz : x*(s-t) = 0 := calc
      _ = x*s-x*t := mul_sub x s t
      _ = y*s-x*t := congrArg (fun w : ℚ => w*s-x*t) hxy
      _ = 0 := hnum
    have hx := (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hs)
    exact ⟨hx, hxy.symm.trans hx⟩
  · rintro ⟨rfl,rfl⟩
    simp

/-- A repeated error value is precisely a plateau of both integer floor counts. -/
theorem nyman_witness_clip_fibres (K H p q : ℕ) (hH : 0 < H) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (lp : max (3*K) H < p) (up : p < 6*K)
    (lq : max (3*K) H < q) (uq : q < 6*K) (m n : ℕ) :
    nymanWitnessError K H m = nymanWitnessError K H n ↔
      nymanBandCount (3*K) (4*K) m = nymanBandCount (3*K) (4*K) n ∧
      nymanBandCount (5*K) (6*K) m = nymanBandCount (5*K) (6*K) n := by
  have hk : 0 < K := by omega
  have hL := (nymanFlatScale_pos (6*K) H hH (by omega)).ne'
  rw [nyman_witness_error_counts K H m hk, nyman_witness_error_counts K H n hk]
  constructor
  · intro he
    have hh := congrArg (fun w : ℝ => w * nymanFlatScale (6*K) H) he
    dsimp only at hh
    rw [div_mul_cancel₀ _ hL, div_mul_cancel₀ _ hL] at hh
    let c (i : ℕ) := nymanBandCount (3*K) (4*K) i
    let e (i : ℕ) := nymanBandCount (5*K) (6*K) i
    have test := nyman_witness_two_amplitudes K H p q hH hp hq hpq lp up lq uq
      ((c m:ℚ)-c n) ((e m:ℚ)-e n)
    have hzero : ((c m:ℚ)-c n) = 0 ∧ ((e m:ℚ)-e n) = 0 := by
      apply test.mp
      push_cast
      dsimp only [c,e]
      linear_combination hh
    exact ⟨by exact_mod_cast sub_eq_zero.mp hzero.1, by exact_mod_cast sub_eq_zero.mp hzero.2⟩
  · rintro ⟨hc,he⟩
    rw [hc,he]

/-- The clipped formula agrees exactly at saturation and the following output, nowhere else. -/
theorem nyman_witness_clip_zero_iff (K H p q : ℕ) (hH : 0 < H) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (lp : max (3*K) H < p) (up : p < 6*K)
    (lq : max (3*K) H < q) (uq : q < 6*K) (m : ℕ) :
    nymanWitnessError K H m = 0 ↔ m = 6*K ∨ m = 6*K+1 := by
  have hk : 0 < K := by omega
  obtain ⟨hc,he⟩ := nyman_ridge_first_layer K (6*K) (by omega)
  have cs : nymanBandCount (3*K) (4*K) (6*K) = K := by omega
  have es : nymanBandCount (5*K) (6*K) (6*K) = K := by omega
  have hz : nymanWitnessError K H (6*K) = 0 := by
    rw [nyman_witness_error_counts K H (6*K) hk, cs, es]
    simp
  have hf := nyman_witness_clip_fibres K H p q hH hp hq hpq lp up lq uq m (6*K)
  rw [hz,cs,es] at hf
  rw [hf]
  by_cases hm : m ≤ 6*K+1
  · obtain ⟨h1,h2⟩ := nyman_ridge_first_layer K m hm
    rw [h1,h2]
    omega
  · have hmono : nymanBandCount (3*K) (4*K) (6*K+2) ≤ nymanBandCount (3*K) (4*K) m := by
      unfold nymanBandCount
      exact Finset.sum_le_sum (fun _ _ => Nat.div_le_div_right (by omega))
    rw [(nyman_ridge_first_double K hk).1] at hmono
    omega

end RHLean.Analysis
