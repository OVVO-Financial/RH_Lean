import «research.EULER_DOUBLE_CENTERED_SOURCE_20261117»

/-! Signed divisor rank and two-row probes on the original frozen floor source. -/

set_option autoImplicit false
noncomputable section

namespace RHLean.Proof

open RHLean.Analysis

/-- A principal restriction, with the original coefficient on both axes. -/
def eulerFrozenMatrix (R : ℕ) (S : Finset ℕ) : Matrix S S ℚ :=
  fun a b => eulerMuQ a * eulerMuQ b * eulerFloorQ R a b

theorem eulerFloorQ_of_root_divisors {R a b : ℕ} (hR : 0 < R)
    (ha : a ∣ R) (hb : b ∣ R) :
    eulerFloorQ R a b = ((R / a : ℕ) : ℚ) * ((R / b : ℕ) : ℚ) - 1 := by
  let k := (R / a) * (R / b)
  have hfac : (a * b) * k = R ^ 2 := by
    dsimp [k]
    calc
      _ = ((R / a) * a) * ((R / b) * b) := by ring
      _ = _ := by rw [Nat.div_mul_cancel ha, Nat.div_mul_cancel hb, pow_two]
  have hp : 0 < (a * b) * k := by rw [hfac]; positivity
  have hk : 1 ≤ k := Nat.pos_of_mul_pos_left hp
  have hquot : squareRootEndpoint R / (a * b) = k - 1 := by
    unfold squareRootEndpoint
    rw [← hfac]
    simpa using Nat.mul_sub_div 0 (a * b) k hp
  unfold eulerFloorQ
  rw [hquot, Nat.cast_sub hk]
  simp [k]

theorem eulerFrozen_rank_le_two {R : ℕ} (hR : 0 < R) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a ∣ R) : (eulerFrozenMatrix R S).rank ≤ 2 := by
  classical
  let u (a : S) : ℚ := eulerMuQ a * ((R / (a : ℕ) : ℕ) : ℚ)
  let v (a : S) : ℚ := eulerMuQ a
  let A : Matrix S (Fin 2) ℚ := fun a => ![u a, v a]
  let B : Matrix (Fin 2) S ℚ := fun i b => ![u b, -v b] i
  have h : eulerFrozenMatrix R S = A * B := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change eulerMuQ i * eulerMuQ j * eulerFloorQ R i j = u i * u j + v i * (-v j)
    dsimp only [u, v]
    rw [eulerFloorQ_of_root_divisors hR (hS _ i.property) (hS _ j.property)]
    ring
  rw [h]
  exact (Matrix.rank_mul_le_left A B).trans (by simpa using Matrix.rank_le_card_width A)

theorem eulerFrozen_prime_minor {R p : ℕ} (hR : 0 < R) (hp : p.Prime) (hd : p ∣ R) :
    let W := fun a b => eulerMuQ a * eulerMuQ b * eulerFloorQ R a b
    W 1 1 * W p p - W 1 p * W p 1 = -((R : ℚ) - ((R / p : ℕ) : ℚ)) ^ 2 := by
  dsimp only
  rw [eulerFloorQ_of_root_divisors hR (one_dvd _) (one_dvd _),
    eulerFloorQ_of_root_divisors hR hd hd, eulerFloorQ_of_root_divisors hR (one_dvd _) hd,
    eulerFloorQ_of_root_divisors hR hd (one_dvd _)]
  simp [eulerMuQ, ArithmeticFunction.moebius_apply_prime hp] <;> ring

theorem eulerFrozen_rank_eq_two {R p : ℕ} (hR : 0 < R) (hp : p.Prime)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a ∣ R) (h1 : 1 ∈ S) (hm : p ∈ S) :
    (eulerFrozenMatrix R S).rank = 2 := by
  classical
  let i : Fin 2 → S := ![⟨1, h1⟩, ⟨p, hm⟩]
  let M := (eulerFrozenMatrix R S).submatrix i i
  have hdet : M.det = -((R : ℚ) - ((R / p : ℕ) : ℚ)) ^ 2 := by
    rw [Matrix.det_fin_two]
    exact eulerFrozen_prime_minor hR hp (hS _ hm)
  have hlt : ((R / p : ℕ) : ℚ) < (R : ℚ) := by exact_mod_cast Nat.div_lt_self hR hp.one_lt
  have hne : M.det ≠ 0 := by rw [hdet]; exact neg_ne_zero.mpr (pow_ne_zero _ (sub_ne_zero.mpr hlt.ne'))
  have hr : M.rank = 2 := by simpa using Matrix.rank_of_det_ne_zero hne
  exact le_antisymm (eulerFrozen_rank_le_two hR S hS)
    (hr ▸ (eulerFrozenMatrix R S).rank_submatrix_le i i)

/-- Probe with physical coefficients and weights (a,-b). Both mixed orientations are retained. -/
def eulerTwoRowProbe (F : ℕ → ℕ → ℚ) (a b : ℕ) : ℚ :=
  let u := (a : ℚ) * eulerMuQ a
  let v := (b : ℚ) * eulerMuQ b
  u * u * F a a - u * v * F a b - v * u * F b a + v * v * F b b

private theorem mul_floor_remainder (R a b : ℕ) :
    (a : ℚ) * (b : ℚ) * eulerFloorQ R a b = (squareRootEndpoint R : ℚ) -
      ((squareRootEndpoint R % (a*b) : ℕ) : ℚ) := by
  have h : ((squareRootEndpoint R % (a*b) : ℕ) : ℚ) +
      ((a : ℚ)*b) * ((squareRootEndpoint R / (a*b) : ℕ) : ℚ) = (squareRootEndpoint R : ℚ) := by
    exact_mod_cast Nat.mod_add_div (squareRootEndpoint R) (a*b)
  unfold eulerFloorQ
  linarith

private theorem prime_probe (F : ℕ → ℕ → ℚ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    eulerTwoRowProbe F p q = (p : ℚ)*p*F p p - (p : ℚ)*q*F p q -
      (q : ℚ)*p*F q p + (q : ℚ)*q*F q q := by
  simp [eulerTwoRowProbe, eulerMuQ, ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hq]

theorem eulerTwoRow_floor_mod (R : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    let X := squareRootEndpoint R
    eulerTwoRowProbe (eulerFloorQ R) p q = 2 * ((X % (p*q) : ℕ) : ℚ) -
      ((X % (p*p) : ℕ) : ℚ) - ((X % (q*q) : ℕ) : ℚ) := by
  dsimp only
  rw [prime_probe _ hp hq]
  simp_rw [mul_floor_remainder]
  rw [Nat.mul_comm q p]
  ring

theorem eulerTwoRow_continuous_zero (R : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    eulerTwoRowProbe (eulerContinuousQ R) p q = 0 := by
  rw [prime_probe _ hp hq]
  simp only [eulerContinuousQ]
  have h : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have k : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  field_simp [h,k] <;> ring

theorem eulerTwoRow_interior (R : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdp : ¬p ∣ R-1) (hdq : ¬q ∣ R-1) :
    eulerTwoRowProbe (eulerDoubleCenteredInteriorKernelQ R) p q =
      eulerTwoRowProbe (eulerFloorQ R) p q + eulerDoubleCenterScaleQ R *
      ((((R-1) % p : ℕ) : ℚ) - (((R-1) % q : ℕ) : ℚ)) ^ 2 := by
  have hc := eulerTwoRow_continuous_zero R hp hq
  rw [prime_probe _ hp hq] at hc
  rw [prime_probe _ hp hq, prime_probe _ hp hq]
  simp only [eulerDoubleCenteredInteriorKernelQ, hdp, hdq, or_self, if_false,
    eulerDoubleCenteredKernelQ, eulerFractionQ]
  rw [eulerHistoricalFracQ_eq_mod_div R p hp.pos, eulerHistoricalFracQ_eq_mod_div R q hq.pos]
  have h : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have k : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  linear_combination (norm := (field_simp [h,k] <;> ring)) -hc

/-- Common membership and the values of both literal quadratic forms. -/
def eulerTwoRowWitness (R : ℕ) (v : ℚ) : Prop :=
  3 ∈ Finset.Icc 1 (R-1) ∧ 5 ∈ Finset.Icc 1 (R-1) ∧
  (¬3 ∣ R) ∧ (¬5 ∣ R) ∧ (¬3 ∣ R-1) ∧ (¬5 ∣ R-1) ∧
  eulerTwoRowProbe (eulerContinuousQ R) 3 5 = 0 ∧
  eulerTwoRowProbe (eulerFloorQ R) 3 5 = v ∧
  eulerTwoRowProbe (eulerDoubleCenteredInteriorKernelQ R) 3 5 = v

private theorem witness_of_residues {R : ℕ} (hR : 6 ≤ R) (h3 : R % 3 = 2)
    (h5 : R % 5 = 2) (v : ℚ)
    (hv : 2 * ((squareRootEndpoint R % 15 : ℕ) : ℚ) -
      ((squareRootEndpoint R % 9 : ℕ) : ℚ) - ((squareRootEndpoint R % 25 : ℕ) : ℚ) = v) :
    eulerTwoRowWitness R v := by
  have h3' : ¬3 ∣ R-1 := by omega
  have h5' : ¬5 ∣ R-1 := by omega
  have hf := eulerTwoRow_floor_mod R Nat.prime_three (by decide : Nat.Prime 5)
  have hraw : eulerTwoRowProbe (eulerFloorQ R) 3 5 = v := hf.trans hv
  refine ⟨Finset.mem_Icc.mpr ⟨by decide, by omega⟩, Finset.mem_Icc.mpr ⟨by decide, by omega⟩,
    by omega, by omega, h3', h5', eulerTwoRow_continuous_zero R Nat.prime_three (by decide), hraw, ?_⟩
  rw [eulerTwoRow_interior R Nat.prime_three (by decide) h3' h5', hraw,
    show (R-1) % 3 = 1 by omega, show (R-1) % 5 = 1 by omega]
  simp

theorem eulerTwoRow_sign_families (n : ℕ) :
    eulerTwoRowWitness (225*n+17) (-7) ∧ eulerTwoRowWitness (225*n+152) 3 ∧
      eulerTwoRowWitness (225*n+227) 0 := by
  have shift (b : ℕ) (hb : 1 ≤ b) :
      squareRootEndpoint (225*n+b) = 225*(225*n*n+2*n*b)+(b*b-1) := by
    have h : (225*n+b)^2 = 225*(225*n*n+2*n*b)+b*b := by ring
    unfold squareRootEndpoint
    rw [h, Nat.add_sub_assoc (show 1 ≤ b*b from Nat.mul_pos hb hb)]
  have m15 (t c : ℕ) : (225*t+c) % 15 = c % 15 := by omega
  have m9 (t c : ℕ) : (225*t+c) % 9 = c % 9 := by omega
  have m25 (t c : ℕ) : (225*t+c) % 25 = c % 25 := by omega
  constructor
  · apply witness_of_residues (by omega) (by omega) (by omega)
    rw [shift 17 (by decide)]
    norm_num [m15, m9, m25]
  constructor
  · apply witness_of_residues (by omega) (by omega) (by omega)
    rw [shift 152 (by decide)]
    norm_num [m15, m9, m25]
  · apply witness_of_residues (by omega) (by omega) (by omega)
    rw [shift 227 (by decide)]
    norm_num [m15, m9, m25]

end RHLean.Proof
