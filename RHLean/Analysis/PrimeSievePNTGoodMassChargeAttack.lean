import Mathlib
import RHLean.Analysis.PrimeSievePNTGoodMassAmplification

/-!
# First attack on the PNT good-mass packet charge

The #329 amplification theorem makes the scalar Selberg good mass
`nativeLambdaTwoGoodRecipMass N 1` an explicit positive coefficient in the
route to the critical packet estimate.  Before trying to exploit individual
good fibres, it is important to calibrate exactly how much strength is hidden
in the factorized scalar charge.

This file proves two deterministic facts.

* The good reciprocal `Lambda_2` mass is bounded above by the total reciprocal
  `Lambda_2` mass.
* Consequently the additive descendant-persistence statement from #329 already
  implies the factorized PNT good-mass charge.  Together with #329's converse,
  the two statements are equivalent at the level of block-uniform
  subpolynomial estimates.

Thus any genuinely new use of positive PNT good mass must eventually open the
sum over good fibres and couple those fibres locally to packet descendants;
leaving the good mass as one scalar factor does not weaken additive persistence.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- The good reciprocal `Lambda_2` mass is a positive submass of the total
reciprocal `Lambda_2` mass. -/
theorem nativeLambdaTwoGoodRecipMass_le_recipMass
    (N : ℕ) (beta : ℝ) :
    nativeLambdaTwoGoodRecipMass N beta ≤ nativeLambdaTwoRecipMass N := by
  unfold nativeLambdaTwoGoodRecipMass nativeLambdaTwoRecipMass
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (nativePNTGoodFiberSet_subset N beta) ?_
  intro n hn _hgood
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)

/-- On every scale `N >= 3`, the good reciprocal mass is bounded by a fixed
multiple of `log(N)^2`.  The constant is deliberately left in terms of
`log 2`; only positivity matters for the amplification argument. -/
theorem nativeLambdaTwoGoodRecipMass_le_const_mul_log_sq
    (N : ℕ) (beta : ℝ) (hN : 3 ≤ N) :
    nativeLambdaTwoGoodRecipMass N beta ≤
      (1 + 1000 / Real.log 2 + 2000 / (Real.log 2) ^ 2) *
        (Real.log (N : ℝ)) ^ 2 := by
  let L : ℝ := Real.log (N : ℝ)
  let l2 : ℝ := Real.log 2
  have hNgt : 1 < N := by omega
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hNgt)
  have hl2pos : 0 < l2 := by
    dsimp [l2]
    exact Real.log_pos (by norm_num)
  have htwoN : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 2 ≤ N by omega)
  have hlower : l2 ≤ L := by
    dsimp [l2, L]
    exact Real.log_le_log (by norm_num) htwoN
  have hquad : l2 * L ≤ L ^ 2 := by
    have := mul_le_mul_of_nonneg_right hlower hLpos.le
    nlinarith
  have hsq : l2 ^ 2 ≤ L ^ 2 := by
    nlinarith [sq_nonneg (L - l2)]
  have hlin : 1000 * L ≤ (1000 / l2) * L ^ 2 := by
    have hfac : 0 ≤ 1000 / l2 := div_nonneg (by norm_num) hl2pos.le
    have h := mul_le_mul_of_nonneg_left hquad hfac
    have hl2ne : l2 ≠ 0 := ne_of_gt hl2pos
    field_simp [hl2ne] at h ⊢
    nlinarith
  have hconst : (2000 : ℝ) ≤ (2000 / l2 ^ 2) * L ^ 2 := by
    have hl2sqpos : 0 < l2 ^ 2 := sq_pos_of_pos hl2pos
    have hfac : 0 ≤ 2000 / l2 ^ 2 := div_nonneg (by norm_num) hl2sqpos.le
    have h := mul_le_mul_of_nonneg_left hsq hfac
    have hl2sqne : l2 ^ 2 ≠ 0 := ne_of_gt hl2sqpos
    field_simp [hl2sqne] at h ⊢
    nlinarith
  have htotal := nativeLambdaTwoRecipMass_upper N hN
  have hgood := nativeLambdaTwoGoodRecipMass_le_recipMass N beta
  calc
    nativeLambdaTwoGoodRecipMass N beta ≤ nativeLambdaTwoRecipMass N := hgood
    _ ≤ L ^ 2 + 1000 * L + 2000 := by simpa [L] using htotal
    _ ≤ (1 + 1000 / l2 + 2000 / l2 ^ 2) * L ^ 2 := by
      nlinarith [hlin, hconst]
    _ = (1 + 1000 / Real.log 2 + 2000 / (Real.log 2) ^ 2) *
        (Real.log (N : ℝ)) ^ 2 := by rfl

/-- **Calibration of the factorized #329 charge.**  Additive descendant
persistence already implies the PNT good-mass charge.  The proof only uses the
upper bound for total reciprocal `Lambda_2` mass; it does not use the PNT lower
bound.

Combined with
`dyadicPacketAdditiveDescendantPersistence_of_pntGoodMassCharge`, this shows
that the scalar factorized charge and additive persistence are equivalent up to
an absolute change of constants. -/
theorem dyadicPacketPNTGoodMassCharge_of_additiveDescendantPersistence
    (cutoff : DyadicPacketCutoff)
    (hA : DyadicPacketAdditiveDescendantPersistenceStatement cutoff) :
    DyadicPacketPNTGoodMassChargeStatement cutoff := by
  intro ε hε B
  obtain ⟨CA, hCA, hAb⟩ := hA ε hε
  let K : ℝ := 1 + 1000 / Real.log 2 + 2000 / (Real.log 2) ^ 2
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K * CA, mul_nonneg hK0 hCA, ?_⟩
  intro k x hk hlow hup
  let y := primorialPNTPrimeSieveCutoff k
  let J := cutoff k x
  let N : ℕ := x + B + 2
  let Q : ℝ := (Real.log (N : ℝ)) ^ 2
  let P : ℝ := Real.rpow ((x : ℝ) + 1) ε
  let A : ℝ := primeSieveDyadicPacketLevelEnergy y x J + ((x : ℝ) + 1)
  let D : ℝ := primeSieveDyadicPacketDeepEnergy y x (J + 1)
  have hxpos : 0 < x := by
    have hW := primorialEndpoint_pos k
    dsimp [primorialBlockLower] at hlow
    omega
  have hN3 : 3 ≤ N := by dsimp [N]; omega
  have hmass : nativeLambdaTwoGoodRecipMass N 1 ≤ K * Q := by
    simpa [K, Q] using
      nativeLambdaTwoGoodRecipMass_le_const_mul_log_sq N 1 hN3
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact primeSieveDyadicPacketDeepEnergy_nonneg y x (J + 1)
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hKQ0 : 0 ≤ K * Q := mul_nonneg hK0 hQ0
  have hpersist : D ≤ CA * P * A := by
    simpa [y, J, P, A, D] using hAb k x hk hlow hup
  calc
    nativeLambdaTwoGoodRecipMass N 1 * D ≤ (K * Q) * D :=
      mul_le_mul_of_nonneg_right hmass hD0
    _ ≤ (K * Q) * (CA * P * A) :=
      mul_le_mul_of_nonneg_left hpersist hKQ0
    _ = (K * CA) * Q * P * A := by ring

/-- The two #329 packet statements are therefore equivalent. -/
theorem dyadicPacketPNTGoodMassCharge_iff_additiveDescendantPersistence
    (cutoff : DyadicPacketCutoff) :
    DyadicPacketPNTGoodMassChargeStatement cutoff ↔
      DyadicPacketAdditiveDescendantPersistenceStatement cutoff := by
  constructor
  · exact dyadicPacketAdditiveDescendantPersistence_of_pntGoodMassCharge cutoff
  · exact dyadicPacketPNTGoodMassCharge_of_additiveDescendantPersistence cutoff

/-! ## Reciprocal-coordinate geometry -/

/-- Consecutive reciprocal floors differ by their continuous hyperbolic gap,
up to the single unit lost by taking the second floor. -/
theorem natCast_div_sub_div_succ_le
    (x d : ℕ) (hd : 1 ≤ d) :
    ((x / d : ℕ) : ℝ) - ((x / (d + 1) : ℕ) : ℝ) ≤
      (x : ℝ) / ((d : ℝ) * ((d + 1 : ℕ) : ℝ)) + 1 := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hspos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hfloorcast :
      (⌊(x : ℝ) / ((d + 1 : ℕ) : ℝ)⌋ : ℝ) =
        ((x / (d + 1) : ℕ) : ℝ) := by
    have hz :
        ⌊(x : ℝ) / ((d + 1 : ℕ) : ℝ)⌋ =
          ((x / (d + 1) : ℕ) : ℤ) := by
      rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
    rw [hz]
    norm_cast
  have hfract :
      Int.fract ((x : ℝ) / ((d + 1 : ℕ) : ℝ)) =
        (x : ℝ) / ((d + 1 : ℕ) : ℝ) -
          ((x / (d + 1) : ℕ) : ℝ) := by
    rw [← Int.self_sub_floor, hfloorcast]
  have hfractLt := Int.fract_lt_one ((x : ℝ) / ((d + 1 : ℕ) : ℝ))
  rw [hfract] at hfractLt
  have hreal :
      (x : ℝ) / (d : ℝ) - (x : ℝ) / ((d + 1 : ℕ) : ℝ) =
        (x : ℝ) / ((d : ℝ) * ((d + 1 : ℕ) : ℝ)) := by
    field_simp [ne_of_gt hdpos, ne_of_gt hspos]
    push_cast
    ring
  rw [← hreal]
  linarith

/-- A reciprocal prime-minus-Li fibre is controlled by the hyperbolic width of
its quotient interval.  This is completely elementary: prime count is bounded
by interval cardinality and Li drifts by at most interval length divided by
`log 2`. -/
theorem primeSieveReciprocalPrimeDiscrepancy_norm_le_floorScale
    {y x d : ℕ} (hy : 2 ≤ y)
    (hd : d ∈ primeSieveQuotientSupport y x) :
    ‖primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤
      (1 + 1 / Real.log 2) *
        ((x : ℝ) / ((d : ℝ) * ((d + 1 : ℕ) : ℝ)) + 1) := by
  have hdI := Finset.mem_Icc.mp hd
  have hd1 : 1 ≤ d := hdI.1
  have hydiv : y < x / d := lt_div_of_mem_primeSieveQuotientSupport hd
  have hmono : x / (d + 1) ≤ x / d :=
    Nat.div_le_div_left (by omega) (by omega)
  have hle :
      primeSieveReciprocalLower y x d ≤ primeSieveReciprocalUpper x d := by
    unfold primeSieveReciprocalLower primeSieveReciprocalUpper
    exact max_le hydiv.le hmono
  have hlower2 : 2 ≤ primeSieveReciprocalLower y x d := by
    exact hy.trans (le_max_left y (x / (d + 1)))
  have hcount :
      ‖primeSieveReciprocalPrimeCount y x d‖ ≤
        (primeSieveReciprocalUpper x d : ℝ) -
          (primeSieveReciprocalLower y x d : ℝ) := by
    rw [primeSieveReciprocalPrimeCount_eq_card]
    have hcard :
        ((primeSieveReciprocalInterval y x d).filter Nat.Prime).card ≤
          (primeSieveReciprocalInterval y x d).card :=
      Finset.card_filter_le _ _
    have hcardI :
        (primeSieveReciprocalInterval y x d).card =
          primeSieveReciprocalUpper x d -
            primeSieveReciprocalLower y x d := by
      simp [primeSieveReciprocalInterval, Nat.card_Ioc]
    rw [Complex.norm_natCast]
    calc
      (((primeSieveReciprocalInterval y x d).filter Nat.Prime).card : ℝ) ≤
          ((primeSieveReciprocalInterval y x d).card : ℝ) := by
        exact_mod_cast hcard
      _ = ((primeSieveReciprocalUpper x d -
          primeSieveReciprocalLower y x d : ℕ) : ℝ) := by rw [hcardI]
      _ = (primeSieveReciprocalUpper x d : ℝ) -
          (primeSieveReciprocalLower y x d : ℝ) := by
        rw [Nat.cast_sub hle]
  have hli0 :=
    abs_logarithmicIntegralFromTwo_sub_le_log_succ
      (y := 1)
      (a := (primeSieveReciprocalLower y x d : ℝ))
      (b := (primeSieveReciprocalUpper x d : ℝ))
      (by norm_num)
      (by exact_mod_cast hlower2)
      (by exact_mod_cast hle)
  have hli :
      ‖primeSieveReciprocalLiMass y x d‖ ≤
        ((primeSieveReciprocalUpper x d : ℝ) -
          (primeSieveReciprocalLower y x d : ℝ)) / Real.log 2 := by
    rw [primeSieveReciprocalLiMass, if_pos hle]
    have hnorm :
        ‖(((logarithmicIntegralFromTwo (primeSieveReciprocalUpper x d : ℝ) -
            logarithmicIntegralFromTwo (primeSieveReciprocalLower y x d : ℝ) : ℝ)) : ℂ)‖ =
          |logarithmicIntegralFromTwo (primeSieveReciprocalUpper x d : ℝ) -
            logarithmicIntegralFromTwo (primeSieveReciprocalLower y x d : ℝ)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    norm_num at hli0
    exact hli0
  have hwidth :
      (primeSieveReciprocalUpper x d : ℝ) -
          (primeSieveReciprocalLower y x d : ℝ) ≤
        ((x / d : ℕ) : ℝ) - ((x / (d + 1) : ℕ) : ℝ) := by
    unfold primeSieveReciprocalUpper primeSieveReciprocalLower
    exact sub_le_sub_left
      (by exact_mod_cast (le_max_right y (x / (d + 1)))) _
  have hcoef : 0 ≤ 1 + 1 / Real.log 2 := by
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hgap := natCast_div_sub_div_succ_le x d hd1
  unfold primeSieveReciprocalPrimeDiscrepancy
  calc
    ‖primeSieveReciprocalPrimeCount y x d -
        primeSieveReciprocalLiMass y x d‖ ≤
      ‖primeSieveReciprocalPrimeCount y x d‖ +
        ‖primeSieveReciprocalLiMass y x d‖ := norm_sub_le _ _
    _ ≤ ((primeSieveReciprocalUpper x d : ℝ) -
          (primeSieveReciprocalLower y x d : ℝ)) +
        ((primeSieveReciprocalUpper x d : ℝ) -
          (primeSieveReciprocalLower y x d : ℝ)) / Real.log 2 :=
      add_le_add hcount hli
    _ = (1 + 1 / Real.log 2) *
        ((primeSieveReciprocalUpper x d : ℝ) -
          (primeSieveReciprocalLower y x d : ℝ)) := by ring
    _ ≤ (1 + 1 / Real.log 2) *
        (((x / d : ℕ) : ℝ) - ((x / (d + 1) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hwidth hcoef
    _ ≤ (1 + 1 / Real.log 2) *
        ((x : ℝ) / ((d : ℝ) * ((d + 1 : ℕ) : ℝ)) + 1) :=
      mul_le_mul_of_nonneg_left hgap hcoef

/-- On a live dyadic reciprocal block, the post-square-root support absorbs the
floor defect in the preceding theorem.  Every fibre on the `j`-th block is
therefore genuinely of hyperbolic size `O(x / 4^j)`. -/
theorem primeSieveReciprocalPrimeDiscrepancy_norm_le_dyadicScale
    {k x j d : ℕ}
    (hk : 2 ≤ k)
    (hup : x ≤ primorialBlockUpper k)
    (hdB : d ∈ primeSieveDyadicBlock
      (primorialPNTPrimeSieveCutoff k) x j) :
    ‖primeSieveReciprocalPrimeDiscrepancy
        (primorialPNTPrimeSieveCutoff k) x d‖ ≤
      (2 * (1 + 1 / Real.log 2)) *
        ((x : ℝ) / (((2 ^ j : ℕ) : ℝ) ^ 2)) := by
  let y := primorialPNTPrimeSieveCutoff k
  let P : ℝ := ((2 ^ j : ℕ) : ℝ)
  let D : ℝ := (d : ℝ) * ((d + 1 : ℕ) : ℝ)
  have hy5 : 5 ≤ primorialWheelCutoff k := five_le_primorialWheelCutoff hk
  have hy2 : 2 ≤ y := by
    dsimp [y, primorialPNTPrimeSieveCutoff]
    omega
  have hdSupport : d ∈ primeSieveQuotientSupport y x := by
    simpa [y] using (mem_primeSieveDyadicBlock.mp hdB).1
  have hdI := Finset.mem_Icc.mp hdSupport
  have hd1 : 1 ≤ d := hdI.1
  have hprod : d * (y + 1) ≤ x :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos y)).1 hdI.2
  have hroot : Nat.sqrt x < y := by
    simpa [y] using
      sqrt_lt_primorialPNTPrimeSieveCutoff_of_le_upper (k := k) hup
  have hxsq : x < y ^ 2 := by
    have hs := Nat.lt_succ_sqrt' x
    have hsy : Nat.sqrt x + 1 ≤ y := by omega
    nlinarith
  have hdy : d ≤ y := by
    by_contra hnot
    have hyd : y < d := Nat.lt_of_not_ge hnot
    have hypos : 0 < y := by omega
    nlinarith [hprod]
  have hdenxNat : d * (d + 1) ≤ x := by
    have hsucc : d + 1 ≤ y + 1 := Nat.add_le_add_right hdy 1
    exact (Nat.mul_le_mul_left d hsucc).trans hprod
  have hdE := hdB
  rw [primeSieveDyadicBlock_eq_explicitIcc] at hdE
  have hpowd : 2 ^ j ≤ d := by
    have hleft := (Finset.mem_Icc.mp hdE).1
    simpa [primeSieveDyadicBlockLeft] using hleft
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hx0 : 0 ≤ (x : ℝ) := by positivity
  have hdenx : D ≤ (x : ℝ) := by
    dsimp [D]
    exact_mod_cast hdenxNat
  have hone : (1 : ℝ) ≤ (x : ℝ) / D := by
    rw [le_div_iff₀ hDpos]
    simpa using hdenx
  have hpowdR : P ≤ (d : ℝ) := by
    dsimp [P]
    exact_mod_cast hpowd
  have hsq : P ^ 2 ≤ (d : ℝ) ^ 2 :=
    pow_le_pow_left₀ hPpos.le hpowdR 2
  have hdSucc : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_succ d)
  have hdsq : (d : ℝ) ^ 2 ≤ D := by
    dsimp [D]
    have hmul := mul_le_mul_of_nonneg_left hdSucc (by positivity : (0 : ℝ) ≤ d)
    simpa [pow_two] using hmul
  have hdenLower : P ^ 2 ≤ D := hsq.trans hdsq
  have hP2pos : 0 < P ^ 2 := pow_pos hPpos 2
  have hdiv : (x : ℝ) / D ≤ (x : ℝ) / (P ^ 2) := by
    rw [div_le_div_iff₀ hDpos hP2pos]
    exact mul_le_mul_of_nonneg_left hdenLower hx0
  have hsum : (x : ℝ) / D + 1 ≤ 2 * ((x : ℝ) / (P ^ 2)) := by
    nlinarith [hone, hdiv]
  have hcoef : 0 ≤ 1 + 1 / Real.log 2 := by
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hfib :=
    primeSieveReciprocalPrimeDiscrepancy_norm_le_floorScale hy2 hdSupport
  calc
    ‖primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤
        (1 + 1 / Real.log 2) * ((x : ℝ) / D + 1) := by
      simpa [D] using hfib
    _ ≤ (1 + 1 / Real.log 2) *
        (2 * ((x : ℝ) / (P ^ 2))) :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = (2 * (1 + 1 / Real.log 2)) *
        ((x : ℝ) / (P ^ 2)) := by ring
    _ = (2 * (1 + 1 / Real.log 2)) *
        ((x : ℝ) / (((2 ^ j : ℕ) : ℝ) ^ 2)) := by rfl

/-- A uniform bound on the reciprocal prime-minus-Li fibres of an interval
controls the width-normalized signed sibling packet on that interval.  No
cancellation is used: each child sum costs its cardinality and the opposite
child-length weights cancel one power of the parent width after normalization. -/
theorem primeSieveSignedSiblingPacketResidual_norm_le_of_fibreBound
    {y x a m b : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (ha : 1 ≤ a) (ham : a ≤ m) (hmb : m ≤ b)
    (hb : b ≤ x / (y + 1) + 1)
    (hfib : ∀ d ∈ Finset.Ico a b,
      ‖primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤ δ) :
    ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ≤
      2 * ((b - a : ℕ) : ℝ) * δ := by
  have habLe : a ≤ b := ham.trans hmb
  by_cases hab : a < b
  · have hleft :
        ‖∑ d ∈ Finset.Ico a m,
            primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤
          ((m - a : ℕ) : ℝ) * δ := by
      calc
        ‖∑ d ∈ Finset.Ico a m,
            primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤
          ∑ d ∈ Finset.Ico a m,
            ‖primeSieveReciprocalPrimeDiscrepancy y x d‖ := by
              simpa using
                (norm_sum_le (Finset.Ico a m)
                  (fun d => primeSieveReciprocalPrimeDiscrepancy y x d))
        _ ≤ ∑ _d ∈ Finset.Ico a m, δ := by
          apply Finset.sum_le_sum
          intro d hd
          apply hfib d
          rw [Finset.mem_Ico] at hd ⊢
          omega
        _ = ((m - a : ℕ) : ℝ) * δ := by
          simp [Nat.card_Ico, nsmul_eq_mul]
    have hright :
        ‖∑ d ∈ Finset.Ico m b,
            primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤
          ((b - m : ℕ) : ℝ) * δ := by
      calc
        ‖∑ d ∈ Finset.Ico m b,
            primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤
          ∑ d ∈ Finset.Ico m b,
            ‖primeSieveReciprocalPrimeDiscrepancy y x d‖ := by
              simpa using
                (norm_sum_le (Finset.Ico m b)
                  (fun d => primeSieveReciprocalPrimeDiscrepancy y x d))
        _ ≤ ∑ _d ∈ Finset.Ico m b, δ := by
          apply Finset.sum_le_sum
          intro d hd
          apply hfib d
          rw [Finset.mem_Ico] at hd ⊢
          omega
        _ = ((b - m : ℕ) : ℝ) * δ := by
          simp [Nat.card_Ico, nsmul_eq_mul]
    have hpacket :
        ‖primeSieveSignedSiblingPacket y x a m b‖ ≤
          2 * ((m - a : ℕ) : ℝ) * ((b - m : ℕ) : ℝ) * δ := by
      rw [primeSieveSignedSiblingPacket_eq_weighted_intervalDiscrepancies
        ha ham hmb hb]
      calc
        ‖(((m - a : ℕ) : ℂ) *
              (∑ d ∈ Finset.Ico m b,
                primeSieveReciprocalPrimeDiscrepancy y x d)) -
            (((b - m : ℕ) : ℂ) *
              (∑ d ∈ Finset.Ico a m,
                primeSieveReciprocalPrimeDiscrepancy y x d))‖ ≤
          ‖((m - a : ℕ) : ℂ) *
              (∑ d ∈ Finset.Ico m b,
                primeSieveReciprocalPrimeDiscrepancy y x d)‖ +
            ‖((b - m : ℕ) : ℂ) *
              (∑ d ∈ Finset.Ico a m,
                primeSieveReciprocalPrimeDiscrepancy y x d)‖ := norm_sub_le _ _
        _ = ((m - a : ℕ) : ℝ) *
              ‖∑ d ∈ Finset.Ico m b,
                primeSieveReciprocalPrimeDiscrepancy y x d‖ +
            ((b - m : ℕ) : ℝ) *
              ‖∑ d ∈ Finset.Ico a m,
                primeSieveReciprocalPrimeDiscrepancy y x d‖ := by
          simp
        _ ≤ ((m - a : ℕ) : ℝ) * (((b - m : ℕ) : ℝ) * δ) +
            ((b - m : ℕ) : ℝ) * (((m - a : ℕ) : ℝ) * δ) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hright (by positivity))
            (mul_le_mul_of_nonneg_left hleft (by positivity))
        _ = 2 * ((m - a : ℕ) : ℝ) * ((b - m : ℕ) : ℝ) * δ := by ring
    let W : ℝ := ((b - a : ℕ) : ℝ)
    let L : ℝ := ((m - a : ℕ) : ℝ)
    let R : ℝ := ((b - m : ℕ) : ℝ)
    have hWpos : 0 < W := by
      dsimp [W]
      exact_mod_cast (show 0 < b - a by omega)
    have hLW : L ≤ W := by
      dsimp [L, W]
      exact_mod_cast (show m - a ≤ b - a by omega)
    have hRW : R ≤ W := by
      dsimp [R, W]
      exact_mod_cast (show b - m ≤ b - a by omega)
    have hLR : L * R ≤ W ^ 2 := by
      calc
        L * R ≤ W * R := mul_le_mul_of_nonneg_right hLW (by positivity)
        _ ≤ W * W := mul_le_mul_of_nonneg_left hRW hWpos.le
        _ = W ^ 2 := by ring
    have hpacketWide :
        ‖primeSieveSignedSiblingPacket y x a m b‖ ≤
          2 * W ^ 2 * δ := by
      calc
        ‖primeSieveSignedSiblingPacket y x a m b‖ ≤
            2 * L * R * δ := by simpa [L, R] using hpacket
        _ = (2 * δ) * (L * R) := by ring
        _ ≤ (2 * δ) * (W ^ 2) :=
          mul_le_mul_of_nonneg_left hLR (mul_nonneg (by norm_num) hδ)
        _ = 2 * W ^ 2 * δ := by ring
    unfold primeSieveSignedSiblingPacketResidual
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hscaled :=
      mul_le_mul_of_nonneg_left hpacketWide (inv_nonneg.mpr hWpos.le)
    calc
      W⁻¹ * ‖primeSieveSignedSiblingPacket y x a m b‖ ≤
          W⁻¹ * (2 * W ^ 2 * δ) := by
        simpa [W] using hscaled
      _ = 2 * W * δ := by
        field_simp [ne_of_gt hWpos]
      _ = 2 * ((b - a : ℕ) : ℝ) * δ := by rfl
  · have hba : b = a := by omega
    subst b
    have hma : m = a := by omega
    subst m
    simp [primeSieveSignedSiblingPacketResidual, primeSieveSignedSiblingPacket]

/-! ## Geometric decay through midpoint refinement -/

private theorem pntGoodMassAttack_midpoint_facts
    {a b : ℕ} (h : a + 1 < b) :
    a < dyadicPacketMidpoint a b ∧ dyadicPacketMidpoint a b < b := by
  unfold dyadicPacketMidpoint
  omega

private theorem pntGoodMassAttack_midpoint_child_widths
    {a b depth : ℕ}
    (hsplit : a + 1 < b)
    (hwidth : b - a ≤ 2 ^ (depth + 1)) :
    dyadicPacketMidpoint a b - a ≤ 2 ^ depth ∧
      b - dyadicPacketMidpoint a b ≤ 2 ^ depth := by
  have hp : 2 ^ (depth + 1) = 2 * 2 ^ depth := by
    rw [pow_succ]
    ring
  rw [hp] at hwidth
  unfold dyadicPacketMidpoint
  omega

/-- If every reciprocal prime-minus-Li fibre on an interval has norm at most
`delta`, the packet energy on recursive level `level` decays geometrically.
The rescaled quantity `4^level * levelEnergy` is bounded by the cube of the
ambient dyadic width. -/
theorem primeSieveDyadicPacketIntervalLevelEnergy_scaled_le_of_fibreBound
    (y x : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ (level j a b : ℕ),
      level ≤ j →
      1 ≤ a →
      b ≤ x / (y + 1) + 1 →
      b - a ≤ 2 ^ j →
      (∀ d ∈ Finset.Ico a b,
        ‖primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤ δ) →
      (((4 ^ level : ℕ) : ℝ)) *
          primeSieveDyadicPacketIntervalLevelEnergy y x level a b ≤
        4 * δ ^ 2 * (((2 ^ j : ℕ) : ℝ) ^ 3) := by
  intro level
  induction level with
  | zero =>
      intro j a b _hlevel ha hb hwidth hfib
      by_cases hsplit : a + 1 < b
      · let m := dyadicPacketMidpoint a b
        have hm := pntGoodMassAttack_midpoint_facts hsplit
        have hres :=
          primeSieveSignedSiblingPacketResidual_norm_le_of_fibreBound
            hδ ha hm.1.le hm.2.le hb hfib
        let W : ℝ := ((b - a : ℕ) : ℝ)
        let P : ℝ := ((2 ^ j : ℕ) : ℝ)
        have hW0 : 0 ≤ W := by dsimp [W]; positivity
        have hWP : W ≤ P := by
          dsimp [W, P]
          exact_mod_cast hwidth
        have hres' :
            ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ≤
              2 * W * δ := by
          simpa [m, W] using hres
        have hsq :
            ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ^ 2 ≤
              (2 * W * δ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hres' 2
        have hcube : W ^ 3 ≤ P ^ 3 :=
          pow_le_pow_left₀ hW0 hWP 3
        calc
          (((4 ^ 0 : ℕ) : ℝ)) *
              primeSieveDyadicPacketIntervalLevelEnergy y x 0 a b =
            W * ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ^ 2 := by
              simp [primeSieveDyadicPacketIntervalLevelEnergy, hsplit, m, W]
          _ ≤ W * (2 * W * δ) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hW0
          _ = (4 * δ ^ 2) * W ^ 3 := by ring
          _ ≤ (4 * δ ^ 2) * P ^ 3 :=
            mul_le_mul_of_nonneg_left hcube (by positivity)
          _ = 4 * δ ^ 2 * (((2 ^ j : ℕ) : ℝ) ^ 3) := by rfl
      · have hRhs :
            0 ≤ 4 * δ ^ 2 * (((2 ^ j : ℕ) : ℝ) ^ 3) := by positivity
        simpa [primeSieveDyadicPacketIntervalLevelEnergy, hsplit] using hRhs
  | succ level ih =>
      intro j a b hlevel ha hb hwidth hfib
      cases j with
      | zero => omega
      | succ j =>
          by_cases hsplit : a + 1 < b
          · let m := dyadicPacketMidpoint a b
            have hm := pntGoodMassAttack_midpoint_facts hsplit
            have hchildren :=
              pntGoodMassAttack_midpoint_child_widths hsplit hwidth
            have hmTop : m ≤ x / (y + 1) + 1 := hm.2.le.trans hb
            have hmOne : 1 ≤ m := ha.trans hm.1.le
            have hfibLeft : ∀ d ∈ Finset.Ico a m,
                ‖primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤ δ := by
              intro d hd
              apply hfib d
              rw [Finset.mem_Ico] at hd ⊢
              omega
            have hfibRight : ∀ d ∈ Finset.Ico m b,
                ‖primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤ δ := by
              intro d hd
              apply hfib d
              rw [Finset.mem_Ico] at hd ⊢
              omega
            have hleft :=
              ih j a m (by omega) ha hmTop hchildren.1 hfibLeft
            have hright :=
              ih j m b (by omega) hmOne hb hchildren.2 hfibRight
            let EL : ℝ :=
              primeSieveDyadicPacketIntervalLevelEnergy y x level a m
            let ER : ℝ :=
              primeSieveDyadicPacketIntervalLevelEnergy y x level m b
            let P : ℝ := ((2 ^ j : ℕ) : ℝ)
            let F : ℝ := ((4 ^ level : ℕ) : ℝ)
            have hleft' : F * EL ≤ 4 * δ ^ 2 * P ^ 3 := by
              simpa [F, EL, P] using hleft
            have hright' : F * ER ≤ 4 * δ ^ 2 * P ^ 3 := by
              simpa [F, ER, P] using hright
            have hsum :
                F * (EL + ER) ≤ 8 * δ ^ 2 * P ^ 3 := by
              calc
                F * (EL + ER) = F * EL + F * ER := by ring
                _ ≤ (4 * δ ^ 2 * P ^ 3) +
                    (4 * δ ^ 2 * P ^ 3) := add_le_add hleft' hright'
                _ = 8 * δ ^ 2 * P ^ 3 := by ring
            have hscaled :
                4 * (F * (EL + ER)) ≤ 4 * (8 * δ ^ 2 * P ^ 3) :=
              mul_le_mul_of_nonneg_left hsum (by norm_num)
            have hfour :
                (((4 ^ (level + 1) : ℕ) : ℝ)) = 4 * F := by
              dsimp [F]
              rw [pow_succ]
              push_cast
              ring
            have htwo :
                (((2 ^ (j + 1) : ℕ) : ℝ)) = 2 * P := by
              dsimp [P]
              rw [pow_succ]
              push_cast
              ring
            calc
              (((4 ^ (level + 1) : ℕ) : ℝ)) *
                  primeSieveDyadicPacketIntervalLevelEnergy
                    y x (level + 1) a b =
                4 * (F * (EL + ER)) := by
                  rw [hfour]
                  simp [primeSieveDyadicPacketIntervalLevelEnergy,
                    hsplit, m, EL, ER]
                  ring
              _ ≤ 4 * (8 * δ ^ 2 * P ^ 3) := hscaled
              _ = 4 * δ ^ 2 * (((2 ^ (j + 1) : ℕ) : ℝ) ^ 3) := by
                rw [htwo]
                ring
          · have hRhs :
                0 ≤ 4 * δ ^ 2 * (((2 ^ (j + 1) : ℕ) : ℝ) ^ 3) := by
              positivity
            simpa [primeSieveDyadicPacketIntervalLevelEnergy, hsplit] using hRhs

-- ATTACK_PATCH: dyadic-level-specialization

private theorem pntGoodMassAttack_dyadicBlock_width_le_two_pow
    (y x j : ℕ) :
    primeSieveDyadicBlockRight y x j + 1 -
        primeSieveDyadicBlockLeft j ≤ 2 ^ j := by
  unfold primeSieveDyadicBlockRight primeSieveDyadicBlockLeft
  have hright :
      min (x / (y + 1)) (2 ^ (j + 1) - 1) + 1 ≤ 2 ^ (j + 1) := by
    have hp : 0 < 2 ^ (j + 1) := by positivity
    omega
  rw [pow_succ] at hright ⊢
  omega

/-- On one reciprocal dyadic block, the fibre estimate and midpoint geometry
combine to an exact scale-invariant level-energy bound. -/
theorem primeSieveDyadicPacketIntervalLevelEnergy_dyadic_scaled
    {k x j level : ℕ}
    (hk : 2 ≤ k)
    (hup : x ≤ primorialBlockUpper k)
    (hlevel : level ≤ j) :
    (((2 ^ j : ℕ) : ℝ)) * (((4 ^ level : ℕ) : ℝ)) *
        primeSieveDyadicPacketIntervalLevelEnergy
          (primorialPNTPrimeSieveCutoff k) x level
          (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight
            (primorialPNTPrimeSieveCutoff k) x j + 1) ≤
      16 * (1 + 1 / Real.log 2) ^ 2 * (x : ℝ) ^ 2 := by
  let y := primorialPNTPrimeSieveCutoff k
  let P : ℝ := ((2 ^ j : ℕ) : ℝ)
  let c : ℝ := 1 + 1 / Real.log 2
  let δ : ℝ := 2 * c * ((x : ℝ) / P ^ 2)
  let F : ℝ := ((4 ^ level : ℕ) : ℝ)
  let E : ℝ := primeSieveDyadicPacketIntervalLevelEnergy y x level
    (primeSieveDyadicBlockLeft j)
    (primeSieveDyadicBlockRight y x j + 1)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hleft1 : 1 ≤ primeSieveDyadicBlockLeft j := by
    simpa [primeSieveDyadicBlockLeft] using (Nat.one_le_pow' j 1)
  have hrightTop :
      primeSieveDyadicBlockRight y x j + 1 ≤ x / (y + 1) + 1 := by
    unfold primeSieveDyadicBlockRight
    omega
  have hwidth := pntGoodMassAttack_dyadicBlock_width_le_two_pow y x j
  have hset :
      Finset.Ico (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j + 1) =
        primeSieveDyadicBlock y x j := by
    rw [primeSieveDyadicBlock_eq_explicitIcc]
    ext d
    simp
    omega
  have hfib : ∀ d ∈ Finset.Ico (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1),
      ‖primeSieveReciprocalPrimeDiscrepancy y x d‖ ≤ δ := by
    intro d hd
    have hdB : d ∈ primeSieveDyadicBlock y x j := by
      rw [← hset]
      exact hd
    have h := primeSieveReciprocalPrimeDiscrepancy_norm_le_dyadicScale
      hk hup (by simpa [y] using hdB)
    simpa [y, δ, c, P] using h
  have hgeneric :=
    primeSieveDyadicPacketIntervalLevelEnergy_scaled_le_of_fibreBound
      y x δ hδ0 level j
      (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1)
      hlevel hleft1 hrightTop hwidth hfib
  have hgeneric' : F * E ≤ 4 * δ ^ 2 * P ^ 3 := by
    simpa [F, E, P] using hgeneric
  have hscaled := mul_le_mul_of_nonneg_left hgeneric' hPpos.le
  change P * F * E ≤ 16 * c ^ 2 * (x : ℝ) ^ 2
  calc
    P * F * E = P * (F * E) := by ring
    _ ≤ P * (4 * δ ^ 2 * P ^ 3) := hscaled
    _ = 16 * c ^ 2 * (x : ℝ) ^ 2 := by
      dsimp [δ]
      field_simp [ne_of_gt hPpos]; ring

/-- Finite telescoping of exact packet levels reconstructs every interval-tree
energy difference. -/
theorem primeSieveDyadicPacketIntervalTreeEnergy_sub_eq_sum_levelEnergy
    (y x a b r s : ℕ) (hrs : r ≤ s) :
    primeSieveDyadicPacketIntervalTreeEnergy y x s a b -
        primeSieveDyadicPacketIntervalTreeEnergy y x r a b =
      ∑ level ∈ Finset.Ico r s,
        primeSieveDyadicPacketIntervalLevelEnergy y x level a b := by
  induction s, hrs using Nat.le_induction with
  | base => simp
  | succ s hrs ih =>
      rw [Finset.sum_Ico_succ_top hrs, ← ih]
      have hstep :=
        primeSieveDyadicPacketIntervalTreeEnergy_succ_sub_eq_levelEnergy
          y x s a b
      linarith

/-- A block deep tail is exactly the sum of its unresolved packet levels. -/
theorem primeSieveDyadicPacketBlockDeepEnergy_eq_sum_levelEnergy
    {y x j J : ℕ} (hJ : J ≤ j) :
    primeSieveDyadicPacketBlockDeepEnergy y x j J =
      ∑ level ∈ Finset.Ico J j,
        primeSieveDyadicPacketIntervalLevelEnergy y x level
          (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j + 1) := by
  unfold primeSieveDyadicPacketBlockDeepEnergy
    primeSieveDyadicPacketTreeBlockEnergy
  rw [min_eq_left hJ]
  exact primeSieveDyadicPacketIntervalTreeEnergy_sub_eq_sum_levelEnergy
    y x (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1) J j hJ

end RHLean.Analysis
