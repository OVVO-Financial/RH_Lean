import Mathlib
import RHLean.Analysis.DyadicTransportCanonicalForm
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Proof.PrimeCombVisualizationFrames

/-!
# Large-prime terminal flip layers

After the square-root phase, a surviving squarefree tail seat has the form
`c*q` with `q` the unique unprocessed large prime.  The lower cofactor `c` has
already acquired its final Möbius sign, and adjoining `q` flips that sign once.
This module isolates that terminal flip in reciprocal quotient layers.

For the canonical endpoint `X_R = R^2 - 1`, primes `q > R` are grouped by
`k = floor(X_R / q)`.  In one fixed layer, every prime has exactly the same
available cofactor set `2,...,k`.  The signed terminal-flip imbalance per prime
is therefore

`sum_{2 <= c <= k} -mu(c) = 1 - M(k)`.

Thus the high-prime coordinate contributes only the positive layer population;
all parity data is already lower-scale.  The first downward terminal flip
requires the positive Möbius cofactor `6`, so layers `k <= 5` are exactly
up-only.  Equivalently, `q > X/6` forces the reciprocal index below `6`.

Finally, summing the middle layers and swapping the order of summation gives the
exact dual weighted form

`- sum_{2 <= c < R} mu(c) * (pi(floor(X_R/c)) - pi(R))`.

The last section puts the untouched prime seat `c = 1` back into the same signed
object.  The complete post-root prime fibre is then `-M(k)`, not `1-M(k)`, and
the upper `k=1` block must remain paired with the first middle layers.  We define
its truncated packet and give the exact finite Abel form before any completion
of the reciprocal coordinate.

No estimate, asymptotic, PNT input, RH hypothesis, or norm bound is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- **Terminal sign law.**  If `q` lies above the square root of `X` and the
positive cofactor `c` still satisfies `c*q <= X`, then `c < q`, so adjoining the
fresh prime `q` negates the Möbius sign of the already-completed cofactor. -/
theorem moebius_mul_largePrime_eq_neg_cofactor
    {X c q : ℕ} (hq : q.Prime) (hqRoot : Nat.sqrt X < q)
    (hcpos : 0 < c) (hcqX : c * q ≤ X) :
    μ (c * q) = -μ c := by
  have hcRoot : c ≤ Nat.sqrt X :=
    cofactor_le_sqrt_of_largePrime_mul_le hqRoot hcqX
  have hcq : c < q := hcRoot.trans_lt hqRoot
  have hcop : Nat.Coprime c q :=
    (Nat.coprime_of_lt_prime (Nat.ne_of_gt hcpos) hcq hq).symm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hq]
  ring

/-- Complex-weight form of the same terminal sign law. -/
theorem canonicalMoebiusWeight_mul_largePrime_eq_neg_cofactor
    {X c q : ℕ} (hq : q.Prime) (hqRoot : Nat.sqrt X < q)
    (hcpos : 0 < c) (hcqX : c * q ≤ X) :
    canonicalMoebiusWeight (c * q) = -canonicalMoebiusWeight c := by
  have hcRoot : c ≤ Nat.sqrt X :=
    cofactor_le_sqrt_of_largePrime_mul_le hqRoot hcqX
  exact canonicalMoebiusWeight_mul_prime_eq_neg
    hcpos (hcRoot.trans_lt hqRoot) hq

/-- The squarefree-zero convention is preserved by the terminal sign law: if
the lower cofactor has already been killed, adjoining the large prime leaves
zero. -/
theorem moebius_mul_largePrime_eq_zero_of_cofactor_not_squarefree
    {X c q : ℕ} (hq : q.Prime) (hqRoot : Nat.sqrt X < q)
    (hcpos : 0 < c) (hcqX : c * q ≤ X)
    (hnsq : ¬ Squarefree c) :
    μ (c * q) = 0 := by
  rw [moebius_mul_largePrime_eq_neg_cofactor hq hqRoot hcpos hcqX,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
  simp

/-- Signed cofactor contribution of one terminal reciprocal layer.  The unit
cofactor `c=1` is excluded because it is an untouched prime seat rather than a
flip. -/
def largePrimeTerminalCofactorImbalance (k : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 2 k, -canonicalMoebiusWeight c

/-- **All parity in one layer is lower-scale.**  For every nonempty positive
prefix, the signed terminal-flip imbalance per large prime is exactly
`1 - M(k)`. -/
theorem largePrimeTerminalCofactorImbalance_eq_one_sub_mertens
    (k : ℕ) (hk : 1 ≤ k) :
    largePrimeTerminalCofactorImbalance k = 1 - mertensSummatory k := by
  have hset :
      Finset.Icc 1 k = ({1} : Finset ℕ) ∪ Finset.Icc 2 k := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 k) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    rw [Finset.mem_singleton] at hc1
    subst c
    simp at hc2
  have hprefix :
      cofactorMobiusPrefixMass k =
        canonicalMoebiusWeight 1 +
          ∑ c ∈ Finset.Icc 2 k, canonicalMoebiusWeight c := by
    unfold cofactorMobiusPrefixMass
    rw [hset, Finset.sum_union hdisj]
    simp
  rw [cofactorMobiusPrefixMass_eq_mertensSummatory k] at hprefix
  have hmu1 : canonicalMoebiusWeight 1 = 1 := by
    simp [canonicalMoebiusWeight]
  rw [hmu1] at hprefix
  have hsum :
      (∑ c ∈ Finset.Icc 2 k, canonicalMoebiusWeight c) =
        mertensSummatory k - 1 := by
    calc
      (∑ c ∈ Finset.Icc 2 k, canonicalMoebiusWeight c) =
          (1 + ∑ c ∈ Finset.Icc 2 k, canonicalMoebiusWeight c) - 1 := by ring
      _ = mertensSummatory k - 1 := by rw [← hprefix]
  unfold largePrimeTerminalCofactorImbalance
  calc
    (∑ c ∈ Finset.Icc 2 k, -canonicalMoebiusWeight c) =
        -(∑ c ∈ Finset.Icc 2 k, canonicalMoebiusWeight c) := by simp
    _ = 1 - mertensSummatory k := by rw [hsum]; ring

/-- Prime population of the canonical reciprocal layer `k`. -/
def squareRootTerminalFlipLayerPrimeCount (R k : ℕ) : ℂ :=
  ((squareRootMiddleHarmonicLayerPrimes R k).card : ℂ)

/-- Signed terminal-flip imbalance of one reciprocal layer. -/
def squareRootTerminalFlipLayerImbalance (R k : ℕ) : ℂ :=
  squareRootTerminalFlipLayerPrimeCount R k *
    largePrimeTerminalCofactorImbalance k

/-- **Fixed-segment imbalance.**  The large-prime coordinate is only a positive
multiplicity profile: one reciprocal layer is exactly
`N_R(k) * (1 - M(k))`. -/
theorem squareRootTerminalFlipLayerImbalance_eq_count_mul_one_sub_mertens
    (R k : ℕ) (hk : 1 ≤ k) :
    squareRootTerminalFlipLayerImbalance R k =
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) k *
        (1 - mertensSummatory k) := by
  unfold squareRootTerminalFlipLayerImbalance
    squareRootTerminalFlipLayerPrimeCount
  rw [largePrimeTerminalCofactorImbalance_eq_one_sub_mertens k hk,
    squareRootMiddleHarmonicLayer_card_eq_reciprocalPrimeCount]

/-- Cofactors whose completed lower-scale sign is positive, hence whose fresh
large-prime terminal flip points downward. -/
def largePrimeTerminalDownCofactors (k : ℕ) : Finset ℕ :=
  (Finset.Icc 2 k).filter fun c => μ c = 1

/-- Cofactors whose completed lower-scale sign is negative, hence whose fresh
large-prime terminal flip points upward. -/
def largePrimeTerminalUpCofactors (k : ℕ) : Finset ℕ :=
  (Finset.Icc 2 k).filter fun c => μ c = -1

private theorem moebius_ne_one_of_two_le_of_le_five
    {c : ℕ} (hc2 : 2 ≤ c) (hc5 : c ≤ 5) :
    μ c ≠ 1 := by
  have hcases : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  · rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)]
    norm_num
  · have hnsq : ¬ Squarefree 4 := by
      rw [Nat.squarefree_iff_prime_squarefree]
      push_neg
      exact ⟨2, Nat.prime_two, by norm_num⟩
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
    norm_num
  · rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)]
    norm_num

/-- **Sharp one-way threshold in reciprocal coordinates.**  Before cofactor `6`
can enter, no positive Möbius cofactor exists, so every nonzero terminal flip
points upward. -/
theorem largePrimeTerminalDownCofactors_eq_empty_of_le_five
    {k : ℕ} (hk : k ≤ 5) :
    largePrimeTerminalDownCofactors k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  rcases Finset.mem_filter.mp hc with ⟨hcRange, hmu⟩
  rcases Finset.mem_Icc.mp hcRange with ⟨hc2, hck⟩
  exact (moebius_ne_one_of_two_le_of_le_five hc2 (hck.trans hk)) hmu

/-- The down-flip count therefore vanishes exactly throughout `k <= 5`. -/
theorem largePrimeTerminalDownCount_eq_zero_of_le_five
    {k : ℕ} (hk : k ≤ 5) :
    (largePrimeTerminalDownCofactors k).card = 0 := by
  rw [largePrimeTerminalDownCofactors_eq_empty_of_le_five hk]
  simp

/-- `q > X/6` is exactly strong enough to force the reciprocal quotient below
`6`; this is the geometric form of the `k <= 5` one-way threshold. -/
theorem reciprocalIndex_le_five_of_sixth_lt
    {X q : ℕ} (hqpos : 0 < q) (hqSixth : X / 6 < q) :
    X / q ≤ 5 := by
  have hXlt : X < q * 6 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 6)).1 hqSixth
  have hXlt' : X < 6 * q := by
    simpa [Nat.mul_comm] using hXlt
  have hdivlt : X / q < 6 :=
    (Nat.div_lt_iff_lt_mul hqpos).2 hXlt'
  omega

private theorem moebius_eq_neg_one_of_two_le_of_le_five_of_ne_zero
    {c : ℕ} (hc2 : 2 ≤ c) (hc5 : c ≤ 5) (hmu0 : μ c ≠ 0) :
    μ c = -1 := by
  have hcases : c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  · rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)]
  · have hnsq : ¬ Squarefree 4 := by
      rw [Nat.squarefree_iff_prime_squarefree]
      push_neg
      exact ⟨2, Nat.prime_two, by norm_num⟩
    have hzero : μ 4 = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
    exact (hmu0 hzero).elim
  · rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)]

/-- **Pointwise up-only form.**  In the genuine terminal sector, if
`q > X/6`, every surviving nonzero cofactor seat flips from `-1` to `+1`. -/
theorem largePrimeTerminalFlip_up_only_of_sixth_lt
    {X c q : ℕ} (hq : q.Prime) (hqRoot : Nat.sqrt X < q)
    (hqSixth : X / 6 < q) (hc2 : 2 ≤ c)
    (hcqX : c * q ≤ X) (hmu0 : μ c ≠ 0) :
    μ (c * q) = 1 := by
  have hcQuot : c ≤ X / q :=
    (Nat.le_div_iff_mul_le hq.pos).2 hcqX
  have hk5 : X / q ≤ 5 :=
    reciprocalIndex_le_five_of_sixth_lt hq.pos hqSixth
  have hc5 : c ≤ 5 := hcQuot.trans hk5
  have hmu : μ c = -1 :=
    moebius_eq_neg_one_of_two_le_of_le_five_of_ne_zero hc2 hc5 hmu0
  rw [moebius_mul_largePrime_eq_neg_cofactor hq hqRoot (by omega) hcqX, hmu]
  norm_num

/-- Total signed terminal-flip contribution of the canonical middle prime
corridor.  It is the middle prime population minus the ordinary middle Mertens
tail, because every large prime contributes `1 - M(floor(X_R/q))`. -/
def squareRootMiddleTerminalFlipMass (R : ℕ) : ℂ :=
  ((squareRootMiddleFibrePrimes R).card : ℂ) -
    squareRootMiddleMertensTail R

/-- Cofactor-first form of the same terminal-flip contribution. -/
def squareRootMiddleTerminalFlipDual (R : ℕ) : ℂ :=
  -∑ c ∈ Finset.Icc 2 (R - 1),
    canonicalMoebiusWeight c *
      ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
        (Nat.primeCounting R : ℂ))

/-- **Exact dual reindexing.**  The entire middle terminal-flip mass is the
weighted lower-scale Möbius sum

`- sum_{2 <= c < R} mu(c) * (pi(floor(X_R/c)) - pi(R))`.

The `c=2` term supplies exactly the raw middle-prime population, while the
`c>=3` terms are the already-formalized swapped middle Mertens tail. -/
theorem squareRootMiddleTerminalFlipMass_eq_dual
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleTerminalFlipMass R =
      squareRootMiddleTerminalFlipDual R := by
  have hset :
      Finset.Icc 2 (R - 1) =
        ({2} : Finset ℕ) ∪ Finset.Icc 3 (R - 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({2} : Finset ℕ) (Finset.Icc 3 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro c hc2 hc3
    rw [Finset.mem_singleton] at hc2
    subst c
    simp at hc3
  have hmu2 : canonicalMoebiusWeight 2 = -1 := by
    unfold canonicalMoebiusWeight
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  have hmidCount :=
    squareRootMiddleFibrePrimes_card_add_primeCounting_root R hR
  have hmidCountC :
      ((squareRootMiddleFibrePrimes R).card : ℂ) =
        (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) -
          (Nat.primeCounting R : ℂ) := by
    have hcast :
        ((squareRootMiddleFibrePrimes R).card : ℂ) +
            (Nat.primeCounting R : ℂ) =
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) := by
      exact_mod_cast hmidCount
    linear_combination hcast
  unfold squareRootMiddleTerminalFlipMass squareRootMiddleTerminalFlipDual
  rw [squareRootMiddleMertensTail_eq_swappedPrimeCounting R hR,
    hset, Finset.sum_union hdisj]
  simp only [Finset.sum_singleton]
  rw [hmu2, hmidCountC]
  ring

/-! ## Put the untouched prime seat back: truncated upper-middle packets -/

/-- Clipped post-root prime prefix at reciprocal depth `d`.

`P_R(d)` counts primes in `(R, max R floor(X_R/d)]`.  The clipping makes the
forward-difference identity valid even at the terminal quotient boundary. -/
def squareRootPostRootPrimePrefix (R d : ℕ) : ℂ :=
  primeSievePrefixPrimeCount (max R (squareRootEndpoint R / d)) -
    primeSievePrefixPrimeCount R

/-- The complete signed post-root packet through reciprocal layer `K`.

The prime seat `c=1` is included.  Hence one complete `d`-fibre contributes
`-M(d)`, and `d=1` is the same-sign upper block rather than a discarded edge. -/
def squareRootTruncatedUpperMiddlePacket (R K : ℕ) : ℂ :=
  -∑ d ∈ Finset.Icc 1 K,
    primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
      mertensSummatory d

/-- On every physical quotient-support layer, the reciprocal prime population
is the forward difference of the clipped post-root prefix. -/
theorem squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff
    {R d : ℕ} (hR : 1 ≤ R) (hd1 : 1 ≤ d) (hdR : d < R) :
    primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d =
      squareRootPostRootPrimePrefix R d -
        squareRootPostRootPrimePrefix R (d + 1) := by
  have htop : squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R hR
  have hdSupport :
      d ∈ primeSieveQuotientSupport R (squareRootEndpoint R) := by
    unfold primeSieveQuotientSupport
    rw [htop]
    exact Finset.mem_Icc.mpr ⟨hd1, by omega⟩
  have hRlt : R < squareRootEndpoint R / d :=
    lt_div_of_mem_primeSieveQuotientSupport hdSupport
  have hmono :
      squareRootEndpoint R / (d + 1) ≤ squareRootEndpoint R / d :=
    Nat.div_le_div_left (by omega) (by omega)
  have hle :
      primeSieveReciprocalLower R (squareRootEndpoint R) d ≤
        primeSieveReciprocalUpper (squareRootEndpoint R) d := by
    unfold primeSieveReciprocalLower primeSieveReciprocalUpper
    exact max_le hRlt.le hmono
  rw [primeSieveReciprocalPrimeCount_eq_sub R (squareRootEndpoint R) d hle]
  unfold squareRootPostRootPrimePrefix
    primeSieveReciprocalLower primeSieveReciprocalUpper
  rw [max_eq_right hRlt.le]
  ring

/-- **Exact finite Abel packet.**  The truncated upper/middle object is a
Möbius-weighted post-root prime prefix plus one terminal `K` boundary.  This is
only a coordinate change; it asserts no estimate. -/
theorem squareRootTruncatedUpperMiddlePacket_eq_abel
    (R K : ℕ) (hR : 1 ≤ R) (hK : K < R) :
    squareRootTruncatedUpperMiddlePacket R K =
      -(∑ d ∈ Finset.Icc 1 K,
          (((μ d : ℤ) : ℂ)) * squareRootPostRootPrimePrefix R d) +
        mertensSummatory K * squareRootPostRootPrimePrefix R (K + 1) := by
  have hrewrite :
      (∑ d ∈ Finset.Icc 1 K,
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d) =
        ∑ d ∈ Finset.Icc 1 K,
          mertensSummatory d *
            (squareRootPostRootPrimePrefix R d -
              squareRootPostRootPrimePrefix R (d + 1)) := by
    apply Finset.sum_congr rfl
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hdK⟩
    rw [squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff
      hR hd1 (hdK.trans_lt hK)]
    ring
  unfold squareRootTruncatedUpperMiddlePacket
  rw [hrewrite, sum_mertensSummatory_mul_forwardDifference]
  ring

/-- Unit-separated Abel form.  The upper boundary and the shallow middle
corrections remain inside one exact packet. -/
theorem squareRootTruncatedUpperMiddlePacket_eq_upper_add_abelMiddle
    (R K : ℕ) (hR : 1 ≤ R) (hK1 : 1 ≤ K) (hKR : K < R) :
    squareRootTruncatedUpperMiddlePacket R K =
      -squareRootPostRootPrimePrefix R 1 -
        (∑ d ∈ Finset.Icc 2 K,
          (((μ d : ℤ) : ℂ)) * squareRootPostRootPrimePrefix R d) +
        mertensSummatory K * squareRootPostRootPrimePrefix R (K + 1) := by
  rw [squareRootTruncatedUpperMiddlePacket_eq_abel R K hR hKR]
  have hset :
      Finset.Icc 1 K = ({1} : Finset ℕ) ∪ Finset.Icc 2 K := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 K) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [Finset.mem_singleton] at hd1
    subst d
    simp at hd2
  rw [hset, Finset.sum_union hdisj]
  simp [ArithmeticFunction.moebius_apply_one]
  ring

/-- The first reciprocal layer is exactly the same-sign top-prime block, with
its actual source sign.  This is the formal guardrail against asking the middle
to self-cancel. -/
theorem squareRootTruncatedUpperMiddlePacket_one_eq_neg_topCard
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTruncatedUpperMiddlePacket R 1 =
      -((squareRootTopFibrePrimes R).card : ℂ) := by
  unfold squareRootTruncatedUpperMiddlePacket
  rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide]
  simp only [Finset.sum_singleton]
  rw [squareRootReciprocalPrimeCount_one_eq_topCard R hR]
  have hM1 : mertensSummatory 1 = 1 := by
    rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
    simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]
  rw [hM1]
  ring

end RHLean.Proof
