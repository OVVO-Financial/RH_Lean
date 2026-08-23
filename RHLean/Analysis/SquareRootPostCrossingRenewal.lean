import Mathlib
import RHLean.Analysis.SquareRootPostCrossingTail
import RHLean.Analysis.SquareRootBornSmoothReciprocalForm
import RHLean.Proof.ReplacementFibreCofactorWindows

/-!
# Renewal normal forms for the post-crossing tail

The crossing residual is not merely a bounded scalar.  Before any norm is
taken it is a shallow linear combination of the same lower-scale Mertens
states that occur in the exact recursive replacement row.  This file keeps
that signed structure intact.

For `1 ≤ K < R` it proves three exact descriptions of the coupled tail:

* a direct remaining-layer cap, with the unfilled part of layer `K` and every
  deeper reciprocal layer kept together with the smooth population;
* an Abel form, where the remaining transport is one signed Möbius/prime-prefix
  tail; and
* a lower-triangular renewal row obtained by subtracting the shallow crossing
  coefficients from the complete recursive replacement row before any norm.

The replacement-fibre dictionary then identifies the packet layer with the
negative cofactor-one prime face.  Consequently every fully admitted shallow
layer cancels its prime diagonal exactly, while the crossing layer retains
precisely `j - N_R(K)`, the negative number of unfilled seats.  The remaining
composite-root and smooth orientations recombine as one signed Type-II
cofactor-prime window mass (with the root cofactor range starting at two), and
that mass stays coupled to the strict descendants in one signed double Gram.

The last form is the genuinely nonlocal bilinear proof object for a subsequent
energy argument.  No diagonal estimate, triangle inequality, RH hypothesis,
or critical tail bound is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators ComplexConjugate

namespace RHLean.Proof

open RHLean.Analysis

/-- Cast form of the partially filled crossing layer. -/
theorem squareRootCrossingLayerPartialPacketInt_cast_complex
    (R K j : ℕ) :
    ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      squareRootTruncatedUpperMiddlePacket R (K - 1) -
        (j : ℂ) * mertensSummatory K := by
  unfold squareRootCrossingLayerPartialPacketInt
  push_cast
  rw [squareRootTruncatedUpperMiddlePacketInt_cast_complex,
    squareRootMertensInt_cast_complex]

private theorem sum_Icc_one_pred_split_at
    (f : ℕ → ℂ) {R K : ℕ} (hK : 1 ≤ K) (hKR : K < R) :
    (∑ d ∈ Finset.Icc 1 (R - 1), f d) =
      (∑ d ∈ Finset.Icc 1 (K - 1), f d) + f K +
        ∑ d ∈ Finset.Icc (K + 1) (R - 1), f d := by
  have hset₁ :
      Finset.Icc 1 (R - 1) =
        Finset.Icc 1 (K - 1) ∪ Finset.Icc K (R - 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj₁ :
      Disjoint (Finset.Icc 1 (K - 1)) (Finset.Icc K (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd₁ hd₂
    simp only [Finset.mem_Icc] at hd₁ hd₂
    omega
  have hset₂ :
      Finset.Icc K (R - 1) =
        ({K} : Finset ℕ) ∪ Finset.Icc (K + 1) (R - 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj₂ :
      Disjoint ({K} : Finset ℕ) (Finset.Icc (K + 1) (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd₁ hd₂
    rw [Finset.mem_singleton] at hd₁
    subst d
    simp at hd₂
  rw [hset₁, Finset.sum_union hdisj₁, hset₂,
    Finset.sum_union hdisj₂]
  simp
  ring

/-- The still-unfilled transport layers after `j` seats have been admitted in
layer `K`.  This is a signed cap, not a sum of separately normed pieces. -/
def squareRootPostCrossingRemainingLayerCap (R K j : ℕ) : ℂ :=
  -(primeSieveReciprocalPrimeCount R (squareRootEndpoint R) K - (j : ℂ)) *
      mertensSummatory K -
    ∑ d ∈ Finset.Icc (K + 1) (R - 1),
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
        mertensSummatory d

/-- Exact remaining-layer form of the raw transport tail. -/
theorem squareRootPostCrossingRawTransportTail_eq_remainingLayerCap
    (R K j : ℕ) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingRawTransportTail R K j =
      squareRootPostCrossingRemainingLayerCap R K j := by
  unfold squareRootPostCrossingRawTransportTail
    squareRootPostCrossingRemainingLayerCap
  rw [show ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      squareRootTruncatedUpperMiddlePacket R (K - 1) -
        (j : ℂ) * mertensSummatory K by
      exact squareRootCrossingLayerPartialPacketInt_cast_complex R K j]
  unfold squareRootTruncatedUpperMiddlePacket
  rw [sum_Icc_one_pred_split_at
    (fun d =>
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
        mertensSummatory d) hK hKR]
  ring

/-- Direct coupled cap: the smooth population remains signed with every
unfilled reciprocal layer before any norm is taken. -/
def squareRootPostCrossingCoupledLayerCap (R K j : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) +
    squareRootPostCrossingRemainingLayerCap R K j

/-- The terminal coupled tail is exactly the direct remaining-layer cap. -/
theorem squareRootPostCrossingCoupledTail_eq_layerCap
    (R K j : ℕ) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      squareRootPostCrossingCoupledLayerCap R K j := by
  unfold squareRootPostCrossingCoupledTail
    squareRootPostCrossingCoupledLayerCap
  rw [squareRootPostCrossingRawTransportTail_eq_remainingLayerCap
    R K j hK hKR]

/-- The clipped post-root prime prefix vanishes at reciprocal depth `R`. -/
theorem squareRootPostRootPrimePrefix_self
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootPostRootPrimePrefix R R = 0 := by
  have hdiv : squareRootEndpoint R / R = R - 1 := by
    have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
    have hsq : R * R = (R - 1) * R + R := by
      calc
        R * R = (R - 1 + 1) * R := by rw [hpred]
        _ = (R - 1) * R + R := by ring
    apply Nat.div_eq_of_lt_le
    · unfold squareRootEndpoint
      rw [pow_two]
      rw [hsq]
      omega
    · unfold squareRootEndpoint
      rw [hpred, pow_two, hsq]
      omega
  unfold squareRootPostRootPrimePrefix
  rw [hdiv, max_eq_left (by omega : R - 1 ≤ R)]
  ring

/-- Abel-coordinate version of the remaining transport.  The boundary term
`(j-P_R(K))M(K)` and the deeper Möbius/prime-prefix tail remain one signed
object. -/
def squareRootPostCrossingRemainingAbelCap (R K j : ℕ) : ℂ :=
  ((j : ℂ) - squareRootPostRootPrimePrefix R K) * mertensSummatory K -
    ∑ d ∈ Finset.Icc (K + 1) (R - 1),
      (((μ d : ℤ) : ℂ)) * squareRootPostRootPrimePrefix R d

/-- Exact Abel form of the raw post-crossing tail. -/
theorem squareRootPostCrossingRawTransportTail_eq_remainingAbelCap
    (R K j : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingRawTransportTail R K j =
      squareRootPostCrossingRemainingAbelCap R K j := by
  unfold squareRootPostCrossingRawTransportTail
    squareRootPostCrossingRemainingAbelCap
  rw [show ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      squareRootTruncatedUpperMiddlePacket R (K - 1) -
        (j : ℂ) * mertensSummatory K by
      exact squareRootCrossingLayerPartialPacketInt_cast_complex R K j]
  rw [squareRootTruncatedUpperMiddlePacket_eq_abel R (R - 1) hR (by omega),
    squareRootTruncatedUpperMiddlePacket_eq_abel R (K - 1) hR (by omega)]
  rw [Nat.sub_add_cancel hR, Nat.sub_add_cancel hK,
    squareRootPostRootPrimePrefix_self R hR]
  simp only [mul_zero, add_zero]
  rw [sum_Icc_one_pred_split_at
    (fun d => (((μ d : ℤ) : ℂ)) * squareRootPostRootPrimePrefix R d)
    hK hKR]
  have hsucc := mertensSummatory_succ (K - 1)
  rw [Nat.sub_add_cancel hK] at hsucc
  rw [hsucc]
  ring

/-- Coupled Abel cap, retaining the smooth term and the remaining signed Abel
tail as one object. -/
def squareRootPostCrossingCoupledAbelCap (R K j : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) +
    squareRootPostCrossingRemainingAbelCap R K j

/-- The coupled tail is exactly the smooth-coupled Abel cap. -/
theorem squareRootPostCrossingCoupledTail_eq_abelCap
    (R K j : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      squareRootPostCrossingCoupledAbelCap R K j := by
  unfold squareRootPostCrossingCoupledTail
    squareRootPostCrossingCoupledAbelCap
  rw [squareRootPostCrossingRawTransportTail_eq_remainingAbelCap
    R K j hR hK hKR]

/-- At a square endpoint the complete Mertens value is `1` minus the unified
prime-indexed rough reciprocal transform. -/
theorem mertensSquareRootEndpoint_eq_one_sub_unifiedReciprocalTransform
    (R : ℕ) (hR : 2 ≤ R) :
    mertensSummatory (squareRootEndpoint R) =
      1 - squareRootUnifiedReciprocalTransform R := by
  have hsquare := squarePrefixMertens_eq_neg_positivePrimeTransform_add_matched
    R (by omega : 1 ≤ R)
  rw [squareRootMatchedBornSmoothTransport_eq_unifiedReciprocalForm R hR]
    at hsquare
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel (by omega : 1 ≤ R)
  simpa [squarePrefixMertens, squarePrefixEndpoint, hpred] using hsquare

/-- Unified reciprocal form of the post-crossing tail.  The shallow residual
is subtracted only after the complete prime-indexed reciprocal transform has
been assembled. -/
theorem squareRootPostCrossingCoupledTail_eq_unifiedReciprocal_sub_partial
    (R K j : ℕ) (hR : 3 ≤ R) :
    squareRootPostCrossingCoupledTail R K j =
      1 - squareRootUnifiedReciprocalTransform R -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) := by
  rw [postCrossingCoupledTail_eq_mertens_sub_partial R K j hR,
    mertensSquareRootEndpoint_eq_one_sub_unifiedReciprocalTransform R
      (by omega)]

/-- Positive coefficient row removed from the complete replacement recurrence
by a partial shallow packet. -/
def squareRootCrossingRemovalCoefficient
    (R K j y : ℕ) : ℂ :=
  (if y ∈ Finset.Icc 1 (K - 1) then
      primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y
    else 0) +
  if y = K then (j : ℂ) else 0

/-- The recursive replacement coefficient after subtracting the partial
crossing packet coefficientwise, before any norm or diagonalization. -/
def squareRootPostCrossingReplacementCoefficient
    (R K j y : ℕ) : ℂ :=
  squareRootReplacementCoefficient R y +
    squareRootCrossingRemovalCoefficient R K j y

/-! ## Prime-face cancellation inside the renewal row -/

/-- Away from the clipped terminal layer, the literal prime count on a
replacement fibre is the packet's reciprocal-layer cardinality. -/
theorem replacementFibrePrimeCount_eq_reciprocalPrimeLayerCard
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z + 1 < R) :
    replacementFibrePrimeCount R z =
      (squareRootReciprocalPrimeLayerCard R z : ℂ) := by
  have hroot : R ≤ squareRootEndpoint R / (z + 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < z + 1)).2
    have hzle : z + 1 ≤ R - 1 := by omega
    have hmul : R * (z + 1) ≤ R * (R - 1) :=
      Nat.mul_le_mul_left R hzle
    have htail : R * (R - 1) ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      rw [pow_two, Nat.mul_sub_left_distrib]
      omega
    exact hmul.trans htail
  have hset :
      Finset.Icc
          (squareRootEndpoint R / (z + 1) + 1)
          (squareRootEndpoint R / z) =
        Finset.Ioc
          (squareRootEndpoint R / (z + 1))
          (squareRootEndpoint R / z) := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  unfold replacementFibrePrimeCount squareRootReciprocalPrimeLayerCard
    squareRootReplacementFibreLower squareRootReplacementFibreUpper
    primeSieveReciprocalInterval primeSieveReciprocalLower
    primeSieveReciprocalUpper
  rw [max_eq_right hroot, hset, ← Finset.sum_filter]
  simp

/-- The cofactor-one prime face of an unclipped reciprocal fibre is the
negative packet layer count. -/
theorem replacementFibrePrimeFaceMass_eq_neg_reciprocalPrimeLayerCard
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z + 1 < R) :
    replacementFibrePrimeFaceMass R z =
      -(squareRootReciprocalPrimeLayerCard R z : ℂ) := by
  rw [replacementFibrePrimeFaceMass_eq_neg_primeCount R z hR hz (by omega),
    replacementFibrePrimeCount_eq_reciprocalPrimeLayerCard R z hR hz hzR]

/-- The cofactor-one dilated prime window is the literal reciprocal-fibre
prime count. -/
theorem replacementFibreRootPrimeWindowCount_one_eq_primeCount
    (R z : ℕ) :
    replacementFibreRootPrimeWindowCount R z 1 =
      replacementFibrePrimeCount R z := by
  classical
  unfold replacementFibreRootPrimeWindowCount replacementFibrePrimeCount
    replacementDilatedFibreLower replacementDilatedFibreUpper
    squareRootReplacementFibreLower squareRootReplacementFibreUpper
  simp only [Nat.mul_one]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hqPrime : q.Prime
  · simp [hqPrime, hqPrime.one_lt]
  · simp [hqPrime]

/-- Every strict-root cofactor window is an existing prime-sieve reciprocal
prime count at the contracted endpoint `X_R / c`, with the cofactor itself as
the lower prime cutoff.  This is the exact interface from the crossing tail to
the repository's reciprocal-prime analytic machinery. -/
theorem replacementFibreRootPrimeWindowCount_eq_reciprocalPrimeCount
    (R z c : ℕ) :
    replacementFibreRootPrimeWindowCount R z c =
      primeSieveReciprocalPrimeCount c (squareRootEndpoint R / c) z := by
  classical
  unfold replacementFibreRootPrimeWindowCount
    primeSieveReciprocalPrimeCount primeSievePrimeIndicator
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc,
    mem_primeSieveReciprocalInterval]
  unfold replacementDilatedFibreLower replacementDilatedFibreUpper
    primeSieveReciprocalLower primeSieveReciprocalUpper
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hprime, hcq⟩
    refine ⟨⟨max_lt hcq ?_, ?_⟩, hprime⟩
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using
        (show squareRootEndpoint R / ((z + 1) * c) < q by omega)
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using hupper
  · rintro ⟨⟨hlower, hupper⟩, hprime⟩
    rcases max_lt_iff.mp hlower with ⟨hcq, hquot⟩
    refine ⟨⟨?_, ?_⟩, hprime, hcq⟩
    · have : squareRootEndpoint R / ((z + 1) * c) < q := by
        simpa [Nat.mul_comm, Nat.mul_left_comm] using hquot
      omega
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using hupper

/-- Smooth-oriented reciprocal prime count at the contracted endpoint.  The
canonical largest prime of the cofactor is the lower cutoff, while `q < c`
retains the smooth orientation inside the same prime interval. -/
def replacementFibreSmoothReciprocalPrimeCount (R z c : ℕ) : ℂ :=
  ∑ q ∈ primeSieveReciprocalInterval
      (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z,
    if q.Prime ∧ q < c then 1 else 0

/-- Every smooth cofactor window is the contracted reciprocal-prime interval
with the orientation cutoff `q < c` retained inside its signed summand. -/
theorem replacementFibreSmoothPrimeWindowCount_eq_reciprocalPrimeCount
    (R z c : ℕ) :
    replacementFibreSmoothPrimeWindowCount R z c =
      replacementFibreSmoothReciprocalPrimeCount R z c := by
  classical
  unfold replacementFibreSmoothPrimeWindowCount
    replacementFibreSmoothReciprocalPrimeCount
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc,
    mem_primeSieveReciprocalInterval]
  unfold replacementDilatedFibreLower replacementDilatedFibreUpper
    primeSieveReciprocalLower primeSieveReciprocalUpper
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hprime, hrough, hqc⟩
    refine ⟨⟨max_lt hrough ?_, ?_⟩, hprime, hqc⟩
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using
        (show squareRootEndpoint R / ((z + 1) * c) < q by omega)
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using hupper
  · rintro ⟨⟨hlower, hupper⟩, hprime, hqc⟩
    rcases max_lt_iff.mp hlower with ⟨hrough, hquot⟩
    refine ⟨⟨?_, ?_⟩, hprime, hrough, hqc⟩
    · have : squareRootEndpoint R / ((z + 1) * c) < q := by
        simpa [Nat.mul_comm, Nat.mul_left_comm] using hquot
      omega
    · simpa [Nat.mul_comm, Nat.mul_left_comm] using hupper
/-- Strict-root mass after removing the cofactor-one prime face. -/
def replacementFibreCompositeRootMass (R z : ℕ) : ℂ :=
  replacementFibreRootMass R z - replacementFibrePrimeFaceMass R z

/-- Removing the cofactor-one prime face from the root orientation leaves
exactly the signed Type-II prime windows with cofactors `c >= 2`. -/
theorem replacementFibreCompositeRootMass_eq_neg_cofactorPrimeWindows
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreCompositeRootMass R z =
      -∑ c ∈ Finset.Icc 2 (R - 1),
        canonicalMoebiusWeight c *
          replacementFibreRootPrimeWindowCount R z c := by
  classical
  unfold replacementFibreCompositeRootMass
  rw [replacementFibreRootMass_eq_neg_cofactorPrimeWindows R z hR hz hzR,
    replacementFibrePrimeFaceMass_eq_neg_primeCount R z hR hz hzR,
    ← replacementFibreRootPrimeWindowCount_one_eq_primeCount R z]
  have hset :
      Finset.Icc 1 (R - 1) =
        ({1} : Finset ℕ) ∪ Finset.Icc 2 (R - 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    rw [Finset.mem_singleton] at hc1
    subst c
    simp at hc2
  rw [hset, Finset.sum_union hdisj]
  simp [canonicalMoebiusWeight]

/-- The two non-prime orientations kept as one signed cofactor-prime object.
The root side starts at cofactor two because the packet has removed the
cofactor-one face; the smooth side retains its canonical roughness condition
inside `replacementFibreSmoothPrimeWindowCount`. -/
def replacementFibreTypeIIWindowMass (R z : ℕ) : ℂ :=
  -((∑ c ∈ Finset.Icc 2 (R - 1),
        canonicalMoebiusWeight c *
          primeSieveReciprocalPrimeCount c
            (squareRootEndpoint R / c) z) +
      ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          replacementFibreSmoothReciprocalPrimeCount R z c)

/-- After prime-face removal, root-composite and smooth orientations are
exactly the single signed Type-II window mass. -/
theorem replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    replacementFibreCompositeRootMass R z +
        replacementFibreSmoothMass R z =
      replacementFibreTypeIIWindowMass R z := by
  rw [replacementFibreCompositeRootMass_eq_neg_cofactorPrimeWindows
      R z hR hz hzR,
    replacementFibreSmoothMass_eq_neg_cofactorPrimeWindows
      R z hR hz hzR]
  simp_rw [replacementFibreRootPrimeWindowCount_eq_reciprocalPrimeCount,
    replacementFibreSmoothPrimeWindowCount_eq_reciprocalPrimeCount]
  unfold replacementFibreTypeIIWindowMass
  ring

/-- The complementary Möbius fibre is the prime face, the remaining strict-root
mass, and the smooth-oriented mass, with all signs retained. -/
theorem squareRootReplacementTailMoebiusCoefficient_eq_prime_add_composite_add_smooth
    (R z : ℕ) (hR : 2 ≤ R) :
    squareRootReplacementTailMoebiusCoefficient R z =
      replacementFibrePrimeFaceMass R z +
        replacementFibreCompositeRootMass R z +
          replacementFibreSmoothMass R z := by
  rw [squareRootReplacementTailMoebiusCoefficient_eq_root_add_smooth R z hR]
  unfold replacementFibreCompositeRootMass
  ring

/-- The prime diagonal after adding the packet-removal row.  This is where the
crossing acts inside the reciprocal-fibre renewal, before any norm. -/
def squareRootPostCrossingPrimeDiagonal
    (R K j y : ℕ) : ℂ :=
  replacementFibrePrimeFaceMass R y +
    squareRootCrossingRemovalCoefficient R K j y

/-- Every completely admitted shallow layer cancels its entire cofactor-one
prime diagonal. -/
theorem squareRootPostCrossingPrimeDiagonal_eq_zero_of_lt
    (R K j y : ℕ) (hR : 2 ≤ R) (hK : K + 1 < R)
    (hy : 1 ≤ y) (hyK : y < K) :
    squareRootPostCrossingPrimeDiagonal R K j y = 0 := by
  have hyR : y + 1 < R := by omega
  unfold squareRootPostCrossingPrimeDiagonal
  rw [replacementFibrePrimeFaceMass_eq_neg_reciprocalPrimeLayerCard
    R y hR hy hyR]
  unfold squareRootCrossingRemovalCoefficient
  rw [squareRootReciprocalPrimeCount_eq_layerCard]
  have hyPred : y ≤ K - 1 := by omega
  have hyNe : y ≠ K := by omega
  simp [Finset.mem_Icc, hy, hyPred, hyNe]

/-- At the crossing layer, the surviving prime diagonal is exactly the signed
number of unfilled seats. -/
theorem squareRootPostCrossingPrimeDiagonal_eq_crossing_remainder
    (R K j : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingPrimeDiagonal R K j K =
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) := by
  unfold squareRootPostCrossingPrimeDiagonal
  rw [replacementFibrePrimeFaceMass_eq_neg_reciprocalPrimeLayerCard
    R K hR hK hKR]
  unfold squareRootCrossingRemovalCoefficient
  have hnotPred : ¬K ≤ K - 1 := by omega
  simp [Finset.mem_Icc, hnotPred]
  ring

/-- The shallow removal row is exactly the negative partial packet. -/
theorem sum_crossingRemovalCoefficient_mul_mertens
    (R K j : ℕ) (hK : 1 ≤ K) (hKR : K < R) :
    (∑ y ∈ Finset.range R,
        squareRootCrossingRemovalCoefficient R K j y *
          mertensSummatory y) =
      -((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) := by
  have hfilter :
      (Finset.range R).filter (fun y => y ∈ Finset.Icc 1 (K - 1)) =
        Finset.Icc 1 (K - 1) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hKmem : K ∈ Finset.range R := Finset.mem_range.mpr hKR
  rw [squareRootCrossingLayerPartialPacketInt_cast_complex]
  unfold squareRootCrossingRemovalCoefficient
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ y ∈ Finset.range R,
          (if y ∈ Finset.Icc 1 (K - 1) then
              primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y
            else 0) * mertensSummatory y) =
        ∑ y ∈ Finset.Icc 1 (K - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y *
            mertensSummatory y := by
    calc
      (∑ y ∈ Finset.range R,
          (if y ∈ Finset.Icc 1 (K - 1) then
              primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y
            else 0) * mertensSummatory y) =
          ∑ y ∈ Finset.range R,
            if y ∈ Finset.Icc 1 (K - 1) then
              primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y *
                mertensSummatory y
            else 0 := by
              apply Finset.sum_congr rfl
              intro y _hy
              by_cases hy : y ∈ Finset.Icc 1 (K - 1) <;> simp [hy]
      _ = ∑ y ∈ (Finset.range R).filter
            (fun y => y ∈ Finset.Icc 1 (K - 1)),
            primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y *
              mertensSummatory y := by
              rw [Finset.sum_filter]
      _ = ∑ y ∈ Finset.Icc 1 (K - 1),
            primeSieveReciprocalPrimeCount R (squareRootEndpoint R) y *
              mertensSummatory y := by rw [hfilter]
  rw [hfirst]
  have hsecond :
      (∑ y ∈ Finset.range R,
          (if y = K then (j : ℂ) else 0) * mertensSummatory y) =
        (j : ℂ) * mertensSummatory K := by
    simp [hKmem]
  rw [hsecond]
  unfold squareRootTruncatedUpperMiddlePacket
  ring

/-- The strict-descendant part of the complementary fibre transform.  The
cofactor-one prime face, composite strict-root face, and smooth face stay
inside the same signed summand. -/
def squareRootOrientedStrictDescendantTransform (R y : ℕ) : ℂ :=
  ∑ z ∈ Finset.Icc (y + 1) (R - 1),
    (replacementFibrePrimeFaceMass R z +
        replacementFibreCompositeRootMass R z +
          replacementFibreSmoothMass R z) *
      squareRootReplacementQuotientKernel z y

/-- Lower triangularity splits the complete quotient transform into its
diagonal fibre and its strict descendants. -/
theorem sum_tailMoebius_mul_quotientKernel_eq_diagonal_add_strict
    (R y : ℕ) (hy : 1 ≤ y) (hyR : y < R) :
    (∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z *
          squareRootReplacementQuotientKernel z y) =
      squareRootReplacementTailMoebiusCoefficient R y +
        ∑ z ∈ Finset.Icc (y + 1) (R - 1),
          squareRootReplacementTailMoebiusCoefficient R z *
            squareRootReplacementQuotientKernel z y := by
  let f : ℕ → ℂ := fun z =>
    squareRootReplacementTailMoebiusCoefficient R z *
      squareRootReplacementQuotientKernel z y
  have hzero : (∑ z ∈ Finset.range y, f z) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    have hzy : z < y := Finset.mem_range.mp hz
    unfold f
    rw [squareRootReplacementQuotientKernel_eq_zero_of_lt hzy]
    ring
  have hset :
      Finset.Ico (y + 1) R = Finset.Icc (y + 1) (R - 1) := by
    ext z
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  calc
    (∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z *
          squareRootReplacementQuotientKernel z y) =
        (∑ z ∈ Finset.range (y + 1), f z) +
          ∑ z ∈ Finset.Ico (y + 1) R, f z := by
            simpa [f] using
              (Finset.sum_range_add_sum_Ico f
                (Nat.succ_le_of_lt hyR)).symm
    _ = ((∑ z ∈ Finset.range y, f z) + f y) +
          ∑ z ∈ Finset.Ico (y + 1) R, f z := by
            rw [Finset.sum_range_succ]
    _ = f y + ∑ z ∈ Finset.Ico (y + 1) R, f z := by rw [hzero, zero_add]
    _ = squareRootReplacementTailMoebiusCoefficient R y +
          ∑ z ∈ Finset.Icc (y + 1) (R - 1),
            squareRootReplacementTailMoebiusCoefficient R z *
              squareRootReplacementQuotientKernel z y := by
      unfold f
      rw [squareRootReplacementQuotientKernel_self hy, hset]
      ring

/-- Renewal coefficient after the packet has canceled the shallow prime
diagonal.  Only the remaining prime diagonal, the two non-prime orientations,
and strict quotient descendants occur. -/
def squareRootPostCrossingPrimeCancelledCoefficient
    (R K j y : ℕ) : ℂ :=
  (if y = R - 1 then 1 else 0) +
    squareRootPostCrossingPrimeDiagonal R K j y +
      replacementFibreCompositeRootMass R y +
        replacementFibreSmoothMass R y +
          squareRootOrientedStrictDescendantTransform R y

/-- **Coefficientwise prime-diagonal cancellation.**  The post-crossing
replacement row is exactly the oriented prime-cancelled quotient row. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
    (R K j y : ℕ) (hR : 2 ≤ R) (hy : 1 ≤ y) (hyR : y < R) :
    squareRootPostCrossingReplacementCoefficient R K j y =
      squareRootPostCrossingPrimeCancelledCoefficient R K j y := by
  unfold squareRootPostCrossingReplacementCoefficient
  rw [show squareRootReplacementCoefficient R y =
      (if y = R - 1 then 1 else 0) +
        ∑ z ∈ Finset.range R,
          squareRootReplacementTailMoebiusCoefficient R z *
            squareRootReplacementQuotientKernel z y by
      unfold squareRootReplacementCoefficient
      rw [squareRootReplacementTailCoefficient_eq_neg_tailMoebiusKernel
        R y hR]
      ring]
  rw [sum_tailMoebius_mul_quotientKernel_eq_diagonal_add_strict R y hy hyR,
    squareRootReplacementTailMoebiusCoefficient_eq_prime_add_composite_add_smooth
      R y hR]
  unfold squareRootPostCrossingPrimeCancelledCoefficient
    squareRootPostCrossingPrimeDiagonal
    squareRootOrientedStrictDescendantTransform
  simp_rw [squareRootReplacementTailMoebiusCoefficient_eq_prime_add_composite_add_smooth
    R _ hR]
  ring

/-- Below the crossing, the complete prime diagonal has disappeared from the
renewal coefficient; no estimate or absolute value is used. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_belowCrossing
    (R K j y : ℕ) (hR : 2 ≤ R) (hKR : K + 1 < R)
    (hy : 1 ≤ y) (hyK : y < K) :
    squareRootPostCrossingReplacementCoefficient R K j y =
      replacementFibreCompositeRootMass R y +
        replacementFibreSmoothMass R y +
          squareRootOrientedStrictDescendantTransform R y := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
    R K j y hR hy (by omega)]
  unfold squareRootPostCrossingPrimeCancelledCoefficient
  rw [squareRootPostCrossingPrimeDiagonal_eq_zero_of_lt
    R K j y hR hKR hy hyK]
  have hpredNe : y ≠ R - 1 := by omega
  simp [hpredNe]

/-- Below the crossing, the residual coefficient is one signed Type-II
cofactor-window mass plus the strict lower-triangular descendants. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_belowCrossing_typeII
    (R K j y : ℕ) (hR : 2 ≤ R) (hKR : K + 1 < R)
    (hy : 1 ≤ y) (hyK : y < K) :
    squareRootPostCrossingReplacementCoefficient R K j y =
      replacementFibreTypeIIWindowMass R y +
        squareRootOrientedStrictDescendantTransform R y := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_belowCrossing
      R K j y hR hKR hy hyK,
    replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
      R y hR hy (by omega)]

/-- At the crossing depth, the only cofactor-one diagonal left in the renewal
row is `j-N_R(K)`, the negative of the unfilled prime seats. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_atCrossing
    (R K j : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingReplacementCoefficient R K j K =
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
        replacementFibreCompositeRootMass R K +
          replacementFibreSmoothMass R K +
            squareRootOrientedStrictDescendantTransform R K := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
    R K j K hR hK (by omega)]
  unfold squareRootPostCrossingPrimeCancelledCoefficient
  rw [squareRootPostCrossingPrimeDiagonal_eq_crossing_remainder
    R K j hR hK hKR]
  have hpredNe : K ≠ R - 1 := by omega
  simp [hpredNe]

/-- At the crossing, the residual row is the exact unfilled-seat remainder,
the same signed Type-II window mass, and the strict descendants. -/
theorem squareRootPostCrossingReplacementCoefficient_eq_atCrossing_typeII
    (R K j : ℕ) (hR : 2 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingReplacementCoefficient R K j K =
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
        replacementFibreTypeIIWindowMass R K +
          squareRootOrientedStrictDescendantTransform R K := by
  rw [squareRootPostCrossingReplacementCoefficient_eq_atCrossing
      R K j hR hK hKR,
    add_assoc
      ((j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ))
      (replacementFibreCompositeRootMass R K)
      (replacementFibreSmoothMass R K),
    replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
      R K hR hK (by omega)]

/-- **Exact post-crossing lower-triangular renewal row.**  The terminal tail is
one signed combination of Mertens states at scales `y < R`; the shallow packet
has modified the same row coefficientwise before any norm is taken. -/
theorem squareRootPostCrossingCoupledTail_eq_replacementRow
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      ∑ y ∈ Finset.range R,
        squareRootPostCrossingReplacementCoefficient R K j y *
          mertensSummatory y := by
  rw [postCrossingCoupledTail_eq_mertens_sub_partial R K j hR,
    mertensEndpoint_eq_recombinedReplacementRow R (by omega)]
  have hremove := sum_crossingRemovalCoefficient_mul_mertens
    R K j hK hKR
  unfold squareRootPostCrossingReplacementCoefficient
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, hremove]
  ring

/-- The terminal tail written on the positive lower scales after the
prime-diagonal cancellation has been performed coefficientwise. -/
theorem squareRootPostCrossingCoupledTail_eq_primeCancelledRow
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingCoupledTail R K j =
      ∑ y ∈ Finset.Icc 1 (R - 1),
        squareRootPostCrossingPrimeCancelledCoefficient R K j y *
          mertensSummatory y := by
  rw [squareRootPostCrossingCoupledTail_eq_replacementRow
    R K j hR hK hKR]
  have hset :
      Finset.range R = ({0} : Finset ℕ) ∪ Finset.Icc 1 (R - 1) := by
    ext y
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_Icc]
    omega
  have hdisj :
      Disjoint ({0} : Finset ℕ) (Finset.Icc 1 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro y hy0 hyIcc
    rw [Finset.mem_singleton] at hy0
    subst y
    simp at hyIcc
  rw [hset, Finset.sum_union hdisj]
  simp only [Finset.sum_singleton]
  rw [mertensSummatory_zero, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro y hy
  rcases Finset.mem_Icc.mp hy with ⟨hy1, hyR⟩
  rw [squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
    R K j y (by omega) hy1 (by omega)]

/-- **Exact crossing split of the prime-cancelled renewal.**  Every completed
shallow prime diagonal is absent, the crossing row contains only the unfilled
prime seats, and the deeper oriented quotient tail remains one signed sum. -/
theorem squareRootPostCrossingCoupledTail_eq_primeCancelledCrossingSplit
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingCoupledTail R K j =
      (∑ y ∈ Finset.Icc 1 (K - 1),
        (replacementFibreCompositeRootMass R y +
            replacementFibreSmoothMass R y +
              squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y) +
      ((j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreCompositeRootMass R K +
            replacementFibreSmoothMass R K +
              squareRootOrientedStrictDescendantTransform R K) *
        mertensSummatory K +
      ∑ y ∈ Finset.Icc (K + 1) (R - 1),
        squareRootPostCrossingPrimeCancelledCoefficient R K j y *
          mertensSummatory y := by
  rw [squareRootPostCrossingCoupledTail_eq_primeCancelledRow
    R K j hR hK (by omega)]
  rw [sum_Icc_one_pred_split_at
    (fun y => squareRootPostCrossingPrimeCancelledCoefficient R K j y *
      mertensSummatory y) hK (by omega)]
  have hbelow :
      (∑ y ∈ Finset.Icc 1 (K - 1),
        squareRootPostCrossingPrimeCancelledCoefficient R K j y *
          mertensSummatory y) =
        ∑ y ∈ Finset.Icc 1 (K - 1),
          (replacementFibreCompositeRootMass R y +
              replacementFibreSmoothMass R y +
                squareRootOrientedStrictDescendantTransform R y) *
            mertensSummatory y := by
    apply Finset.sum_congr rfl
    intro y hy
    rcases Finset.mem_Icc.mp hy with ⟨hy1, hyK⟩
    have hyLt : y < K := by omega
    rw [← squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
      R K j y (by omega) hy1 (by omega),
      squareRootPostCrossingReplacementCoefficient_eq_belowCrossing
        R K j y (by omega) hKR hy1 hyLt]
  have hat :
      squareRootPostCrossingPrimeCancelledCoefficient R K j K =
        (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreCompositeRootMass R K +
            replacementFibreSmoothMass R K +
              squareRootOrientedStrictDescendantTransform R K := by
    rw [← squareRootPostCrossingReplacementCoefficient_eq_primeCancelled
      R K j K (by omega) hK (by omega),
      squareRootPostCrossingReplacementCoefficient_eq_atCrossing
        R K j (by omega) hK hKR]
  rw [hbelow, hat]

/-- **Type-II crossing normal form.**  The completed shallow rows contain no
cofactor-one prime term: their whole diagonal contribution is the single
signed cofactor-window mass.  The crossing row differs only by its exact
unfilled-seat remainder, while the deep tail remains coupled. -/
theorem squareRootPostCrossingCoupledTail_eq_typeIICrossingSplit
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K + 1 < R) :
    squareRootPostCrossingCoupledTail R K j =
      (∑ y ∈ Finset.Icc 1 (K - 1),
        (replacementFibreTypeIIWindowMass R y +
            squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y) +
      ((j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreTypeIIWindowMass R K +
            squareRootOrientedStrictDescendantTransform R K) *
        mertensSummatory K +
      ∑ y ∈ Finset.Icc (K + 1) (R - 1),
        squareRootPostCrossingPrimeCancelledCoefficient R K j y *
          mertensSummatory y := by
  rw [squareRootPostCrossingCoupledTail_eq_primeCancelledCrossingSplit
    R K j hR hK hKR]
  have hbelow :
      (∑ y ∈ Finset.Icc 1 (K - 1),
        (replacementFibreCompositeRootMass R y +
            replacementFibreSmoothMass R y +
              squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y) =
        ∑ y ∈ Finset.Icc 1 (K - 1),
          (replacementFibreTypeIIWindowMass R y +
              squareRootOrientedStrictDescendantTransform R y) *
            mertensSummatory y := by
    apply Finset.sum_congr rfl
    intro y hy
    rcases Finset.mem_Icc.mp hy with ⟨hy1, hyK⟩
    rw [replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
      R y (by omega) hy1 (by omega)]
  have hat :
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreCompositeRootMass R K +
            replacementFibreSmoothMass R K +
              squareRootOrientedStrictDescendantTransform R K =
        (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
          replacementFibreTypeIIWindowMass R K +
            squareRootOrientedStrictDescendantTransform R K := by
    calc
      (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
            replacementFibreCompositeRootMass R K +
              replacementFibreSmoothMass R K +
                squareRootOrientedStrictDescendantTransform R K =
          squareRootPostCrossingReplacementCoefficient R K j K :=
            (squareRootPostCrossingReplacementCoefficient_eq_atCrossing
              R K j (by omega) hK hKR).symm
      _ = (j : ℂ) - (squareRootReciprocalPrimeLayerCard R K : ℂ) +
            replacementFibreTypeIIWindowMass R K +
              squareRootOrientedStrictDescendantTransform R K :=
          squareRootPostCrossingReplacementCoefficient_eq_atCrossing_typeII
            R K j (by omega) hK hKR
  rw [hbelow, hat]

/-- One summand of the oriented prime-cancelled renewal row. -/
def squareRootPostCrossingPrimeCancelledTerm
    (R K j y : ℕ) : ℂ :=
  squareRootPostCrossingPrimeCancelledCoefficient R K j y *
    mertensSummatory y

/-- Full signed Gram after the cofactor-one prime diagonal has been canceled
inside the coefficient row.  Strict descendants and both non-prime
orientations remain coupled in the double sum. -/
def squareRootPostCrossingPrimeCancelledGram
    (R K j : ℕ) : ℂ :=
  ∑ y ∈ Finset.Icc 1 (R - 1),
    ∑ z ∈ Finset.Icc 1 (R - 1),
      squareRootPostCrossingPrimeCancelledTerm R K j y *
        conj (squareRootPostCrossingPrimeCancelledTerm R K j z)

/-- The oriented, prime-cancelled Gram is exactly the coupled-tail energy. -/
theorem squareRootPostCrossingPrimeCancelledGram_eq_tail_mul_conj
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingPrimeCancelledGram R K j =
      squareRootPostCrossingCoupledTail R K j *
        conj (squareRootPostCrossingCoupledTail R K j) := by
  rw [squareRootPostCrossingCoupledTail_eq_primeCancelledRow
    R K j hR hK hKR]
  unfold squareRootPostCrossingPrimeCancelledGram
    squareRootPostCrossingPrimeCancelledTerm
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]

/-- Real norm-square form of the exact prime-cancelled Gram identity. -/
theorem squareRootPostCrossingPrimeCancelledGram_eq_tail_norm_sq
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingPrimeCancelledGram R K j =
      ((‖squareRootPostCrossingCoupledTail R K j‖ ^ 2 : ℝ) : ℂ) := by
  rw [squareRootPostCrossingPrimeCancelledGram_eq_tail_mul_conj
    R K j hR hK hKR, Complex.mul_conj']
  norm_cast

/-- One lower-scale summand in the post-crossing replacement row. -/
def squareRootPostCrossingReplacementTerm
    (R K j y : ℕ) : ℂ :=
  squareRootPostCrossingReplacementCoefficient R K j y *
    mertensSummatory y

/-- The complete signed Gram of the post-crossing replacement row.  Both
indices remain inside one double sum, so no diagonal/off-diagonal separation
has occurred. -/
def squareRootPostCrossingReplacementGram
    (R K j : ℕ) : ℂ :=
  ∑ y ∈ Finset.range R,
    ∑ z ∈ Finset.range R,
      squareRootPostCrossingReplacementTerm R K j y *
        conj (squareRootPostCrossingReplacementTerm R K j z)

/-- The nonlocal replacement Gram is exactly the coupled-tail energy before
coercing the real norm square into an inequality. -/
theorem squareRootPostCrossingReplacementGram_eq_tail_mul_conj
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingReplacementGram R K j =
      squareRootPostCrossingCoupledTail R K j *
        conj (squareRootPostCrossingCoupledTail R K j) := by
  rw [squareRootPostCrossingCoupledTail_eq_replacementRow
    R K j hR hK hKR]
  unfold squareRootPostCrossingReplacementGram
    squareRootPostCrossingReplacementTerm
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]

/-- Real-energy form of the exact signed Gram identity. -/
theorem squareRootPostCrossingReplacementGram_eq_tail_norm_sq
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootPostCrossingReplacementGram R K j =
      ((‖squareRootPostCrossingCoupledTail R K j‖ ^ 2 : ℝ) : ℂ) := by
  rw [squareRootPostCrossingReplacementGram_eq_tail_mul_conj
    R K j hR hK hKR, Complex.mul_conj']
  norm_cast

end RHLean.Proof
