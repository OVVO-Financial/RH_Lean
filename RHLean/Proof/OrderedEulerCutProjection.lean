import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge
import RHLean.Proof.SignedPrefixEventLifetime

/-!
# Ordered Euler cut projection

The final oriented square-root boundary is not treated here as unrelated
coordinate systems. One tagged occurrence `(t,(c,p))` is kept intact and
projected simultaneously to

* the low Boolean-face product `a = P(t)`;
* the crossing prime `p`;
* the rough high cofactor `c`;
* the squarefree parent integer `m = c*a`;
* the fresh-prime child integer `n = c*(p*a)`;
* the half-open root lifetime in which the occurrence remains exposed.

On the actual oriented carrier the quotient coordinate is already the canonical
pivot. Every face prime is below that pivot and every cofactor prime is above it.
Consequently the signed low-wheel weight is the ordinary Möbius weight of `m`,
and adjoining the crossing prime changes it to its negative.

The main theorem gives an exact static lifetime representation. For a valid
ordered cut, membership in the oriented tagged boundary at root `R` is equivalent
to one interval condition `birthRoot <= R < deathRoot`. Thus the same atom can
be followed through all square roots without rebuilding its sign or factor
coordinates at each endpoint.

No norm, asymptotic estimate, prime-gap input, independence assumption, PNT input,
or RH hypothesis appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- One occurrence of the canonically oriented boundary, with its Boolean face
retained. -/
abbrev OrderedEulerCutTaggedState :=
  Finset ℕ × LowWheelCofactorQuotientState

/-- Static arithmetic validity of an ordered Euler cut. This predicate has no
root parameter: it records only factor ordering and squarefree data. -/
def OrderedEulerCutShape (y : OrderedEulerCutTaggedState) : Prop :=
  y.2.2.Prime ∧
    1 ≤ y.2.1 ∧
    Squarefree y.2.1 ∧
    ¬ y.2.2 ∣ y.2.1 ∧
    (∀ q ∈ y.1, q.Prime ∧ q < y.2.2) ∧
    RoughAbove y.2.2 y.2.1

/-- Product of all already-processed face primes, i.e. the root-side parent. -/
def orderedEulerCutLowProduct (y : OrderedEulerCutTaggedState) : ℕ :=
  primeFaceProduct y.1

/-- The distinguished crossing prime. -/
def orderedEulerCutPivot (y : OrderedEulerCutTaggedState) : ℕ :=
  y.2.2

/-- The rough cofactor whose prime factors lie strictly above the crossing
prime. -/
def orderedEulerCutHighCofactor (y : OrderedEulerCutTaggedState) : ℕ :=
  y.2.1

/-- The squarefree parent integer before the crossing prime is inserted. -/
def orderedEulerCutParentInteger (y : OrderedEulerCutTaggedState) : ℕ :=
  orderedEulerCutHighCofactor y * orderedEulerCutLowProduct y

/-- The physical child integer after the crossing prime is inserted. -/
def orderedEulerCutChildInteger (y : OrderedEulerCutTaggedState) : ℕ :=
  orderedEulerCutHighCofactor y *
    (orderedEulerCutPivot y * orderedEulerCutLowProduct y)

/-- Signed occurrence weight in the native low-wheel coordinates. -/
def orderedEulerCutWeight (y : OrderedEulerCutTaggedState) : ℂ :=
  canonicalMoebiusWeight (orderedEulerCutHighCofactor y) *
    (booleanCubeSign y.1 : ℂ)

/-- Root at which all monotone entrance constraints for the occurrence have
become true. The three pieces are `P(t) <= R`, `c < R`, and the physical square
cutoff `c*p*P(t) <= R^2-1`. -/
def orderedEulerCutBirthRoot (y : OrderedEulerCutTaggedState) : ℕ :=
  max (orderedEulerCutLowProduct y)
    (max (orderedEulerCutHighCofactor y + 1)
      (Nat.sqrt (orderedEulerCutChildInteger y) + 1))

/-- Root at which the missing fresh-prime partner becomes complete. -/
def orderedEulerCutDeathRoot (y : OrderedEulerCutTaggedState) : ℕ :=
  orderedEulerCutPivot y * orderedEulerCutLowProduct y

/-- The root-dependent tagged oriented occurrence predicate. -/
def OrderedEulerCutOccursAt (R : ℕ) (y : OrderedEulerCutTaggedState) : Prop :=
  y.1 ∈ (primesUpTo R).powerset ∧
    y.2 ∈ lowWheelCanonicalDowncrossOrientedPart R y.1

/-- Concrete finite tagged occurrence carrier at one root. -/
def orderedEulerCutCarrier (R : ℕ) : Finset OrderedEulerCutTaggedState :=
  ((primesUpTo R).powerset.product
      (lowWheelCanonicalDowncrossOrientedStateAmbient R)).filter fun y =>
    y.2 ∈ lowWheelCanonicalDowncrossOrientedPart R y.1

@[simp] theorem mem_orderedEulerCutCarrier
    {R : ℕ} {y : OrderedEulerCutTaggedState} :
    y ∈ orderedEulerCutCarrier R ↔ OrderedEulerCutOccursAt R y := by
  constructor
  · intro hy
    have h := Finset.mem_filter.mp hy
    have hp := Finset.mem_product.mp h.1
    exact ⟨hp.1, h.2⟩
  · rintro ⟨ht, hx⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨ht, ?_⟩, hx⟩
    exact lowWheelCanonicalDowncrossOrientedPart_subset_stateAmbient hx

/-- A prime divisor which is minimal among all prime divisors is `minFac`. -/
private theorem minFac_eq_of_prime_dvd_and_le_prime_divisors
    {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hle : ∀ r, r.Prime → r ∣ n → p ≤ r) :
    Nat.minFac n = p := by
  have hminLe : Nat.minFac n ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le hpn
  have hn1 : n ≠ 1 := by
    intro hn
    have hp1 : p ∣ 1 := by simpa [hn] using hpn
    have hpEq : p = 1 := Nat.dvd_one.mp hp1
    exact hp.ne_one hpEq
  have hminPrime : (Nat.minFac n).Prime := Nat.minFac_prime hn1
  have hminDvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  have hpLeMin : p ≤ Nat.minFac n := hle _ hminPrime hminDvd
  exact Nat.le_antisymm hminLe hpLeMin

/-- The static ordering data force the quotient coordinate to be its own
canonical least-prime pivot. -/
theorem orderedEulerCutShape_canonicalPivot
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    lowWheelCanonicalDowncrossPivot y.2 = orderedEulerCutPivot y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change Nat.minFac (c * p) = p
  have hcpos : 0 < c := lt_of_lt_of_le Nat.zero_lt_one hy.2.1
  have hc0 : c ≠ 0 := Nat.ne_of_gt hcpos
  apply minFac_eq_of_prime_dvd_and_le_prime_divisors hy.1
  · exact dvd_mul_left p c
  · intro r hr hrd
    rcases hr.dvd_mul.mp hrd with hrc | hrp
    · have hrcMem : r ∈ c.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hr, hrc, hc0⟩
      exact Nat.le_of_lt (hy.2.2.2.2.2 r hrcMem)
    · have hre : r = p :=
        (Nat.prime_dvd_prime_iff_eq hr hy.1).mp hrp
      simp [hre]

/-- Face products are positive for every ordered cut. -/
theorem orderedEulerCutLowProduct_pos
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    0 < orderedEulerCutLowProduct y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  unfold orderedEulerCutLowProduct
  have ht : t ∈ (primesUpTo p).powerset := by
    apply Finset.mem_powerset.mpr
    intro q hq
    exact mem_primesUpTo.mpr ⟨(hy.2.2.2.2.1 q hq).1,
      Nat.le_of_lt (hy.2.2.2.2.1 q hq).2⟩
  exact primeFaceProduct_pos_of_mem_powerset ht

/-- The crossing prime is fresh to the complete low face product. -/
theorem orderedEulerCutPivot_not_dvd_lowProduct
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    ¬ orderedEulerCutPivot y ∣ orderedEulerCutLowProduct y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change ¬ p ∣ primeFaceProduct t
  intro hpdiv
  have hpdiv' : p ∣ t.prod id := by
    simpa [primeFaceProduct] using hpdiv
  rcases (Prime.dvd_finset_prod_iff hy.1.prime id).mp hpdiv' with
    ⟨q, hqt, hpq⟩
  have hqPrime := (hy.2.2.2.2.1 q hqt).1
  have hpEq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hy.1 hqPrime).mp hpq
  have hlt := (hy.2.2.2.2.1 q hqt).2
  rw [← hpEq] at hlt
  exact (Nat.lt_irrefl p) hlt

/-- The low face product is a canonical ancestry core below the distinguished
crossing prime. -/
theorem orderedEulerCut_lowSourceData
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    CanonicalSourceData (orderedEulerCutPivot y)
      (orderedEulerCutLowProduct y) := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  have hlowPos : 0 < primeFaceProduct t :=
    orderedEulerCutLowProduct_pos hy
  have hmu : μ (primeFaceProduct t) = booleanCubeSign t :=
    moebius_primeFaceProduct_eq_booleanCubeSign t
      (fun q hq => (hy.2.2.2.2.1 q hq).1)
  have hmuNe : μ (primeFaceProduct t) ≠ 0 := by
    rw [hmu]
    unfold booleanCubeSign
    exact pow_ne_zero _ (by norm_num)
  have hsq : Squarefree (primeFaceProduct t) :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
  have hcop : Nat.Coprime p (primeFaceProduct t) :=
    (hy.1.coprime_iff_not_dvd).2 (orderedEulerCutPivot_not_dvd_lowProduct hy)
  refine ⟨hy.1, Nat.succ_le_iff.mpr hlowPos, hsq, hcop, ?_⟩
  intro q hqPrime hqDvd
  have hqProd : q ∣ t.prod id := by
    simpa [primeFaceProduct] using hqDvd
  rcases (Prime.dvd_finset_prod_iff hqPrime.prime id).mp hqProd with
    ⟨r, hrt, hqr⟩
  have hrPrime := (hy.2.2.2.2.1 r hrt).1
  have hqrEq : q = r :=
    (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
  subst q
  exact (hy.2.2.2.2.1 r hrt).2

/-- The rough high cofactor and low face product have disjoint prime support. -/
theorem orderedEulerCut_highCofactor_coprime_lowProduct
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    Nat.Coprime (orderedEulerCutHighCofactor y)
      (orderedEulerCutLowProduct y) := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change Nat.Coprime c (primeFaceProduct t)
  have hcpos : 0 < c := lt_of_lt_of_le Nat.zero_lt_one hy.2.1
  have hc0 : c ≠ 0 := Nat.ne_of_gt hcpos
  have ha0 : primeFaceProduct t ≠ 0 :=
    Nat.ne_of_gt (orderedEulerCutLowProduct_pos hy)
  rw [← Nat.disjoint_primeFactors hc0 ha0]
  rw [Finset.disjoint_left]
  intro q hqc hqa
  have hqHigh : p < q := hy.2.2.2.2.2 q hqc
  rcases Nat.mem_primeFactors.mp hqa with ⟨hqPrime, hqDvd, _ha0⟩
  have hqProd : q ∣ t.prod id := by
    simpa [primeFaceProduct] using hqDvd
  rcases (Prime.dvd_finset_prod_iff hqPrime.prime id).mp hqProd with
    ⟨r, hrt, hqr⟩
  have hrPrime := (hy.2.2.2.2.1 r hrt).1
  have hqrEq : q = r :=
    (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
  subst q
  have hrLow := (hy.2.2.2.2.1 r hrt).2
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hqHigh)) hrLow

/-- The native low-wheel sign is exactly the ordinary Möbius weight of the
single parent integer `c * P(t)`. -/
theorem orderedEulerCutWeight_eq_parentMoebius
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    orderedEulerCutWeight y =
      canonicalMoebiusWeight (orderedEulerCutParentInteger y) := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  have hcop0 := orderedEulerCut_highCofactor_coprime_lowProduct hy
  have hcop : Nat.Coprime c (primeFaceProduct t) := by
    simpa [orderedEulerCutHighCofactor, orderedEulerCutLowProduct] using hcop0
  have hface : μ (primeFaceProduct t) = booleanCubeSign t :=
    moebius_primeFaceProduct_eq_booleanCubeSign t
      (fun q hq => (hy.2.2.2.2.1 q hq).1)
  change canonicalMoebiusWeight c * (booleanCubeSign t : ℂ) =
    canonicalMoebiusWeight (c * primeFaceProduct t)
  unfold canonicalMoebiusWeight
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    hface]
  push_cast
  ring

/-- The crossing prime is fresh to the entire parent integer. -/
theorem orderedEulerCutPivot_not_dvd_parentInteger
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    ¬ orderedEulerCutPivot y ∣ orderedEulerCutParentInteger y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  change ¬ p ∣ c * primeFaceProduct t
  intro hp
  rcases hy.1.dvd_mul.mp hp with hpc | hpa
  · exact hy.2.2.2.1 hpc
  · exact orderedEulerCutPivot_not_dvd_lowProduct hy hpa

/-- **Euler sign reversal on the common integer coordinate.** The physical
child has exactly the opposite Möbius weight from the tagged parent occurrence. -/
theorem orderedEulerCutChildWeight_eq_neg
    {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    canonicalMoebiusWeight (orderedEulerCutChildInteger y) =
      -orderedEulerCutWeight y := by
  have hchild : orderedEulerCutChildInteger y =
      orderedEulerCutParentInteger y * orderedEulerCutPivot y := by
    unfold orderedEulerCutChildInteger orderedEulerCutParentInteger
      orderedEulerCutHighCofactor orderedEulerCutLowProduct orderedEulerCutPivot
    ring
  calc
    canonicalMoebiusWeight (orderedEulerCutChildInteger y) =
        canonicalMoebiusWeight
          (orderedEulerCutParentInteger y * orderedEulerCutPivot y) := by rw [hchild]
    _ = -canonicalMoebiusWeight (orderedEulerCutParentInteger y) := by
      exact canonicalMoebiusWeight_mul_freshPrime hy.1
        (orderedEulerCutPivot_not_dvd_parentInteger hy)
    _ = -orderedEulerCutWeight y := by
      rw [orderedEulerCutWeight_eq_parentMoebius hy]

/-- A square-product cutoff is exactly a lower bound on the square-root clock
for every positive ordered-cut child. -/
theorem orderedEulerCutChild_le_endpoint_iff
    {R : ℕ} {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    orderedEulerCutChildInteger y ≤ squareRootEndpoint R ↔
      Nat.sqrt (orderedEulerCutChildInteger y) < R := by
  have hcpos : 0 < orderedEulerCutHighCofactor y :=
    lt_of_lt_of_le Nat.zero_lt_one hy.2.1
  have hchildPos : 0 < orderedEulerCutChildInteger y := by
    unfold orderedEulerCutChildInteger
    exact Nat.mul_pos hcpos
      (Nat.mul_pos hy.1.pos (orderedEulerCutLowProduct_pos hy))
  constructor
  · intro h
    have hRpos : 0 < R := by
      by_contra hnot
      have hR0 : R = 0 := Nat.eq_zero_of_not_pos hnot
      subst R
      unfold squareRootEndpoint at h
      simp at h
      exact (Nat.ne_of_gt hchildPos) h
    apply (Nat.sqrt_lt').2
    have hend : squareRootEndpoint R < R ^ 2 := by
      unfold squareRootEndpoint
      have hsquare : 0 < R ^ 2 := pow_pos hRpos 2
      omega
    exact h.trans_lt hend
  · intro h
    have hlt : orderedEulerCutChildInteger y < R ^ 2 :=
      (Nat.sqrt_lt').1 h
    unfold squareRootEndpoint
    omega

/-- **Exact lifetime characterization.** For a static ordered Euler cut, being
an oriented physical boundary occurrence at root `R` is equivalent to one
half-open lifetime interval. -/
theorem orderedEulerCutOccursAt_iff_lifetime
    {R : ℕ} {y : OrderedEulerCutTaggedState} (hy : OrderedEulerCutShape y) :
    OrderedEulerCutOccursAt R y ↔
      orderedEulerCutBirthRoot y ≤ R ∧ R < orderedEulerCutDeathRoot y := by
  rcases y with ⟨t, ⟨c, p⟩⟩
  have hpivot : lowWheelCanonicalDowncrossPivot (c, p) = p :=
    orderedEulerCutShape_canonicalPivot hy
  have hpivotCQ : lowWheelCanonicalCofactorQuotientPivot (c, p) = p := by
    simpa [lowWheelCanonicalDowncrossPivot] using hpivot
  have hlowPos : 0 < primeFaceProduct t :=
    orderedEulerCutLowProduct_pos hy
  have hcpos : 0 < c := lt_of_lt_of_le Nat.zero_lt_one hy.2.1
  constructor
  · rintro ⟨_ht, hx⟩
    have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
    have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
    dsimp only at hgeom
    have hparent := lowWheelCanonicalDowncrossOriented_parent_eq_faceProduct hx
    have hphys :=
      mem_lowWheelCanonicalPhysicalStateSet.mp
        (mem_lowWheelCanonicalDowncrossPart.mp hdown).1
    have hcR : c < R := (Finset.mem_Ico.mp hphys.1).2
    have hparentR := hgeom.2.2.2.1
    rw [hparent] at hparentR
    have hdeath := hgeom.2.2.2.2.1
    rw [hpivot, hparent] at hdeath
    have hchild := hgeom.2.2.2.2.2
    rw [hpivot, hparent] at hchild
    have hchildWrapped :
        orderedEulerCutChildInteger (t, (c, p)) ≤ squareRootEndpoint R := by
      simpa [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct] using hchild
    have hsqrtWrapped :=
      (orderedEulerCutChild_le_endpoint_iff (R := R) hy).1 hchildWrapped
    have hsqrt : Nat.sqrt (c * (p * primeFaceProduct t)) < R := by
      simpa [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct] using hsqrtWrapped
    constructor
    · change max (primeFaceProduct t)
        (max (c + 1) (Nat.sqrt (c * (p * primeFaceProduct t)) + 1)) ≤ R
      apply Nat.max_le.mpr
      refine ⟨hparentR, Nat.max_le.mpr ⟨Nat.succ_le_iff.mpr hcR, ?_⟩⟩
      exact Nat.succ_le_iff.mpr hsqrt
    · change R < p * primeFaceProduct t
      exact hdeath
  · rintro ⟨hbirth, hdeath⟩
    change max (primeFaceProduct t)
      (max (c + 1) (Nat.sqrt (c * (p * primeFaceProduct t)) + 1)) ≤ R at hbirth
    change R < p * primeFaceProduct t at hdeath
    rcases Nat.max_le.mp hbirth with ⟨hlowR, hrest⟩
    rcases Nat.max_le.mp hrest with ⟨hcSuccR, hsqrtSuccR⟩
    have hcLt : c < R := Nat.lt_of_succ_le hcSuccR
    have hsqrt : Nat.sqrt (c * (p * primeFaceProduct t)) < R :=
      Nat.lt_of_succ_le hsqrtSuccR
    have hsqrtWrapped :
        Nat.sqrt (orderedEulerCutChildInteger (t, (c, p))) < R := by
      simpa [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct] using hsqrt
    have hchildWrapped :=
      (orderedEulerCutChild_le_endpoint_iff (R := R) hy).2 hsqrtWrapped
    have hchild : c * (p * primeFaceProduct t) ≤ squareRootEndpoint R := by
      simpa [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct] using hchildWrapped
    have htPow : t ∈ (primesUpTo R).powerset := by
      apply Finset.mem_powerset.mpr
      intro q hqt
      have hqData := hy.2.2.2.2.1 q hqt
      have hqDvd : q ∣ primeFaceProduct t := by
        simpa [primeFaceProduct] using Finset.dvd_prod_of_mem id hqt
      have hqLe : q ≤ primeFaceProduct t := Nat.le_of_dvd hlowPos hqDvd
      exact mem_primesUpTo.mpr ⟨hqData.1, hqLe.trans hlowR⟩
    have hchildPos : 0 < c * (p * primeFaceProduct t) :=
      Nat.mul_pos hcpos (Nat.mul_pos hy.1.pos hlowPos)
    have hpDvdChild : p ∣ c * (p * primeFaceProduct t) := by
      refine ⟨c * primeFaceProduct t, ?_⟩
      ring
    have hpLeChild : p ≤ c * (p * primeFaceProduct t) :=
      Nat.le_of_dvd hchildPos hpDvdChild
    have hphysical : (c, p) ∈ lowWheelCanonicalPhysicalStateSet R t := by
      apply mem_lowWheelCanonicalPhysicalStateSet.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨hy.2.1, hcLt⟩,
        Finset.mem_Icc.mpr ⟨hy.1.one_le, hpLeChild.trans hchild⟩,
        hy.2.2.1, ?_⟩
      unfold LowWheelTransportPairCarrier
      refine ⟨hy.2.1, hcLt, ?_, ?_⟩
      · simpa [Nat.mul_comm] using hdeath
      · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hchild
    have hdown : (c, p) ∈ lowWheelCanonicalDowncrossPart R t := by
      apply mem_lowWheelCanonicalDowncrossPart.mpr
      refine ⟨hphysical, ?_, ?_⟩
      · rw [hpivotCQ]
        exact hy.2.2.2.1
      · rw [hpivotCQ, Nat.div_self hy.1.pos, Nat.mul_one]
        exact hlowR
    have horiented : (c, p) ∈ lowWheelCanonicalDowncrossOrientedPart R t := by
      apply mem_lowWheelCanonicalDowncrossOrientedPart.mpr
      refine ⟨hdown, ?_⟩
      intro q hqParent
      have hparentEq :
          LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent
              t (c, p) = primeFaceProduct t := by
        unfold LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossParent
          LowWheelCanonicalDowncrossOwnership.lowWheelCanonicalDowncrossPivot
        rw [hpivotCQ, Nat.div_self hy.1.pos, Nat.mul_one]
      rw [hparentEq] at hqParent
      rcases Nat.mem_primeFactors.mp hqParent with
        ⟨hqPrime, hqDvd, _hface0⟩
      have hqProd : q ∣ t.prod id := by
        simpa [primeFaceProduct] using hqDvd
      rcases (Prime.dvd_finset_prod_iff hqPrime.prime id).mp hqProd with
        ⟨r, hrt, hqr⟩
      have hrPrime := (hy.2.2.2.2.1 r hrt).1
      have hqrEq : q = r :=
        (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
      subst q
      rw [hpivot]
      exact (hy.2.2.2.2.1 r hrt).2
    exact ⟨htPow, horiented⟩

/-- The abstract lifetime indicator applies literally to every static ordered
cut which occurs at `R`. -/
theorem orderedEulerCut_lifetimeActivity_eq_one
    {R : ℕ} {y : OrderedEulerCutTaggedState}
    (hy : OrderedEulerCutShape y)
    (hocc : OrderedEulerCutOccursAt R y) :
    lifetimeActivity (orderedEulerCutBirthRoot y)
        (orderedEulerCutDeathRoot y) R = 1 := by
  have hlife := (orderedEulerCutOccursAt_iff_lifetime hy).1 hocc
  simp [lifetimeActivity, hlife]

/-- Every actual tagged carrier point has the static ordered-cut shape. -/
theorem orderedEulerCutShape_of_mem_carrier
    {R : ℕ} {y : OrderedEulerCutTaggedState}
    (hy : y ∈ orderedEulerCutCarrier R) : OrderedEulerCutShape y := by
  have hocc := mem_orderedEulerCutCarrier.mp hy
  rcases y with ⟨t, ⟨c, k⟩⟩
  rcases hocc with ⟨ht, hx⟩
  have hq : k = lowWheelCanonicalDowncrossPivot (c, k) :=
    lowWheelCanonicalDowncrossOriented_quotient_eq_pivot hx
  have hdown := (mem_lowWheelCanonicalDowncrossOrientedPart.mp hx).1
  have hgeom := lowWheelCanonicalDowncross_firstFailure_geometry hdown
  dsimp only at hgeom
  have hphys :=
    mem_lowWheelCanonicalPhysicalStateSet.mp
      (mem_lowWheelCanonicalDowncrossPart.mp hdown).1
  have hkPrime : k.Prime := by
    rw [hq]
    exact hgeom.1
  have hkNot : ¬ k ∣ c := by
    rw [hq]
    exact hgeom.2.1
  have hfaces : ∀ q ∈ t, q.Prime ∧ q < k := by
    intro q hqt
    have hqPrime := prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hqt)
    have hqLt := lowWheelCanonicalDowncrossOriented_facePrime_lt_pivot ht hx hqt
    refine ⟨hqPrime, ?_⟩
    rw [hq]
    exact hqLt
  have hroughPivot := lowWheelCanonicalDowncrossOriented_cofactor_roughAbove hx
  have hrough : RoughAbove k c := by
    rw [hq]
    exact hroughPivot
  exact ⟨hkPrime, (Finset.mem_Ico.mp hphys.1).1, hphys.2.2.1,
    hkNot, hfaces, hrough⟩

/-- Hence the finite root carrier is literally the set of static ordered cuts
whose lifetime contains the current root. -/
theorem mem_orderedEulerCutCarrier_iff_shape_lifetime
    {R : ℕ} {y : OrderedEulerCutTaggedState} :
    y ∈ orderedEulerCutCarrier R ↔
      OrderedEulerCutShape y ∧
        orderedEulerCutBirthRoot y ≤ R ∧ R < orderedEulerCutDeathRoot y := by
  constructor
  · intro hy
    have hshape := orderedEulerCutShape_of_mem_carrier hy
    have hocc := mem_orderedEulerCutCarrier.mp hy
    exact ⟨hshape, (orderedEulerCutOccursAt_iff_lifetime hshape).1 hocc⟩
  · rintro ⟨hshape, hlife⟩
    apply mem_orderedEulerCutCarrier.mpr
    exact (orderedEulerCutOccursAt_iff_lifetime hshape).2 hlife

/-- **Simultaneous tagged projection of the oriented ledger.** The original
oriented boundary is exactly the signed sum over the common ordered-cut carrier.
The equality is before every norm and keeps the same atoms used by the lifetime,
Möbius-parent, and ancestry projections above. -/
theorem lowWheelCanonicalDowncrossOrientedLedger_eq_sum_orderedEulerCutWeights
    (R : ℕ) :
    lowWheelCanonicalDowncrossOrientedLedger R =
      ∑ y ∈ orderedEulerCutCarrier R, orderedEulerCutWeight y := by
  unfold lowWheelCanonicalDowncrossOrientedLedger orderedEulerCutCarrier
    orderedEulerCutWeight orderedEulerCutHighCofactor
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t _ht
  simpa only [Prod.fst, Prod.snd] using
    (sum_orientedPart_eq_sum_stateAmbient_indicator R t).symm

end RHLean.Proof
