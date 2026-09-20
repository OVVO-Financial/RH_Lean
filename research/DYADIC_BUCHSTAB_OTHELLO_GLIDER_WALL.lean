import Mathlib
import «research.DYADIC_LONG_RANGE_TETHER_AUDIT»
import RHLean.Proof.PrefixCarrierOthelloWalls
import RHLean.Proof.VanishingTransitionRelevanceBase
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Proof.RecursivePrimeReplacement
import RHLean.Proof.ReplacementFibreOrientationSplit
import RHLean.Analysis.SquareRootPostCrossingRenewal
import RHLean.Proof.TerminalMertensReduction
import RHLean.Proof.PrimeWheelRoughSeatCorrelation
import RHLean.Arithmetic.MobiusFiniteDifferenceIdentification
import RHLean.Proof.SquareRootLowPrimeBornSquareBoundary
import RHLean.Proof.CanonicalRoughAdaptiveWeightedIteration

/-!
# Dyadic Buchstab/Othello splice: the joint packet is already an escape wall

The prime-two Othello involution acts on the complete prefix (0,B].
Every interior two-cycle cancels with opposite Mobius sign, every fixed
square-hit carries zero Mobius mass, and the only surviving cutoff wall is

    B / 2 < n <= B, n odd.

That wall is exactly dyadicCofactorBoundary B.

Thus the top odd dyadic annulus introduced by the smooth/high joint packet is
not a fresh bulk region whose whole interior still has to be cancelled: it is
already the prime-two Othello escape wall left after the complete prefix has
played out.

The wall can then be played again with any finite list of distinguished primes.
The signed mass remains unchanged while every new interior two-cycle cancels.
The surviving iteratedPrimeEscapePart is the exact finite glider boundary.

This file also records the sign-correct Buchstab splice. The ordered replication
response has the paper transport orientation, hence it enters with a minus sign
against the native high-source orientation.

No norm, cardinality estimate, asymptotic input, or RH hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-! ## Prime two turns the whole prefix into the odd dyadic wall -/

/-- The lower anchor wall is empty for the full prefix (0,B]. -/
theorem primeTwoAnchorWall_zero (B : ℕ) :
    primeCarrierAnchorWall 2 0 B = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  rcases mem_primeCarrierAnchorWall.mp hn with
    ⟨hnIoc, _hdvd, _hsq, hle⟩
  have hnBounds := Finset.mem_Ioc.mp hnIoc
  norm_num at hle
  omega

/-- The prime-two cutoff wall of (0,B] is literally the odd dyadic annulus. -/
theorem primeTwoCutoffWall_eq_dyadicCofactorBoundary (B : ℕ) :
    primeCarrierCutoffWall 2 0 B = dyadicCofactorBoundary B := by
  ext n
  constructor
  · intro hn
    rcases mem_primeCarrierCutoffWall.mp hn with
      ⟨hnIoc, h2n, hcut⟩
    have hnBounds := Finset.mem_Ioc.mp hnIoc
    have hodd : Odd n := by
      rcases Nat.even_or_odd n with heven | hodd
      · exfalso
        apply h2n
        rcases heven with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        omega
      · exact hodd
    exact mem_dyadicCofactorBoundary.mpr
      ⟨by omega, hnBounds.2, hodd, by simpa [Nat.mul_comm] using hcut⟩
  · intro hn
    rcases mem_dyadicCofactorBoundary.mp hn with
      ⟨hn1, hnB, hodd, hcut⟩
    have h2n : ¬ 2 ∣ n := by
      intro hd
      rcases hd with ⟨k, hk⟩
      rcases hodd with ⟨j, hj⟩
      omega
    exact mem_primeCarrierCutoffWall.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, hnB⟩, h2n,
        by simpa [Nat.mul_comm] using hcut⟩

/-- Prime-two glider set: the entire escape part of (0,B] is exactly the odd
dyadic annulus. -/
theorem primeEscapePart_two_Ioc_zero_eq_dyadicCofactorBoundary (B : ℕ) :
    primeEscapePart 2 (Finset.Ioc 0 B) = dyadicCofactorBoundary B := by
  rw [primeEscapePart_Ioc_eq_walls Nat.prime_two 0 B,
    primeTwoAnchorWall_zero, Finset.empty_union,
    primeTwoCutoffWall_eq_dyadicCofactorBoundary]

/-- Integer form of the Game-of-Life statement: the whole prefix interior has
cancelled and only the prime-two escape wall carries the signed mass. -/
theorem sum_moebius_Ioc_zero_eq_dyadicEscapeWall (B : ℕ) :
    (∑ n ∈ Finset.Ioc 0 B, μ n) =
      ∑ n ∈ dyadicCofactorBoundary B, μ n := by
  rw [sum_moebius_eq_sum_primeEscapePart Nat.prime_two (Finset.Ioc 0 B),
    primeEscapePart_two_Ioc_zero_eq_dyadicCofactorBoundary]

/-! ## Replaying the game on the surviving wall -/

/-- Complex-scalar version of the iterated global Othello theorem. -/
theorem sum_canonicalMoebiusWeight_eq_sum_iteratedPrimeEscapePart
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime) (S : Finset ℕ) :
    (∑ n ∈ S, canonicalMoebiusWeight n) =
      ∑ n ∈ iteratedPrimeEscapePart ps S, canonicalMoebiusWeight n := by
  have h := sum_moebius_eq_sum_iteratedPrimeEscapePart ps hps S
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  simpa [canonicalMoebiusWeight] using hc

/-- The iterated survivor/glider boundary obtained by replaying Othello on the
prime-two dyadic wall. -/
def dyadicJointGliderBoundary (ps : List ℕ) (B : ℕ) : Finset ℕ :=
  iteratedPrimeEscapePart ps (dyadicCofactorBoundary B)

/-- Exact glider-boundary theorem. The signed smooth/high joint packet at
boundary scale B is carried entirely by the iterated Othello boundary after any
finite list of prime peels. Every complementary interior two-cycle has already
cancelled before this equality is read. -/
theorem dyadicJointPacketAt_eq_iteratedGliderBoundaryMass
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime) (R B : ℕ) :
    dyadicJointPacketAt R B =
      ∑ n ∈ dyadicJointGliderBoundary ps B, canonicalMoebiusWeight n := by
  rw [dyadicJointPacketAt_eq_boundaryMass]
  unfold dyadicCofactorBoundaryMass dyadicJointGliderBoundary
  exact sum_canonicalMoebiusWeight_eq_sum_iteratedPrimeEscapePart
    ps hps (dyadicCofactorBoundary B)


/-! ## Subdoubling rigidity: every live atom is already a glider -/

/-- A squarefree atom on the strict dyadic wall has no odd-prime mate on the
same wall.  If p divides n once, dividing by p falls below B/2; if p does not
divide n, multiplying by p jumps above B.  A p-square fixed point is excluded
by squarefreeness. -/
theorem squarefree_dyadicAtom_toggle_not_mem
    {B p n : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hn : n ∈ dyadicCofactorBoundary B) (hsf : Squarefree n) :
    primeCarrierToggle p n ∉ dyadicCofactorBoundary B := by
  have hsq : ¬ p ^ 2 ∣ n := by
    simpa [pow_two] using
      (Nat.squarefree_iff_prime_squarefree.mp hsf p hp)
  rcases mem_dyadicCofactorBoundary.mp hn with
    ⟨hn1, hnB, _hnOdd, hB2n⟩
  by_cases hdvd : p ∣ n
  · rw [primeCarrierToggle_of_dvd hdvd hsq]
    intro hmate
    have hmateData := mem_dyadicCofactorBoundary.mp hmate
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hdvd
    have hle : 2 * (n / p) ≤ p * (n / p) :=
      Nat.mul_le_mul_right (n / p) hp.two_le
    rw [hmul] at hle
    omega
  · rw [primeCarrierToggle_of_not_dvd hdvd]
    intro hmate
    have hmateData := mem_dyadicCofactorBoundary.mp hmate
    have hlt : 2 * n < n * p := by
      have h :=
        Nat.mul_lt_mul_of_pos_left hp2 (by omega : 0 < n)
      simpa [Nat.mul_comm] using h
    omega

/-- The same escape statement on any subcarrier of the dyadic wall. -/
theorem squarefree_dyadicAtom_mem_escape_of_subset
    {B p n : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hp2 : 2 < p)
    (hS : S ⊆ dyadicCofactorBoundary B)
    (hn : n ∈ S) (hsf : Squarefree n) :
    n ∈ primeEscapePart p S := by
  refine mem_primeEscapePart.mpr ⟨hn, ?_⟩
  intro hmate
  exact squarefree_dyadicAtom_toggle_not_mem hp hp2 (hS hn) hsf (hS hmate)

/-- Every squarefree live atom survives every finite sequence of odd-prime
Othello peels.  Repeated fixed-prime pairing can remove square-hit zeroes from
the dyadic wall, but it cannot pair away any nonzero Mobius atom. -/
theorem squarefree_dyadicAtom_mem_iteratedEscape_of_subset
    (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime ∧ 2 < p)
    {B n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ dyadicCofactorBoundary B)
    (hn : n ∈ S) (hsf : Squarefree n) :
    n ∈ iteratedPrimeEscapePart ps S := by
  induction ps generalizing S with
  | nil =>
      simpa using hn
  | cons p ps ih =>
      have hpData : p.Prime ∧ 2 < p := hps p (by simp)
      have htail : ∀ q ∈ ps, q.Prime ∧ 2 < q := by
        intro q hq
        exact hps q (by simp [hq])
      have hfirst : n ∈ primeEscapePart p S :=
        squarefree_dyadicAtom_mem_escape_of_subset
          hpData.1 hpData.2 hS hn hsf
      exact ih htail
        ((primeEscapePart_subset p S).trans hS) hfirst

/-- In particular every squarefree atom of the original dyadic wall survives
the named glider boundary after any finite odd-prime peel. -/
theorem squarefree_dyadicAtom_mem_gliderBoundary
    (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime ∧ 2 < p)
    {B n : ℕ}
    (hn : n ∈ dyadicCofactorBoundary B) (hsf : Squarefree n) :
    n ∈ dyadicJointGliderBoundary ps B := by
  unfold dyadicJointGliderBoundary
  exact squarefree_dyadicAtom_mem_iteratedEscape_of_subset
    ps hps (Finset.Subset.refl _) hn hsf

/-- Cardinality guardrail: every squarefree live cell remains on the iterated
odd-prime glider boundary.  Hence a small-boundary proof cannot come merely from
replaying fixed-prime Othello on the same strict dyadic annulus. -/
theorem card_squarefreeDyadic_le_gliderBoundary
    (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime ∧ 2 < p)
    (B : ℕ) :
    ((dyadicCofactorBoundary B).filter Squarefree).card ≤
      (dyadicJointGliderBoundary ps B).card := by
  apply Finset.card_le_card
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hnB, hsf⟩
  exact squarefree_dyadicAtom_mem_gliderBoundary ps hps hnB hsf

/-- Top-endpoint specialization of the exact glider-boundary theorem. -/
theorem squareRootDyadicJointPacket_eq_iteratedGliderBoundaryMass
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime) (R : ℕ) :
    squareRootDyadicJointPacket R =
      ∑ n ∈ dyadicJointGliderBoundary ps (squareRootEndpoint R),
        canonicalMoebiusWeight n := by
  rw [squareRootDyadicJointPacket_eq_at_top]
  exact dyadicJointPacketAt_eq_iteratedGliderBoundaryMass
    ps hps R (squareRootEndpoint R)

/-! ## The live glider wall is the odd squarefree part of replacement fibre one -/

/-- Nonzero Mobius atoms on the prime-two escape wall.  This is the literal
live-cell carrier; nonsquarefree wall sites have zero native weight. -/
def squareRootDyadicLiveGliderSet (R : ℕ) : Finset ℕ :=
  (dyadicCofactorBoundary (squareRootEndpoint R)).filter Squarefree

/-- Every point of a strict dyadic boundary has reciprocal quotient exactly one.
This is the exact reason the top glider wall belongs to replacement fibre
\`z = 1\`. -/
theorem dyadicCofactorBoundary_div_eq_one
    {B n : ℕ} (hn : n ∈ dyadicCofactorBoundary B) :
    B / n = 1 := by
  rcases mem_dyadicCofactorBoundary.mp hn with
    ⟨hn1, hnB, _hodd, hB2n⟩
  have hnpos : 0 < n := by omega
  have hlo : 1 ≤ B / n :=
    (Nat.one_le_div_iff hnpos).2 hnB
  have hhi : B / n < 2 :=
    (Nat.div_lt_iff_lt_mul hnpos).2
      (by simpa [Nat.mul_comm] using hB2n)
  omega

/-- Every live top-wall atom lies in the replacement fibre \`z = 1\`.
The converse is intentionally not stated: the full reciprocal fibre also
contains even atoms already removed by the prime-two Othello pairing. -/
theorem squareRootDyadicLiveGlider_mem_replacementFibre_one
    {R n : ℕ} (hn : n ∈ squareRootDyadicLiveGliderSet R) :
    n ∈ Finset.Icc
      (squareRootReplacementFibreLower R 1)
      (squareRootReplacementFibreUpper R 1) := by
  rcases Finset.mem_filter.mp hn with ⟨hnWall, _hsf⟩
  have hn1 : 1 ≤ n :=
    (mem_dyadicCofactorBoundary.mp hnWall).1
  have hdiv : squareRootEndpoint R / n = 1 :=
    dyadicCofactorBoundary_div_eq_one hnWall
  exact
    (squareRootEndpoint_div_eq_iff_mem_replacementFibre
      (R := R) (n := n) (z := 1) hn1 (by norm_num)).1 hdiv

/-- The complete prime-two wall mass is already carried by its squarefree live
cells; nonsquarefree sites vanish rather than needing an estimate. -/
theorem dyadicCofactorBoundaryMass_eq_liveGliderMass (R : ℕ) :
    dyadicCofactorBoundaryMass (squareRootEndpoint R) =
      ∑ n ∈ squareRootDyadicLiveGliderSet R,
        canonicalMoebiusWeight n := by
  unfold dyadicCofactorBoundaryMass squareRootDyadicLiveGliderSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hsf : Squarefree n
  · simp [hsf]
  · have hzero : (μ n : ℤ) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
    simp [hsf, canonicalMoebiusWeight, hzero]

/-- The top joint packet is literally the signed mass of the live glider cells. -/
theorem squareRootDyadicJointPacket_eq_liveGliderMass (R : ℕ) :
    squareRootDyadicJointPacket R =
      ∑ n ∈ squareRootDyadicLiveGliderSet R,
        canonicalMoebiusWeight n := by
  rw [squareRootDyadicJointPacket_eq_annulusMass,
    dyadicCofactorBoundaryMass_eq_liveGliderMass]

/-- **Exact glider-to-replacement pushforward.**  The whole signed live wall,
not its atoms separately, is the completed-square Mertens value and hence the
existing lower-triangular recursive replacement row.  All replacement
coefficients remain recombined before any norm. -/
theorem squareRootLiveGliderMass_eq_recombinedReplacementRow
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ squareRootDyadicLiveGliderSet R,
        canonicalMoebiusWeight n) =
      ∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          mertensSummatory y := by
  calc
    (∑ n ∈ squareRootDyadicLiveGliderSet R,
        canonicalMoebiusWeight n) =
      squareRootDyadicJointPacket R :=
        (squareRootDyadicJointPacket_eq_liveGliderMass R).symm
    _ = dyadicJointPacketAt R (squareRootEndpoint R) :=
      squareRootDyadicJointPacket_eq_at_top R
    _ = mertensSummatory (squareRootEndpoint R) :=
      dyadicJointPacketAt_eq_mertensSummatory R (squareRootEndpoint R)
    _ = ∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          mertensSummatory y :=
      mertensEndpoint_eq_recombinedReplacementRow R hR

/-- The same replacement-row pushforward read from any Othello glider boundary.
The Othello chronology changes the carrier, but not the signed mass. -/
theorem iteratedGliderBoundaryMass_eq_recombinedReplacementRow
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime)
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ dyadicJointGliderBoundary ps (squareRootEndpoint R),
        canonicalMoebiusWeight n) =
      ∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          mertensSummatory y := by
  calc
    (∑ n ∈ dyadicJointGliderBoundary ps (squareRootEndpoint R),
        canonicalMoebiusWeight n) =
      squareRootDyadicJointPacket R :=
        (squareRootDyadicJointPacket_eq_iteratedGliderBoundaryMass
          ps hps R).symm
    _ = ∑ y ∈ Finset.range R,
        squareRootReplacementCoefficient R y *
          mertensSummatory y :=
      (squareRootDyadicJointPacket_eq_liveGliderMass R).trans
        (squareRootLiveGliderMass_eq_recombinedReplacementRow R hR)

/-- **Prime-swap sign guardrail.**  Replacing one fresh prime by another while
holding the cofactor fixed preserves the Mobius sign: both products are
\`-mu(c)\`.  Therefore replacement fibres are not an atomwise sign-reversing
matching between low-prime and high-prime multiples of the same cofactor. -/
theorem canonicalMoebiusWeight_primeSwap_eq_of_rough
    {c p q : ℕ}
    (hc : 0 < c)
    (hp : p.Prime) (hq : q.Prime)
    (hpFresh : canonicalLargestPrimeFactor c < p)
    (hqFresh : canonicalLargestPrimeFactor c < q) :
    canonicalMoebiusWeight (c * p) =
      canonicalMoebiusWeight (c * q) := by
  rw [canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hc hp hpFresh,
    canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hc hq hqFresh]

/-- Kernel-locked size of the first production live-glider wall. -/
theorem squareRootDyadicLiveGliderSet_card_56 :
    (squareRootDyadicLiveGliderSet 56).card = 634 := by
  native_decide

/-! ## Prime-face extraction and the complete Type-II glider splice -/

/-- The admitted packet is removed from the whole signed glider mass.  This is
the exact interface to the post-crossing renewal, not a pointwise prime swap.
The smooth carrier is already included in the coupled tail. -/
theorem squareRootLiveGliderMass_sub_partial_eq_coupledTail
    (R K j : ℕ) (hR : 3 ≤ R) :
    (∑ n ∈ squareRootDyadicLiveGliderSet R, canonicalMoebiusWeight n) -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      squareRootPostCrossingCoupledTail R K j := by
  rw [← squareRootDyadicJointPacket_eq_liveGliderMass,
    squareRootDyadicJointPacket_eq_at_top,
    dyadicJointPacketAt_eq_mertensSummatory,
    postCrossingCoupledTail_eq_mertens_sub_partial R K j hR]

/-- **Glider-to-Type-II splice.**  Prime extraction, composite-root/smooth
recombination, the predecessor endpoint, and all strict quotient descendants
are retained in one signed row.  At completed shallow layers the named prime
diagonal is exactly zero; at the crossing it is the unfilled-seat remainder.
No estimate is supplied by this equality. -/
theorem squareRootLiveGliderMass_sub_partial_eq_typeIIRow
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    (∑ n ∈ squareRootDyadicLiveGliderSet R, canonicalMoebiusWeight n) -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      ∑ y ∈ Finset.Icc 1 (R - 1),
        ((if y = R - 1 then 1 else 0) +
            squareRootPostCrossingPrimeDiagonal R K j y +
            replacementFibreTypeIIWindowMass R y +
            squareRootOrientedStrictDescendantTransform R y) *
          mertensSummatory y := by
  rw [squareRootLiveGliderMass_sub_partial_eq_coupledTail R K j hR,
    squareRootPostCrossingCoupledTail_eq_primeCancelledRow R K j hR hK hKR]
  apply Finset.sum_congr rfl
  intro y hy
  rcases Finset.mem_Icc.mp hy with ⟨hy1, hyR⟩
  have hsplice := replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
    R y (by omega) hy1 (by omega)
  congr 1
  unfold squareRootPostCrossingPrimeCancelledCoefficient
  linear_combination hsplice

/-- **Canonical reciprocal Type-II glider row.**  The diagonal starts at
cofactor two, while strict descendants still contain their cofactor-one faces.
Consequently the prime-face cancellation must not be applied a second time
inside the descendants.  All cross-scale interference remains signed. -/
theorem squareRootLiveGliderMass_sub_partial_eq_canonicalRoughTypeIIRow
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    (∑ n ∈ squareRootDyadicLiveGliderSet R, canonicalMoebiusWeight n) -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      ∑ y ∈ Finset.Icc 1 (R - 1),
        ((if y = R - 1 then 1 else 0) +
            squareRootPostCrossingPrimeDiagonal R K j y +
            replacementFibreCanonicalRoughReciprocalMass R y +
            squareRootCanonicalRoughStrictDescendantTransform R y) *
          mertensSummatory y := by
  rw [squareRootLiveGliderMass_sub_partial_eq_typeIIRow R K j hR hK hKR]
  simp_rw [replacementFibreTypeIIWindowMass_eq_canonicalRoughReciprocalMass
    R _ (by omega),
    squareRootOrientedStrictDescendantTransform_eq_canonicalRough R _ (by omega)]

/-- The full first reciprocal fibre includes even states: its mass is nine,
whereas the odd live-glider wall has mass six. -/
theorem squareRootReplacementTailMoebiusCoefficient_56_one :
    squareRootReplacementTailMoebiusCoefficient 56 1 = 9 := by
  have h : (∑ n ∈ Finset.Icc 56 3135,
      if 3135 / n = 1 then (μ n : ℤ) else 0) = 9 := by native_decide
  change (∑ n ∈ Finset.Icc 56 3135,
    if 3135 / n = 1 then ((μ n : ℤ) : ℂ) else 0) = 9
  exact_mod_cast h

/-- Exact prime-face extraction at the first production root. -/
theorem replacementFibrePrimeFaceMass_56_one :
    replacementFibrePrimeFaceMass 56 1 = -198 := by
  have h : squareRootReciprocalPrimeLayerCard 56 1 = 198 := by native_decide
  rw [replacementFibrePrimeFaceMass_eq_neg_reciprocalPrimeLayerCard
    56 1 (by norm_num) (by norm_num) (by norm_num), h]
  norm_num

/-- The prime-cancelled composite diagonal is 207, not the glider mass six.
This finite value does not rule out a bound on the complete signed row; it
records the multiplicity that any such argument must retain and cancel. -/
theorem replacementFibreTypeIIWindowMass_56_one :
    replacementFibreTypeIIWindowMass 56 1 = 207 := by
  have hsplit :=
    squareRootReplacementTailMoebiusCoefficient_eq_prime_add_composite_add_smooth
      56 1 (by norm_num)
  have hsplice := replacementFibreCompositeRoot_add_smooth_eq_typeIIWindowMass
    56 1 (by norm_num) (by norm_num) (by norm_num)
  rw [squareRootReplacementTailMoebiusCoefficient_56_one,
    replacementFibrePrimeFaceMass_56_one] at hsplit
  linear_combination -hsplit - hsplice

/-- Reindexing as a canonical rough reciprocal mass preserves the same 207;
the coordinate change does not itself reduce its amplitude. -/
theorem replacementFibreCanonicalRoughReciprocalMass_56_one :
    replacementFibreCanonicalRoughReciprocalMass 56 1 = 207 := by
  rw [← replacementFibreTypeIIWindowMass_eq_canonicalRoughReciprocalMass
    56 1 (by norm_num), replacementFibreTypeIIWindowMass_56_one]

/-- The actual shallow crossing admits two seats at depth eighteen and leaves
zero partial-packet overshoot. -/
theorem squareRootCrossingLayerPartialPacketInt_56_18_two :
    squareRootCrossingLayerPartialPacketInt 56 18 2 = 0 := by
  native_decide

/-- At that crossing the complete Type-II/descendant tail still has mass six.
The prime-face cancellation is exact without making the entire tail vanish. -/
theorem squareRootPostCrossingCoupledTail_56_18_two :
    squareRootPostCrossingCoupledTail 56 18 2 = 6 := by
  rw [postCrossingCoupledTail_eq_mertens_sub_partial 56 18 2 (by norm_num),
    squareRootCrossingLayerPartialPacketInt_56_18_two]
  simp only [Int.cast_zero, sub_zero]
  change mertensSummatory 3135 = 6
  have h : squareRootMertensInt 3135 = 6 := by native_decide
  rw [← squareRootMertensInt_cast_complex, h]
  norm_num

/-! ## What the complete cross-scale Fubini collapse actually leaves -/

/-- Swapping the reciprocal-depth and cofactor sums in the unweighted Type-II
diagonal produces signed prime-partner counts.  This diagonal sum is not the
complete post-crossing row: the latter also has Mertens weights, strict
descendants, and the explicit packet baseline. -/
theorem sum_canonicalRoughTypeII_eq_neg_compositePartnerMass (R : ℕ) :
    (∑ y ∈ Finset.Icc 1 (R - 1),
        replacementFibreCanonicalRoughReciprocalMass R y) =
      -∑ c ∈ Finset.Icc 2 (squareRootEndpoint R),
        canonicalMoebiusWeight c *
          squareRootCanonicalRoughPrimePartnerCount R c := by
  unfold replacementFibreCanonicalRoughReciprocalMass
    squareRootCanonicalRoughPrimePartnerCount
    squareRootCanonicalRoughPrimeMultiplicity
  simp_rw [Finset.mul_sum]
  simp_rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

/-- **Complete signed glider Fubini.**  The unit Mobius renewal sends each
positive quotient depth to one, not zero.  Consequently the intact cofactor
response collapses to its fresh-prime partner count; the signed correlation
over cofactors remains after all lower Mertens states have telescoped. -/
theorem squareRootLiveGliderMass_sub_partial_eq_baseline_sub_partnerMass
    (R K j : ℕ) (hR : 3 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    (∑ n ∈ squareRootDyadicLiveGliderSet R, canonicalMoebiusWeight n) -
        ((squareRootCrossingLayerPartialPacketInt R K j : ℤ) : ℂ) =
      squareRootPostCrossingCanonicalBaseline R K j -
        ∑ c ∈ Finset.Icc 1 (squareRootEndpoint R),
          canonicalMoebiusWeight c *
            squareRootCanonicalRoughPrimePartnerCount R c := by
  rw [squareRootLiveGliderMass_sub_partial_eq_coupledTail R K j hR,
    squareRootPostCrossingCoupledTail_eq_baseline_sub_correlation
      R K j hR hK hKR,
    squareRootCanonicalRoughCorrelation_eq_weighted_primePartnerCount
      R (by omega)]

/-- A composite cofactor survives the complete, un-normed renewal collapse.
At R=56, c=6 has 94 fresh prime partners.  The full divisor sum of six is zero,
but the cofactor response is a prime-partner count, not that divisor sum. -/
theorem squareRootCanonicalRoughCofactorResponse_56_six :
    squareRootCanonicalRoughCofactorResponse 56 6 = 94 := by
  have hgt : 1 < (6 : ℕ) := by norm_num
  have hlpfPrime : (canonicalLargestPrimeFactor 6).Prime :=
    canonicalLargestPrimeFactor_prime hgt
  have hlpfDvd : canonicalLargestPrimeFactor 6 ∣ 6 :=
    canonicalLargestPrimeFactor_dvd hgt
  have hthreeLe : 3 ≤ canonicalLargestPrimeFactor 6 :=
    CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
      hgt (by norm_num) (by norm_num)
  have hlpf : canonicalLargestPrimeFactor 6 = 3 := by
    have hprodDvd : canonicalLargestPrimeFactor 6 ∣ 2 * 3 := by
      simpa using hlpfDvd
    rcases hlpfPrime.dvd_mul.mp hprodDvd with htwo | hthree
    · have heq : canonicalLargestPrimeFactor 6 = 2 :=
        (Nat.prime_dvd_prime_iff_eq hlpfPrime (by norm_num)).mp htwo
      rw [heq] at hthreeLe
      omega
    · exact
        (Nat.prime_dvd_prime_iff_eq hlpfPrime (by norm_num)).mp hthree
  have hset :
      squareRootCanonicalRoughPrimePartnerSet 56 6 =
        (Finset.Icc 10 522).filter Nat.Prime := by
    ext q
    rw [mem_squareRootCanonicalRoughPrimePartnerSet_iff
      (R := 56) (c := 6) (q := q) (by norm_num) (by norm_num)]
    rw [hlpf]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hqPrime, h3q, hroot, hupper⟩
      have hupper' : 6 * q ≤ 3135 := by
        simpa [squareRootEndpoint] using hupper
      exact ⟨⟨by omega, by omega⟩, hqPrime⟩
    · rintro ⟨⟨h10, h522⟩, hqPrime⟩
      refine ⟨hqPrime, by omega, by omega, ?_⟩
      norm_num [squareRootEndpoint]
      omega
  have hcard : ((Finset.Icc 10 522).filter Nat.Prime).card = 94 := by
    native_decide
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount
    56 6 (by norm_num),
    squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card,
    hset, hcard]
  norm_num

/-! ## Fresh-prime cutoff shell: exact masked-fibre Stokes identity -/

/-- Signed divisor flux whose fresh-prime edge crosses the strict root mask.
Every divisor pair \`d <-> p*d\` that lies wholly on one side of the mask
cancels; only edges with \`d < R <= p*d\` remain. -/
def squareRootReplacementCrossingShell (R c p : ℕ) : ℂ :=
  ∑ d ∈ c.divisors,
    if d < R ∧ R ≤ p * d then (((μ d : ℤ) : ℂ)) else 0

/-- Divisors after adjoining a prime split into the old divisor family and its
prime-multiple copy.  Freshness is not needed for the set equality, only for
the disjoint signed cancellation below. -/
private theorem divisors_mul_prime_eq_union_image
    {c p : ℕ} (hp : p.Prime) :
    (c * p).divisors =
      c.divisors ∪ c.divisors.image (fun d => p * d) := by
  classical
  rw [Nat.mul_comm c p, Nat.divisors_mul, hp.divisors]
  ext n
  constructor
  · intro hn
    rcases Finset.mem_mul.mp hn with ⟨a, ha, b, hb, hab⟩
    have ha' : a = 1 ∨ a = p := by
      simpa using ha
    rcases ha' with rfl | rfl
    · have hbn : b = n := by simpa using hab
      exact Finset.mem_union.mpr (Or.inl (hbn ▸ hb))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨b, hb, hab⟩))
  · intro hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact Finset.mem_mul.mpr ⟨1, by simp, n, hn, by simp⟩
    · rcases Finset.mem_image.mp hn with ⟨d, hd, hdn⟩
      exact Finset.mem_mul.mpr ⟨p, by simp, d, hd, hdn⟩

/-- Freshness makes the old divisor family disjoint from its prime-multiple
copy. -/
private theorem disjoint_divisors_mul_freshPrime
    {c p : ℕ} (hfresh : ¬ p ∣ c) :
    Disjoint c.divisors
      (c.divisors.image (fun d => p * d)) := by
  classical
  rw [Finset.disjoint_left]
  intro n hnD hnImage
  rcases Finset.mem_image.mp hnImage with ⟨d, hdD, hdn⟩
  have hpdD : p * d ∣ c := by
    apply Nat.dvd_of_mem_divisors
    rw [hdn]
    exact hnD
  apply hfresh
  exact dvd_trans ⟨d, rfl⟩ hpdD

/-- **Exact fresh-prime crossing-shell identity.**  A fresh prime flips the
Mobius sign on its divisor-copy.  All pairs admitted on both sides of the
strict cutoff cancel pointwise, and all pairs excluded on both sides contribute
zero.  The truncated replacement kernel is therefore exactly the signed flux
of divisor edges crossing \`d < R <= p*d\`. -/
theorem squareRootReplacementKernel_mul_freshPrime_eq_crossingShell
    {R c p : ℕ}
    (_hc : 0 < c)
    (hp : p.Prime)
    (hfresh : ¬ p ∣ c) :
    squareRootReplacementKernel R (c * p) =
      squareRootReplacementCrossingShell R c p := by
  classical
  have hcop : Nat.Coprime p c := (hp.coprime_iff_not_dvd).2 hfresh
  unfold squareRootReplacementKernel
  rw [divisors_mul_prime_eq_union_image hp]
  rw [Finset.sum_union (disjoint_divisors_mul_freshPrime hfresh)]
  have hinj : Set.InjOn (fun d : ℕ => p * d) c.divisors := by
    intro a _ha b _hb hab
    exact Nat.mul_left_cancel hp.pos hab
  rw [Finset.sum_image hinj]
  unfold squareRootReplacementCrossingShell squareRootReplacementSeed
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hddvd : d ∣ c := Nat.dvd_of_mem_divisors hd
  have hcopd : Nat.Coprime p d := hcop.of_dvd_right hddvd
  have hmu : μ (p * d) = -μ d := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopd]
    rw [ArithmeticFunction.moebius_apply_prime hp]
    ring
  have hdp : d ≤ p * d := by
    simpa using Nat.mul_le_mul_right d hp.one_le
  by_cases hdR : d < R
  · by_cases hpdR : p * d < R
    · have hnot : ¬ R ≤ p * d := Nat.not_le_of_gt hpdR
      simp [hdR, hpdR, hnot, hmu]
    · have hRpd : R ≤ p * d := Nat.le_of_not_gt hpdR
      simp [hdR, hpdR, hRpd]
  · have hRd : R ≤ d := Nat.le_of_not_gt hdR
    have hRpd : R ≤ p * d := hRd.trans hdp
    have hnot : ¬ p * d < R := Nat.not_lt_of_ge hRpd
    simp [hdR, hnot, hRpd]

/-- Every product of two distinct primes below R whose product reaches R has
truncated replacement kernel -1.  The crossing-shell form shows exactly why:
the unit divisor stays below the mask after the q-step, while the p-divisor
crosses it and contributes mu(p) = -1. -/
theorem squareRootReplacementKernel_of_distinct_low_primes
    {R p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpR : p < R) (hqR : q < R) (hprod : R ≤ p * q) :
    squareRootReplacementKernel R (p * q) = -1 := by
  have hqFresh : ¬ q ∣ p := by
    intro hqp
    rcases hp.eq_one_or_self_of_dvd q hqp with hq1 | hqpEq
    · exact hq.ne_one hq1
    · exact hpq hqpEq.symm
  rw [squareRootReplacementKernel_mul_freshPrime_eq_crossingShell
    (c := p) (p := q) hp.pos hq hqFresh]
  have h1R : 1 < R := hp.one_lt.trans hpR
  have hqNot : ¬ R ≤ q := by omega
  have hqpCross : R ≤ q * p := by
    simpa [Nat.mul_comm] using hprod
  simp [squareRootReplacementCrossingShell, hp.divisors, h1R, hpR,
    hqNot, hqpCross, ArithmeticFunction.moebius_apply_prime hp]

/-- An explicit squarefree composite well below X=3135 retains a nonzero
truncated divisor sum, although its complete divisor sum vanishes. -/
theorem squareRootReplacementKernel_56_899 :
    squareRootReplacementKernel 56 899 = -1 := by
  exact squareRootReplacementKernel_of_distinct_low_primes
    (p := 29) (q := 31) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The production counterexample is literally one crossing-shell atom:
\`d = 29\` crosses the \`R = 56\` mask under the fresh prime \`31\`. -/
theorem squareRootReplacementCrossingShell_56_29_31 :
    squareRootReplacementCrossingShell 56 29 31 = -1 := by
  rw [← squareRootReplacementKernel_mul_freshPrime_eq_crossingShell
    (c := 29) (p := 31) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [squareRootReplacementKernel_56_899]


/-! ## Operator and adaptive-carrier handoff -/


/-- Positive-support indicator used to identify the truncated wheel kernel with
the production finite-difference operator without importing another research
module. -/
def squareRootReplacementPositiveIndicator (y : ℕ) : ℤ :=
  if y = 0 then 0 else 1

/-- The wheel cutoff kernel is the canonical finite-difference operator applied
to the positive-support indicator. -/
theorem primeWheelTruncatedMoebiusKernel_eq_replacementFiniteDifferenceIndicator
    (S : Finset ℕ) (X : ℕ) :
    primeWheelTruncatedMoebiusKernel S X =
      finiteDifferenceOperator S squareRootReplacementPositiveIndicator X := by
  classical
  rw [finiteDifferenceOperator_apply]
  unfold primeWheelTruncatedMoebiusKernel
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  by_cases hdX : d ≤ X
  · have hq1 : 1 ≤ X / d := (Nat.one_le_div_iff hdpos).2 hdX
    have hq0 : X / d ≠ 0 := by omega
    simp [squareRootReplacementPositiveIndicator, hdX, hq0]
  · have hXd : X < d := Nat.lt_of_not_ge hdX
    have hq0 : X / d = 0 := Nat.div_eq_of_lt hXd
    simp [squareRootReplacementPositiveIndicator, hdX, hq0]

/-- On a squarefree wheel product, the root-truncated replacement kernel is
literally the ordinary wheel cutoff kernel at R - 1.  This is only a
coordinate identification; no cancellation or estimate is added here. -/
theorem squareRootReplacementKernel_primorial_eq_truncatedWheelKernel
    (S : Finset ℕ) (R : ℕ) (hR : 1 ≤ R) :
    squareRootReplacementKernel R (RHLean.Arithmetic.primorial S) =
      ((primeWheelTruncatedMoebiusKernel S (R - 1) : ℤ) : ℂ) := by
  unfold squareRootReplacementKernel squareRootReplacementSeed
    primeWheelTruncatedMoebiusKernel
  push_cast
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdR : d < R
  · have hdPred : d ≤ R - 1 := by omega
    simp [hdR, hdPred]
  · have hdPred : ¬ d ≤ R - 1 := by omega
    simp [hdR, hdPred]

/-- Crossing shell = the fresh-prime finite-difference operator.  When the
parent is an old prime wheel, the exact masked-fibre flux is precisely the
canonical finite-difference operator after adjoining the fresh prime. -/
theorem squareRootReplacementCrossingShell_primorial_eq_finiteDifferenceOperator
    (S : Finset ℕ) (R p : ℕ)
    (hR : 1 ≤ R) (hp : p.Prime) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, q.Prime) :
    squareRootReplacementCrossingShell R (RHLean.Arithmetic.primorial S) p =
      (((finiteDifferenceOperator (insert p S)
          squareRootReplacementPositiveIndicator) (R - 1) : ℤ) : ℂ) := by
  have hcpos : 0 < RHLean.Arithmetic.primorial S := by
    unfold RHLean.Arithmetic.primorial
    exact Finset.prod_pos fun q hq => (hprime q hq).pos
  have hcop : Nat.Coprime p (RHLean.Arithmetic.primorial S) :=
    prime_coprime_primorial S p hp hpS hprime
  have hfresh : ¬ p ∣ RHLean.Arithmetic.primorial S :=
    (hp.coprime_iff_not_dvd).mp hcop
  rw [← squareRootReplacementKernel_mul_freshPrime_eq_crossingShell
    hcpos hp hfresh]
  have hprod : RHLean.Arithmetic.primorial S * p =
      RHLean.Arithmetic.primorial (insert p S) := by
    rw [primorial_insert S p hpS]
    exact Nat.mul_comm _ _
  rw [hprod,
    squareRootReplacementKernel_primorial_eq_truncatedWheelKernel
      (insert p S) R hR,
    primeWheelTruncatedMoebiusKernel_eq_replacementFiniteDifferenceIndicator]

/-- Expanded operator form of the same shell.  This is the exact fresh-prime
difference D_(S+p) = D_S - D_S after the p-shift. -/
theorem squareRootReplacementCrossingShell_primorial_eq_old_sub_shift
    (S : Finset ℕ) (R p : ℕ)
    (hR : 1 ≤ R) (hp : p.Prime) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, q.Prime) :
    squareRootReplacementCrossingShell R (RHLean.Arithmetic.primorial S) p =
      (((finiteDifferenceOperator S squareRootReplacementPositiveIndicator) (R - 1) -
        (finiteDifferenceOperator S
          (shift p squareRootReplacementPositiveIndicator)) (R - 1) : ℤ) : ℂ) := by
  rw [squareRootReplacementCrossingShell_primorial_eq_finiteDifferenceOperator
    S R p hR hp hpS hprime]
  have hins :=
    finiteDifferenceOperator_insert (R := ℤ)
      S p hp hpS hprime squareRootReplacementPositiveIndicator
  rw [hins]
  rfl


/-- **Presentation-free squarefree operator bridge.**  Every squarefree parent
is its own prime-factor wheel, so the crossing shell is the same canonical
finite-difference operator with no chosen primorial presentation.  In
particular, numerical wheels such as 210 are only regression instances. -/
theorem squareRootReplacementCrossingShell_squarefree_eq_finiteDifferenceOperator
    {R c p : ℕ}
    (hR : 1 ≤ R) (hsq : Squarefree c)
    (hp : p.Prime) (hfresh : ¬ p ∣ c) :
    squareRootReplacementCrossingShell R c p =
      (((finiteDifferenceOperator (insert p c.primeFactors)
          squareRootReplacementPositiveIndicator) (R - 1) : ℤ) : ℂ) := by
  have hprime : ∀ q ∈ c.primeFactors, q.Prime := by
    intro q hq
    exact (Nat.mem_primeFactors.mp hq).1
  have hpS : p ∉ c.primeFactors := by
    intro hpMem
    exact hfresh (Nat.mem_primeFactors.mp hpMem).2.1
  have hcWheel : RHLean.Arithmetic.primorial c.primeFactors = c := by
    simpa [RHLean.Arithmetic.primorial] using Nat.prod_primeFactors_of_squarefree hsq
  have h :=
    squareRootReplacementCrossingShell_primorial_eq_finiteDifferenceOperator
      c.primeFactors R p hR hp hpS hprime
  simpa [hcWheel] using h

/-- Presentation-free expanded insertion law for every squarefree parent. -/
theorem squareRootReplacementCrossingShell_squarefree_eq_old_sub_shift
    {R c p : ℕ}
    (hR : 1 ≤ R) (hsq : Squarefree c)
    (hp : p.Prime) (hfresh : ¬ p ∣ c) :
    squareRootReplacementCrossingShell R c p =
      (((finiteDifferenceOperator c.primeFactors
          squareRootReplacementPositiveIndicator) (R - 1) -
        (finiteDifferenceOperator c.primeFactors
          (shift p squareRootReplacementPositiveIndicator)) (R - 1) : ℤ) : ℂ) := by
  have hprime : ∀ q ∈ c.primeFactors, q.Prime := by
    intro q hq
    exact (Nat.mem_primeFactors.mp hq).1
  have hpS : p ∉ c.primeFactors := by
    intro hpMem
    exact hfresh (Nat.mem_primeFactors.mp hpMem).2.1
  have hcWheel : RHLean.Arithmetic.primorial c.primeFactors = c := by
    simpa [RHLean.Arithmetic.primorial] using Nat.prod_primeFactors_of_squarefree hsq
  have h :=
    squareRootReplacementCrossingShell_primorial_eq_old_sub_shift
      c.primeFactors R p hR hp hpS hprime
  simpa [hcWheel] using h

/-- Literal divisor-edge carrier of the crossing shell. -/
def squareRootReplacementCrossingShellCarrier
    (R c p : ℕ) : Finset ℕ :=
  c.divisors.filter fun d => d < R ∧ R ≤ p * d

@[simp] theorem mem_squareRootReplacementCrossingShellCarrier
    {R c p d : ℕ} :
    d ∈ squareRootReplacementCrossingShellCarrier R c p ↔
      d ∈ c.divisors ∧ d < R ∧ R ≤ p * d := by
  simp [squareRootReplacementCrossingShellCarrier, and_assoc]

/-- The crossing shell is exactly the signed Mobius mass of its Boolean edge
carrier. -/
theorem squareRootReplacementCrossingShell_eq_carrierMass
    (R c p : ℕ) :
    squareRootReplacementCrossingShell R c p =
      ∑ d ∈ squareRootReplacementCrossingShellCarrier R c p,
        (((μ d : ℤ) : ℂ)) := by
  unfold squareRootReplacementCrossingShell
    squareRootReplacementCrossingShellCarrier
  rw [← Finset.sum_filter]

/-- Divisor-shell atom -> canonical threshold-loss cell.  In the canonical
fresh orientation P+(c) < p, every admitted divisor edge d < R <= p*d has p
itself as a literal threshold-loss partner of d.  The physical endpoint
assumption on c*p is inherited by every divisor d|c. -/
theorem squareRootReplacementCrossingShellCarrier_selfPrime_mem_thresholdLoss
    {R c p d : ℕ}
    (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hupper : c * p ≤ squareRootEndpoint R)
    (hd : d ∈ squareRootReplacementCrossingShellCarrier R c p) :
    p ∈ squareRootCanonicalRoughFreshThresholdLossBoundary R d p := by
  rcases mem_squareRootReplacementCrossingShellCarrier.mp hd with
    ⟨hdDivs, _hdR, hcross⟩
  have hdc : d ∣ c := Nat.dvd_of_mem_divisors hdDivs
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hdDivs
  have hdle : d ≤ c := Nat.le_of_dvd hc hdc
  have hdrough : canonicalLargestPrimeFactor d < p := by
    by_cases hcOne : c = 1
    · subst c
      have hdEq : d = 1 := Nat.dvd_one.mp hdc
      subst d
      simpa [canonicalLargestPrimeFactor] using hp.one_lt
    · have hcGt : 1 < c := by omega
      exact (canonicalLargestPrimeFactor_le_of_dvd hdpos hcGt hdc).trans_lt
        hrough
  apply
    (mem_squareRootCanonicalRoughFreshThresholdLossBoundary_iff
      hR hdpos hp hdrough).2
  refine ⟨hp, hdrough, ?_, ?_, le_rfl⟩
  · simpa [Nat.mul_comm] using hcross
  · calc
      d * p ≤ c * p := Nat.mul_le_mul_right p hdle
      _ ≤ squareRootEndpoint R := hupper

/-- Crossing-shell atom -> four-corner chronology.  On a complete descending
prime prefix, an admitted shell divisor is a literal threshold-loss cell, while
the evolved child raw atom is already zero in both inherited coefficient
placements.  If a larger physical extension exists this is the existing
four-corner kill; if none exists the child rough response is already empty.
The surviving signed boundary ledger itself is deliberately not declared zero. -/
theorem squareRootReplacementCrossingShellCarrier_handoff_to_fourCorner
    {R c p d : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hupper : c * p ≤ squareRootEndpoint R)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs)
    (hd : d ∈ squareRootReplacementCrossingShellCarrier R c p) :
    p ∈ squareRootCanonicalRoughFreshThresholdLossBoundary R d p ∧
      let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs
        (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))
      a d * squareRootCanonicalRoughRawCorrelationSummand R (d * p) = 0 ∧
        a (d * p) *
          squareRootCanonicalRoughRawCorrelationSummand R (d * p) = 0 := by
  have hthreshold :=
    squareRootReplacementCrossingShellCarrier_selfPrime_mem_thresholdLoss
      hR hc hp hrough hupper hd
  refine ⟨hthreshold, ?_⟩
  rcases mem_squareRootReplacementCrossingShellCarrier.mp hd with
    ⟨hdDivs, _hdR, _hcross⟩
  have hdc : d ∣ c := Nat.dvd_of_mem_divisors hdDivs
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hdDivs
  have hdrough : canonicalLargestPrimeFactor d < p := by
    by_cases hcOne : c = 1
    · subst c
      have hdEq : d = 1 := Nat.dvd_one.mp hdc
      subst d
      simpa [canonicalLargestPrimeFactor] using hp.one_lt
    · have hcGt : 1 < c := by omega
      exact (canonicalLargestPrimeFactor_le_of_dvd hdpos hcGt hdc).trans_lt
        hrough
  exact evolvedRawCoefficient_mul_childRaw_eq_zero_of_completeDescendingPrefix
    qs hR hdpos hp hdrough hcomplete

/-! ## Sign-correct smooth/high Buchstab splice -/

/-- The ordered root-weighted replication response has paper transport sign,
which is the negative of the canonical high-source sign on the dyadic wall. -/
theorem orderedPrimeReplicationResponse_eq_neg_dyadicCanonicalHighSourceMass
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationResponse R =
      -dyadicCanonicalHighSourceMass R := by
  rw [orderedPrimeReplicationResponse_eq_transport R hR,
    squareRootTransportCofactorFirst_eq_neg_dyadicCanonicalHighSourceMass]

/-- Exact pre-norm Buchstab splice. Smooth mass and ordered replication response
must enter with opposite paper orientations. Their assembled value is the same
top dyadic joint packet from the previous layer. -/
theorem squareRoot_positive_add_born_sub_orderedResponse_eq_dyadicJointPacket
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootPositiveSmoothMass R + squareRootBornSmoothMass R -
        orderedPrimeReplicationResponse R =
      squareRootDyadicJointPacket R := by
  rw [orderedPrimeReplicationResponse_eq_transport R hR]
  exact squareRoot_positive_add_born_sub_transport_eq_dyadicJointPacket
    R (by omega)

/-- The sign-correct physical smooth/response amplitude can therefore be played
by any finite Othello prime list and read entirely on the resulting glider
boundary. -/
theorem squareRoot_positive_add_born_sub_orderedResponse_eq_gliderBoundaryMass
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime)
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootPositiveSmoothMass R + squareRootBornSmoothMass R -
        orderedPrimeReplicationResponse R =
      ∑ n ∈ dyadicJointGliderBoundary ps (squareRootEndpoint R),
        canonicalMoebiusWeight n := by
  rw [squareRoot_positive_add_born_sub_orderedResponse_eq_dyadicJointPacket
    R hR]
  exact squareRootDyadicJointPacket_eq_iteratedGliderBoundaryMass ps hps R

/-! ## The active middle is not an automatic zero -/

/-- Existing exact middle/top chronology restated as a guardrail for the glider
picture. The intermediate-prime residual is the negative full Mertens value, so
a theorem that it vanishes identically would be strictly too strong. -/
theorem squareRootActiveMiddleResidual_eq_neg_fullMertens
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleCancellationResidual R =
      -squarePrefixMertens (R - 1) :=
  squareRootMiddleCancellationResidual_eq_neg_mertens R hR

end RHLean.Proof
