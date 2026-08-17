import Mathlib
import RHLean.Analysis.SquareRootMatchedTransport

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

namespace BornSmoothAncestrySquareClockPushforward

open CanonicalGapAncestryBridge
open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open SquareRootBornSmoothAncestry

/-!
# Born-smooth ancestry at the square clock

This file identifies the original born-smooth square-prefix mass with the
integer-square-root pushforward of the concrete canonical ancestry flow.  It
then rewrites that pushforward in lower-scale transport-root coordinates.

Everything here is exact.  No logarithmic integral, prime number theorem,
prime-counting error split, norm, or analytic estimate is used.

The canonical ancestry universe starts with a distinguished prime, whereas the
original born-smooth sum also contains the Mobius unit `m = 1`.  We therefore
carry that single exact unit contribution explicitly and absorb it into the
`c = 1` root coefficient in the final lower-scale formula.
-/

/-- Nonunit born-smooth integers carrying nonzero Mobius weight.  Zero Mobius
weights are omitted because they contribute exactly zero to the original mass. -/
def bornSmoothNonunitSet (R : ℕ) : Finset ℕ :=
  ((cumulativeSquarePrefixSet (R - 1)).erase 1).filter fun m =>
    1 < m ∧
      canonicalLargestPrimeFactor m ≤ R ∧
      canonicalLargestPrimeFactor m ≤ canonicalCofactor m ∧
      μ m ≠ 0

/-- Active smooth ancestry sources at the native square clock, again with zero
weights removed harmlessly. -/
def activeSmoothSourceSet (R : ℕ) :
    Finset (SourceIndex (squareRootEndpoint R)) :=
  Finset.univ.filter fun s =>
    SmoothOriented s ∧
      sourceClock (squareRootEndpoint R) s ≤ R - 1 ∧
      sourceWeight s ≠ 0

private theorem pred_succ_eq_self {R : ℕ} (hR : 1 ≤ R) :
    R - 1 + 1 = R := by
  omega

private theorem bornSmoothNonunit_mem_prefix {R m : ℕ}
    (hm : m ∈ bornSmoothNonunitSet R) :
    m ∈ cumulativeSquarePrefixSet (R - 1) := by
  exact (Finset.mem_erase.mp (Finset.mem_filter.mp hm).1).1

private theorem bornSmoothNonunit_gt_one {R m : ℕ}
    (hm : m ∈ bornSmoothNonunitSet R) : 1 < m :=
  (Finset.mem_filter.mp hm).2.1

private theorem bornSmoothNonunit_lpf_le {R m : ℕ}
    (hm : m ∈ bornSmoothNonunitSet R) :
    canonicalLargestPrimeFactor m ≤ R :=
  (Finset.mem_filter.mp hm).2.2.1

private theorem bornSmoothNonunit_orientation {R m : ℕ}
    (hm : m ∈ bornSmoothNonunitSet R) :
    canonicalLargestPrimeFactor m ≤ canonicalCofactor m :=
  (Finset.mem_filter.mp hm).2.2.2.1

private theorem bornSmoothNonunit_moebius_ne {R m : ℕ}
    (hm : m ∈ bornSmoothNonunitSet R) : μ m ≠ 0 :=
  (Finset.mem_filter.mp hm).2.2.2.2

private theorem bornSmoothNonunit_squarefree {R m : ℕ}
    (hm : m ∈ bornSmoothNonunitSet R) : Squarefree m :=
  ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
    (bornSmoothNonunit_moebius_ne hm)

private theorem prefix_mem_le_squareRootEndpoint {R m : ℕ}
    (hR : 1 ≤ R) (hm : m ∈ cumulativeSquarePrefixSet (R - 1)) :
    m ≤ squareRootEndpoint R := by
  have hlt := (mem_cumulativeSquarePrefixSet_iff.mp hm)
  have hpred : R - 1 + 1 = R := pred_succ_eq_self hR
  have hlt' : m < R ^ 2 := by simpa [hpred] using hlt
  unfold squareRootEndpoint
  omega

private theorem bornSmoothNonunit_le_endpoint {R m : ℕ}
    (hR : 2 ≤ R) (hm : m ∈ bornSmoothNonunitSet R) :
    m ≤ squareRootEndpoint R :=
  prefix_mem_le_squareRootEndpoint (by omega)
    (bornSmoothNonunit_mem_prefix hm)

private theorem bornSmooth_orientation_strict {R m : ℕ}
    (hm : m ∈ bornSmoothNonunitSet R) :
    canonicalLargestPrimeFactor m < canonicalCofactor m := by
  have hsq := bornSmoothNonunit_squarefree hm
  have hmgt := bornSmoothNonunit_gt_one hm
  have hle := bornSmoothNonunit_orientation hm
  have hne :
      canonicalLargestPrimeFactor m ≠ canonicalCofactor m := by
    intro heq
    apply canonicalLargestPrimeFactor_not_dvd_cofactor hsq hmgt
    rw [← heq]
  omega

private theorem bornSmooth_canonicalSource_smooth {R m : ℕ}
    (hR : 2 ≤ R) (hm : m ∈ bornSmoothNonunitSet R) :
    SmoothOriented
      (canonicalSourceIndex (squareRootEndpoint R) m
        (bornSmoothNonunit_squarefree hm)
        (bornSmoothNonunit_gt_one hm)
        (bornSmoothNonunit_le_endpoint hR hm)) := by
  refine ⟨canonicalSourceIndex_admissible
      (bornSmoothNonunit_squarefree hm)
      (bornSmoothNonunit_gt_one hm)
      (bornSmoothNonunit_le_endpoint hR hm), ?_⟩
  change canonicalLargestPrimeFactor m < canonicalCofactor m
  exact bornSmooth_orientation_strict hm

private theorem bornSmooth_canonicalSource_clock_le {R m : ℕ}
    (hR : 2 ≤ R) (hm : m ∈ bornSmoothNonunitSet R) :
    sourceClock (squareRootEndpoint R)
        (canonicalSourceIndex (squareRootEndpoint R) m
          (bornSmoothNonunit_squarefree hm)
          (bornSmoothNonunit_gt_one hm)
          (bornSmoothNonunit_le_endpoint hR hm)) ≤ R - 1 := by
  rw [canonicalSourceIndex_clock]
  exact (canonicalEntry_le_iff_mem_cumulativeSquarePrefixSet
    (R - 1) m).2 (bornSmoothNonunit_mem_prefix hm)

private theorem bornSmooth_canonicalSource_weight_ne {R m : ℕ}
    (hR : 2 ≤ R) (hm : m ∈ bornSmoothNonunitSet R) :
    sourceWeight
        (canonicalSourceIndex (squareRootEndpoint R) m
          (bornSmoothNonunit_squarefree hm)
          (bornSmoothNonunit_gt_one hm)
          (bornSmoothNonunit_le_endpoint hR hm)) ≠ 0 := by
  rw [canonicalSourceIndex_weight]
  exact bornSmoothNonunit_moebius_ne hm

private theorem bornSmooth_canonicalSource_mem_active {R m : ℕ}
    (hR : 2 ≤ R) (hm : m ∈ bornSmoothNonunitSet R) :
    canonicalSourceIndex (squareRootEndpoint R) m
        (bornSmoothNonunit_squarefree hm)
        (bornSmoothNonunit_gt_one hm)
        (bornSmoothNonunit_le_endpoint hR hm) ∈
      activeSmoothSourceSet R := by
  simp only [activeSmoothSourceSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨bornSmooth_canonicalSource_smooth hR hm,
    bornSmooth_canonicalSource_clock_le hR hm,
    bornSmooth_canonicalSource_weight_ne hR hm⟩

/-- A smooth source visible by square clock `R-1` has distinguished prime
strictly below `R`.  This is the elementary square-block support fact that puts
all terminal transport roots on the lower scale. -/
theorem sourcePrime_lt_cutoff_of_smooth_clock
    {R B : ℕ} (hR : 2 ≤ R) (s : SourceIndex B)
    (hsmooth : SmoothOriented s)
    (hclock : sourceClock B s ≤ R - 1) :
    sourcePrime s < R := by
  have hmem : sourceProduct s ∈ cumulativeSquarePrefixSet (R - 1) :=
    (canonicalEntry_le_iff_mem_cumulativeSquarePrefixSet
      (R - 1) (sourceProduct s)).1 hclock
  have hlt := mem_cumulativeSquarePrefixSet_iff.mp hmem
  have hpred : R - 1 + 1 = R := pred_succ_eq_self (by omega)
  have hprod_lt : sourceProduct s < R ^ 2 := by
    simpa [hpred] using hlt
  have hqpos : 0 < sourcePrime s := hsmooth.1.1.pos
  have hqq_lt : sourcePrime s * sourcePrime s < sourceProduct s := by
    unfold sourceProduct
    exact Nat.mul_lt_mul_of_pos_left hsmooth.2 hqpos
  by_contra h
  have hRq : R ≤ sourcePrime s := Nat.le_of_not_gt h
  nlinarith [hqq_lt, hprod_lt]

private theorem activeSmoothSource_product_mem_bornSmoothNonunitSet
    {R : ℕ} (hR : 2 ≤ R)
    {s : SourceIndex (squareRootEndpoint R)}
    (hs : s ∈ activeSmoothSourceSet R) :
    sourceProduct s ∈ bornSmoothNonunitSet R := by
  rcases Finset.mem_filter.mp hs with ⟨_huniv, hsmooth, hclock, hweight⟩
  have hprime_lt := sourcePrime_lt_cutoff_of_smooth_clock hR s hsmooth hclock
  have hmem : sourceProduct s ∈ cumulativeSquarePrefixSet (R - 1) :=
    (canonicalEntry_le_iff_mem_cumulativeSquarePrefixSet
      (R - 1) (sourceProduct s)).1 hclock
  have hprod_gt : 1 < sourceProduct s := by
    unfold sourceProduct
    have hq2 := hsmooth.1.1.two_le
    have hc1 := hsmooth.1.2.1
    nlinarith
  have hprod_ne_one : sourceProduct s ≠ 1 := by omega
  have hlpf := sourcePrime_eq_canonicalLargestPrimeFactor s hsmooth.1
  have hcore := sourceCore_eq_canonicalCofactor s hsmooth.1
  have hmu : μ (sourceProduct s) ≠ 0 := by
    rw [sourceWeight_of_admissible s hsmooth.1] at hweight
    exact hweight
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_erase.mpr ⟨hprod_ne_one, hmem⟩, hprod_gt, ?_, ?_, hmu⟩
  · rw [← hlpf]
    exact hprime_lt.le
  · rw [← hlpf, ← hcore]
    exact hsmooth.2.le

/-- The native square-clock pushforward is literally the sum over the active
smooth source population; removing zero source weights changes nothing. -/
theorem squareRootSmoothAncestryPushforward_eq_active_sum (R : ℕ) :
    squareRootSmoothAncestryPushforward R =
      ∑ s ∈ activeSmoothSourceSet R, sourceWeight s := by
  classical
  simp [squareRootSmoothAncestryPushforward, activeSmoothSourceSet,
    clockPushforward, smoothSourceField, and_assoc, and_left_comm, and_comm]

/-- Exact finite reindexing from nonunit born-smooth integers to active
smooth ancestry sources. -/
theorem bornSmoothNonunit_sum_eq_activeSource_sum
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ m ∈ bornSmoothNonunitSet R, (μ m : ℤ)) =
      ∑ s ∈ activeSmoothSourceSet R, sourceWeight s := by
  classical
  refine Finset.sum_bij
    (fun m hm =>
      canonicalSourceIndex (squareRootEndpoint R) m
        (bornSmoothNonunit_squarefree hm)
        (bornSmoothNonunit_gt_one hm)
        (bornSmoothNonunit_le_endpoint hR hm))
    ?_ ?_ ?_ ?_
  · intro m hm
    exact bornSmooth_canonicalSource_mem_active hR hm
  · intro m hm
    exact canonicalSourceIndex_weight
      (bornSmoothNonunit_squarefree hm)
      (bornSmoothNonunit_gt_one hm)
      (bornSmoothNonunit_le_endpoint hR hm)
  · intro m₁ m₂ hm₁ hm₂ heq
    have hp := congrArg sourceProduct heq
    simpa [canonicalSourceIndex_product
      (bornSmoothNonunit_squarefree hm₁)
      (bornSmoothNonunit_gt_one hm₁)
      (bornSmoothNonunit_le_endpoint hR hm₁),
      canonicalSourceIndex_product
      (bornSmoothNonunit_squarefree hm₂)
      (bornSmoothNonunit_gt_one hm₂)
      (bornSmoothNonunit_le_endpoint hR hm₂)] using hp
  · intro s hs
    let m := sourceProduct s
    have hm : m ∈ bornSmoothNonunitSet R :=
      activeSmoothSource_product_mem_bornSmoothNonunitSet hR hs
    refine ⟨m, hm, ?_⟩
    have hsmooth := (Finset.mem_filter.mp hs).2.1
    apply sourceProduct_injective_on_admissible
      (canonicalSourceIndex_admissible
        (bornSmoothNonunit_squarefree hm)
        (bornSmoothNonunit_gt_one hm)
        (bornSmoothNonunit_le_endpoint hR hm))
      hsmooth.1
    rw [canonicalSourceIndex_product]

/-- The original born-smooth mass is exactly the Mobius unit plus the complex
cast of the square-clock smooth-ancestry pushforward. -/
theorem squareRootBornSmoothMass_eq_one_add_ancestryPushforward
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootBornSmoothMass R =
      1 + ((squareRootSmoothAncestryPushforward R : ℤ) : ℂ) := by
  classical
  let P := cumulativeSquarePrefixSet (R - 1)
  let f : ℕ → ℂ := fun m =>
    if canonicalLargestPrimeFactor m ≤ R ∧
        canonicalLargestPrimeFactor m ≤ canonicalCofactor m then
      canonicalMoebiusWeight m
    else 0
  have h1mem : 1 ∈ P := by
    dsimp [P]
    rw [mem_cumulativeSquarePrefixSet_iff]
    have hpred : R - 1 + 1 = R := pred_succ_eq_self (by omega)
    rw [hpred]
    nlinarith
  have hunit : f 1 = 1 := by
    simp [f, canonicalLargestPrimeFactor, canonicalCofactor,
      canonicalMoebiusWeight, hR]
  have herase :
      (∑ m ∈ P.erase 1, f m) =
        ∑ m ∈ bornSmoothNonunitSet R, ((μ m : ℤ) : ℂ) := by
    rw [bornSmoothNonunitSet, Finset.sum_filter]
    apply Finset.sum_congr
    · rfl
    · intro m hm
      have hmne : m ≠ 1 := (Finset.mem_erase.mp hm).1
      by_cases hm0 : m = 0
      · subst m
        simp [f, canonicalLargestPrimeFactor, canonicalCofactor]
      have hmgt : 1 < m := by omega
      by_cases hborn :
          canonicalLargestPrimeFactor m ≤ R ∧
            canonicalLargestPrimeFactor m ≤ canonicalCofactor m
      · by_cases hmu : μ m = 0
        · simp [f, hborn, hmgt, hmu, canonicalMoebiusWeight]
        · simp [f, hborn, hmgt, hmu, canonicalMoebiusWeight]
      · simp [f, hborn, hmgt]
  have hsplit :
      (∑ m ∈ P, f m) =
        1 + ∑ m ∈ bornSmoothNonunitSet R, ((μ m : ℤ) : ℂ) := by
    calc
      (∑ m ∈ P, f m) = (∑ m ∈ P.erase 1, f m) + f 1 :=
        (Finset.sum_erase_add _ h1mem).symm
      _ = 1 + ∑ m ∈ bornSmoothNonunitSet R, ((μ m : ℤ) : ℂ) := by
        rw [hunit, herase]
        ring
  unfold squareRootBornSmoothMass
  change (∑ m ∈ P, f m) = _
  rw [hsplit]
  have hreindex := bornSmoothNonunit_sum_eq_activeSource_sum R hR
  have hpush := squareRootSmoothAncestryPushforward_eq_active_sum R
  have hint :
      (∑ m ∈ bornSmoothNonunitSet R, (μ m : ℤ)) =
        squareRootSmoothAncestryPushforward R := hreindex.trans hpush.symm
  have hcast := congrArg (fun z : ℤ => (z : ℂ)) hint
  simpa using hcast

/-! ## Lower-scale transport-root coordinates -/

/-- Root field restricted to distinguished primes below `R`. -/
def lowPrimeRootField (R B : ℕ) : SourceIndex B → ℤ := fun s =>
  if sourcePrime s < R then (boundedSourceFlow B).rootField s else 0

/-- Signed unit basis for transport roots with fixed lower-scale core `c`.
The value `-1` is chosen because a transport root `q*c` has Mobius weight
`-μ(c)`. -/
def lowRootCoreBasis (R B c : ℕ) : SourceIndex B → ℤ := fun s =>
  if TransportOriented s ∧ sourcePrime s < R ∧ sourceCore s = c then -1 else 0

private theorem sourcePrime_eq_of_parent {B : ℕ} {s t : SourceIndex B}
    (hparent : sourceParent s = some t) :
    sourcePrime t = sourcePrime s := by
  classical
  by_cases h : SmoothOriented s
  · have ht : parentIndex s h = t := by
      simpa [sourceParent, h] using hparent
    subst t
    simp
  · simp [sourceParent, h] at hparent

private theorem rootField_eq_transportIndicator (B : ℕ) (s : SourceIndex B) :
    (boundedSourceFlow B).rootField s =
      if TransportOriented s then sourceWeight s else 0 := by
  classical
  by_cases hadm : SourceAdmissible s
  · have hiff := sourceParent_eq_none_iff_transport s hadm
    by_cases htrans : TransportOriented s
    · have hp : sourceParent s = none := hiff.mpr htrans
      simp [boundedSourceFlow, rootField, hp, htrans]
    · have hp : sourceParent s ≠ none := by
        intro hp
        exact htrans (hiff.mp hp)
      cases hparent : sourceParent s with
      | none => exact (hp hparent).elim
      | some t => simp [boundedSourceFlow, rootField, hparent, htrans]
  · have hw : sourceWeight s = 0 := by
      simp [sourceWeight, hadm]
    cases hparent : sourceParent s <;>
      simp [boundedSourceFlow, rootField, hparent, hw, hadm,
        TransportOriented, SourceAdmissible]

private theorem transport_sourceWeight_eq_neg_core_moebius
    {B : ℕ} (s : SourceIndex B) (h : TransportOriented s) :
    sourceWeight s = -(μ (sourceCore s) : ℤ) := by
  rcases h.1 with ⟨hq, _hcpos, _hsq, hcop, _hdom⟩
  rw [sourceWeight_of_admissible s h.1]
  unfold sourceProduct
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hq]
  ring

/-- Exact decomposition of the low-prime root field by its lower-scale core.
Transport orientation gives `1 ≤ c ≤ q < R`, so no core outside `c < R`
appears. -/
theorem lowPrimeRootField_eq_core_sum (R B : ℕ) :
    lowPrimeRootField R B =
      ∑ c ∈ Finset.Ico 1 R,
        (μ c : ℤ) • lowRootCoreBasis R B c := by
  classical
  funext s
  by_cases hq : sourcePrime s < R
  · by_cases ht : TransportOriented s
    · have hcpos : 1 ≤ sourceCore s := ht.1.2.1
      have hclt : sourceCore s < R := lt_of_le_of_lt ht.2 hq
      have hcmem : sourceCore s ∈ Finset.Ico 1 R :=
        Finset.mem_Ico.mpr ⟨hcpos, hclt⟩
      rw [lowPrimeRootField]
      simp only [hq, if_true]
      rw [rootField_eq_transportIndicator]
      simp only [ht, if_true]
      rw [transport_sourceWeight_eq_neg_core_moebius s ht]
      simp [lowRootCoreBasis, ht, hq, hcmem]
    · simp [lowPrimeRootField, hq, rootField_eq_transportIndicator,
        ht, lowRootCoreBasis]
  · simp [lowPrimeRootField, hq, lowRootCoreBasis]

/-- `U ↦ alternatingPrefix(S,U,depth) - U` as an additive operator. -/
def ancestryTailOperator {M : Type*} [AddCommGroup M]
    (S : M →+ M) (depth : ℕ) : M →+ M where
  toFun U := alternatingPrefix S U depth - U
  map_zero' := by
    induction depth with
    | zero => simp [alternatingPrefix]
    | succ n ih => simp [alternatingPrefix, ih]
  map_add' U V := by
    have hadd :
        alternatingPrefix S (U + V) depth =
          alternatingPrefix S U depth + alternatingPrefix S V depth := by
      induction depth with
      | zero => simp [alternatingPrefix]
      | succ n ih =>
          simp only [alternatingPrefix]
          rw [ih, map_add]
          abel
    rw [hadd]
    abel

/-- Square-clock response of an arbitrary transport-root field through the
finite canonical ancestry tail. -/
def squareClockRootResponseHom (R B : ℕ) :
    (SourceIndex B → ℤ) →+ ℤ :=
  (clockPushforward (sourceClock B) (R - 1)).comp
    (ancestryTailOperator (boundedSourceFlow B).successorOperator (B + 1))

/-- Integer response coefficient of the fixed-core transport-root basis. -/
def squareRootBornSmoothRootResponse (R c : ℕ) : ℤ :=
  let B := squareRootEndpoint R
  squareClockRootResponseHom R B (lowRootCoreBasis R B c)

/-- Explicit lower-scale coefficient `Xi_R(c)`.  The Mobius unit is absorbed at
`c = 1`, so the final formula has no external singleton correction. -/
def squareRootBornSmoothXi (R c : ℕ) : ℤ :=
  squareRootBornSmoothRootResponse R c + if c = 1 then 1 else 0

private theorem alternatingPrefix_root_eq_low_of_prime_lt
    (R B depth : ℕ) (s : SourceIndex B)
    (hq : sourcePrime s < R) :
    alternatingPrefix (boundedSourceFlow B).successorOperator
        (boundedSourceFlow B).rootField depth s =
      alternatingPrefix (boundedSourceFlow B).successorOperator
        (lowPrimeRootField R B) depth s := by
  induction depth generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [alternatingPrefix, Pi.sub_apply]
      have hroot : lowPrimeRootField R B s =
          (boundedSourceFlow B).rootField s := by
        simp [lowPrimeRootField, hq]
      rw [hroot]
      cases hp : sourceParent s with
      | none =>
          simp [boundedSourceFlow, successorOperator, hp]
      | some t =>
          have hqt : sourcePrime t < R := by
            rw [sourcePrime_eq_of_parent hp]
            exact hq
          simp [boundedSourceFlow, successorOperator, hp, ih t hqt]

private theorem alternatingPrefix_low_eq_zero_of_prime_ge
    (R B depth : ℕ) (s : SourceIndex B)
    (hq : ¬ sourcePrime s < R) :
    alternatingPrefix (boundedSourceFlow B).successorOperator
        (lowPrimeRootField R B) depth s = 0 := by
  induction depth generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [alternatingPrefix, Pi.sub_apply]
      have hroot : lowPrimeRootField R B s = 0 := by
        simp [lowPrimeRootField, hq]
      rw [hroot]
      cases hp : sourceParent s with
      | none => simp [boundedSourceFlow, successorOperator, hp]
      | some t =>
          have hqt : ¬ sourcePrime t < R := by
            rw [sourcePrime_eq_of_parent hp]
            exact hq
          simp [boundedSourceFlow, successorOperator, hp, ih t hqt]

/-- On the visible square prefix the smooth ancestry pushforward is exactly the
response of the low-prime transport-root field.  Roots with prime coordinate at
least `R` cannot feed a smooth source before the `R^2` square cutoff. -/
theorem squareRootSmoothAncestryPushforward_eq_lowRootResponse
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootSmoothAncestryPushforward R =
      squareClockRootResponseHom R (squareRootEndpoint R)
        (lowPrimeRootField R (squareRootEndpoint R)) := by
  classical
  let B := squareRootEndpoint R
  unfold squareRootSmoothAncestryPushforward squareClockRootResponseHom
    ancestryTailOperator
  change
    clockPushforward (sourceClock B) (R - 1) (smoothSourceField B) =
      clockPushforward (sourceClock B) (R - 1)
        (alternatingPrefix (boundedSourceFlow B).successorOperator
            (lowPrimeRootField R B) (B + 1) - lowPrimeRootField R B)
  unfold clockPushforward
  apply Finset.sum_congr rfl
  intro s _hs
  by_cases hclock : sourceClock B s ≤ R - 1
  · simp only [hclock, if_true]
    by_cases hq : sourcePrime s < R
    · have hfull := congrFun (smoothSourceField_eq_alternating_sub_root B) s
      rw [hfull]
      rw [alternatingPrefix_root_eq_low_of_prime_lt R B (B + 1) s hq]
      simp [lowPrimeRootField, hq]
    · have hnotSmooth : ¬ SmoothOriented s := by
        intro hsmooth
        exact hq (sourcePrime_lt_cutoff_of_smooth_clock hR s hsmooth hclock)
      have hzero := alternatingPrefix_low_eq_zero_of_prime_ge
        R B (B + 1) s hq
      simp [smoothSourceField, hnotSmooth, hzero, lowPrimeRootField, hq]
  · simp [hclock]

/-- Exact lower-scale root-coordinate expansion of the ancestry pushforward. -/
theorem squareRootSmoothAncestryPushforward_eq_rootResponseSum
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootSmoothAncestryPushforward R =
      ∑ c ∈ Finset.Ico 1 R,
        (μ c : ℤ) * squareRootBornSmoothRootResponse R c := by
  rw [squareRootSmoothAncestryPushforward_eq_lowRootResponse R hR,
    lowPrimeRootField_eq_core_sum R (squareRootEndpoint R)]
  unfold squareRootBornSmoothRootResponse
  simp only
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [map_zsmul]
  simp

/-- Final exact lower-scale formula requested for the born-smooth population:

`A_R^born = sum_{1 <= c < R} mu(c) * Xi_R(c)`.

The coefficient is an explicit finite square-clock response of transport roots
with core `c`; `Xi_R(1)` also carries the original Mobius unit. -/
theorem squareRootBornSmoothMass_eq_rootCoordinateSum
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootBornSmoothMass R =
      ∑ c ∈ Finset.Ico 1 R,
        canonicalMoebiusWeight c * ((squareRootBornSmoothXi R c : ℤ) : ℂ) := by
  rw [squareRootBornSmoothMass_eq_one_add_ancestryPushforward R hR,
    squareRootSmoothAncestryPushforward_eq_rootResponseSum R hR]
  have h1mem : 1 ∈ Finset.Ico 1 R := by
    exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  unfold squareRootBornSmoothXi canonicalMoebiusWeight
  push_cast
  rw [Finset.sum_add_distrib]
  simp [h1mem]

/-!
The remaining analytic target is intentionally not restated or split here.
It is the existing joint signed born-smooth / raw-transport Gram, with no
separate treatment of floor or prime-counting discrepancies.  This module only
supplies the exact arithmetic coordinate change needed before that attack.
-/

end BornSmoothAncestrySquareClockPushforward

end RHLean.Proof
