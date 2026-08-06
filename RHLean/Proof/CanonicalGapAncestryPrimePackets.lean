import Mathlib
import RHLean.Proof.CanonicalGapAncestryProjectedRenewal

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapAncestryPrimePackets

open CanonicalGapAncestryFlow
open CanonicalGapAncestryFlow.ParentFlow
open CanonicalGapAncestryBridge
open CanonicalGapAncestryHighRealization
open CanonicalGapAncestryProjectedRenewal

/-!
# Dyadic prime packets for the canonical ancestry renewal

This module refines the exact projected ancestry renewal by two arithmetic
scales:

* `k`, the dyadic scale of the distinguished prime `q`; and
* `j`, the dyadic scale of the largest prime stripped from the child core.

The packetization is exact and finite.  It also records a generic partial
baseline identity in which near-diagonal packets remain coupled to the root,
while only scale-separated packets are replaced by a supplied deterministic
model.  No prime-density model or analytic estimate is asserted here.
-/

/-! ## Exact dyadic scale coordinates -/

/-- Base-two dyadic scale of the distinguished source prime. -/
def sourcePrimeDyadicScale {B : ℕ} (s : SourceIndex B) : ℕ :=
  Nat.log 2 (sourcePrime s)

/-- Largest prime stripped from the core on a canonical parent edge.  The
harmless repository convention gives value `1` on cores `0` and `1`. -/
def sourceStrippedPrime {B : ℕ} (s : SourceIndex B) : ℕ :=
  canonicalLargestPrimeFactor (sourceCore s)

/-- Base-two dyadic scale of the stripped core prime. -/
def sourceStrippedPrimeDyadicScale {B : ℕ} (s : SourceIndex B) : ℕ :=
  Nat.log 2 (sourceStrippedPrime s)

/-- The largest prime factor of a nontrivial integer is at most that integer. -/
theorem canonicalLargestPrimeFactor_le_self
    {c : ℕ} (hc : 1 < c) :
    canonicalLargestPrimeFactor c ≤ c := by
  have hprod := canonicalCofactor_mul_largestPrimeFactor hc
  have hdvd : canonicalLargestPrimeFactor c ∣ c := by
    refine ⟨canonicalCofactor c, ?_⟩
    simpa [Nat.mul_comm] using hprod.symm
  exact Nat.le_of_dvd (by omega) hdvd

/-- Every distinguished-prime scale fits in the finite source cutoff. -/
theorem sourcePrimeDyadicScale_lt_bound
    {B : ℕ} (s : SourceIndex B) :
    sourcePrimeDyadicScale s < B + 1 := by
  exact lt_of_le_of_lt
    (Nat.log_le_self 2 (sourcePrime s)) s.1.2

/-- Every stripped-prime scale also fits in the finite source cutoff. -/
theorem sourceStrippedPrimeDyadicScale_lt_bound
    {B : ℕ} (s : SourceIndex B) :
    sourceStrippedPrimeDyadicScale s < B + 1 := by
  by_cases hc : 1 < sourceCore s
  · have hp_le : sourceStrippedPrime s ≤ sourceCore s := by
      simpa [sourceStrippedPrime] using
        (canonicalLargestPrimeFactor_le_self hc)
    exact lt_of_le_of_lt
      ((Nat.log_le_self 2 (sourceStrippedPrime s)).trans hp_le) s.2.2
  · simp [sourceStrippedPrimeDyadicScale, sourceStrippedPrime,
      canonicalLargestPrimeFactor, hc]

/-- On a smooth child, the stripped core prime is strictly below the
unchanged distinguished prime. -/
theorem sourceStrippedPrime_lt_sourcePrime_of_smooth
    {B : ℕ} {s : SourceIndex B} (hs : SmoothOriented s) :
    sourceStrippedPrime s < sourcePrime s := by
  rcases hs.1 with ⟨hq, _hcpos, _hsq, _hcop, hdom⟩
  have hcgt : 1 < sourceCore s := lt_trans hq.one_lt hs.2
  have hpPrime : (sourceStrippedPrime s).Prime := by
    simpa [sourceStrippedPrime] using
      (canonicalLargestPrimeFactor_prime hcgt)
  have hpDvd : sourceStrippedPrime s ∣ sourceCore s := by
    have hprod := canonicalCofactor_mul_largestPrimeFactor hcgt
    refine ⟨canonicalCofactor (sourceCore s), ?_⟩
    simpa [sourceStrippedPrime, Nat.mul_comm] using hprod.symm
  exact hdom (sourceStrippedPrime s) hpPrime hpDvd

/-- Consequently the stripped-prime scale is no larger than the
`q`-scale on every smooth child. -/
theorem sourceStrippedPrimeDyadicScale_le_sourcePrimeDyadicScale_of_smooth
    {B : ℕ} {s : SourceIndex B} (hs : SmoothOriented s) :
    sourceStrippedPrimeDyadicScale s ≤ sourcePrimeDyadicScale s := by
  unfold sourceStrippedPrimeDyadicScale sourcePrimeDyadicScale
  exact Nat.log_mono_right
    (Nat.le_of_lt (sourceStrippedPrime_lt_sourcePrime_of_smooth hs))

/-! ## Generic finite packet projectors -/

/-- Restrict a source field to one distinguished-prime dyadic scale. -/
def sourceQPacketField (B k : ℕ) (f : SourceIndex B → ℤ) :
    SourceIndex B → ℤ := fun s =>
  if sourcePrimeDyadicScale s = k then f s else 0

/-- Restrict a source field to one stripped-prime and distinguished-prime
scale pair `(j,k)`. -/
def sourceQPPacketField (B j k : ℕ) (f : SourceIndex B → ℤ) :
    SourceIndex B → ℤ := fun s =>
  if sourcePrimeDyadicScale s = k ∧
      sourceStrippedPrimeDyadicScale s = j then f s else 0

/-- Exact finite recombination of all distinguished-prime packets. -/
theorem sourceField_eq_qPacket_sum
    (B : ℕ) (f : SourceIndex B → ℤ) :
    f = ∑ k ∈ Finset.range (B + 1), sourceQPacketField B k f := by
  classical
  funext s
  have hk : sourcePrimeDyadicScale s ∈ Finset.range (B + 1) :=
    Finset.mem_range.mpr (sourcePrimeDyadicScale_lt_bound s)
  rw [Finset.sum_eq_single (sourcePrimeDyadicScale s)]
  · simp [sourceQPacketField]
  · intro k _hk hne
    have hne' : sourcePrimeDyadicScale s ≠ k := Ne.symm hne
    simp [sourceQPacketField, hne']
  · intro hnot
    exact (hnot hk).elim

/-- Exact finite recombination of all two-parameter prime packets. -/
theorem sourceField_eq_qpPacket_sum
    (B : ℕ) (f : SourceIndex B → ℤ) :
    f = ∑ k ∈ Finset.range (B + 1),
      ∑ j ∈ Finset.range (B + 1), sourceQPPacketField B j k f := by
  classical
  funext s
  have hk : sourcePrimeDyadicScale s ∈ Finset.range (B + 1) :=
    Finset.mem_range.mpr (sourcePrimeDyadicScale_lt_bound s)
  have hj : sourceStrippedPrimeDyadicScale s ∈ Finset.range (B + 1) :=
    Finset.mem_range.mpr (sourceStrippedPrimeDyadicScale_lt_bound s)
  rw [Finset.sum_eq_single (sourcePrimeDyadicScale s)]
  · rw [Finset.sum_eq_single (sourceStrippedPrimeDyadicScale s)]
    · simp [sourceQPPacketField]
    · intro j _hj hne
      have hne' : sourceStrippedPrimeDyadicScale s ≠ j := Ne.symm hne
      simp [sourceQPPacketField, hne']
    · intro hnot
      exact (hnot hj).elim
  · intro k _hk hne
    apply Finset.sum_eq_zero
    intro j _hj
    have hne' : sourcePrimeDyadicScale s ≠ k := Ne.symm hne
    simp [sourceQPPacketField, hne']
  · intro hnot
    exact (hnot hk).elim

/-- A field supported on smooth children has no packet strictly above the
triangular region `j ≤ k`. -/
theorem sourceQPPacketField_eq_zero_of_k_lt_j
    {B j k : ℕ} (f : SourceIndex B → ℤ)
    (hvanish : ∀ s, ¬ SmoothOriented s → f s = 0)
    (hjk : k < j) :
    sourceQPPacketField B j k f = 0 := by
  classical
  funext s
  by_cases hs : SmoothOriented s
  · have hscale :=
      sourceStrippedPrimeDyadicScale_le_sourcePrimeDyadicScale_of_smooth hs
    have hnot : ¬(sourcePrimeDyadicScale s = k ∧
        sourceStrippedPrimeDyadicScale s = j) := by
      rintro ⟨hq, hp⟩
      omega
    simp [sourceQPPacketField, hnot]
  · simp [sourceQPPacketField, hvanish s hs]

/-! ## Projected-renewal packets -/

/-- The two projected successor populations retained as one signed field. -/
def sourceProjectedSuccessorField (Λ : ℝ) (B : ℕ) :
    SourceIndex B → ℤ :=
  sourceLowToHighSuccessorField Λ B + sourceHighToHighSuccessorField Λ B

/-- The projected renewal with both successor populations recombined. -/
theorem sourceHighField_eq_root_sub_projectedSuccessor
    (Λ : ℝ) (B : ℕ) :
    sourceHighField Λ B =
      sourceHighRootField Λ B - sourceProjectedSuccessorField Λ B := by
  rw [sourceHighField_eq_projectedRenewal]
  unfold sourceProjectedSuccessorField
  abel

/-- One `q`-scale packet of the projected root field. -/
def sourceHighRootQPacketField (Λ : ℝ) (B k : ℕ) :
    SourceIndex B → ℤ :=
  sourceQPacketField B k (sourceHighRootField Λ B)

/-- One `(p,q)`-scale packet of the complete projected successor field. -/
def sourceProjectedSuccessorPQPacketField
    (Λ : ℝ) (B j k : ℕ) : SourceIndex B → ℤ :=
  sourceQPPacketField B j k (sourceProjectedSuccessorField Λ B)

/-- Exact recombination of the projected root packets. -/
theorem sourceHighRootField_eq_qPacket_sum
    (Λ : ℝ) (B : ℕ) :
    sourceHighRootField Λ B =
      ∑ k ∈ Finset.range (B + 1), sourceHighRootQPacketField Λ B k := by
  exact sourceField_eq_qPacket_sum B (sourceHighRootField Λ B)

/-- Exact recombination of the projected successor packets. -/
theorem sourceProjectedSuccessorField_eq_qpPacket_sum
    (Λ : ℝ) (B : ℕ) :
    sourceProjectedSuccessorField Λ B =
      ∑ k ∈ Finset.range (B + 1),
        ∑ j ∈ Finset.range (B + 1),
          sourceProjectedSuccessorPQPacketField Λ B j k := by
  exact sourceField_eq_qpPacket_sum B (sourceProjectedSuccessorField Λ B)

/-- The projected successor field vanishes away from smooth children. -/
theorem sourceProjectedSuccessorField_eq_zero_of_not_smooth
    (Λ : ℝ) (B : ℕ) (s : SourceIndex B)
    (hs : ¬ SmoothOriented s) :
    sourceProjectedSuccessorField Λ B s = 0 := by
  have hparent : sourceParent s = none :=
    (sourceParent_eq_none_iff s).2 hs
  unfold sourceProjectedSuccessorField sourceLowToHighSuccessorField
    sourceHighToHighSuccessorField sourceLowField sourceHighField
  simp [sourceHighProjector, successorOperator, boundedSourceFlow, hparent]

/-- The projected successor packets have exact triangular support `j ≤ k`. -/
theorem sourceProjectedSuccessorPQPacketField_eq_zero_of_k_lt_j
    {Λ : ℝ} {B j k : ℕ} (hjk : k < j) :
    sourceProjectedSuccessorPQPacketField Λ B j k = 0 := by
  exact sourceQPPacketField_eq_zero_of_k_lt_j
    (sourceProjectedSuccessorField Λ B)
    (sourceProjectedSuccessorField_eq_zero_of_not_smooth Λ B) hjk

/-- Exact field-level two-parameter packet renewal. -/
theorem sourceHighField_eq_primePacketRenewal
    (Λ : ℝ) (B : ℕ) :
    sourceHighField Λ B =
      (∑ k ∈ Finset.range (B + 1), sourceHighRootQPacketField Λ B k) -
        ∑ k ∈ Finset.range (B + 1),
          ∑ j ∈ Finset.range (B + 1),
            sourceProjectedSuccessorPQPacketField Λ B j k := by
  rw [sourceHighField_eq_root_sub_projectedSuccessor,
    sourceHighRootField_eq_qPacket_sum,
    sourceProjectedSuccessorField_eq_qpPacket_sum]

/-! ## Clock pushforward and window paths -/

/-- Clock-pushed projected root packet. -/
def sourceHighRootQPacketPrefix
    (Λ : ℝ) (B k x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x (sourceHighRootQPacketField Λ B k)

/-- Clock-pushed complete projected successor packet. -/
def sourceProjectedSuccessorPQPacketPrefix
    (Λ : ℝ) (B j k x : ℕ) : ℤ :=
  clockPushforward (sourceClock B) x
    (sourceProjectedSuccessorPQPacketField Λ B j k)

/-- Exact packet renewal after the native square-root clock pushforward. -/
theorem sourceHighPrefix_eq_primePacketRenewal
    (Λ : ℝ) (B x : ℕ) :
    sourceHighPrefix Λ B x =
      (∑ k ∈ Finset.range (B + 1), sourceHighRootQPacketPrefix Λ B k x) -
        ∑ k ∈ Finset.range (B + 1),
          ∑ j ∈ Finset.range (B + 1),
            sourceProjectedSuccessorPQPacketPrefix Λ B j k x := by
  unfold sourceHighRootQPacketPrefix sourceProjectedSuccessorPQPacketPrefix
  change clockPushforward (sourceClock B) x (sourceHighField Λ B) = _
  rw [sourceHighField_eq_primePacketRenewal, map_sub, map_sum, map_sum]
  apply congrArg₂ Sub.sub rfl
  apply Finset.sum_congr rfl
  intro k _hk
  rw [map_sum]

/-- Actual projected root packet path in a translated window. -/
def sourceHighRootQPacketWindowPath
    (Λ : ℝ) (B k N : ℕ) : ℕ → ℤ := fun r =>
  sourceHighRootQPacketPrefix Λ B k (N + r)

/-- Actual complete projected successor packet path in a translated window. -/
def sourceProjectedSuccessorPQPacketWindowPath
    (Λ : ℝ) (B j k N : ℕ) : ℕ → ℤ := fun r =>
  sourceProjectedSuccessorPQPacketPrefix Λ B j k (N + r)

/-- Exact fibered packet renewal on an actual translated window. -/
theorem sourceHighWindowPath_eq_primePacketRenewal
    (Λ : ℝ) (B N : ℕ) :
    sourceHighWindowPath Λ B N = fun r =>
      ∑ k ∈ Finset.range (B + 1),
        (sourceHighRootQPacketWindowPath Λ B k N r -
          ∑ j ∈ Finset.range (B + 1),
            sourceProjectedSuccessorPQPacketWindowPath Λ B j k N r) := by
  funext r
  unfold sourceHighWindowPath sourceHighRootQPacketWindowPath
    sourceProjectedSuccessorPQPacketWindowPath
  rw [Finset.sum_sub_distrib]
  exact sourceHighPrefix_eq_primePacketRenewal Λ B (N + r)

/-! ## Generic partial-baseline algebra -/

section PartialBaseline

variable {M : Type*} [AddCommGroup M]

/-- Scale-separated packet sum `j + L ≤ k`. -/
def farPacketSum
    (scaleBound L k : ℕ) (packet : ℕ → ℕ → M) : M :=
  ∑ j ∈ Finset.range (scaleBound + 1),
    if j + L ≤ k then packet j k else 0

/-- Near-diagonal packet sum, retaining the complement of `j + L ≤ k`. -/
def nearPacketSum
    (scaleBound L k : ℕ) (packet : ℕ → ℕ → M) : M :=
  ∑ j ∈ Finset.range (scaleBound + 1),
    if j + L ≤ k then 0 else packet j k

/-- The complete packet fiber splits exactly into its near and far parts. -/
theorem packetSum_eq_near_add_far
    (scaleBound L k : ℕ) (packet : ℕ → ℕ → M) :
    (∑ j ∈ Finset.range (scaleBound + 1), packet j k) =
      nearPacketSum scaleBound L k packet +
        farPacketSum scaleBound L k packet := by
  classical
  unfold nearPacketSum farPacketSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hfar : j + L ≤ k <;> simp [hfar]

/-- Root minus near actual packets minus the modeled far packets. -/
def partialMainFiber
    (scaleBound L k : ℕ)
    (root : ℕ → M) (actual model : ℕ → ℕ → M) : M :=
  root k - nearPacketSum scaleBound L k actual -
    farPacketSum scaleBound L k model

/-- Total discrepancy between actual and modeled far packets. -/
def farPacketDiscrepancyFiber
    (scaleBound L k : ℕ)
    (actual model : ℕ → ℕ → M) : M :=
  farPacketSum scaleBound L k actual -
    farPacketSum scaleBound L k model

/-- Exact non-circular partial-baseline identity.  Near packets remain coupled
to the root, and the same fixed far model is added and subtracted. -/
theorem packetFiber_eq_partialMain_sub_farDiscrepancy
    (scaleBound L k : ℕ)
    (root : ℕ → M) (actual model : ℕ → ℕ → M) :
    root k - (∑ j ∈ Finset.range (scaleBound + 1), actual j k) =
      partialMainFiber scaleBound L k root actual model -
        farPacketDiscrepancyFiber scaleBound L k actual model := by
  rw [packetSum_eq_near_add_far]
  unfold partialMainFiber farPacketDiscrepancyFiber
  abel

end PartialBaseline

/-! ## Partial baseline on the concrete projected packet window -/

/-- A fixed real-valued model for packet `(j,k)` at window offset `r`.
The exact layer places no existential quantifier over this object. -/
abbrev PrimePacketWindowModel := ℕ → ℕ → ℕ → ℝ

/-- Real cast of one root packet window path. -/
def sourceHighRootQPacketRealWindowPath
    (Λ : ℝ) (B k N : ℕ) : ℕ → ℝ := fun r =>
  (sourceHighRootQPacketWindowPath Λ B k N r : ℝ)

/-- Real cast of one complete projected successor packet window path. -/
def sourceProjectedSuccessorPQPacketRealWindowPath
    (Λ : ℝ) (B j k N : ℕ) : ℕ → ℝ := fun r =>
  (sourceProjectedSuccessorPQPacketWindowPath Λ B j k N r : ℝ)

/-- Near-coupled coherent defect for one distinguished-prime fiber. -/
def projectedPrimePacketPartialMainWindowPath
    (model : PrimePacketWindowModel) (L : ℕ)
    (Λ : ℝ) (B k N : ℕ) : ℕ → ℝ := fun r =>
  partialMainFiber B L k
    (fun k' => sourceHighRootQPacketRealWindowPath Λ B k' N r)
    (fun j' k' =>
      sourceProjectedSuccessorPQPacketRealWindowPath Λ B j' k' N r)
    (fun j' k' => model j' k' r)

/-- Scale-separated actual-minus-model discrepancy for one `q`-fiber. -/
def projectedPrimePacketFarDiscrepancyWindowPath
    (model : PrimePacketWindowModel) (L : ℕ)
    (Λ : ℝ) (B k N : ℕ) : ℕ → ℝ := fun r =>
  farPacketDiscrepancyFiber B L k
    (fun j' k' =>
      sourceProjectedSuccessorPQPacketRealWindowPath Λ B j' k' N r)
    (fun j' k' => model j' k' r)

/-- Real-cast form of the exact fibered packet renewal. -/
theorem sourceHighWindowPath_real_eq_primePacketRenewal
    (Λ : ℝ) (B N r : ℕ) :
    (sourceHighWindowPath Λ B N r : ℝ) =
      ∑ k ∈ Finset.range (B + 1),
        (sourceHighRootQPacketRealWindowPath Λ B k N r -
          ∑ j ∈ Finset.range (B + 1),
            sourceProjectedSuccessorPQPacketRealWindowPath Λ B j k N r) := by
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (congrFun (sourceHighWindowPath_eq_primePacketRenewal Λ B N) r)
  simpa [sourceHighRootQPacketRealWindowPath,
    sourceProjectedSuccessorPQPacketRealWindowPath] using h

/-- Fully exact partial-baseline decomposition.  The model is fixed by the
caller; no estimate and no existence claim is included. -/
theorem sourceHighWindowPath_real_eq_partialBaseline
    (model : PrimePacketWindowModel) (L : ℕ)
    (Λ : ℝ) (B N : ℕ) :
    (fun r => (sourceHighWindowPath Λ B N r : ℝ)) = fun r =>
      ∑ k ∈ Finset.range (B + 1),
        (projectedPrimePacketPartialMainWindowPath model L Λ B k N r -
          projectedPrimePacketFarDiscrepancyWindowPath model L Λ B k N r) := by
  funext r
  rw [sourceHighWindowPath_real_eq_primePacketRenewal]
  apply Finset.sum_congr rfl
  intro k _hk
  exact packetFiber_eq_partialMain_sub_farDiscrepancy B L k
    (fun k' => sourceHighRootQPacketRealWindowPath Λ B k' N r)
    (fun j' k' =>
      sourceProjectedSuccessorPQPacketRealWindowPath Λ B j' k' N r)
    (fun j' k' => model j' k' r)

end CanonicalGapAncestryPrimePackets

end RHLean.Proof
