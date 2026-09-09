import Mathlib
import RHLean.Proof.LowWheelLeastLargestStableTransfer
import RHLean.Proof.LowWheelTransportTripleCarrier
import RHLean.Proof.SquareRootCanonicalDowncrossFinalSeam

/-!
# The largest-prime stable defect is the terminal seam, not a reduction of it

`LowWheelLeastLargestStableTransfer` already proves the exact coordinate
synthesis

`lowWheelCanonicalDowncrossLedger R = lowWheelLargestDefectLedger R`.

That equality is an *identity of the same signed object*, so a linear bound on
the largest-prime stable defect is not a step toward the terminal seam: it **is**
the terminal seam.  This file records that explicitly, so the largest-prime
defect is not mistaken for an already-smaller remaining piece.

Concretely:

* `SquareRootLargestDefectLinearBound` is proved equivalent to
  `SquareRootCanonicalDowncrossLinearBound`, in both directions;
* consequently `riemannHypothesis_of_largestDefectLinear` derives the Riemann
  hypothesis from it through the existing square-prefix energy bridge;
* `lowWheelLargestDefect_geometry` classifies the exact pointwise carrier of
  the largest-prime stable defect before any norm or cardinality estimate;
* the defect is then split exactly at its largest-prime root scale `q <= R`
  versus `R < q`, with the two RH-scale `R^(1+epsilon)` bounds left explicit
  and open.

Anything that proves the largest-prime defect *linear* bound therefore proves
RH and more; it is not the quantitative target used below.  The RH-scale target
is the epsilon-loss bound, matching the existing oriented seam.

Two consequences worth stating for whoever picks this up next.

1.  The *signed* target is RH-strength.  It cannot be reached by exhibiting the
    defect's surviving pieces inside already-root-bounded endpoint populations
    unless those pieces also come with their signs and their mutual
    cancellation, because the total is the whole endpoint object.

2.  The *cardinality* target is dead by a full power of `R`, which is exactly
    the recorded support-only no-go.  Direct enumeration of
    `lowWheelLargestDefectPart` gives `|defect| / R` rising steadily
    `18.6, 22.7, ..., 140.1` across `R = 8, 9, ..., 30`, i.e. growth of order
    `R^2`, while the signed mass over the same range stays in `[-7, 9]`.  (That
    is a numerical observation, not a compiled claim; it is recorded only to
    stop the cardinality route being re-attempted.)

No norm, estimate, or density input is introduced in the geometric
classifications below.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Linear-mass proposition stated on the largest-prime stable defect. -/
def SquareRootLargestDefectLinearBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ‖lowWheelLargestDefectLedger R‖ ≤ C * (R : ℝ)

/-- **The two propositions are the same theorem.**  The largest-prime stable
defect carries exactly the canonical downcross ledger, so neither direction
costs anything beyond the compiled coordinate synthesis. -/
theorem squareRootLargestDefectLinear_iff_canonicalDowncrossLinear :
    SquareRootLargestDefectLinearBound ↔
      SquareRootCanonicalDowncrossLinearBound := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, fun R hR => ?_⟩
    rw [lowWheelCanonicalDowncrossLedger_eq_largestDefectLedger]
    exact hbound R hR
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, fun R hR => ?_⟩
    rw [← lowWheelCanonicalDowncrossLedger_eq_largestDefectLedger]
    exact hbound R hR

/-- **Therefore the largest-prime defect linear bound implies the Riemann
hypothesis.**  It is stronger than the epsilon-loss seam used below. -/
theorem riemannHypothesis_of_largestDefectLinear
    (h : SquareRootLargestDefectLinearBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonicalDowncrossLinear
    (squareRootLargestDefectLinear_iff_canonicalDowncrossLinear.mp h)

/-! ## Exact pointwise geometry -/

/-- If an active fixed-prime cofactor/quotient toggle still satisfies the
physical carrier inequalities, then it belongs to the actual finite physical
state set.  This fixed-prime closure is used below in both the removal and
insertion directions. -/
private theorem lowWheelCofactorQuotientToggleAt_mem_physical_of_carrier
    {R p : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (hp : p.Prime)
    (hx : x ∈ lowWheelCanonicalPhysicalStateSet R t)
    (hactive : p ∣ x.1 ∨ p ∣ x.2)
    (hmate : LowWheelTransportPairCarrier R t
      (lowWheelCofactorQuotientToggleAt p x)) :
    lowWheelCofactorQuotientToggleAt p x ∈
      lowWheelCanonicalPhysicalStateSet R t := by
  rcases x with ⟨c, k⟩
  have hsq : Squarefree c :=
    lowWheelCanonicalPhysicalStateSet_squarefree (c, k) hx
  have hsquare :
      Squarefree (lowWheelCofactorQuotientToggleAt p (c, k)).1 := by
    by_cases hpc : p ∣ c
    · have hd : c / p ∣ c :=
        ⟨p, (Nat.div_mul_cancel hpc).symm⟩
      have hsqd : Squarefree (c / p) := hsq.squarefree_of_dvd hd
      unfold lowWheelCofactorQuotientToggleAt
      rw [if_pos hpc]
      exact hsqd
    · have hpk : p ∣ k := hactive.resolve_left hpc
      have hmuC : μ c ≠ 0 :=
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
      have hmu := moebius_prime_mul hp hpc
      have hmuNe : μ (p * c) ≠ 0 := by
        rw [hmu]
        exact neg_ne_zero.mpr hmuC
      have hsqp : Squarefree (p * c) :=
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuNe
      unfold lowWheelCofactorQuotientToggleAt
      rw [if_neg hpc, if_pos hpk]
      simpa [Nat.mul_comm] using hsqp
  have hrange := lowWheelTransportPairCarrier_mem_ranges hmate
  apply mem_lowWheelCanonicalPhysicalStateSet.mpr
  exact ⟨hrange.1, hrange.2, hsquare, hmate⟩

/-- **Exact largest-prime defect geometry.**

If a state survives under the completed largest-prime Othello mate only because
its raw mate leaves the physical carrier, then the largest prime
`q = P⁺(c*k)` can only be moving from the quotient into the cofactor.  It is
prime, is absent from the cofactor, divides the quotient, and the failed
insertion is exactly the root-downcross `P(t) * (k/q) ≤ R`. -/
theorem lowWheelLargestDefect_geometry
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelLargestDefectPart R t) :
    let q := lowWheelLargestCofactorQuotientPivot x
    q.Prime ∧
      ¬ q ∣ x.1 ∧
      q ∣ x.2 ∧
      primeFaceProduct t * (x.2 / q) ≤ R := by
  rcases x with ⟨c, k⟩
  dsimp
  have hdata := Finset.mem_filter.mp hx
  have hxF : (c, k) ∈ lowWheelCanonicalPhysicalStateSet R t := hdata.1
  have hprod : c * k ≠ 1 := hdata.2.1
  have hnotMate :
      lowWheelLargestCofactorQuotientToggle (c, k) ∉
        lowWheelCanonicalPhysicalStateSet R t := hdata.2.2
  have hqPrime :
      (lowWheelLargestCofactorQuotientPivot (c, k)).Prime :=
    lowWheelLargestCofactorQuotientPivot_prime ht hxF hprod
  have hactive :
      lowWheelLargestCofactorQuotientPivot (c, k) ∣ c ∨
        lowWheelLargestCofactorQuotientPivot (c, k) ∣ k :=
    lowWheelLargestCofactorQuotientPivot_active ht hxF hprod
  have hcarrier : LowWheelTransportPairCarrier R t (c, k) :=
    (mem_lowWheelCanonicalPhysicalStateSet.mp hxF).2.2.2
  have hnotC : ¬ lowWheelLargestCofactorQuotientPivot (c, k) ∣ c := by
    intro hqc
    apply hnotMate
    unfold lowWheelLargestCofactorQuotientToggle
    exact lowWheelCofactorQuotientToggleAt_mem_physical_of_carrier
      hqPrime hxF hactive
      (lowWheelCofactorQuotientToggleAt_preserves_of_dvd_cofactor
        hqPrime hcarrier hqc)
  have hqK : lowWheelLargestCofactorQuotientPivot (c, k) ∣ k :=
    hactive.resolve_left hnotC
  refine ⟨hqPrime, hnotC, hqK, ?_⟩
  rcases lowWheelCofactorQuotientToggleAt_preserves_or_downcross_of_dvd_quotient
      hqPrime hcarrier hnotC hqK with hmate | hdown
  · exfalso
    apply hnotMate
    unfold lowWheelLargestCofactorQuotientToggle
    exact lowWheelCofactorQuotientToggleAt_mem_physical_of_carrier
      hqPrime hxF hactive hmate
  · exact hdown

/-! ## Root-scale split of the stable defect -/

/-- Largest-defect states whose largest invariant prime factor is at most the
root cutoff. -/
def lowWheelLargestDefectLowPart
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelLargestDefectPart R t).filter fun x =>
    lowWheelLargestCofactorQuotientPivot x ≤ R

/-- Largest-defect states whose largest invariant prime factor lies strictly
above the root cutoff. -/
def lowWheelLargestDefectHighPart
    (R : ℕ) (t : Finset ℕ) : Finset LowWheelCofactorQuotientState :=
  (lowWheelLargestDefectPart R t).filter fun x =>
    R < lowWheelLargestCofactorQuotientPivot x

@[simp] theorem mem_lowWheelLargestDefectLowPart
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelLargestDefectLowPart R t ↔
      x ∈ lowWheelLargestDefectPart R t ∧
        lowWheelLargestCofactorQuotientPivot x ≤ R := by
  simp [lowWheelLargestDefectLowPart]

@[simp] theorem mem_lowWheelLargestDefectHighPart
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState} :
    x ∈ lowWheelLargestDefectHighPart R t ↔
      x ∈ lowWheelLargestDefectPart R t ∧
        R < lowWheelLargestCofactorQuotientPivot x := by
  simp [lowWheelLargestDefectHighPart]

/-- The low- and high-largest-prime regimes exhaust the defect carrier. -/
theorem lowWheelLargestDefectPart_eq_low_union_high
    (R : ℕ) (t : Finset ℕ) :
    lowWheelLargestDefectLowPart R t ∪
        lowWheelLargestDefectHighPart R t =
      lowWheelLargestDefectPart R t := by
  classical
  ext x
  simp only [Finset.mem_union, mem_lowWheelLargestDefectLowPart,
    mem_lowWheelLargestDefectHighPart]
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    by_cases hq : lowWheelLargestCofactorQuotientPivot x ≤ R
    · exact Or.inl ⟨hx, hq⟩
    · exact Or.inr ⟨hx, Nat.lt_of_not_ge hq⟩

/-- The two root-scale regimes are disjoint. -/
theorem lowWheelLargestDefectLow_disjoint_high
    (R : ℕ) (t : Finset ℕ) :
    Disjoint (lowWheelLargestDefectLowPart R t)
      (lowWheelLargestDefectHighPart R t) := by
  classical
  rw [Finset.disjoint_left]
  intro x hlow hhigh
  have hqLow := (mem_lowWheelLargestDefectLowPart.mp hlow).2
  have hqHigh := (mem_lowWheelLargestDefectHighPart.mp hhigh).2
  omega

/-- Signed low-largest-prime part of the global defect ledger. -/
def lowWheelLargestDefectLowLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelLargestDefectLowPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- Signed high-largest-prime part of the global defect ledger. -/
def lowWheelLargestDefectHighLedger (R : ℕ) : ℂ :=
  ∑ t ∈ (primesUpTo R).powerset,
    ∑ x ∈ lowWheelLargestDefectHighPart R t,
      canonicalMoebiusWeight x.1 * (booleanCubeSign t : ℂ)

/-- **Exact `q <= R` / `q > R` split of the largest-prime defect ledger.** -/
theorem lowWheelLargestDefectLedger_eq_low_add_high
    (R : ℕ) :
    lowWheelLargestDefectLedger R =
      lowWheelLargestDefectLowLedger R + lowWheelLargestDefectHighLedger R := by
  classical
  unfold lowWheelLargestDefectLedger lowWheelLargestDefectLowLedger
    lowWheelLargestDefectHighLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [← Finset.sum_union (lowWheelLargestDefectLow_disjoint_high R t),
    lowWheelLargestDefectPart_eq_low_union_high R t]

/-- **Low-side geometry.**  Below the root, the distinguished pivot is not just
low: it dominates every prime divisor of the invariant product.  Thus `c*k` is
entirely `R`-smooth, while the failed insertion is still the exact root
boundary `P(t)*(k/q) <= R`. -/
theorem lowWheelLargestDefectLow_geometry
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelLargestDefectLowPart R t) :
    let q := lowWheelLargestCofactorQuotientPivot x
    q.Prime ∧
      q ≤ R ∧
      ¬ q ∣ x.1 ∧
      q ∣ x.2 ∧
      primeFaceProduct t * (x.2 / q) ≤ R ∧
      (∀ p : ℕ, p.Prime → p ∣ x.1 * x.2 → p ≤ R) := by
  rcases mem_lowWheelLargestDefectLowPart.mp hx with ⟨hdefect, hqR⟩
  have hgeom := lowWheelLargestDefect_geometry ht hdefect
  dsimp at hgeom ⊢
  rcases hgeom with ⟨hqPrime, hqC, hqK, hdown⟩
  refine ⟨hqPrime, hqR, hqC, hqK, hdown, ?_⟩
  intro p hp hpdvd
  have hdefData := Finset.mem_filter.mp hdefect
  have hxPhys := hdefData.1
  have hprodNe : x.1 * x.2 ≠ 1 := hdefData.2.1
  have hphysData := mem_lowWheelCanonicalPhysicalStateSet.mp hxPhys
  have hcPos : 0 < x.1 := by
    have hc1 := (Finset.mem_Ico.mp hphysData.1).1
    omega
  have hkPos : 0 < x.2 := by
    have hk1 := (Finset.mem_Icc.mp hphysData.2.1).1
    omega
  have hprodPos : 0 < x.1 * x.2 := Nat.mul_pos hcPos hkPos
  have hprodGt : 1 < x.1 * x.2 := by omega
  have hpTop :=
    CanonicalGapAncestryBridge.prime_dvd_le_canonicalLargestPrimeFactor
      hprodGt hp hpdvd
  have hpQ : p ≤ lowWheelLargestCofactorQuotientPivot x := by
    simpa [lowWheelLargestCofactorQuotientPivot] using hpTop
  exact hpQ.trans hqR

/-- **High-side geometry on the existing high-transport coordinate system.**
A high-largest-prime defect carries a genuine prime `q > R` dividing the whole
quotient `k`, but the state does not collapse to `(1,q)`.  Its original
`(c,t,k)` coordinates lie in the exact quotient interval of
`lowWheelTransportTripleLedger`, i.e. the pre-existing prime-count-free high
transport carrier. -/
theorem lowWheelLargestDefectHigh_geometry
    {R : ℕ} {t : Finset ℕ} {x : LowWheelCofactorQuotientState}
    (ht : t ∈ (primesUpTo R).powerset)
    (hx : x ∈ lowWheelLargestDefectHighPart R t) :
    let q := lowWheelLargestCofactorQuotientPivot x
    q.Prime ∧
      R < q ∧
      ¬ q ∣ x.1 ∧
      q ∣ x.2 ∧
      primeFaceProduct t * (x.2 / q) ≤ R ∧
      x.1 ∈ Finset.Ico 1 R ∧
      x.2 ∈ Finset.Ioc
        (R / primeFaceProduct t)
        (squareRootEndpoint R / (x.1 * primeFaceProduct t)) := by
  rcases mem_lowWheelLargestDefectHighPart.mp hx with ⟨hdefect, hRq⟩
  have hgeom := lowWheelLargestDefect_geometry ht hdefect
  dsimp at hgeom ⊢
  rcases hgeom with ⟨hqPrime, hqC, hqK, hdown⟩
  have hdefData := Finset.mem_filter.mp hdefect
  have hxPhys := hdefData.1
  have hphysData := mem_lowWheelCanonicalPhysicalStateSet.mp hxPhys
  have hcRange : x.1 ∈ Finset.Ico 1 R := hphysData.1
  have hcPos : 0 < x.1 := by
    have hc1 := (Finset.mem_Ico.mp hcRange).1
    omega
  have hcarrier := hphysData.2.2.2
  have hkInterval :
      x.2 ∈ Finset.Ioc
        (R / primeFaceProduct t)
        (squareRootEndpoint R / (x.1 * primeFaceProduct t)) := by
    apply (mem_lowWheelTransport_quotientInterval_iff hcPos ht).2
    exact ⟨hcarrier.2.2.1, hcarrier.2.2.2⟩
  exact ⟨hqPrime, hRq, hqC, hqK, hdown, hcRange, hkInterval⟩

/-- Open RH-scale target for the smooth (`q <= R`) side. -/
def LargestDefectLowEpsilonBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 3 ≤ R →
        ‖lowWheelLargestDefectLowLedger R‖ ≤
          C * Real.rpow (R : ℝ) (1 + ε)

/-- Open RH-scale target for the post-root (`q > R`) side. -/
def LargestDefectHighEpsilonBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 3 ≤ R →
        ‖lowWheelLargestDefectHighLedger R‖ ≤
          C * Real.rpow (R : ℝ) (1 + ε)

end RHLean.Proof
