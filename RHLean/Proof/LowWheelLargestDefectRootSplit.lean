import Mathlib
import RHLean.Proof.LowWheelLargestDefectSeamEquivalence
import RHLean.Proof.LowWheelTransportTripleCarrier

/-!
# Largest-prime stable defect split at the root scale

The largest-prime stable defect is the terminal signed seam itself, so this
module does not try to bound it by cardinality or by an `O(R)` estimate.
Instead it performs the exact root-scale split of its largest-prime pivot

`q = P⁺(c*k)`

before any norm:

* `q <= R`: every prime factor of the invariant product `c*k` is low, so the
  state is genuinely smooth and the only failure is the root-downcross already
  isolated by `lowWheelLargestDefect_geometry`;
* `R < q`: the quotient contains a genuine post-root prime factor.  This does
  **not** collapse the state to the old terminal `(1,q)` carrier.  The original
  `(c,t,k)` state remains in the existing prime-count-free high-transport triple
  geometry, with `q` retained only as a distinguished high divisor of `k`.

The final quantitative scale is therefore left as two explicit open
`R^(1+epsilon)` propositions.  No claim that either proposition is proved is
made here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

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
