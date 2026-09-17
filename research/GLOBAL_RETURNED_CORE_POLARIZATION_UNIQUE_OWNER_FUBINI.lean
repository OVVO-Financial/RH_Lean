import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION»
import «research.GLOBAL_RETURNED_CORE_DESCENDING_PAIR_OWNER»
import «research.GLOBAL_RETURNED_CORE_ARBITRARY_FRESH_PRIME_DESCENT»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_GREATEST_OWNER_FUBINI»

/-!
# Unique greatest-owner Fubini on the full Dirichlet polarization carrier

The clipped population must never be removed from the polarization and estimated
separately.  Therefore the natural induction carrier is not the admitted square:
it is the full p-free lower-signature base square.

Every off-diagonal pair `(a,b)` in one `(p,sig)` base cell has a unique greatest
fresh prime `r`.  Because both endpoints have the same lower-p signature and are
p-free, every fresh prime is strictly larger than `p`, whether either endpoint
is admitted or clipped.  Stripping such an `r` keeps both endpoints in the same
base cell.  Thus the full Dirichlet polarization is closed under greatest-owner
descent without manufacturing a clipped residual class.

The owner fibres are disjoint and give exact signed Fubini identities.  The
clipped/clipped atoms remain present in the carrier but are already pointwise
zero by `GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION`.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Full off-diagonal pair carrier of one p-free lower-signature base cell. -/
def lowOwnerFirstOwnerBaseOffDiagonalPairCarrier
    (R p : ℕ) (sig : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerFirstOwnerBaseFiber R p sig).product
    (lowOwnerFirstOwnerBaseFiber R p sig)).filter fun ab => ab.1 ≠ ab.2

/-- Positive-lag form of the same carrier. -/
def lowOwnerFirstOwnerBasePositivePairCarrier
    (R p : ℕ) (sig : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerFirstOwnerBaseFiber R p sig).product
    (lowOwnerFirstOwnerBaseFiber R p sig)).filter fun ab => ab.1 < ab.2

/-- Greatest-owner fibre on the full polarization carrier. -/
def lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerBaseOffDiagonalPairCarrier R p sig).filter fun ab =>
    IsSquarefreePairGreatestFreshPrimeOwner r ab.1 ab.2

/-- Positive-lag part of one full-polarization owner fibre. -/
def lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r).filter
    (fun ab => ab.1 < ab.2)

/-- Any fresh prime of two sites in the same base cell lies strictly above the
current first owner p.  Admitted/clipped status is irrelevant. -/
theorem lowOwnerFirstOwnerBasePair_freshPrime_gt_owner
    {R p r a b : ℕ} {sig : Finset ℕ}
    (_hp : p.Prime)
    (ha : a ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hb : b ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hrFresh : r ∈ squarefreePairFreshPrimeSet a b) :
    p < r := by
  rcases Finset.mem_filter.mp ha with ⟨haCar, haData⟩
  rcases Finset.mem_filter.mp hb with ⟨hbCar, hbData⟩
  have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar).2
  have hbPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hbCar).2
  have hrPrime := (freshPrime_of_nonzeroPhysicalPair haCar hbCar hrFresh).1
  have hxor :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor
      hrPrime haPos hbPos).1 hrFresh
  by_contra hnot
  have hrle : r ≤ p := Nat.le_of_not_gt hnot
  by_cases hrp : r = p
  · subst r
    rcases hxor with h | h
    · exact haData.2 h.1
    · exact hbData.2 h.1
  · have hrlt : r < p := lt_of_le_of_ne hrle hrp
    have hsigEq : squarefreeLowerPrimeSignature p a =
        squarefreeLowerPrimeSignature p b := by
      rw [haData.1, hbData.1]
    rcases hxor with h | h
    · have hrFaceA : r ∈ squarefreePrimeFace a :=
        (prime_mem_squarefreePrimeFace_iff_dvd_public hrPrime haPos).2 h.1
      have hrLowA : r ∈ squarefreeLowerPrimeSignature p a :=
        Finset.mem_filter.mpr ⟨hrFaceA, hrlt⟩
      have hrLowB : r ∈ squarefreeLowerPrimeSignature p b := by
        rw [← hsigEq]
        exact hrLowA
      have hrFaceB := (Finset.mem_filter.mp hrLowB).1
      have hrDivB :=
        (prime_mem_squarefreePrimeFace_iff_dvd_public hrPrime hbPos).1 hrFaceB
      exact h.2 hrDivB
    · have hrFaceB : r ∈ squarefreePrimeFace b :=
        (prime_mem_squarefreePrimeFace_iff_dvd_public hrPrime hbPos).2 h.1
      have hrLowB : r ∈ squarefreeLowerPrimeSignature p b :=
        Finset.mem_filter.mpr ⟨hrFaceB, hrlt⟩
      have hrLowA : r ∈ squarefreeLowerPrimeSignature p a := by
        rw [hsigEq]
        exact hrLowB
      have hrFaceA := (Finset.mem_filter.mp hrLowA).1
      have hrDivA :=
        (prime_mem_squarefreePrimeFace_iff_dvd_public hrPrime haPos).1 hrFaceA
      exact h.2 hrDivA

/-- Stripping a larger fresh prime from a base-cell site keeps it in the same
base cell.  No admitted p-child hypothesis is needed. -/
theorem lowOwnerFirstOwner_primeParent_mem_same_base
    {R p r a : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (ha : a ∈ lowOwnerFirstOwnerBaseFiber R p sig) :
    squarefreePrimeFamilyParent r a ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
  rcases Finset.mem_filter.mp ha with ⟨haCar, haData⟩
  rcases Finset.mem_filter.mp haCar with ⟨haIcc, hmuA⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar with
    ⟨haSq, haPos⟩
  let u := squarefreePrimeFamilyParent r a
  have huPos : 0 < u := squarefreePrimeFamilyParent_pos_public hr haPos
  have huDvd : u ∣ a := squarefreePrimeFamilyParent_dvd_public r a
  have hua : u ≤ a := Nat.le_of_dvd haPos huDvd
  have huX : u ≤ squareRootEndpoint R :=
    hua.trans (Finset.mem_Icc.mp haIcc).2
  have hmuU : realMoebiusStep u ≠ 0 := by
    by_cases hra : r ∣ a
    · have huEq : u = a / r := by
        simp [u, squarefreePrimeFamilyParent, hra]
      have hrnot : ¬ r ∣ a / r :=
        prime_not_dvd_div_of_squarefree hr haSq hra
      have hsign := realMoebiusStep_mul_prime_eq_neg hr hrnot
      have heq : r * (a / r) = a := Nat.mul_div_cancel' hra
      intro hz
      have hzdiv : realMoebiusStep (a / r) = 0 := by
        simpa [huEq] using hz
      apply hmuA
      rw [← heq, hsign, hzdiv, neg_zero]
    · have huEq : u = a := by
        simp [u, squarefreePrimeFamilyParent, hra]
      simpa [huEq] using hmuA
  have huCar : u ∈ lowOwnerNonzeroMobiusCarrier R :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, huX⟩, hmuU⟩
  have hsigU : squarefreeLowerPrimeSignature p u = sig := by
    by_cases hra : r ∣ a
    · have huEq : u = a / r := by
        simp [u, squarefreePrimeFamilyParent, hra]
      have heq : r * u = a := by
        rw [huEq]
        exact Nat.mul_div_cancel' hra
      have hlower := squarefreeLowerPrimeSignature_mul_larger_prime
        (p := p) (r := r) (a := u) hr hpr huPos
      calc
        squarefreeLowerPrimeSignature p u =
            squarefreeLowerPrimeSignature p (r * u) := hlower.symm
        _ = squarefreeLowerPrimeSignature p a := by rw [heq]
        _ = sig := haData.1
    · have huEq : u = a := by
        simp [u, squarefreePrimeFamilyParent, hra]
      simpa [huEq] using haData.1
  have hpne : p ≠ r := by omega
  have hpFreeU : ¬ p ∣ u := by
    intro hpu
    have hiff := prime_dvd_squarefreePrimeFamilyParent_iff_of_ne_public
      (p := r) (q := p) (n := a) hr hp hpne
    have hpuParent : p ∣ squarefreePrimeFamilyParent r a := by
      simpa [u] using hpu
    exact haData.2 (hiff.mp hpuParent)
  exact Finset.mem_filter.mpr ⟨huCar, ⟨hsigU, hpFreeU⟩⟩

/-- Stripping any fresh coordinate of a full-polarization pair returns both
coordinates to the same base cell. -/
theorem lowOwnerFirstOwnerBasePair_freshPrime_parents_mem_same_cell
    {R p r a b : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (ha : a ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hb : b ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hrFresh : r ∈ squarefreePairFreshPrimeSet a b) :
    let ua := squarefreePrimeFamilyParent r a
    let ub := squarefreePrimeFamilyParent r b
    ua ∈ lowOwnerFirstOwnerBaseFiber R p sig ∧
      ub ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
  have hgt := lowOwnerFirstOwnerBasePair_freshPrime_gt_owner
    hp ha hb hrFresh
  have haCar := (Finset.mem_filter.mp ha).1
  have hbCar := (Finset.mem_filter.mp hb).1
  have hrPrime := (freshPrime_of_nonzeroPhysicalPair haCar hbCar hrFresh).1
  dsimp only
  exact ⟨lowOwnerFirstOwner_primeParent_mem_same_base hp hrPrime hgt ha,
    lowOwnerFirstOwner_primeParent_mem_same_base hp hrPrime hgt hb⟩

/-- Every full-base off-diagonal pair has a unique greatest fresh owner on the
physical prime clock above p. -/
theorem lowOwnerFirstOwnerBaseOffDiagonalPair_has_greatestOwner
    {R p : ℕ} {sig : Finset ℕ} {a b : ℕ}
    (hp : p.Prime)
    (hab : (a, b) ∈ lowOwnerFirstOwnerBaseOffDiagonalPairCarrier R p sig) :
    ∃ r ∈ lowOwnerRevealedPrimesAbove R p,
      IsSquarefreePairGreatestFreshPrimeOwner r a b := by
  rcases Finset.mem_filter.mp hab with ⟨hpair, hne⟩
  rcases Finset.mem_product.mp hpair with ⟨ha, hb⟩
  have haCar := (Finset.mem_filter.mp ha).1
  have hbCar := (Finset.mem_filter.mp hb).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar with ⟨haSq, _haPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hbCar with ⟨hbSq, _hbPos⟩
  have hleast := squarefreePairFreshPrimeOwner_isOwner haSq hbSq hne
  let S := squarefreePairFreshPrimeSet a b
  have hSnonempty : S.Nonempty := ⟨squarefreePairFreshPrimeOwner a b, hleast.1⟩
  let r := S.max' hSnonempty
  have hrFresh : r ∈ S := Finset.max'_mem S hSnonempty
  have hrGreatest : ∀ q ∈ S, q ≤ r := by
    intro q hq
    exact Finset.le_max' S q hq
  have howner : IsSquarefreePairGreatestFreshPrimeOwner r a b :=
    ⟨hrFresh, hrGreatest⟩
  have hrData := freshPrime_of_nonzeroPhysicalPair haCar hbCar hrFresh
  have hpr := lowOwnerFirstOwnerBasePair_freshPrime_gt_owner hp ha hb hrFresh
  exact ⟨r, Finset.mem_filter.mpr ⟨mem_primesUpTo.mpr hrData, hpr⟩, howner⟩

/-- Full-polarization greatest-owner fibres are pairwise disjoint. -/
theorem lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber_pairwiseDisjoint
    (R p : ℕ) (sig : Finset ℕ) :
    Set.PairwiseDisjoint (↑(lowOwnerRevealedPrimesAbove R p))
      (lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig) := by
  intro r _hr s _hs hrs
  change Disjoint
    (lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r)
    (lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig s)
  rw [Finset.disjoint_left]
  intro ab har has
  have hro := (Finset.mem_filter.mp har).2
  have hso := (Finset.mem_filter.mp has).2
  exact hrs (squarefreePairGreatestFreshPrimeOwner_unique hro hso)

/-- Exact off-diagonal carrier partition by the unique greatest owner. -/
theorem lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber_biUnion
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (lowOwnerRevealedPrimesAbove R p).biUnion
        (lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig) =
      lowOwnerFirstOwnerBaseOffDiagonalPairCarrier R p sig := by
  ext ab
  rcases ab with ⟨a, b⟩
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨r, _hr, hab⟩
    exact (Finset.mem_filter.mp hab).1
  · intro hab
    rcases lowOwnerFirstOwnerBaseOffDiagonalPair_has_greatestOwner hp hab with
      ⟨r, hr, howner⟩
    exact Finset.mem_biUnion.mpr
      ⟨r, hr, Finset.mem_filter.mpr ⟨hab, howner⟩⟩

/-- Exact signed Fubini for arbitrary pair weights on the full polarization
carrier. -/
theorem sum_lowOwnerFirstOwnerBaseOffDiagonal_eq_sum_polarizationOwnerFibers
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime)
    (f : ℕ × ℕ → ℝ) :
    (∑ ab ∈ lowOwnerFirstOwnerBaseOffDiagonalPairCarrier R p sig, f ab) =
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        ∑ ab ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r,
          f ab := by
  rw [← lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber_biUnion hp]
  exact Finset.sum_biUnion
    (lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber_pairwiseDisjoint
      R p sig)

/-- Positive owner fibres are pairwise disjoint as well. -/
theorem lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber_pairwiseDisjoint
    (R p : ℕ) (sig : Finset ℕ) :
    Set.PairwiseDisjoint (↑(lowOwnerRevealedPrimesAbove R p))
      (lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber R p sig) := by
  intro r _hr s _hs hrs
  change Disjoint
    (lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber R p sig r)
    (lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber R p sig s)
  rw [Finset.disjoint_left]
  intro ab har has
  have hro := (Finset.mem_filter.mp (Finset.mem_filter.mp har).1).2
  have hso := (Finset.mem_filter.mp (Finset.mem_filter.mp has).1).2
  exact hrs (squarefreePairGreatestFreshPrimeOwner_unique hro hso)

/-- Exact positive-lag partition on the full polarization carrier. -/
theorem lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber_biUnion
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (lowOwnerRevealedPrimesAbove R p).biUnion
        (lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber R p sig) =
      lowOwnerFirstOwnerBasePositivePairCarrier R p sig := by
  ext ab
  rcases ab with ⟨a, b⟩
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨r, _hr, hab⟩
    rcases Finset.mem_filter.mp hab with ⟨howner, hlt⟩
    have hbase := (Finset.mem_filter.mp howner).1
    have hpair := (Finset.mem_filter.mp hbase).1
    exact Finset.mem_filter.mpr ⟨hpair, hlt⟩
  · intro hab
    rcases Finset.mem_filter.mp hab with ⟨hpair, hlt⟩
    have hoff : (a, b) ∈ lowOwnerFirstOwnerBaseOffDiagonalPairCarrier R p sig :=
      Finset.mem_filter.mpr ⟨hpair, ne_of_lt hlt⟩
    rcases lowOwnerFirstOwnerBaseOffDiagonalPair_has_greatestOwner hp hoff with
      ⟨r, hr, howner⟩
    exact Finset.mem_biUnion.mpr
      ⟨r, hr,
        Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hoff, howner⟩, hlt⟩⟩

/-- **Full-polarization positive-lag signed Fubini.** -/
theorem sum_lowOwnerFirstOwnerBasePositive_eq_sum_polarizationOwnerFibers
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime)
    (f : ℕ × ℕ → ℝ) :
    (∑ ab ∈ lowOwnerFirstOwnerBasePositivePairCarrier R p sig, f ab) =
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        ∑ ab ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber R p sig r,
          f ab := by
  rw [← lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber_biUnion hp]
  exact Finset.sum_biUnion
    (lowOwnerFirstOwnerPolarizationGreatestOwnerPositiveFiber_pairwiseDisjoint
      R p sig)

end RHLean.Proof