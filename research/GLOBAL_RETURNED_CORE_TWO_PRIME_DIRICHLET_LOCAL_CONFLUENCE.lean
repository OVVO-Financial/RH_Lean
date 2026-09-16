import Mathlib
import «research.GLOBAL_RETURNED_CORE_ARBITRARY_FRESH_PRIME_DESCENT»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_DIRECT_SUM_CONTRACTION»
import «research.GLOBAL_RETURNED_CORE_VIRTUAL_OWNER_CORNER_CLASSIFICATION»

/-!
# Two-prime local confluence on the completed signed-energy state

The unrestricted prime-strip calculus is abelian.  The only possible failure of
confluence comes from restricting the arithmetic to the physical clock.  This
file therefore separates the two issues.

First, distinct prime strips commute exactly on every endpoint.  We then package
the completed parent pair together with all data that the signed telescope and
its reciprocal-energy consumer actually use:

* both lower-p signatures;
* the admitted / clipped-Excess / outside Dirichlet class of each coordinate;
* the Mobius pair weight;
* the Dirichlet incidence pair coefficient and full polarization atom;
* the owner-labelled Euler pair coefficient `C` for any later owner `t`;
* the reciprocal pair energy of the current parent.

The resulting state is exactly invariant under swapping two distinct prime
strips.  In particular clipped Excess is a live class, distinct from outside;
only outside is Dirichlet zero.

Finally, on squarefree positive support where both primes are fresh, composing
the already-compiled arbitrary-prime descent twice shows that the signed pair
returns to its original parity and that reciprocal energy acquires the exact
atom multiplier `1/r^2 * 1/s^2`, independent of strip order.

This is the atom-level local diamond.  It deliberately does not replace the
separate block-level theorem still needed for path-independent products of exact
child multiplicities `m/r^2`.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The three Dirichlet states of one first-owner parent coordinate.  Clipped
Excess remains a live state; it is not identified with outside. -/
inductive LowOwnerCompletedSiteClass where
  | admitted
  | clippedExcess
  | outside
  deriving DecidableEq, Repr

/-- Classification of a parent site relative to the current first owner `p`. -/
def lowOwnerCompletedSiteClass (R p n : ℕ) : LowOwnerCompletedSiteClass :=
  if squareRootEndpoint R < n then
    .outside
  else if p * n ≤ squareRootEndpoint R then
    .admitted
  else
    .clippedExcess

@[simp] theorem lowOwnerCompletedSiteClass_eq_outside
    {R p n : ℕ} (hout : squareRootEndpoint R < n) :
    lowOwnerCompletedSiteClass R p n = .outside := by
  simp [lowOwnerCompletedSiteClass, hout]

@[simp] theorem lowOwnerCompletedSiteClass_eq_admitted
    {R p n : ℕ} (hn : n ≤ squareRootEndpoint R)
    (hchild : p * n ≤ squareRootEndpoint R) :
    lowOwnerCompletedSiteClass R p n = .admitted := by
  simp [lowOwnerCompletedSiteClass, Nat.not_lt.mpr hn, hchild]

@[simp] theorem lowOwnerCompletedSiteClass_eq_clippedExcess
    {R p n : ℕ} (hn : n ≤ squareRootEndpoint R)
    (hclip : squareRootEndpoint R < p * n) :
    lowOwnerCompletedSiteClass R p n = .clippedExcess := by
  have hnot : ¬ p * n ≤ squareRootEndpoint R := Nat.not_le.mpr hclip
  simp [lowOwnerCompletedSiteClass, Nat.not_lt.mpr hn, hnot]

/-- Distinct prime-removal operations commute on one endpoint. -/
theorem squarefreePrimeFamilyParent_comm_of_prime_ne
    {r s n : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) :
    squarefreePrimeFamilyParent r (squarefreePrimeFamilyParent s n) =
      squarefreePrimeFamilyParent s (squarefreePrimeFamilyParent r n) := by
  have hsr : s ≠ r := Ne.symm hrs
  by_cases hrn : r ∣ n
  · by_cases hsn : s ∣ n
    · have hrDiv : r ∣ n / s := by
        have h :=
          (prime_dvd_squarefreePrimeFamilyParent_iff_of_ne_public
            hs hr hrs).2 hrn
        simpa [squarefreePrimeFamilyParent, hsn] using h
      have hsDiv : s ∣ n / r := by
        have h :=
          (prime_dvd_squarefreePrimeFamilyParent_iff_of_ne_public
            hr hs hsr).2 hsn
        simpa [squarefreePrimeFamilyParent, hrn] using h
      simp [squarefreePrimeFamilyParent, hrn, hsn, hrDiv, hsDiv,
        Nat.div_div_eq_div_mul, Nat.mul_comm]
    · have hsNot : ¬ s ∣ n / r := by
        intro hdiv
        have h :=
          (prime_dvd_squarefreePrimeFamilyParent_iff_of_ne_public
            hr hs hsr).1
            (by simpa [squarefreePrimeFamilyParent, hrn] using hdiv)
        exact hsn h
      simp [squarefreePrimeFamilyParent, hrn, hsn, hsNot]
  · by_cases hsn : s ∣ n
    · have hrNot : ¬ r ∣ n / s := by
        intro hdiv
        have h :=
          (prime_dvd_squarefreePrimeFamilyParent_iff_of_ne_public
            hs hr hrs).1
            (by simpa [squarefreePrimeFamilyParent, hsn] using hdiv)
        exact hrn h
      simp [squarefreePrimeFamilyParent, hrn, hsn, hrNot]
    · simp [squarefreePrimeFamilyParent, hrn, hsn]

/-- Apply two prime strips coordinatewise, without reorienting the pair. -/
def lowOwnerTwoPrimeParent
    (r s : ℕ) (mn : ℕ × ℕ) : ℕ × ℕ :=
  (squarefreePrimeFamilyParent s (squarefreePrimeFamilyParent r mn.1),
    squarefreePrimeFamilyParent s (squarefreePrimeFamilyParent r mn.2))

/-- The two-prime parent is independent of strip order. -/
theorem lowOwnerTwoPrimeParent_comm
    {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (mn : ℕ × ℕ) :
    lowOwnerTwoPrimeParent r s mn = lowOwnerTwoPrimeParent s r mn := by
  apply Prod.ext
  · exact squarefreePrimeFamilyParent_comm_of_prime_ne hr hs hrs
  · exact squarefreePrimeFamilyParent_comm_of_prime_ne hr hs hrs

/-- Full completed state seen by the signed telescope and reciprocal-energy
consumer after a sequence of prime strips. -/
structure LowOwnerCompletedSignedEnergyState where
  parent : ℕ × ℕ
  leftLowerSignature : Finset ℕ
  rightLowerSignature : Finset ℕ
  leftClass : LowOwnerCompletedSiteClass
  rightClass : LowOwnerCompletedSiteClass
  moebiusPairWeight : ℝ
  dirichletIncidencePairCoefficient : ℝ
  dirichletPolarizationAtom : ℝ
  eulerPairCoefficient : ℝ
  reciprocalPairEnergy : ℝ
  deriving Repr

/-- Read the complete signed-plus-energy state at a current parent pair.  `t` is
an arbitrary later owner whose Euler coefficient is retained. -/
def lowOwnerCompletedSignedEnergyState
    (R p t : ℕ) (parent : ℕ × ℕ) : LowOwnerCompletedSignedEnergyState :=
  {
    parent := parent
    leftLowerSignature := squarefreeLowerPrimeSignature p parent.1
    rightLowerSignature := squarefreeLowerPrimeSignature p parent.2
    leftClass := lowOwnerCompletedSiteClass R p parent.1
    rightClass := lowOwnerCompletedSiteClass R p parent.2
    moebiusPairWeight := realMoebiusStep parent.1 * realMoebiusStep parent.2
    dirichletIncidencePairCoefficient :=
      lowOwnerFirstOwnerDirichletIncidenceSite R p parent.1 *
        lowOwnerFirstOwnerDirichletIncidenceSite R p parent.2
    dirichletPolarizationAtom :=
      lowOwnerFirstOwnerDirichletPolarizationAtom R p parent
    eulerPairCoefficient := lowOwnerThresholdEulerPairCoefficient R p t parent
    reciprocalPairEnergy := postRootCovarianceReciprocalPairEnergy parent
  }

/-- **Atom-level two-prime Dirichlet diamond.**  Swapping two distinct prime
strips preserves the entire completed signed-plus-energy state, including the
clipped-versus-outside distinction, Dirichlet polarization, Euler `C`, and
current reciprocal parent energy. -/
theorem lowOwnerCompletedSignedEnergyState_twoPrime_comm
    {R p t r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (mn : ℕ × ℕ) :
    lowOwnerCompletedSignedEnergyState R p t (lowOwnerTwoPrimeParent r s mn) =
      lowOwnerCompletedSignedEnergyState R p t (lowOwnerTwoPrimeParent s r mn) := by
  rw [lowOwnerTwoPrimeParent_comm hr hs hrs]

/-- One atom acquires this exact reciprocal-energy multiplier after two distinct
fresh-prime strips. -/
def lowOwnerTwoPrimeAtomEnergyMultiplier (r s : ℕ) : ℝ :=
  (1 / (r : ℝ) ^ 2) * (1 / (s : ℝ) ^ 2)

@[simp] theorem lowOwnerTwoPrimeAtomEnergyMultiplier_comm
    (r s : ℕ) :
    lowOwnerTwoPrimeAtomEnergyMultiplier r s =
      lowOwnerTwoPrimeAtomEnergyMultiplier s r := by
  unfold lowOwnerTwoPrimeAtomEnergyMultiplier
  ring

/-- A stripped endpoint of a squarefree endpoint is still squarefree. -/
theorem squarefree_squarefreePrimeFamilyParent
    {r n : ℕ} (hnSq : Squarefree n) :
    Squarefree (squarefreePrimeFamilyParent r n) := by
  exact hnSq.squarefree_of_dvd (squarefreePrimeFamilyParent_dvd_public r n)

/-- **Two fresh strips restore the Mobius pair parity.** -/
theorem arbitraryTwoFreshPrimes_pairWeight_eq_finalPairWeight
    {r s m n : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hmSq : Squarefree m) (hnSq : Squarefree n)
    (hm : 0 < m) (hn : 0 < n)
    (hrFresh : r ∈ squarefreePairFreshPrimeSet m n)
    (hsFresh : s ∈ squarefreePairFreshPrimeSet m n) :
    realMoebiusStep m * realMoebiusStep n =
      realMoebiusStep (lowOwnerTwoPrimeParent r s (m, n)).1 *
        realMoebiusStep (lowOwnerTwoPrimeParent r s (m, n)).2 := by
  have hsr : s ≠ r := Ne.symm hrs
  have hrXor :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor hr hm hn).1 hrFresh
  have hmRPos := squarefreePrimeFamilyParent_pos_public hr hm
  have hnRPos := squarefreePrimeFamilyParent_pos_public hr hn
  have hmRSq := squarefree_squarefreePrimeFamilyParent hmSq
  have hnRSq := squarefree_squarefreePrimeFamilyParent hnSq
  have hsFreshAfterR :
      s ∈ squarefreePairFreshPrimeSet
        (squarefreePrimeFamilyParent r m)
        (squarefreePrimeFamilyParent r n) :=
    (mem_freshPrimeSet_stripped_iff_of_ne hr hs hsr hm hn).2 hsFresh
  have hsXorAfterR :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor
      hs hmRPos hnRPos).1 hsFreshAfterR
  have hR := arbitraryFreshPrime_pairWeight_eq_neg_parentPairWeight
    hr hmSq hnSq hm hn hrXor
  have hS := arbitraryFreshPrime_pairWeight_eq_neg_parentPairWeight
    hs hmRSq hnRSq hmRPos hnRPos hsXorAfterR
  dsimp [lowOwnerTwoPrimeParent]
  calc
    realMoebiusStep m * realMoebiusStep n =
        -(realMoebiusStep (squarefreePrimeFamilyParent r m) *
          realMoebiusStep (squarefreePrimeFamilyParent r n)) := hR
    _ = -(-(realMoebiusStep
          (squarefreePrimeFamilyParent s (squarefreePrimeFamilyParent r m)) *
        realMoebiusStep
          (squarefreePrimeFamilyParent s (squarefreePrimeFamilyParent r n)))) := by
          rw [hS]
    _ = realMoebiusStep
          (squarefreePrimeFamilyParent s (squarefreePrimeFamilyParent r m)) *
        realMoebiusStep
          (squarefreePrimeFamilyParent s (squarefreePrimeFamilyParent r n)) := by
          ring

/-- **Exact two-step reciprocal-energy descent for one atom.** -/
theorem arbitraryTwoFreshPrimes_reciprocalPairEnergy_descent
    {r s m n : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hmSq : Squarefree m) (hnSq : Squarefree n)
    (hm : 0 < m) (hn : 0 < n)
    (hrFresh : r ∈ squarefreePairFreshPrimeSet m n)
    (hsFresh : s ∈ squarefreePairFreshPrimeSet m n) :
    postRootCovarianceReciprocalPairEnergy (m, n) =
      lowOwnerTwoPrimeAtomEnergyMultiplier r s *
        postRootCovarianceReciprocalPairEnergy
          (lowOwnerTwoPrimeParent r s (m, n)) := by
  have hsr : s ≠ r := Ne.symm hrs
  have hrXor :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor hr hm hn).1 hrFresh
  have hmRPos := squarefreePrimeFamilyParent_pos_public hr hm
  have hnRPos := squarefreePrimeFamilyParent_pos_public hr hn
  have hmRSq := squarefree_squarefreePrimeFamilyParent hmSq
  have hnRSq := squarefree_squarefreePrimeFamilyParent hnSq
  have hsFreshAfterR :
      s ∈ squarefreePairFreshPrimeSet
        (squarefreePrimeFamilyParent r m)
        (squarefreePrimeFamilyParent r n) :=
    (mem_freshPrimeSet_stripped_iff_of_ne hr hs hsr hm hn).2 hsFresh
  have hsXorAfterR :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor
      hs hmRPos hnRPos).1 hsFreshAfterR
  have hR := arbitraryFreshPrime_reciprocalPairEnergy_descent
    hr hmSq hnSq hm hn hrXor
  have hS := arbitraryFreshPrime_reciprocalPairEnergy_descent
    hs hmRSq hnRSq hmRPos hnRPos hsXorAfterR
  rw [hR, hS]
  unfold lowOwnerTwoPrimeAtomEnergyMultiplier lowOwnerTwoPrimeParent
  ring

/-- The exact two-step atom energy ledger is therefore independent of the strip
order, before any `2/9` or `1/9` majorant is used. -/
theorem arbitraryTwoFreshPrimes_reciprocalPairEnergy_descent_comm
    {r s m n : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hmSq : Squarefree m) (hnSq : Squarefree n)
    (hm : 0 < m) (hn : 0 < n)
    (hrFresh : r ∈ squarefreePairFreshPrimeSet m n)
    (hsFresh : s ∈ squarefreePairFreshPrimeSet m n) :
    lowOwnerTwoPrimeAtomEnergyMultiplier r s *
        postRootCovarianceReciprocalPairEnergy
          (lowOwnerTwoPrimeParent r s (m, n)) =
      lowOwnerTwoPrimeAtomEnergyMultiplier s r *
        postRootCovarianceReciprocalPairEnergy
          (lowOwnerTwoPrimeParent s r (m, n)) := by
  rw [lowOwnerTwoPrimeAtomEnergyMultiplier_comm]
  rw [lowOwnerTwoPrimeParent_comm hr hs hrs]

end RHLean.Proof
