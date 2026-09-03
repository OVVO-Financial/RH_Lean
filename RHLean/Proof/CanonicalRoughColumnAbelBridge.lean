import Mathlib
import RHLean.Proof.CanonicalRoughBoundaryProfileAbelReturn
import RHLean.Proof.CanonicalRoughTruncatedWheelManyPrimeTelescope

/-!
# Canonical unweighted columns land on the Abel primitive

The unweighted-column law turns each `mu(c)/c`-shaped column into `q` times a
discrete drop of the canonical reciprocal boundary profile, and the finite Abel
return closes the resulting prime-weighted variation.  This file composes the
two, identifying the column aggregate with the signed primitive

```text
A_X(K) = sum_{n < K} B_n(X) - K * B_K(X),
```

both over a full prime prefix and over a half-open prime band.  Nothing here is
normed: routing through the primitive is what keeps the nonlocal signed
cancellation available downstream.

## These columns are canonical, not yet physical

The summands below are

```text
primorialTruncatedSignedReciprocalCube (primesUpTo (q-1)) (X / q)
  - primorialSignedContractionFactor (primesUpTo (q-1)),
```

which is a *canonical* truncated-wheel column indexed by the full prime prefix
`primesUpTo (q-1)`.  It is **not** yet a sum of the literal physical face masses
`squareRootCanonicalRoughCompleteWheelTopEscapePartnerFaceMass` or
`...BirthPartnerFaceMass`.  The physical identification of those masses carries
hypotheses `p < q`, `q < R` and `SquareRootCanonicalRoughCompleteWheelBelowRoot
R p`, and the many-prime transported ledger is generic in an arbitrary prime
list `ps`, landing on the boundary indexed by `ps.toFinset`.

The final section now resolves one part of that gap: the complete-wheel legal
`p` coordinates form an initial prime segment.  It does **not** yet identify the
chronological transported ledger with the literal face-mass aggregate.  What it
does prove is that the set-level difference from the full canonical prefix is
one explicit upper prime tail, which is the next object to route into the
root/external machinery.

## The two orientations

The profile is parameterized by the truncation, so one band theorem covers both.
A post-root escape column runs over `R < q <= X_R` against the square endpoint.
A birth owner column runs against the lower global cutoff `R - 1`, and its band
is pinned by the birth hypotheses themselves: `q` prime with `p < q` for a prime
`p` forces `q > 2`, while `c * q < R` with `c >= 1` forces `q < R`.  So the
birth band is exactly `2 < q < R`, and since the boundary profile vanishes while
the complete wheel still fits inside the truncation, the birth orientation
collapses to the single primitive value `A_{R-1}(R-1)`.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-! ## Canonical column aggregates -/

/-- **The canonical unweighted column aggregate is the Abel primitive.** -/
theorem canonicalUnweightedColumn_eq_abelPrimitive (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive X K := by
  rw [primorialTruncatedBoundary_unweightedUpperColumn_eq_primeWeightedDrops X K]
  exact primorialTruncatedBoundary_primeWeightedDrops_eq_abelPrimitive X K

/-- **Interval form.**  Over a half-open prime band the aggregate returns the
difference of the primitives at the band endpoints. -/
theorem canonicalUnweightedColumn_primeBand_eq_abelPrimitive_sub
    (X : ℕ) {K₀ K₁ : ℕ} (hK : K₀ ≤ K₁) :
    (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive X K₁ -
        primorialTruncatedWheelAbelPrimitive X K₀ := by
  have hcongr :
      (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
        (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1)))) =
        ∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
          (q : ℝ) *
            (primorialTruncatedWheelBoundaryProfile X (q - 1) -
              primorialTruncatedWheelBoundaryProfile X q) := by
    refine Finset.sum_congr rfl ?_
    intro q hq
    exact primorialTruncatedBoundary_unweightedColumn_eq_prime_mul_boundaryDrop
      X (mem_primesUpTo_sdiff.mp hq).1
  rw [hcongr]
  exact primorialTruncatedBoundary_primeBand_eq_abelPrimitive_sub X hK

/-! ## Vanishing of the profile below the first incomplete wheel -/

/-- While the complete wheel still fits inside the truncation, the truncated
profile has already stabilized on its Euler contraction, so the boundary
vanishes. -/
theorem primorialTruncatedWheelBoundaryProfile_eq_zero_of_complete
    {X n : ℕ} (hX : primorialWheelProduct (primesUpTo n) ≤ X) :
    primorialTruncatedWheelBoundaryProfile X n = 0 := by
  unfold primorialTruncatedWheelBoundaryProfile
  rw [primorialTruncatedSignedReciprocalCube_eq_factor (primesUpTo n) X
    (fun _p hp => prime_of_mem_primesUpTo hp) hX]
  exact sub_self _

theorem primesUpTo_eq_empty_of_le_one {n : ℕ} (hn : n ≤ 1) : primesUpTo n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  rcases mem_primesUpTo.mp hq with ⟨hqPrime, hqle⟩
  have h2 := hqPrime.two_le
  omega

theorem primesUpTo_two : primesUpTo 2 = {2} := by
  ext q
  rw [mem_primesUpTo, Finset.mem_singleton]
  constructor
  · rintro ⟨hqPrime, hqle⟩
    have h2 := hqPrime.two_le
    omega
  · rintro rfl
    exact ⟨Nat.prime_two, le_rfl⟩

theorem primorialWheelProduct_primesUpTo_of_le_one {n : ℕ} (hn : n ≤ 1) :
    primorialWheelProduct (primesUpTo n) = 1 := by
  rw [primesUpTo_eq_empty_of_le_one hn]
  simp [primorialWheelProduct]

theorem primorialWheelProduct_primesUpTo_two :
    primorialWheelProduct (primesUpTo 2) = 2 := by
  rw [primesUpTo_two]
  simp [primorialWheelProduct]

/-- **The Abel primitive vanishes at the initial cutoff.**  Through the prime
`2` the complete wheel already fits inside any truncation of size at least two,
so every profile value involved is zero. -/
theorem primorialTruncatedWheelAbelPrimitive_two_eq_zero {X : ℕ} (hX : 2 ≤ X) :
    primorialTruncatedWheelAbelPrimitive X 2 = 0 := by
  have h0 : primorialTruncatedWheelBoundaryProfile X 0 = 0 :=
    primorialTruncatedWheelBoundaryProfile_eq_zero_of_complete
      (by rw [primorialWheelProduct_primesUpTo_of_le_one (by omega : (0:ℕ) ≤ 1)]; omega)
  have h1 : primorialTruncatedWheelBoundaryProfile X 1 = 0 :=
    primorialTruncatedWheelBoundaryProfile_eq_zero_of_complete
      (by rw [primorialWheelProduct_primesUpTo_of_le_one (by omega : (1:ℕ) ≤ 1)]; omega)
  have h2 : primorialTruncatedWheelBoundaryProfile X 2 = 0 :=
    primorialTruncatedWheelBoundaryProfile_eq_zero_of_complete
      (by rw [primorialWheelProduct_primesUpTo_two]; omega)
  unfold primorialTruncatedWheelAbelPrimitive boundaryProfileAbelPrimitive
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2]
  norm_num

/-! ## The post-root orientation -/

theorem le_squareRootEndpoint_self {R : ℕ} (hR : 2 ≤ R) :
    R ≤ squareRootEndpoint R := by
  unfold squareRootEndpoint
  have h : R * 2 ≤ R * R := Nat.mul_le_mul (le_refl R) hR
  rw [pow_two]
  omega

/-- Canonical column aggregate over the complete external band `R < q <= X_R`,
against the square endpoint. -/
theorem canonicalPostRootBandColumn_eq_abelPrimitive_sub {R : ℕ} (hR : 2 ≤ R) :
    (∑ q ∈ primesUpTo (squareRootEndpoint R) \ primesUpTo R,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
          (squareRootEndpoint R / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R)
          (squareRootEndpoint R) -
        primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R) R :=
  canonicalUnweightedColumn_primeBand_eq_abelPrimitive_sub
    (squareRootEndpoint R) (le_squareRootEndpoint_self hR)

/-! ## The birth orientation -/

/-- Canonical column aggregate against the lower global cutoff `R - 1`. -/
theorem canonicalBirthColumn_eq_abelPrimitive_sub
    (R : ℕ) {K₀ K₁ : ℕ} (hK : K₀ ≤ K₁) :
    (∑ q ∈ primesUpTo K₁ \ primesUpTo K₀,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
          ((R - 1) / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive (R - 1) K₁ -
        primorialTruncatedWheelAbelPrimitive (R - 1) K₀ :=
  canonicalUnweightedColumn_primeBand_eq_abelPrimitive_sub (R - 1) hK

/-- **Birth owner band.**  The birth hypotheses pin the band exactly: a prime
`p < q` forces `q > 2`, and `c * q < R` with `c >= 1` forces `q < R`.  Over that
band the aggregate collapses to a single primitive value, because the lower
endpoint `A_{R-1}(2)` vanishes. -/
theorem canonicalBirthOwnerBandColumn_eq_abelPrimitive {R : ℕ} (hR : 3 ≤ R) :
    (∑ q ∈ primesUpTo (R - 1) \ primesUpTo 2,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
          ((R - 1) / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive (R - 1) (R - 1) := by
  rw [canonicalBirthColumn_eq_abelPrimitive_sub R (by omega : (2:ℕ) ≤ R - 1),
    primorialTruncatedWheelAbelPrimitive_two_eq_zero (by omega : (2:ℕ) ≤ R - 1)]
  ring

/-- **Three nontrivial primitive values.**  Combining the two orientations, the
signed post-root minus birth aggregate is carried by exactly three primitive
values rather than four: the birth lower endpoint is zero. -/
theorem canonicalPostRoot_sub_canonicalBirth_eq_threePrimitiveValues
    {R : ℕ} (hR : 3 ≤ R) :
    ((∑ q ∈ primesUpTo (squareRootEndpoint R) \ primesUpTo R,
        (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
            (squareRootEndpoint R / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1)))) -
      (∑ q ∈ primesUpTo (R - 1) \ primesUpTo 2,
        (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1))
            ((R - 1) / q) -
          primorialSignedContractionFactor (primesUpTo (q - 1))))) =
      primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R)
          (squareRootEndpoint R) -
        primorialTruncatedWheelAbelPrimitive (squareRootEndpoint R) R -
        primorialTruncatedWheelAbelPrimitive (R - 1) (R - 1) := by
  rw [canonicalPostRootBandColumn_eq_abelPrimitive_sub (by omega : (2:ℕ) ≤ R),
    canonicalBirthOwnerBandColumn_eq_abelPrimitive hR]

/-! ## Complete-wheel legal schedules -/

/-- Prime prefixes are monotone in their numerical cutoff. -/
theorem primesUpTo_mono_schedule {a b : ℕ} (hab : a ≤ b) :
    primesUpTo a ⊆ primesUpTo b := by
  intro p hp
  rcases mem_primesUpTo.mp hp with ⟨hpPrime, hpa⟩
  exact mem_primesUpTo.mpr ⟨hpPrime, hpa.trans hab⟩

/-- **Complete-wheel admissibility is downward closed.**  This is the core
schedule geometry: adding primes can only increase the complete wheel product. -/
theorem squareRootCanonicalRoughCompleteWheelBelowRoot_mono
    {R a b : ℕ} (hab : a ≤ b)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R b) :
    SquareRootCanonicalRoughCompleteWheelBelowRoot R a := by
  unfold SquareRootCanonicalRoughCompleteWheelBelowRoot at hWheel ⊢
  exact
    (primeFaceProduct_le_full_primesUpTo
      (primesUpTo_mono_schedule hab)).trans_lt hWheel

/-- A prime coordinate whose complete wheel fits below `R` is itself below `R`.
Hence post-root partners cannot change which complete-wheel coordinates are
legal. -/
theorem prime_lt_root_of_completeWheel
    {R p : ℕ} (hp : p.Prime)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    p < R := by
  unfold SquareRootCanonicalRoughCompleteWheelBelowRoot at hWheel
  have hpMem : p ∈ primesUpTo p := mem_primesUpTo.mpr ⟨hp, le_rfl⟩
  have hsingleton : ({p} : Finset ℕ) ⊆ primesUpTo p := by
    intro r hr
    have hrEq : r = p := Finset.mem_singleton.mp hr
    simpa [hrEq] using hpMem
  have hle := primeFaceProduct_le_full_primesUpTo hsingleton
  have hpLe : p ≤ primeFaceProduct (primesUpTo p) := by
    simpa [primeFaceProduct] using hle
  exact hpLe.trans_lt hWheel

/-- Legal complete-wheel Euler coordinates for one fixed partner cutoff `q`.
This is the set-level conjunction of the hypotheses `p < q` and complete wheel
below the root used by the fixed-partner shell specialization. -/
def squareRootCanonicalRoughCompleteWheelPrimeSchedule (R q : ℕ) : Finset ℕ :=
  (primesUpTo (q - 1)).filter fun p =>
    SquareRootCanonicalRoughCompleteWheelBelowRoot R p

/-- Membership in the legal schedule in predecessor-cutoff form. -/
theorem mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff
    {R q p : ℕ} :
    p ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R q ↔
      p.Prime ∧ p ≤ q - 1 ∧
        SquareRootCanonicalRoughCompleteWheelBelowRoot R p := by
  simp only [squareRootCanonicalRoughCompleteWheelPrimeSchedule,
    Finset.mem_filter, mem_primesUpTo]
  tauto

/-- Membership in the legal schedule in strict physical-order form. -/
theorem mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt
    {R q p : ℕ} :
    p ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R q ↔
      p.Prime ∧ p < q ∧
        SquareRootCanonicalRoughCompleteWheelBelowRoot R p := by
  rw [mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff]
  constructor
  · rintro ⟨hp, hpq, hWheel⟩
    have hpTwo := hp.two_le
    exact ⟨hp, by omega, hWheel⟩
  · rintro ⟨hp, hpq, hWheel⟩
    exact ⟨hp, by omega, hWheel⟩

/-- **No holes in the legal schedule.**  If a legal coordinate `p` is present,
then every earlier prime coordinate is present as well. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeSchedule_mem_of_prime_le
    {R q p r : ℕ}
    (hp : p ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R q)
    (hr : r.Prime) (hrp : r ≤ p) :
    r ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R q := by
  rw [mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt] at hp ⊢
  rcases hp with ⟨_hpPrime, hpq, hWheel⟩
  exact ⟨hr, hrp.trans_lt hpq,
    squareRootCanonicalRoughCompleteWheelBelowRoot_mono hrp hWheel⟩

/-- Any greatest legal coordinate identifies the whole schedule with the full
prime prefix through that coordinate. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeSchedule_eq_primesUpTo_of_greatest
    {R q k : ℕ}
    (hk : k ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R q)
    (hgreatest : ∀ p ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R q,
      p ≤ k) :
    squareRootCanonicalRoughCompleteWheelPrimeSchedule R q = primesUpTo k := by
  ext p
  constructor
  · intro hp
    have hdata :=
      mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt.mp hp
    exact mem_primesUpTo.mpr ⟨hdata.1, hgreatest p hp⟩
  · intro hp
    rcases mem_primesUpTo.mp hp with ⟨hpPrime, hpk⟩
    exact
      squareRootCanonicalRoughCompleteWheelPrimeSchedule_mem_of_prime_le
        hk hpPrime hpk

/-- Finite maximum form of the initial-segment theorem. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeSchedule_eq_primesUpTo_max'
    {R q : ℕ}
    (hne : (squareRootCanonicalRoughCompleteWheelPrimeSchedule R q).Nonempty) :
    squareRootCanonicalRoughCompleteWheelPrimeSchedule R q =
      primesUpTo
        ((squareRootCanonicalRoughCompleteWheelPrimeSchedule R q).max' hne) := by
  apply
    squareRootCanonicalRoughCompleteWheelPrimeSchedule_eq_primesUpTo_of_greatest
  · exact Finset.max'_mem _ hne
  · intro p hp
    exact Finset.le_max' _ p hp

/-- At root scale the legal schedule is nonempty as soon as `R >= 3`: the prime
`2` is legal because its complete wheel has product exactly `2 < R`. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeSchedule_root_nonempty
    {R : ℕ} (hR : 3 ≤ R) :
    (squareRootCanonicalRoughCompleteWheelPrimeSchedule R R).Nonempty := by
  refine ⟨2, ?_⟩
  rw [mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt]
  refine ⟨Nat.prime_two, by omega, ?_⟩
  unfold SquareRootCanonicalRoughCompleteWheelBelowRoot
  have hprod : primeFaceProduct (primesUpTo 2) = 2 := by
    rw [primesUpTo_two]
    simp [primeFaceProduct]
  rw [hprod]
  omega

/-- The last complete-wheel prime coordinate below the root. -/
def squareRootCanonicalRoughCompleteWheelPrimeCutoff
    (R : ℕ) (hR : 3 ≤ R) : ℕ :=
  (squareRootCanonicalRoughCompleteWheelPrimeSchedule R R).max'
    (squareRootCanonicalRoughCompleteWheelPrimeSchedule_root_nonempty hR)

/-- The root-scale schedule is exactly the prime prefix through `kappa_R`. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeSchedule_root_eq_primesUpTo_cutoff
    {R : ℕ} (hR : 3 ≤ R) :
    squareRootCanonicalRoughCompleteWheelPrimeSchedule R R =
      primesUpTo (squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR) := by
  unfold squareRootCanonicalRoughCompleteWheelPrimeCutoff
  exact
    squareRootCanonicalRoughCompleteWheelPrimeSchedule_eq_primesUpTo_max'
      (squareRootCanonicalRoughCompleteWheelPrimeSchedule_root_nonempty hR)

/-- The root cutoff itself is a legal prime coordinate. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeCutoff_mem
    {R : ℕ} (hR : 3 ≤ R) :
    squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR ∈
      squareRootCanonicalRoughCompleteWheelPrimeSchedule R R := by
  unfold squareRootCanonicalRoughCompleteWheelPrimeCutoff
  exact Finset.max'_mem _
    (squareRootCanonicalRoughCompleteWheelPrimeSchedule_root_nonempty hR)

/-- In particular the root cutoff is prime and strictly below `R`. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeCutoff_prime_lt_root
    {R : ℕ} (hR : 3 ≤ R) :
    (squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR).Prime ∧
      squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR < R := by
  have hmem := squareRootCanonicalRoughCompleteWheelPrimeCutoff_mem hR
  have hdata :=
    mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt.mp hmem
  exact ⟨hdata.1, hdata.2.1⟩

/-- **Exact schedule characterization.**  For every partner cutoff `q`, the
legal complete-wheel coordinates are the intersection of the partner prefix
with the fixed root prefix through `kappa_R`.  Equivalently, they are the prime
prefix through the smaller of those two cutoffs. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeSchedule_eq_inter_cutoff
    {R : ℕ} (hR : 3 ≤ R) (q : ℕ) :
    squareRootCanonicalRoughCompleteWheelPrimeSchedule R q =
      primesUpTo (q - 1) ∩
        primesUpTo (squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR) := by
  ext p
  constructor
  · intro hp
    have hdata :=
      mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff.mp hp
    have hpRoot :
        p ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R R := by
      rw [mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt]
      exact ⟨hdata.1,
        prime_lt_root_of_completeWheel hdata.1 hdata.2.2,
        hdata.2.2⟩
    have hpCutoff :
        p ∈ primesUpTo (squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR) := by
      rw [← squareRootCanonicalRoughCompleteWheelPrimeSchedule_root_eq_primesUpTo_cutoff hR]
      exact hpRoot
    exact Finset.mem_inter.mpr ⟨
      mem_primesUpTo.mpr ⟨hdata.1, hdata.2.1⟩, hpCutoff⟩
  · intro hp
    rcases Finset.mem_inter.mp hp with ⟨hpPrefix, hpCutoff⟩
    rcases mem_primesUpTo.mp hpPrefix with ⟨hpPrime, hpPred⟩
    have hpRoot :
        p ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R R := by
      rw [squareRootCanonicalRoughCompleteWheelPrimeSchedule_root_eq_primesUpTo_cutoff hR]
      exact hpCutoff
    have hWheel :=
      (mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt.mp hpRoot).2.2
    exact
      mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff.mpr
        ⟨hpPrime, hpPred, hWheel⟩

/-- For every post-root partner `q > R`, the legal schedule has already
saturated at the fixed root prefix through `kappa_R`. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeSchedule_postRoot_eq_primesUpTo_cutoff
    {R q : ℕ} (hR : 3 ≤ R) (hRq : R < q) :
    squareRootCanonicalRoughCompleteWheelPrimeSchedule R q =
      primesUpTo (squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR) := by
  ext p
  rw [mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt,
    mem_primesUpTo]
  constructor
  · rintro ⟨hp, _hpq, hWheel⟩
    have hpRoot :
        p ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R R := by
      rw [mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt]
      exact ⟨hp, prime_lt_root_of_completeWheel hp hWheel, hWheel⟩
    rw [← squareRootCanonicalRoughCompleteWheelPrimeSchedule_root_eq_primesUpTo_cutoff hR]
    exact hpRoot
  · rintro ⟨hp, hpCutoff⟩
    have hpRoot :
        p ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R R := by
      rw [squareRootCanonicalRoughCompleteWheelPrimeSchedule_root_eq_primesUpTo_cutoff hR]
      exact mem_primesUpTo.mpr ⟨hp, hpCutoff⟩
    have hdata :=
      mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt.mp hpRoot
    exact ⟨hp, hdata.2.1.trans hRq, hdata.2.2⟩

/-- The canonical prefix coordinates on which the complete-wheel physical shell
specialization is not legal. -/
def squareRootCanonicalRoughCompleteWheelMissingPrimeTail (R q : ℕ) : Finset ℕ :=
  primesUpTo (q - 1) \
    squareRootCanonicalRoughCompleteWheelPrimeSchedule R q

/-- **Explicit missing-prime tail.**  The gap from the canonical full prefix is
literally the upper prime interval above the fixed root cutoff. -/
theorem squareRootCanonicalRoughCompleteWheelMissingPrimeTail_eq_sdiff_cutoff
    {R : ℕ} (hR : 3 ≤ R) (q : ℕ) :
    squareRootCanonicalRoughCompleteWheelMissingPrimeTail R q =
      primesUpTo (q - 1) \
        primesUpTo (squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR) := by
  unfold squareRootCanonicalRoughCompleteWheelMissingPrimeTail
  rw [squareRootCanonicalRoughCompleteWheelPrimeSchedule_eq_inter_cutoff hR q]
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- The missing tail is upward closed among primes below the partner: once a
complete wheel has failed, every later prime coordinate also fails it. -/
theorem squareRootCanonicalRoughCompleteWheelMissingPrimeTail_mem_of_le_prime_lt
    {R q p r : ℕ}
    (hp : p ∈ squareRootCanonicalRoughCompleteWheelMissingPrimeTail R q)
    (hr : r.Prime) (hpr : p ≤ r) (hrq : r < q) :
    r ∈ squareRootCanonicalRoughCompleteWheelMissingPrimeTail R q := by
  unfold squareRootCanonicalRoughCompleteWheelMissingPrimeTail at hp ⊢
  rcases Finset.mem_sdiff.mp hp with ⟨_hpPrefix, hpNotSchedule⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨mem_primesUpTo.mpr ⟨hr, by omega⟩, ?_⟩
  intro hrSchedule
  have hrWheel :=
    (mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt.mp
      hrSchedule).2.2
  have hpWheel :=
    squareRootCanonicalRoughCompleteWheelBelowRoot_mono hpr hrWheel
  apply hpNotSchedule
  have hpData := mem_primesUpTo.mp _hpPrefix
  exact mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff.mpr
    ⟨hpData.1, hpData.2, hpWheel⟩

end RHLean.Proof
