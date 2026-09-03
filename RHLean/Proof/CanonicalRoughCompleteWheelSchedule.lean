import Mathlib
import RHLean.Proof.CanonicalRoughColumnAbelBridge
import RHLean.Proof.CanonicalRoughCompleteSubrootDefectReduction

/-!
# Complete-wheel schedules are initial prime prefixes

The fixed-partner physical shell theorems require the current Euler coordinate
`p` to satisfy two structural conditions:

* `p < q`, where `q` is the fixed partner prime;
* `SquareRootCanonicalRoughCompleteWheelBelowRoot R p`.

The second condition is monotone downward in `p`: once the complete wheel
through some cutoff still fits below `R`, every earlier complete wheel does too.
Consequently the legal complete-wheel coordinates below a fixed partner cannot
form a ragged subset of the prime prefix.  They form one initial prime segment.

For `R >= 3` this file defines its last root-scale coordinate `kappa_R` as the
maximum legal coordinate below `R` and proves the exact schedule identity

```text
{p prime : p < q and completeWheelBelowRoot R p}
  = primesUpTo (min (q - 1) kappa_R).
```

Thus the difference between the full canonical prefix `primesUpTo (q-1)` and
the coordinates on which the complete-wheel physical shell theorem is legal is
an explicit upper prime tail.  This is only a coordinate-set theorem: it does
not yet identify a chronological transported ledger with the physical face-mass
aggregate, and it does not norm the missing tail.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Prime prefixes are monotone in their numerical cutoff. -/
theorem primesUpTo_mono_schedule {a b : ℕ} (hab : a ≤ b) :
    primesUpTo a ⊆ primesUpTo b := by
  intro p hp
  rcases mem_primesUpTo.mp hp with ⟨hpPrime, hpa⟩
  exact mem_primesUpTo.mpr ⟨hpPrime, hpa.trans hab⟩

/-- **Complete-wheel admissibility is downward closed.**

This is the key geometry: adding primes can only increase the complete wheel
product, so if the wheel through `b` is still below the root then the wheel
through every earlier cutoff `a <= b` is also below the root. -/
theorem squareRootCanonicalRoughCompleteWheelBelowRoot_mono
    {R a b : ℕ} (hab : a ≤ b)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R b) :
    SquareRootCanonicalRoughCompleteWheelBelowRoot R a := by
  unfold SquareRootCanonicalRoughCompleteWheelBelowRoot at hWheel ⊢
  exact
    (primeFaceProduct_le_full_primesUpTo
      (primesUpTo_mono_schedule hab)).trans_lt hWheel

/-- A prime coordinate whose complete wheel fits below `R` is itself below `R`.
This will make the post-root fixed-partner schedule independent of the partner
`q > R`. -/
theorem prime_lt_root_of_completeWheel
    {R p : ℕ} (hp : p.Prime)
    (hWheel : SquareRootCanonicalRoughCompleteWheelBelowRoot R p) :
    p < R := by
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
This is exactly the set-level conjunction of the two hypotheses used by the
fixed-partner shell specialization: prime `p < q` and complete wheel below the
root. -/
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

/-- Membership in the legal schedule in the physical strict-order form. -/
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

/-- The last complete-wheel prime coordinate below the root.  The proof argument
is explicit because the cutoff is only used in the nonempty regime `R >= 3`. -/
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

/-- For every post-root partner `q > R`, the legal `p`-schedule is independent
of `q`: complete-wheel admissibility already forces `p < R < q`. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeSchedule_eq_root_of_root_lt
    {R q : ℕ} (hRq : R < q) :
    squareRootCanonicalRoughCompleteWheelPrimeSchedule R q =
      squareRootCanonicalRoughCompleteWheelPrimeSchedule R R := by
  ext p
  rw [mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt,
    mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt]
  constructor
  · rintro ⟨hp, _hpq, hWheel⟩
    exact ⟨hp, prime_lt_root_of_completeWheel hp hWheel, hWheel⟩
  · rintro ⟨hp, hpR, hWheel⟩
    exact ⟨hp, hpR.trans hRq, hWheel⟩

/-- **Exact schedule characterization.**

For every partner cutoff `q`, the legal complete-wheel coordinates are exactly
all primes through `min (q-1) kappa_R`.  This is the set-theoretic bridge that
was missing from the generic transported-shell ledger. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeSchedule_eq_primesUpTo_min_cutoff
    {R : ℕ} (hR : 3 ≤ R) (q : ℕ) :
    squareRootCanonicalRoughCompleteWheelPrimeSchedule R q =
      primesUpTo
        (min (q - 1) (squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR)) := by
  ext p
  rw [mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt,
    mem_primesUpTo]
  constructor
  · rintro ⟨hp, hpq, hWheel⟩
    have hpRoot :
        p ∈ squareRootCanonicalRoughCompleteWheelPrimeSchedule R R := by
      rw [mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt]
      exact ⟨hp, prime_lt_root_of_completeWheel hp hWheel, hWheel⟩
    have hpCutoff :
        p ≤ squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR := by
      unfold squareRootCanonicalRoughCompleteWheelPrimeCutoff
      exact Finset.le_max' _ p hpRoot
    refine ⟨hp, ?_⟩
    rw [Nat.le_min_iff]
    exact ⟨by omega, hpCutoff⟩
  · rintro ⟨hp, hpMin⟩
    rw [Nat.le_min_iff] at hpMin
    have hcutMem := squareRootCanonicalRoughCompleteWheelPrimeCutoff_mem hR
    have hpRoot :=
      squareRootCanonicalRoughCompleteWheelPrimeSchedule_mem_of_prime_le
        hcutMem hp hpMin.2
    have hWheel :=
      (mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt.mp hpRoot).2.2
    exact ⟨hp, by
      have hpTwo := hp.two_le
      omega, hWheel⟩

/-- Post-root specialization: for `q > R` the minimum has already saturated, so
the legal schedule is the fixed root prefix through `kappa_R`. -/
theorem squareRootCanonicalRoughCompleteWheelPrimeSchedule_postRoot_eq_primesUpTo_cutoff
    {R q : ℕ} (hR : 3 ≤ R) (hRq : R < q) :
    squareRootCanonicalRoughCompleteWheelPrimeSchedule R q =
      primesUpTo (squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR) := by
  rw [squareRootCanonicalRoughCompleteWheelPrimeSchedule_eq_root_of_root_lt hRq,
    squareRootCanonicalRoughCompleteWheelPrimeSchedule_root_eq_primesUpTo_cutoff hR]

/-- The canonical prefix coordinates on which the complete-wheel physical shell
specialization is not legal. -/
def squareRootCanonicalRoughCompleteWheelMissingPrimeTail (R q : ℕ) : Finset ℕ :=
  primesUpTo (q - 1) \
    squareRootCanonicalRoughCompleteWheelPrimeSchedule R q

/-- The missing coordinates are exactly the primes below `q` whose complete
wheel no longer fits below the root. -/
theorem mem_squareRootCanonicalRoughCompleteWheelMissingPrimeTail_iff
    {R q p : ℕ} :
    p ∈ squareRootCanonicalRoughCompleteWheelMissingPrimeTail R q ↔
      p.Prime ∧ p < q ∧
        ¬ SquareRootCanonicalRoughCompleteWheelBelowRoot R p := by
  constructor
  · intro hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpPrefix, hpNotSchedule⟩
    rcases mem_primesUpTo.mp hpPrefix with ⟨hpPrime, hpPred⟩
    have hpq : p < q := by
      have hpTwo := hpPrime.two_le
      omega
    refine ⟨hpPrime, hpq, ?_⟩
    intro hWheel
    exact hpNotSchedule
      (mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt.mpr
        ⟨hpPrime, hpq, hWheel⟩)
  · rintro ⟨hpPrime, hpq, hpNotWheel⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_primesUpTo.mpr ⟨hpPrime, by omega⟩, ?_⟩
    intro hpSchedule
    exact hpNotWheel
      (mem_squareRootCanonicalRoughCompleteWheelPrimeSchedule_iff_lt.mp
        hpSchedule).2.2

/-- The missing tail is upward closed among primes below the fixed partner. -/
theorem squareRootCanonicalRoughCompleteWheelMissingPrimeTail_mem_of_le_prime_lt
    {R q p r : ℕ}
    (hp : p ∈ squareRootCanonicalRoughCompleteWheelMissingPrimeTail R q)
    (hr : r.Prime) (hpr : p ≤ r) (hrq : r < q) :
    r ∈ squareRootCanonicalRoughCompleteWheelMissingPrimeTail R q := by
  rw [mem_squareRootCanonicalRoughCompleteWheelMissingPrimeTail_iff] at hp ⊢
  rcases hp with ⟨_hpPrime, _hpq, hpNotWheel⟩
  refine ⟨hr, hrq, ?_⟩
  intro hrWheel
  exact hpNotWheel
    (squareRootCanonicalRoughCompleteWheelBelowRoot_mono hpr hrWheel)

/-- **Explicit missing-prefix tail.**  After the schedule characterization, the
unproved part of the canonical full prefix is literally the prime interval above
`min (q-1) kappa_R`. -/
theorem squareRootCanonicalRoughCompleteWheelMissingPrimeTail_eq_sdiff_min_cutoff
    {R : ℕ} (hR : 3 ≤ R) (q : ℕ) :
    squareRootCanonicalRoughCompleteWheelMissingPrimeTail R q =
      primesUpTo (q - 1) \
        primesUpTo
          (min (q - 1) (squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR)) := by
  unfold squareRootCanonicalRoughCompleteWheelMissingPrimeTail
  rw [squareRootCanonicalRoughCompleteWheelPrimeSchedule_eq_primesUpTo_min_cutoff
    hR q]

/-- Post-root form of the missing tail: every partner `q > R` sees the same
physical cutoff `kappa_R`, and only the upper prime interval depends on `q`. -/
theorem squareRootCanonicalRoughCompleteWheelMissingPrimeTail_postRoot_eq_sdiff_cutoff
    {R q : ℕ} (hR : 3 ≤ R) (hRq : R < q) :
    squareRootCanonicalRoughCompleteWheelMissingPrimeTail R q =
      primesUpTo (q - 1) \
        primesUpTo (squareRootCanonicalRoughCompleteWheelPrimeCutoff R hR) := by
  unfold squareRootCanonicalRoughCompleteWheelMissingPrimeTail
  rw [squareRootCanonicalRoughCompleteWheelPrimeSchedule_postRoot_eq_primesUpTo_cutoff
    hR hRq]

end RHLean.Proof
