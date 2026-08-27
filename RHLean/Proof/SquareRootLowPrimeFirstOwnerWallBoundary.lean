import Mathlib
import RHLean.Proof.SquareRootLowPrimeFirstOwnerFalloutWidth

/-!
# First-owner square-wall fallout is an old-prime born boundary

The fixed-owner width theorem leaves two intrinsic ways for a canonical
`p`-child to disappear from the original processed carrier.  The response-fibre
tail is the genuine horizontal finite difference.  This module shows that the
other alternative, crossing the square wall, is already a shallow born
boundary rather than a new high-prime defect.

Assume the actual schedule ends below the root, `U < R`, and `p` is the first
scheduled prime above `P⁺(c)`.  If `p*c > X_R`, then necessarily `R <= c`.
Hence the high response of `c` is identically zero and its whole combined
response is the born partner count.  Moreover every born partner `q` satisfies
`q < p`; firstness then forces `q <= K`.  Thus every unit of first-owner wall
fallout is supported on an old prime coordinate already present at the shallow
cutoff.

No estimate is taken here.  The next reindexing can therefore swap the wall
population into old-prime cofactor windows before any absolute value.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A first scheduled owner is itself one of the fresh scheduled primes. -/
theorem squareRootLowPrimeFirstOwnerAbove_mem_freshPrimeList
    {K U L p : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) L = some p) :
    p ∈ squareRootLowPrimeFreshPrimeList K U := by
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, _hpre, _hLp⟩
  rw [hsplit]
  simp

/-- **A first-owner square-wall crossing forces the parent cofactor to have
reached the root.** -/
theorem squareRootLowPrimeFirstOwnerWall_forces_root_le_cofactor
    {R K U p c : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hwall : squareRootEndpoint R < p * c) :
    R ≤ c := by
  have hpList := squareRootLowPrimeFirstOwnerAbove_mem_freshPrimeList hfirst
  have hpSet : p ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hpList
  have hpData := Finset.mem_filter.mp hpSet
  have hpPrime : p.Prime := hpData.2
  have hpU : p ≤ U := (Finset.mem_Ioc.mp hpData.1).2
  have hpR : p < R := hpU.trans_lt hUR
  by_contra hnot
  have hcR : c < R := Nat.lt_of_not_ge hnot
  have hcPos : 0 < c := by
    by_contra hc0
    have hcZero : c = 0 := Nat.eq_zero_of_not_pos hc0
    rw [hcZero, Nat.mul_zero] at hwall
    omega
  have hprod : p * c < R * R := by
    calc
      p * c < R * c := Nat.mul_lt_mul_of_pos_right hpR hcPos
      _ < R * R := Nat.mul_lt_mul_of_pos_left hcR (by omega)
  have hprod' : p * c < R ^ 2 := by
    simpa [pow_two] using hprod
  unfold squareRootEndpoint at hwall
  omega

/-- At or beyond the root the processed combined response is purely born: the
honest high channel has already ended. -/
theorem squareRootLowPrimeCombinedFreshResponse_eq_born_of_root_le
    {R K j c : ℕ} (hcR : R ≤ c) :
    squareRootLowPrimeCombinedFreshResponse R K j c =
      squareRootBornPartnerCount R c := by
  unfold squareRootLowPrimeCombinedFreshResponse
  have hnot : ¬ c ≤ R - 1 := by omega
  simp [hnot]

/-- **Every born partner on a first-owner wall is an old prime `q <= K`.**

The born product satisfies `c*q <= X_R`, whereas the first scheduled owner has
`X_R < c*p`; hence `q < p`.  If `q` were also fresh (`K < q`), it would appear
in the increasing schedule before `p`, contradicting firstness. -/
theorem squareRootLowPrimeFirstOwnerWall_bornPartner_le_shallowCutoff
    {R K U p c q : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hwall : squareRootEndpoint R < p * c)
    (hq : q ∈ squareRootBornPartnerSet R c) :
    q ≤ K := by
  rcases Finset.mem_filter.mp hq with
    ⟨_hqRange, hqPrime, hrough, hqc, hqProduct⟩
  have hcPos : 0 < c := lt_of_lt_of_le hqPrime.pos hqc
  have hqp : q < p := by
    by_contra hnot
    have hpq : p ≤ q := Nat.le_of_not_gt hnot
    have hmul : p * c ≤ q * c := Nat.mul_le_mul_right c hpq
    have hmul' : p * c ≤ c * q := by
      simpa [Nat.mul_comm] using hmul
    omega
  by_contra hnotK
  have hKq : K < q := Nat.lt_of_not_ge hnotK
  have hpList := squareRootLowPrimeFirstOwnerAbove_mem_freshPrimeList hfirst
  have hpSet : p ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hpList
  have hpU : p ≤ U := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpSet).1).2
  have hqU : q ≤ U := (Nat.le_of_lt hqp).trans hpU
  have hqSet : q ∈ squareRootLowPrimeFreshPrimeSet K U := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hKq, hqU⟩, hqPrime⟩
  have hqList : q ∈ squareRootLowPrimeFreshPrimeList K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hqSet
  have hpq := squareRootLowPrimeFirstOwnerAbove_le_of_mem
    hfirst hqList hrough
  omega

/-- The full born partner set of a first-owner wall is supported on the old
prime interval `[2,K]`. -/
theorem squareRootLowPrimeFirstOwnerWall_bornPartnerSet_subset_Icc
    {R K U p c : ℕ}
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hwall : squareRootEndpoint R < p * c) :
    squareRootBornPartnerSet R c ⊆ Finset.Icc 2 K := by
  intro q hq
  have hqRange := (Finset.mem_filter.mp hq).1
  have hqTwo : 2 ≤ q := (Finset.mem_Icc.mp hqRange).1
  exact Finset.mem_Icc.mpr
    ⟨hqTwo,
      squareRootLowPrimeFirstOwnerWall_bornPartner_le_shallowCutoff
        hfirst hwall hq⟩

/-- **Exact wall width = old-prime born multiplicity.** -/
theorem squareRootLowPrimeFirstOwnerWall_falloutWidth_eq_born
    {R K j U p c : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hwall : squareRootEndpoint R < p * c) :
    squareRootLowPrimeCanonicalOwnerFalloutWidth R K j p c =
      squareRootBornPartnerCount R c := by
  have hcR := squareRootLowPrimeFirstOwnerWall_forces_root_le_cofactor
    hR hUR hfirst hwall
  unfold squareRootLowPrimeCanonicalOwnerFalloutWidth
  rw [if_pos hwall,
    squareRootLowPrimeCombinedFreshResponse_eq_born_of_root_le hcR]

end RHLean.Proof
