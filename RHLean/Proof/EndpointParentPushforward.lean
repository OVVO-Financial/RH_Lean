import Mathlib
import RHLean.Proof.EndpointGlobalSquareResidualMass

/-!
# One canonical Euler level below the endpoint carrier

The half-scale child bound is not enough at `X_R ~ R^2`.  This module keeps the
globally reassembled signed carrier and descends one further canonical Euler
level, from the child `m` to the parent `c = m / P+(m)` left after stripping the
unique largest-prime owner.

## The parent contraction

Every child in the endpoint population satisfies `P+(m) * m <= X`, and `m = c q`
with `q = P+(m)`.  Hence

```text
q^2 c <= X,
```

so `c <= X/4` for every parent, and `c <= X/9` once the parent is not the unit
(there `q >= 3`, because the only prefix rough below `2` is the unit itself).
This is a contraction on the common carrier: it is a statement about the whole
reassembled population, not a sum of ownerwise estimates.

## The parent pushforward is noninjective, and its multiplicity is a prime fibre

Stripping the owner is not injective: many owners sit above one parent.  The
multiplicity is preserved exactly, as the signed fresh-prime fibre

```text
endpointOwnerFibre K X c = { q prime : q <= K, P+(c) < q, q^2 c <= X },
```

and the pushforward is the exact identity

```text
sum_{m in P(K,X)} mu(m) = - sum_{c} card(fibre c) * mu(c),
```

equivalently, at the endpoint,

```text
squareRootLowPrimeLiteralWallSquareResidualMass R K
  = sum_{c} card(fibre c) * mu(c).
```

No norm is taken anywhere on the way: the fibre cardinality enters as a signed
weight on the parent, not as a bound on a subsum.  Note that this exchanges a
`+-1`-weighted sum over children for a prime-count-weighted sum over parents, so
the *trivial* estimate gets worse, not better.  That is the point: the object is
now one signed sum over a quarter-scale carrier whose weights are prime counts,
and the contraction must come from cancellation in `c`.

## The mate frontier

The last section supplies the first Euler/Othello ingredient on that carrier.
For a prime `p`, the fibre above the mate `p c` is always contained in the fibre
above `c`, and when the mate does not move the roughness floor
(`P+(p c) = P+(c)`, which holds for `p = 2` and every `c > 1`) the containment is
exact:

```text
fibre(p c) = fibre(c) \ frontier(c,p),
frontier(c,p) = { q in fibre(c) : q^2 (p c) > X },
card fibre(c) = card fibre(p c) + card frontier(c,p).
```

So pairing a parent with its mate cancels the two fibres against each other down
to the owners the mate pushes past the square cutoff.  The involution that turns
this into a global cancellation, and the sign bookkeeping at parents whose mate
leaves the carrier, are not proved here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## Stripping the canonical owner -/

/-- **Owner-squared parent inequality.**  Stripping the unique largest-prime
owner from an endpoint child leaves a parent that still fits below `X` after
*two* multiplications by that owner. -/
theorem endpointSecondContactPopulation_ownerSq_mul_parent_le
    {K X m : ℕ} (hm : m ∈ endpointSecondContactPopulation K X) :
    canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m *
        canonicalCofactor m ≤ X := by
  rcases mem_endpointSecondContactPopulation.mp hm with
    ⟨⟨hm2, _hmX⟩, _hsq, _hK, hcontact⟩
  have hm1 : 1 < m := by omega
  have hfactor : canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hm1
  calc
    canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m *
          canonicalCofactor m =
        canonicalLargestPrimeFactor m *
          (canonicalCofactor m * canonicalLargestPrimeFactor m) := by ring
    _ = canonicalLargestPrimeFactor m * m := by rw [hfactor]
    _ ≤ X := hcontact

/-- Endpoint parents are positive. -/
theorem endpointSecondContactPopulation_parent_pos
    {K X m : ℕ} (hm : m ∈ endpointSecondContactPopulation K X) :
    0 < canonicalCofactor m := by
  rcases mem_endpointSecondContactPopulation.mp hm with
    ⟨⟨hm2, _hmX⟩, _hsq, _hK, _hcontact⟩
  have hm1 : 1 < m := by omega
  have hfactor : canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hm1
  by_contra hcon
  have hc0 : canonicalCofactor m = 0 := by omega
  rw [hc0, Nat.zero_mul] at hfactor
  omega

/-- Endpoint parents are squarefree. -/
theorem endpointSecondContactPopulation_parent_squarefree
    {K X m : ℕ} (hm : m ∈ endpointSecondContactPopulation K X) :
    Squarefree (canonicalCofactor m) := by
  rcases mem_endpointSecondContactPopulation.mp hm with
    ⟨⟨hm2, _hmX⟩, hsq, _hK, _hcontact⟩
  have hm1 : 1 < m := by omega
  have hfactor : canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hm1
  exact hsq.squarefree_of_dvd ⟨canonicalLargestPrimeFactor m, hfactor.symm⟩

/-- **Quarter-scale parent contraction.**  Every parent of the reassembled
endpoint carrier lies at quarter scale. -/
theorem endpointSecondContactPopulation_parent_le_quarterScale
    {K X m : ℕ} (hm : m ∈ endpointSecondContactPopulation K X) :
    canonicalCofactor m ≤ X / 4 := by
  have hownerSq := endpointSecondContactPopulation_ownerSq_mul_parent_le hm
  rcases mem_endpointSecondContactPopulation.mp hm with
    ⟨⟨hm2, _hmX⟩, _hsq, _hK, _hcontact⟩
  have hm1 : 1 < m := by omega
  have hq2 : 2 ≤ canonicalLargestPrimeFactor m :=
    (canonicalLargestPrimeFactor_prime hm1).two_le
  have hqq : 2 * 2 ≤
      canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m :=
    Nat.mul_le_mul hq2 hq2
  refine (Nat.le_div_iff_mul_le (by norm_num : 0 < (4 : ℕ))).2 ?_
  calc
    canonicalCofactor m * 4 = 2 * 2 * canonicalCofactor m := by ring
    _ ≤ canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m *
        canonicalCofactor m := Nat.mul_le_mul_right (canonicalCofactor m) hqq
    _ ≤ X := hownerSq

/-- **Strict parents contract to ninth scale.**  A parent above the unit forces
its owner to be at least `3`, because the only prefix rough below `2` is the
unit itself. -/
theorem endpointSecondContactPopulation_strictParent_le_ninthScale
    {K X m : ℕ} (hm : m ∈ endpointSecondContactPopulation K X)
    (hc : 1 < canonicalCofactor m) :
    canonicalCofactor m ≤ X / 9 := by
  have hownerSq := endpointSecondContactPopulation_ownerSq_mul_parent_le hm
  rcases mem_endpointSecondContactPopulation.mp hm with
    ⟨⟨hm2, _hmX⟩, hsq, _hK, _hcontact⟩
  have hm1 : 1 < m := by omega
  have hrough : canonicalLargestPrimeFactor (canonicalCofactor m) <
      canonicalLargestPrimeFactor m :=
    canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hm1 hsq
  have hcTwo : 2 ≤ canonicalLargestPrimeFactor (canonicalCofactor m) :=
    (canonicalLargestPrimeFactor_prime hc).two_le
  have hq3 : 3 ≤ canonicalLargestPrimeFactor m := by omega
  have hqq : 3 * 3 ≤
      canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m :=
    Nat.mul_le_mul hq3 hq3
  refine (Nat.le_div_iff_mul_le (by norm_num : 0 < (9 : ℕ))).2 ?_
  calc
    canonicalCofactor m * 9 = 3 * 3 * canonicalCofactor m := by ring
    _ ≤ canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m *
        canonicalCofactor m := Nat.mul_le_mul_right (canonicalCofactor m) hqq
    _ ≤ X := hownerSq

/-! ## The parent carrier -/

/-- Parents of the endpoint population after the canonical owner is stripped. -/
def endpointSecondContactParents (K X : ℕ) : Finset ℕ :=
  (endpointSecondContactPopulation K X).image canonicalCofactor

theorem mem_endpointSecondContactParents {K X c : ℕ} :
    c ∈ endpointSecondContactParents K X ↔
      ∃ m ∈ endpointSecondContactPopulation K X, canonicalCofactor m = c := by
  unfold endpointSecondContactParents
  exact Finset.mem_image

theorem endpointSecondContactParents_pos
    {K X c : ℕ} (hc : c ∈ endpointSecondContactParents K X) : 0 < c := by
  rcases mem_endpointSecondContactParents.mp hc with ⟨m, hm, hcm⟩
  rw [← hcm]
  exact endpointSecondContactPopulation_parent_pos hm

theorem endpointSecondContactParents_squarefree
    {K X c : ℕ} (hc : c ∈ endpointSecondContactParents K X) : Squarefree c := by
  rcases mem_endpointSecondContactParents.mp hc with ⟨m, hm, hcm⟩
  rw [← hcm]
  exact endpointSecondContactPopulation_parent_squarefree hm

/-- **The parent carrier sits at quarter scale.** -/
theorem endpointSecondContactParents_subset_quarterScale (K X : ℕ) :
    endpointSecondContactParents K X ⊆ Finset.Icc 1 (X / 4) := by
  intro c hc
  rcases mem_endpointSecondContactParents.mp hc with ⟨m, hm, hcm⟩
  have hpos := endpointSecondContactPopulation_parent_pos hm
  have hquarter := endpointSecondContactPopulation_parent_le_quarterScale hm
  rw [hcm] at hpos hquarter
  exact Finset.mem_Icc.mpr ⟨hpos, hquarter⟩

theorem endpointSecondContactParents_card_le_quarterScale (K X : ℕ) :
    (endpointSecondContactParents K X).card ≤ X / 4 := by
  calc
    (endpointSecondContactParents K X).card ≤ (Finset.Icc 1 (X / 4)).card :=
      Finset.card_le_card (endpointSecondContactParents_subset_quarterScale K X)
    _ = X / 4 := by simp

/-! ## The signed fresh-prime owner fibre -/

/-- **Owner fibre above a parent.**  Its cardinality is exactly the multiplicity
the noninjective parent pushforward has to preserve. -/
def endpointOwnerFibre (K X c : ℕ) : Finset ℕ :=
  (Finset.Icc 2 K).filter fun q =>
    q.Prime ∧ canonicalLargestPrimeFactor c < q ∧ q * q * c ≤ X

theorem mem_endpointOwnerFibre {K X c q : ℕ} :
    q ∈ endpointOwnerFibre K X c ↔
      (2 ≤ q ∧ q ≤ K) ∧
        q.Prime ∧ canonicalLargestPrimeFactor c < q ∧ q * q * c ≤ X := by
  unfold endpointOwnerFibre
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- **The population fibre over a parent is the owner fibre.**  Both directions
are exact: the owner is recovered from the child, and every admissible owner
produces a child of the carrier. -/
theorem endpointSecondContactPopulation_parentFibre_eq_image
    {K X c : ℕ} (hcSq : Squarefree c) (hcPos : 0 < c) :
    (endpointSecondContactPopulation K X).filter
        (fun m => canonicalCofactor m = c) =
      (endpointOwnerFibre K X c).image (fun q => q * c) := by
  have hc1 : 1 ≤ c := hcPos
  ext m
  constructor
  · intro hm
    rcases Finset.mem_filter.mp hm with ⟨hmPop, hmc⟩
    rcases mem_endpointSecondContactPopulation.mp hmPop with
      ⟨⟨hm2, _hmX⟩, hmsq, hK, _hcontact⟩
    have hm1 : 1 < m := by omega
    have hfactor : canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
      canonicalCofactor_mul_largestPrimeFactor hm1
    have hqPrime := canonicalLargestPrimeFactor_prime hm1
    have hrough :=
      canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hm1 hmsq
    have hownerSq := endpointSecondContactPopulation_ownerSq_mul_parent_le hmPop
    refine Finset.mem_image.mpr ⟨canonicalLargestPrimeFactor m, ?_, ?_⟩
    · refine mem_endpointOwnerFibre.mpr ⟨⟨hqPrime.two_le, hK⟩, hqPrime, ?_, ?_⟩
      · rw [← hmc]
        exact hrough
      · rw [← hmc]
        exact hownerSq
    · rw [← hmc, Nat.mul_comm]
      exact hfactor
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨q, hq, hqm⟩
    rcases mem_endpointOwnerFibre.mp hq with ⟨⟨hq2, hqK⟩, hqPrime, hrough, hcut⟩
    have hflip : μ (c * q) = -μ c :=
      moebius_mul_prime_eq_neg_of_rough hcPos hqPrime hrough
    have hcne : μ c ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hcSq
    have hmsq : Squarefree m := by
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
      rw [← hqm, Nat.mul_comm, hflip]
      simpa using hcne
    have howner : canonicalLargestPrimeFactor m = q := by
      rw [← hqm, Nat.mul_comm]
      exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcPos hqPrime hrough
    have hcof : canonicalCofactor m = c := by
      rw [← hqm, Nat.mul_comm]
      exact canonicalCofactor_mul_prime_eq_of_rough hcPos hqPrime hrough
    have htwo : 2 * 1 ≤ q * c := Nat.mul_le_mul hq2 hc1
    have hm2 : 2 ≤ m := by omega
    have hcontact : canonicalLargestPrimeFactor m * m ≤ X := by
      rw [howner, ← hqm]
      calc
        q * (q * c) = q * q * c := by ring
        _ ≤ X := hcut
    have hqq : q ≤ q * q := by
      calc
        q = q * 1 := by ring
        _ ≤ q * q := Nat.mul_le_mul (le_refl q) (by omega)
    have hmX : m ≤ X := by
      calc
        m = q * c := hqm.symm
        _ ≤ q * q * c := Nat.mul_le_mul_right c hqq
        _ ≤ X := hcut
    refine Finset.mem_filter.mpr ⟨?_, hcof⟩
    refine mem_endpointSecondContactPopulation.mpr ⟨⟨hm2, hmX⟩, hmsq, ?_, hcontact⟩
    rw [howner]
    exact hqK

/-- Möbius mass of one parent fibre: the multiplicity times the parent sign. -/
theorem endpointSecondContactPopulation_parentFibre_moebiusSum
    {K X c : ℕ} (hcSq : Squarefree c) (hcPos : 0 < c) :
    (∑ m ∈ (endpointSecondContactPopulation K X).filter
        (fun m => canonicalCofactor m = c), μ m) =
      -(((endpointOwnerFibre K X c).card : ℤ) * μ c) := by
  rw [endpointSecondContactPopulation_parentFibre_eq_image hcSq hcPos]
  have himage :
      (∑ m ∈ (endpointOwnerFibre K X c).image (fun q => q * c), μ m) =
        ∑ q ∈ endpointOwnerFibre K X c, μ (q * c) := by
    apply Finset.sum_image
    intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_right hcPos hab
  have hpoint : ∀ q ∈ endpointOwnerFibre K X c, μ (q * c) = -μ c := by
    intro q hq
    rcases mem_endpointOwnerFibre.mp hq with ⟨_hbounds, hqPrime, hrough, _hcut⟩
    have hflip := moebius_mul_prime_eq_neg_of_rough hcPos hqPrime hrough
    rw [Nat.mul_comm]
    exact hflip
  rw [himage, Finset.sum_congr rfl hpoint, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Exact noninjective parent pushforward.**  Stripping the owner is not
injective; the multiplicity survives exactly as the owner-fibre cardinality, and
no norm is taken. -/
theorem endpointSecondContactPopulation_moebiusSum_eq_neg_parentFibreSum
    (K X : ℕ) :
    (∑ m ∈ endpointSecondContactPopulation K X, μ m) =
      -∑ c ∈ endpointSecondContactParents K X,
        ((endpointOwnerFibre K X c).card : ℤ) * μ c := by
  have hmaps : ∀ m ∈ endpointSecondContactPopulation K X,
      canonicalCofactor m ∈ endpointSecondContactParents K X := by
    intro m hm
    exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun m => μ m)
  rw [← hfib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro c hc
  exact endpointSecondContactPopulation_parentFibre_moebiusSum
    (endpointSecondContactParents_squarefree hc)
    (endpointSecondContactParents_pos hc)

/-- **The endpoint mass on the parent carrier.**  One signed sum over parents at
quarter scale, weighted by the exact owner multiplicity. -/
theorem squareRootLowPrimeLiteralWallSquareResidualMass_eq_parentFibreSum
    (R K : ℕ) :
    squareRootLowPrimeLiteralWallSquareResidualMass R K =
      ∑ c ∈ endpointSecondContactParents K (squareRootEndpoint R),
        ((endpointOwnerFibre K (squareRootEndpoint R) c).card : ℤ) * μ c := by
  rw [squareRootLowPrimeLiteralWallSquareResidualMass_eq_neg_endpointPopulationMass,
    endpointSecondContactPopulation_moebiusSum_eq_neg_parentFibreSum]
  ring

/-! ## The mate frontier -/

/-- The canonical largest prime factor is always at least one. -/
theorem one_le_canonicalLargestPrimeFactor (m : ℕ) :
    1 ≤ canonicalLargestPrimeFactor m := by
  by_cases h : 1 < m
  · exact (canonicalLargestPrimeFactor_prime h).one_lt.le
  · simp [canonicalLargestPrimeFactor, h]

/-- Adjoining a prime can only raise the canonical largest prime factor. -/
theorem canonicalLargestPrimeFactor_le_mul_prime
    {c p : ℕ} (hcPos : 0 < c) (hp : p.Prime) :
    canonicalLargestPrimeFactor c ≤ canonicalLargestPrimeFactor (p * c) := by
  by_cases hc1 : 1 < c
  · have hpc1 : 1 < p * c := by
      calc
        1 < c := hc1
        _ = 1 * c := by ring
        _ ≤ p * c := Nat.mul_le_mul_right c hp.one_lt.le
    have hpcPos : 0 < p * c := Nat.mul_pos hp.pos hcPos
    have hmem : canonicalLargestPrimeFactor c ∈ (p * c).primeFactors := by
      refine Nat.mem_primeFactors.mpr
        ⟨canonicalLargestPrimeFactor_prime hc1, ?_, ?_⟩
      · exact (canonicalLargestPrimeFactor_dvd hc1).mul_left p
      · omega
    exact primeFactor_le_canonicalLargestPrimeFactor hpc1 hmem
  · have hcOne : c = 1 := by omega
    subst hcOne
    have h1 : canonicalLargestPrimeFactor 1 = 1 := by
      simp [canonicalLargestPrimeFactor]
    rw [h1]
    exact one_le_canonicalLargestPrimeFactor (p * 1)

/-- Doubling a parent above the unit does not move its roughness floor. -/
theorem canonicalLargestPrimeFactor_two_mul
    {c : ℕ} (hc : 1 < c) :
    canonicalLargestPrimeFactor (2 * c) = canonicalLargestPrimeFactor c := by
  have hcPos : 0 < c := by omega
  have h2c : 1 < 2 * c := by omega
  refine le_antisymm ?_
    (canonicalLargestPrimeFactor_le_mul_prime hcPos Nat.prime_two)
  have hmem := canonicalLargestPrimeFactor_mem_primeFactors h2c
  rcases Nat.mem_primeFactors.mp hmem with ⟨hprime, hdvd, _hne⟩
  rcases (Nat.Prime.dvd_mul hprime).mp hdvd with h2 | hcdvd
  · have htwo : canonicalLargestPrimeFactor (2 * c) = 2 :=
      (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp h2
    rw [htwo]
    exact (canonicalLargestPrimeFactor_prime hc).two_le
  · exact primeFactor_le_canonicalLargestPrimeFactor hc
      (Nat.mem_primeFactors.mpr ⟨hprime, hcdvd, by omega⟩)

/-- **Mate frontier.**  The owners surviving above `c` whose mate `p*c` pushes
them past the square cutoff. -/
def endpointMateFrontier (K X c p : ℕ) : Finset ℕ :=
  (endpointOwnerFibre K X c).filter fun q => ¬ (q * q * (p * c) ≤ X)

/-- **Mate monotonicity.**  Adjoining a prime to a parent can only shrink its
owner fibre. -/
theorem endpointOwnerFibre_mul_prime_subset
    {K X c p : ℕ} (hcPos : 0 < c) (hp : p.Prime) :
    endpointOwnerFibre K X (p * c) ⊆ endpointOwnerFibre K X c := by
  intro q hq
  rcases mem_endpointOwnerFibre.mp hq with ⟨⟨hq2, hqK⟩, hqPrime, hrough, hcut⟩
  refine mem_endpointOwnerFibre.mpr ⟨⟨hq2, hqK⟩, hqPrime, ?_, ?_⟩
  · exact lt_of_le_of_lt (canonicalLargestPrimeFactor_le_mul_prime hcPos hp) hrough
  · have hcp : c ≤ p * c := by
      calc
        c = 1 * c := by ring
        _ ≤ p * c := Nat.mul_le_mul_right c hp.one_lt.le
    calc
      q * q * c ≤ q * q * (p * c) := Nat.mul_le_mul (le_refl (q * q)) hcp
      _ ≤ X := hcut

/-- **Exact mate cancellation down to the frontier.**  When the mate leaves the
roughness floor where it was, the fibre above the mate is exactly the fibre above
the parent with the frontier removed. -/
theorem endpointOwnerFibre_mul_prime_eq_sdiff_frontier
    {K X c p : ℕ} (hcPos : 0 < c) (hp : p.Prime)
    (htop : canonicalLargestPrimeFactor (p * c) =
      canonicalLargestPrimeFactor c) :
    endpointOwnerFibre K X (p * c) =
      endpointOwnerFibre K X c \ endpointMateFrontier K X c p := by
  ext q
  constructor
  · intro hq
    have hqc := endpointOwnerFibre_mul_prime_subset hcPos hp hq
    refine Finset.mem_sdiff.mpr ⟨hqc, ?_⟩
    intro hfront
    rcases Finset.mem_filter.mp hfront with ⟨_hmem, hnot⟩
    exact hnot (mem_endpointOwnerFibre.mp hq).2.2.2
  · intro hq
    rcases Finset.mem_sdiff.mp hq with ⟨hqc, hnot⟩
    rcases mem_endpointOwnerFibre.mp hqc with
      ⟨⟨hq2, hqK⟩, hqPrime, hrough, _hcut⟩
    have hcutMate : q * q * (p * c) ≤ X := by
      by_contra hcon
      exact hnot (Finset.mem_filter.mpr ⟨hqc, hcon⟩)
    refine mem_endpointOwnerFibre.mpr ⟨⟨hq2, hqK⟩, hqPrime, ?_, hcutMate⟩
    rw [htop]
    exact hrough

/-- Cardinal form of the mate cancellation. -/
theorem endpointOwnerFibre_card_eq_mate_add_frontier
    {K X c p : ℕ} (hcPos : 0 < c) (hp : p.Prime)
    (htop : canonicalLargestPrimeFactor (p * c) =
      canonicalLargestPrimeFactor c) :
    (endpointOwnerFibre K X c).card =
      (endpointOwnerFibre K X (p * c)).card +
        (endpointMateFrontier K X c p).card := by
  have hsub : endpointMateFrontier K X c p ⊆ endpointOwnerFibre K X c := by
    unfold endpointMateFrontier
    exact Finset.filter_subset _ _
  have hcard : (endpointOwnerFibre K X (p * c)).card =
      (endpointOwnerFibre K X c).card - (endpointMateFrontier K X c p).card := by
    rw [endpointOwnerFibre_mul_prime_eq_sdiff_frontier hcPos hp htop]
    exact Finset.card_sdiff hsub
  have hle : (endpointMateFrontier K X c p).card ≤
      (endpointOwnerFibre K X c).card := Finset.card_le_card hsub
  omega

end RHLean.Proof
