import RHLean.Proof.StableFarWallUnitRenewalCentering

/-!
# Exact outer-owner window of the centered stable-far renewal

After depth-one renewal, every nonunit crossing return lands at one descended
child `y = (r,(e,p))`.  The remaining coefficient is the number of old outer
owners `q` that could have produced that same child.

This file makes that multiplicity arithmetic.  The fibre over `y` is in
bijection, by the outer-owner coordinate, with the prime window

  r < q < R,
  q*r*e*p <= X_R < q^2*r*e*p.

No owner is discarded and no cardinality estimate is used.  This is the exact
prime-window coordinate on which a first-failure/Buchstab or prime-count
finite-difference argument can act.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Exact fibre of nonunit crossings returning to one descended child. -/
def lowWheelFarPrimeQ2CrossingNextFiber
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeQ2NonUnitCrossingTriples R).filter fun t =>
    lowWheelFarPrimeQ2CrossingNextChild t = y

/-- Arithmetic window of possible old outer owners for one descended child. -/
def lowWheelFarPrimeQ2CrossingOuterOwnerSet
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) : Finset ℕ :=
  (primesUpTo (R - 1)).filter fun q =>
    y.1 < q ∧
      q * y.1 * y.2.1 * y.2.2 ≤ squareRootEndpoint R ∧
      squareRootEndpoint R < q * q * y.1 * y.2.1 * y.2.2

/-- A point in one next-child fibre has its stripped cofactor and far prime
uniquely recovered from the child. -/
theorem lowWheelFarPrimeQ2CrossingNextFiber_coordinates
    {R : ℕ} {y t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeQ2CrossingNextFiber R y) :
    t.2.1 = y.1 * y.2.1 ∧ t.2.2 = y.2.2 := by
  have htNon := (Finset.mem_filter.mp ht).1
  have hnext := (Finset.mem_filter.mp ht).2
  have hdgt : 1 < t.2.1 := (Finset.mem_filter.mp htNon).2
  have hlpf : canonicalLargestPrimeFactor t.2.1 = y.1 :=
    congrArg (fun z : ℕ × (ℕ × ℕ) => z.1) hnext
  have hcof : canonicalCofactor t.2.1 = y.2.1 :=
    congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.1) hnext
  have hp : t.2.2 = y.2.2 :=
    congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.2) hnext
  have hprod := canonicalCofactor_mul_largestPrimeFactor hdgt
  constructor
  · calc
      t.2.1 = canonicalCofactor t.2.1 *
          canonicalLargestPrimeFactor t.2.1 := hprod.symm
      _ = y.2.1 * y.1 := by rw [hcof, hlpf]
      _ = y.1 * y.2.1 := by ring
  · exact hp

/-- Forgetting everything except the old outer owner is injective on one
next-child fibre. -/
theorem lowWheelFarPrimeQ2CrossingNextFiber_fst_injOn
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) :
    Set.InjOn Prod.fst (lowWheelFarPrimeQ2CrossingNextFiber R y :
      Set (ℕ × (ℕ × ℕ))) := by
  intro a ha b hb hq
  have haCoord := lowWheelFarPrimeQ2CrossingNextFiber_coordinates
    (Finset.mem_coe.mp ha)
  have hbCoord := lowWheelFarPrimeQ2CrossingNextFiber_coordinates
    (Finset.mem_coe.mp hb)
  apply Prod.ext hq
  apply Prod.ext
  · exact haCoord.1.trans hbCoord.1.symm
  · exact haCoord.2.trans hbCoord.2.symm

/-- **Exact owner-window classification.**  On an actual descended child, the
outer-owner projection of its renewal fibre is precisely the explicit prime
window `r<q<R`, `q*r*e*p<=X_R<q^2*r*e*p`. -/
theorem lowWheelFarPrimeQ2CrossingNextFiber_fst_image_eq_ownerSet
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    (lowWheelFarPrimeQ2CrossingNextFiber R y).image Prod.fst =
      lowWheelFarPrimeQ2CrossingOuterOwnerSet R y := by
  ext q
  constructor
  · intro hqImage
    rcases Finset.mem_image.mp hqImage with ⟨t, htFiber, htq⟩
    have htNon := (Finset.mem_filter.mp htFiber).1
    have htCross := (Finset.mem_filter.mp htNon).1
    have hbase : t ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp htCross).1
    have hcross := (Finset.mem_filter.mp htCross).2
    rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
      ⟨htPrime, htR, _hd1, _hpPrime, _hpR, _hdsq, hdq, hcut⟩
    have hnext := (Finset.mem_filter.mp htFiber).2
    have hlpf : canonicalLargestPrimeFactor t.2.1 = y.1 :=
      congrArg (fun z : ℕ × (ℕ × ℕ) => z.1) hnext
    have hcoord := lowWheelFarPrimeQ2CrossingNextFiber_coordinates htFiber
    subst q
    apply Finset.mem_filter.mpr
    refine ⟨mem_primesUpTo.mpr ⟨htPrime, Nat.le_pred_of_lt htR⟩, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [hlpf] using hdq
    · simpa [hcoord.1, hcoord.2, Nat.mul_assoc] using hcut
    · simpa [hcoord.1, hcoord.2, Nat.mul_assoc] using hcross
  · intro hqOwner
    rcases Finset.mem_filter.mp hqOwner with ⟨hqOld, hrq, hcut, hcross⟩
    have hqData := mem_primesUpTo.mp hqOld
    have hyBase : y ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp hy).1
    rcases lowWheelFarPrimeLowCofactorTriple_data hyBase with
      ⟨hrPrime, hrR, he1, hpPrime, hpR, heSq, her, _hyCut⟩
    have hRpos : 0 < R := hrPrime.pos.trans hrR
    have hqR : q < R := Nat.lt_of_le_pred hRpos hqData.2
    have hnot : ¬ y.1 ∣ y.2.1 :=
      squareRootLowPrimePrime_fresh_of_lpf_lt he1 hrPrime her
    have hcop : Nat.Coprime y.1 y.2.1 :=
      (hrPrime.coprime_iff_not_dvd).2 hnot
    have hdSq : Squarefree (y.1 * y.2.1) :=
      (Nat.squarefree_mul hcop).2 ⟨hrPrime.squarefree, heSq⟩
    have hd1 : 1 ≤ y.1 * y.2.1 := by
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hrPrime.ne_zero (by omega))
    have hlpf : canonicalLargestPrimeFactor (y.1 * y.2.1) = y.1 := by
      have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough
        (by omega : 0 < y.2.1) hrPrime her
      simpa [Nat.mul_comm] using h
    have hcof : canonicalCofactor (y.1 * y.2.1) = y.2.1 := by
      have h := canonicalCofactor_mul_prime_eq_of_rough
        (by omega : 0 < y.2.1) hrPrime her
      simpa [Nat.mul_comm] using h
    have hdq : canonicalLargestPrimeFactor (y.1 * y.2.1) < q := by
      rw [hlpf]
      exact hrq
    have htriple :
        (q, (y.1 * y.2.1, y.2.2)) ∈ lowWheelFarPrimeLowCofactorTriples R := by
      apply lowWheelFarPrimeLowCofactorTriple_mem_of_data
        hqData.1 hqR hd1 hpPrime hpR hdSq hdq
      simpa [Nat.mul_assoc] using hcut
    have hcrossTriple :
        (q, (y.1 * y.2.1, y.2.2)) ∈ lowWheelFarPrimeQ2CrossingTriples R :=
      Finset.mem_filter.mpr ⟨htriple, by
        simpa [Nat.mul_assoc] using hcross⟩
    have hdgt : 1 < y.1 * y.2.1 := by
      have hr2 := hrPrime.two_le
      nlinarith
    have hnon :
        (q, (y.1 * y.2.1, y.2.2)) ∈
          lowWheelFarPrimeQ2NonUnitCrossingTriples R :=
      Finset.mem_filter.mpr ⟨hcrossTriple, hdgt⟩
    have hnext :
        lowWheelFarPrimeQ2CrossingNextChild
            (q, (y.1 * y.2.1, y.2.2)) = y := by
      simp [lowWheelFarPrimeQ2CrossingNextChild, hlpf, hcof]
    have hfiber :
        (q, (y.1 * y.2.1, y.2.2)) ∈
          lowWheelFarPrimeQ2CrossingNextFiber R y :=
      Finset.mem_filter.mpr ⟨hnon, hnext⟩
    exact Finset.mem_image.mpr
      ⟨(q, (y.1 * y.2.1, y.2.2)), hfiber, rfl⟩

/-- **Multiplicity is exactly prime-window cardinality.**  The centered
coefficient introduced in the renewal normal form is not an opaque fibre count:
it is the number of primes in the explicit second-contact owner window. -/
theorem lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_ownerSet_card
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingNextMultiplicity R y =
      (lowWheelFarPrimeQ2CrossingOuterOwnerSet R y).card := by
  have himage := lowWheelFarPrimeQ2CrossingNextFiber_fst_image_eq_ownerSet hy
  have hinj := lowWheelFarPrimeQ2CrossingNextFiber_fst_injOn R y
  calc
    lowWheelFarPrimeQ2CrossingNextMultiplicity R y =
        (lowWheelFarPrimeQ2CrossingNextFiber R y).card := by rfl
    _ = ((lowWheelFarPrimeQ2CrossingNextFiber R y).image Prod.fst).card := by
      symm
      exact Finset.card_image_iff.mpr hinj
    _ = (lowWheelFarPrimeQ2CrossingOuterOwnerSet R y).card := by rw [himage]

end RHLean.Proof
