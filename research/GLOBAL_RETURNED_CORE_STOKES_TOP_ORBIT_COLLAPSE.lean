import Mathlib
import «research.GLOBAL_RETURNED_CORE_STOKES_TWO_STEP_BOUNDARY_NORMAL_FORM»

/-!
# Top-half Stokes orbit collapse

The canonical signed-Stokes chronology starts every nonempty remaining-owner
schedule at a prime `q > X_R / 2`.  Before estimating either of the two surviving
Stokes boundary steps, it is useful to record the exact one-dimensional geometry
forced by that top-half condition.

For any positive finite carrier contained in `[1,X]`, a `q`-interior point has
its q-toggle in the same carrier.  If `q ∤ n`, this forces `q*n <= X < 2q`, hence
`n = 1`.  If `q ∣ n`, positivity and `n <= X < 2q` force `n = q`.  Therefore

  primeInteriorPart q B ⊆ {1,q}.

On an actual first-owner base cell the surviving q-interior has at most two
sites, and the corresponding two-coordinate pair interior has at most four
states.  This is exact carrier collapse, not a density estimate or energy bound.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- **Top-half one-coordinate orbit collapse.**  On any positive carrier
bounded by `X`, a prime coordinate above `X/2` can have interior states only at
`1` and at the prime itself. -/
theorem primeInteriorPart_subset_one_insert_prime_of_top
    {B : Finset ℕ} {X q : ℕ}
    (hB : ∀ n ∈ B, 0 < n ∧ n ≤ X)
    (hq : q.Prime) (hqTop : X / 2 < q) :
    primeInteriorPart q B ⊆ ({1, q} : Finset ℕ) := by
  intro n hn
  rcases mem_primeInteriorPart.mp hn with ⟨hnB, hmateB⟩
  have hnData := hB n hnB
  have h2q : X < 2 * q := by omega
  by_cases hqn : q ∣ n
  · rcases hqn with ⟨k, hk⟩
    have hkPos : 0 < k := by
      by_contra hnot
      have hk0 : k = 0 := by omega
      rw [hk0] at hk
      simp at hk
      omega
    have hqkLt : q * k < q * 2 := by
      rw [← hk]
      exact hnData.2.trans_lt h2q
    have hkLt : k < 2 :=
      (Nat.mul_lt_mul_left hq.pos).mp hqkLt
    have hk1 : k = 1 := by omega
    rw [hk, hk1]
    simp
  · rw [primeCarrierToggle_of_not_dvd hqn] at hmateB
    have hmateData := hB (n * q) hmateB
    have hqnLt : q * n < q * 2 := by
      have h : n * q < 2 * q := hmateData.2.trans_lt h2q
      simpa [Nat.mul_comm] using h
    have hnLt : n < 2 :=
      (Nat.mul_lt_mul_left hq.pos).mp hqnLt
    have hn1 : n = 1 := by omega
    rw [hn1]
    simp

/-- The top-half collapse on the literal first-owner base carrier. -/
theorem lowOwnerFirstOwner_topPrimeInterior_subset_one_insert_prime
    {R p q : ℕ} {sig : Finset ℕ}
    (hq : q.Prime)
    (hqTop : squareRootEndpoint R / 2 < q) :
    primeInteriorPart q (lowOwnerFirstOwnerBaseFiber R p sig) ⊆
      ({1, q} : Finset ℕ) := by
  exact primeInteriorPart_subset_one_insert_prime_of_top
    (fun n hn => lowOwnerFirstOwnerBaseFiber_pos_le_endpoint hn)
    hq hqTop

/-- Consequently one top-half first-owner cell has at most two surviving
one-coordinate states. -/
theorem card_lowOwnerFirstOwner_topPrimeInterior_le_two
    {R p q : ℕ} {sig : Finset ℕ}
    (hq : q.Prime)
    (hqTop : squareRootEndpoint R / 2 < q) :
    (primeInteriorPart q (lowOwnerFirstOwnerBaseFiber R p sig)).card ≤ 2 := by
  have hsub :=
    lowOwnerFirstOwner_topPrimeInterior_subset_one_insert_prime
      (R := R) (p := p) (q := q) (sig := sig) hq hqTop
  calc
    (primeInteriorPart q (lowOwnerFirstOwnerBaseFiber R p sig)).card ≤
        (({1, q} : Finset ℕ).card) := Finset.card_le_card hsub
    _ ≤ 2 := by simp

/-- **Top-half pair collapse.**  After the first canonical Stokes peel, the
complete two-coordinate interior of any first-owner/signature cell has at most
four states. -/
theorem card_lowOwnerFirstOwner_topPrimePairInterior_le_four
    {R p q : ℕ} {sig : Finset ℕ}
    (hq : q.Prime)
    (hqTop : squareRootEndpoint R / 2 < q) :
    (pairPrimeTwoCoordinateInterior q
      (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)).card ≤ 4 := by
  unfold lowOwnerFirstOwnerSignedCellPairCarrier
  rw [pairPrimeTwoCoordinateInterior_product, Finset.card_product]
  have hcard :=
    card_lowOwnerFirstOwner_topPrimeInterior_le_two
      (R := R) (p := p) (q := q) (sig := sig) hq hqTop
  calc
    (primeInteriorPart q (lowOwnerFirstOwnerBaseFiber R p sig)).card *
        (primeInteriorPart q (lowOwnerFirstOwnerBaseFiber R p sig)).card ≤
      2 * 2 := Nat.mul_le_mul hcard hcard
    _ = 4 := by norm_num

end RHLean.Proof
