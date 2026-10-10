import «research.VF_MID_919_OAI_NATIVE_PRINCIPAL_WELD»

/-!
# A native AMP obstruction to one occurrencewise centered rectangle

The witness uses the existing physical AMP weight, not a replacement weight.
It excludes a single difference of two separable products on independent
factor occurrences. It does not exclude regrouping over factorizations or
several rectangles, and supplies no uniform analytic estimate.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic

/-- One centered rectangle has a vanishing three-by-three determinant,
including complex separable phases absorbed into the four factors. -/
theorem vf919CenteredRectangle_det_eq_zero
    (f g u v : Fin 3 → ℂ) :
    Matrix.det (fun i j => f i * g j - u i * v j) = 0 := by
  rw [Matrix.det_fin_three]
  ring

/-- The literal native low reciprocal owners at the witness root. -/
theorem vf919LowOwners317 :
    canonicalRoughLowQ2Owners 317 = {3, 5, 7, 11, 13, 17} := by
  classical
  ext q
  have hm : q ∈ canonicalRoughLowQ2Owners 317 ↔
      q ≠ 2 ∧ (q.Prime ∧ q ≤ 316) ∧ q * q < 317 := by
    simp only [canonicalRoughLowQ2Owners, canonicalRoughHighQ2Owners,
      Finset.mem_sdiff, Finset.mem_filter, Finset.mem_erase,
      mem_primesUpTo, show 317 - 1 = 316 by norm_num]
    constructor
    · rintro ⟨hq, hnot⟩
      refine ⟨hq.1, hq.2, ?_⟩
      by_contra h
      exact hnot ⟨hq, by omega⟩
    · rintro ⟨hne, hp, hs⟩
      exact ⟨⟨hne, hp⟩, fun h => by omega⟩
  rw [hm]
  constructor
  · rintro ⟨hne, ⟨hp, _⟩, hs⟩
    have hq : q ≤ 17 := by nlinarith
    revert hp hne
    interval_cases q <;> norm_num
  · intro hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def vf919RankWitnessRows : Fin 3 → ℕ := ![7, 13, 19]
def vf919RankWitnessColumns : Fin 3 → ℕ := ![31, 37, 61]

/-- These are distinct-prime, odd squarefree sites inside both physical
parent and doubled-child cutoffs; every prime factor is 1 modulo 3. -/
theorem vf919RankWitness_sites (i j : Fin 3) :
    (vf919RankWitnessRows i).Prime ∧
    (vf919RankWitnessColumns j).Prime ∧
    vf919RankWitnessRows i % 3 = 1 ∧
    vf919RankWitnessColumns j % 3 = 1 ∧
    Odd (vf919RankWitnessRows i * vf919RankWitnessColumns j) ∧
    Squarefree (vf919RankWitnessRows i * vf919RankWitnessColumns j) ∧
    2 * (vf919RankWitnessRows i * vf919RankWitnessColumns j) ≤
      squareRootEndpoint 317 := by
  have hp : (vf919RankWitnessRows i).Prime := by
    fin_cases i <;> norm_num [vf919RankWitnessRows]
  have hp' : (vf919RankWitnessColumns j).Prime := by
    fin_cases j <;> norm_num [vf919RankWitnessColumns]
  have hc : (vf919RankWitnessRows i).Coprime (vf919RankWitnessColumns j) :=
    (Nat.coprime_primes hp hp').2 (by
      fin_cases i <;> fin_cases j <;> decide)
  refine ⟨hp, hp', ?_, ?_, ?_,
    (Nat.squarefree_mul hc).2 ⟨hp.prime.squarefree, hp'.prime.squarefree⟩, ?_⟩
  · fin_cases i <;> decide
  · fin_cases j <;> decide
  · fin_cases i <;> fin_cases j <;> decide
  · fin_cases i <;> fin_cases j <;> decide

/-- The coefficient matrix is taken directly from the native AMP definition. -/
def vf919OwnerTwoSiteMatrix317 : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => (255255 : ℂ) *
    (lowOwnerZeroFrequencyMobiusWeight 317
      (vf919RankWitnessRows i * vf919RankWitnessColumns j) : ℂ)

theorem vf919OwnerTwoSiteMatrix317_eq :
    vf919OwnerTwoSiteMatrix317 =
      !![230456, 230456, 470696;
         470696, 470696, 451061;
         470696, 451061, 427856] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [vf919OwnerTwoSiteMatrix317, vf919RankWitnessRows,
      vf919RankWitnessColumns, lowOwnerZeroFrequencyMobiusWeight,
      lowOwnerFarTailWeight, lowOwnerReciprocalDaughterWeight,
      vf919LowOwners317, rawQ2ChildCutoff, squareRootEndpoint]

theorem vf919OwnerTwoSiteMatrix317_det :
    Matrix.det vf919OwnerTwoSiteMatrix317 = -2309174383131000 := by
  rw [vf919OwnerTwoSiteMatrix317_eq, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two]

theorem vf919OwnerTwoSiteMatrix317_det_ne_zero :
    Matrix.det vf919OwnerTwoSiteMatrix317 ≠ 0 := by
  rw [vf919OwnerTwoSiteMatrix317_det]
  norm_num

/-- No single centered separable rectangle, even with complex factors,
matches these physical coefficients occurrence by occurrence. -/
theorem vf919OwnerTwoSiteMatrix317_not_single_centered_rectangle :
    ¬ ∃ f g u v : Fin 3 → ℂ, ∀ i j,
      vf919OwnerTwoSiteMatrix317 i j = f i * g j - u i * v j := by
  rintro ⟨f, g, u, v, h⟩
  apply vf919OwnerTwoSiteMatrix317_det_ne_zero
  have heq : vf919OwnerTwoSiteMatrix317 =
      (fun i j => f i * g j - u i * v j) := by
    funext i j
    exact h i j
  rw [heq]
  exact vf919CenteredRectangle_det_eq_zero f g u v

end RHLean.Proof
