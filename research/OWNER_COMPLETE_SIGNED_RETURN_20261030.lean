import Mathlib
import «research.COVARIANCE_REMAINDER_OWNER_FUBINI»
import «research.ZERO_TARGET_SQUARE_FINITE_DIFFERENCE_REDUCTION»

/-!
# Exact signed return on the original owner fibres

A sum of squared reciprocal amplitudes is not the square of their signed sum.
All children of one fixed parent have the opposite parent sign, so their
within-fibre mixed terms reinforce. The complete physical fibre below is
proved by owner chronology, the two-candidate theorem, and coprimality.
No arbitrary coefficient model or full-return power estimate is assumed.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

theorem ownerReturn_child_reciprocalAmplitude
    {W p : ℕ} {parent mn : ℕ × ℕ}
    (hmnMem : mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p) :
    postRootCovarianceReciprocalPairAmplitude mn =
      -(1 / (p : ℝ)) * postRootCovarianceReciprocalPairAmplitude parent := by
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hmnMem with ⟨hownerFilter, hparent⟩
  rcases Finset.mem_filter.mp hownerFilter with ⟨hweightFilter, howner⟩
  rcases Finset.mem_filter.mp hweightFilter with ⟨hrec, hweight⟩
  rcases Finset.mem_filter.mp hrec with ⟨hremainder, _hparentNe⟩
  have hphysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hremainder).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hphysical with
    ⟨hm1, _hmW, hn1, _hnW, hmnlt⟩
  have hmstep : realMoebiusStep m ≠ 0 := by
    intro hmzero
    exact hweight (by rw [hmzero, zero_mul])
  have hnstep : realMoebiusStep n ≠ 0 := by
    intro hnzero
    exact hweight (by rw [hnzero, mul_zero])
  have ha := postRootCovarianceReciprocalPairAmplitude_owner_descent
    (squarefree_of_realMoebiusStep_ne_zero hmstep)
    (squarefree_of_realMoebiusStep_ne_zero hnstep)
    (ne_of_lt hmnlt) (by omega) (by omega)
  dsimp only at ha
  rw [howner] at ha
  have hp' : covarianceOrderedPair
      (squarefreePrimeFamilyParent p m)
      (squarefreePrimeFamilyParent p n) = parent := by
    unfold squarefreePairFreshPrimeOrderedParent at hparent
    simpa [howner] using! hparent
  rwa [hp'] at ha

/-- The coherent coefficient is k/p, not k/p^2. -/
theorem ownerReturn_fixedOwner_signed_sum
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
      postRootCovarianceReciprocalPairAmplitude mn) =
      -((postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
        (p : ℝ)) * postRootCovarianceReciprocalPairAmplitude parent := by
  calc
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
      postRootCovarianceReciprocalPairAmplitude mn) =
      ∑ _mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        -(1 / (p : ℝ)) * postRootCovarianceReciprocalPairAmplitude parent := by
      apply Finset.sum_congr rfl
      intro mn hmn
      exact ownerReturn_child_reciprocalAmplitude hmn
    _ = _ := by
      unfold postRootCovarianceFixedOwnerChildMultiplicity
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

def ownerReturnSignedReciprocalOutgoing (W : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ p ∈ primesUpTo W,
    ∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
      postRootCovarianceReciprocalPairAmplitude mn

def ownerReturnHarmonicMultiplicity (W : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ p ∈ primesUpTo W,
    (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) / (p : ℝ)

theorem ownerReturnSignedReciprocalOutgoing_eq
    (W : ℕ) (parent : ℕ × ℕ) :
    ownerReturnSignedReciprocalOutgoing W parent =
      -ownerReturnHarmonicMultiplicity W parent *
        postRootCovarianceReciprocalPairAmplitude parent := by
  unfold ownerReturnSignedReciprocalOutgoing ownerReturnHarmonicMultiplicity
  simp_rw [ownerReturn_fixedOwner_signed_sum, neg_mul]
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul]

/-- Physical inverse weights exactly remove the reciprocal suppression. -/
theorem ownerReturn_pair_unweight (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ((m : ℝ) * (n : ℝ)) *
      postRootCovarianceReciprocalPairAmplitude (m, n) =
        realMoebiusStep m * realMoebiusStep n := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  unfold postRootCovarianceReciprocalPairAmplitude
  dsimp only
  field_simp [hm0, hn0]

/-- Complete square, with every coherent cross term retained. -/
theorem ownerReturn_signed_square_eq_diagonal_add_cross
    (S : Finset (ℕ × ℕ)) :
    (∑ mn ∈ S, postRootCovarianceReciprocalPairAmplitude mn) ^ 2 =
      (∑ mn ∈ S, postRootCovarianceReciprocalPairEnergy mn) +
      ∑ mn ∈ S, ∑ uv ∈ S.erase mn,
        postRootCovarianceReciprocalPairAmplitude mn *
          postRootCovarianceReciprocalPairAmplitude uv := by
  let a := postRootCovarianceReciprocalPairAmplitude
  have hsplit (mn : ℕ × ℕ) (hmn : mn ∈ S) :
      (∑ uv ∈ S, a mn * a uv) = a mn ^ 2 +
        ∑ uv ∈ S.erase mn, a mn * a uv := by
    rw [← Finset.sum_erase_add _ _ hmn]
    ring
  change (∑ mn ∈ S, a mn) ^ 2 =
    (∑ mn ∈ S, a mn ^ 2) + ∑ mn ∈ S, ∑ uv ∈ S.erase mn, a mn * a uv
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    (∑ mn ∈ S, ∑ uv ∈ S, a mn * a uv) =
      ∑ mn ∈ S, (a mn ^ 2 + ∑ uv ∈ S.erase mn, a mn * a uv) := by
      apply Finset.sum_congr rfl
      exact hsplit
    _ = _ := Finset.sum_add_distrib

/-! ## Actual arithmetic fibre: complete support proved structurally -/

private theorem ownerReturn_face_values :
    squarefreePairFreshPrimeSet 1 7 = {7} ∧
    squarefreePairFreshPrimeSet 1 14 = {2,7} ∧
    squarefreePairFreshPrimeSet 1 21 = {3,7} ∧
    squarefreePairFreshPrimeSet 1 35 = {5,7} ∧
    squarefreePairFreshPrimeSet 2 7 = {2,7} ∧
    squarefreePairFreshPrimeSet 3 7 = {3,7} ∧
    squarefreePairFreshPrimeSet 5 7 = {5,7} := by
  decide +kernel

/-- Exact original least-separating-prime labels. -/
theorem ownerReturn_owner_values :
    squarefreePairFreshPrimeOwner 1 7 = 7 ∧
    squarefreePairFreshPrimeOwner 1 14 = 2 ∧
    squarefreePairFreshPrimeOwner 1 21 = 3 ∧
    squarefreePairFreshPrimeOwner 1 35 = 5 ∧
    squarefreePairFreshPrimeOwner 2 7 = 2 ∧
    squarefreePairFreshPrimeOwner 3 7 = 3 ∧
    squarefreePairFreshPrimeOwner 5 7 = 5 := by
  rcases ownerReturn_face_values with ⟨h7,h14,h21,h35,h2,h3,h5⟩
  simp [squarefreePairFreshPrimeOwner,h7,h14,h21,h35,h2,h3,h5]

private theorem ownerReturn_parent_values :
    squarefreePairFreshPrimeOrderedParent 1 14 = (1,7) ∧
    squarefreePairFreshPrimeOrderedParent 1 21 = (1,7) ∧
    squarefreePairFreshPrimeOrderedParent 1 35 = (1,7) ∧
    squarefreePairFreshPrimeOrderedParent 2 7 = (1,7) ∧
    squarefreePairFreshPrimeOrderedParent 3 7 = (1,7) ∧
    squarefreePairFreshPrimeOrderedParent 5 7 = (1,7) := by
  rcases ownerReturn_owner_values with ⟨_h7,h14,h21,h35,h2,h3,h5⟩
  norm_num [squarefreePairFreshPrimeOrderedParent,
    squarefreePrimeFamilyParent,h14,h21,h35,h2,h3,h5]

private theorem ownerReturn_mu_values :
    (μ 1 : ℤ) = 1 ∧ (μ 2 : ℤ) = -1 ∧ (μ 3 : ℤ) = -1 ∧
    (μ 5 : ℤ) = -1 ∧ (μ 7 : ℤ) = -1 ∧ (μ 14 : ℤ) = 1 ∧
    (μ 21 : ℤ) = 1 ∧ (μ 35 : ℤ) = 1 := by
  decide +kernel

private theorem ownerReturn_coprime_mem_remainder
    {W m n : ℕ} (hm : 1 ≤ m) (hmW : m ≤ W)
    (hn : 1 ≤ n) (hnW : n ≤ W) (hmn : m < n) (hcop : Nat.Coprime m n) :
    (m,n) ∈ postRootCovarianceRemainderPhysicalPairCarrier W := by
  apply mem_postRootCovarianceRemainderPhysicalPairCarrier.mpr
  refine ⟨mem_mertensPositivePhysicalPairCarrier.mpr ⟨hm,hmW,hn,hnW,hmn⟩, ?_⟩
  intro hbad
  rcases mem_postRootPrimePhysicalPairUnion.mp hbad with ⟨p,hp,hpair⟩
  rcases mem_postRootPrimePhysicalPairCarrier.mp hpair with
    ⟨_hm,_hmW,_hn,_hnW,_hmn,hpm,hpn⟩
  have hg : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hpn
  rw [hcop.gcd_eq_one] at hg
  have hp1 : p = 1 := Nat.eq_one_of_dvd_one hg
  exact (mem_postRootPrimeFamilySet.mp hp).2.2.ne_one hp1

private theorem ownerReturn_coprime_child_mem
    {m n : ℕ} (hm : 1 ≤ m) (hmW : m ≤ 35)
    (hn : 1 ≤ n) (hnW : n ≤ 35) (hmn : m < n) (hcop : Nat.Coprime m n)
    (hw : realMoebiusStep m * realMoebiusStep n ≠ 0)
    (hp : squarefreePairFreshPrimeOrderedParent m n = (1,7)) :
    (m,n) ∈ postRootCovarianceFixedParentChildFiber 35 (1,7) := by
  have hrem := ownerReturn_coprime_mem_remainder hm hmW hn hnW hmn hcop
  have hne : ¬ SquarefreePairFreshPrimeParentsEqual (m,n) := by
    intro heq
    change squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m =
      squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n at heq
    have hdiag : (squarefreePairFreshPrimeOrderedParent m n).1 =
        (squarefreePairFreshPrimeOrderedParent m n).2 := by
      simp [squarefreePairFreshPrimeOrderedParent,heq]
    rw [hp] at hdiag
    norm_num at hdiag
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hrem,hne⟩,hw⟩,hp⟩

/-- ENTIRE original fibre: chronology forces p<7, hence p=2,3,5; each has
exactly the two admitted mixed-corner children. -/
theorem ownerReturn_parent_one_seven_at_35 :
    postRootCovarianceFixedParentChildFiber 35 (1, 7) =
      {(1, 14), (1, 21), (1, 35), (2, 7), (3, 7), (5, 7)} := by
  ext mn
  constructor
  · rcases mn with ⟨m,n⟩
    intro hmem
    rcases Finset.mem_filter.mp hmem with ⟨hweighted,hparent⟩
    rcases Finset.mem_filter.mp hweighted with ⟨hrec,hweight⟩
    have hdesc := postRootCovarianceRemainderRecursivePair_owner_descent hrec hweight
    dsimp only at hdesc
    have hlt : squarefreePairFreshPrimeOwner m n < 7 := by
      have hh := hdesc.2.1
      rw [hparent] at hh
      simpa only [ownerReturn_owner_values.1] using hh
    have hphys := (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp
      (Finset.mem_filter.mp hrec).1).1
    rcases mem_mertensPositivePhysicalPairCarrier.mp hphys with
      ⟨hm,_hmW,hn,_hnW,hmn⟩
    have hm0 : realMoebiusStep m ≠ 0 := by
      intro hz
      exact hweight (by rw [hz,zero_mul])
    have hn0 : realMoebiusStep n ≠ 0 := by
      intro hz
      exact hweight (by rw [hz,mul_zero])
    have hprime := squarefreePairFreshPrimeOwner_prime
      (squarefree_of_realMoebiusStep_ne_zero hm0)
      (squarefree_of_realMoebiusStep_ne_zero hn0) (ne_of_lt hmn)
    have hsmall (p : ℕ) (hp : p.Prime) (hp7 : p < 7) :
        p = 2 ∨ p = 3 ∨ p = 5 := by
      have hp2 := hp.two_le
      interval_cases p <;> norm_num at *
    have hcases := hsmall _ hprime hlt
    have hfixed : (m,n) ∈ postRootCovarianceFixedOwnerChildFiber 35 (1,7)
        (squarefreePairFreshPrimeOwner m n) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hrec,hweight⟩,rfl⟩,hparent⟩
    have hc := postRootCovarianceFixedOwnerChildFiber_subset_candidates
      35 (1,7) (squarefreePairFreshPrimeOwner m n) hfixed
    rcases hcases with hp | hp | hp <;>
      simp [hp,covarianceOwnerChildCandidates,covarianceOrderedPair] at hc
    all_goals
      simp only [Finset.mem_insert,Finset.mem_singleton]
      aesop
  · intro hmem
    rcases ownerReturn_parent_values with ⟨hp14,hp21,hp35,hp2,hp3,hp5⟩
    rcases ownerReturn_mu_values with ⟨h1,h2,h3,h5,h7,h14,h21,h35⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      apply ownerReturn_coprime_child_mem <;>
        norm_num [realMoebiusStep,h1,h2,h3,h5,h7,h14,h21,h35,
          hp14,hp21,hp35,hp2,hp3,hp5]

theorem ownerReturn_fibre_diagonal_energy :
    (∑ mn ∈ postRootCovarianceFixedParentChildFiber 35 (1, 7),
      postRootCovarianceReciprocalPairEnergy mn) = (361 / 22050 : ℝ) := by
  rcases ownerReturn_mu_values with ⟨h1,h2,h3,h5,h7,h14,h21,h35⟩
  rw [ownerReturn_parent_one_seven_at_35]
  norm_num [postRootCovarianceReciprocalPairEnergy,
    postRootCovarianceReciprocalPairAmplitude, realMoebiusStep,
    h1,h2,h3,h5,h7,h14,h21,h35]

theorem ownerReturn_fibre_signed_amplitude :
    (∑ mn ∈ postRootCovarianceFixedParentChildFiber 35 (1, 7),
      postRootCovarianceReciprocalPairAmplitude mn) = (31 / 105 : ℝ) := by
  rcases ownerReturn_mu_values with ⟨h1,h2,h3,h5,h7,h14,h21,h35⟩
  rw [ownerReturn_parent_one_seven_at_35]
  norm_num [postRootCovarianceReciprocalPairAmplitude,realMoebiusStep,
    h1,h2,h3,h5,h7,h14,h21,h35]

theorem ownerReturn_fibre_unweighted_mass :
    (∑ mn ∈ postRootCovarianceFixedParentChildFiber 35 (1, 7),
      realMoebiusStep mn.1 * realMoebiusStep mn.2) = 6 := by
  rcases ownerReturn_mu_values with ⟨h1,h2,h3,h5,h7,h14,h21,h35⟩
  rw [ownerReturn_parent_one_seven_at_35]
  norm_num [realMoebiusStep,h1,h2,h3,h5,h7,h14,h21,h35]

/-- Diagonal energy contracts but coherent signed-square energy expands on
this genuine physical fibre. No global cross-parent theorem is refuted. -/
theorem ownerReturn_actual_diagonal_contracts_but_signed_square_expands :
    (∑ mn ∈ postRootCovarianceFixedParentChildFiber 35 (1, 7),
      postRootCovarianceReciprocalPairEnergy mn) <
        postRootCovarianceReciprocalPairEnergy (1, 7) ∧
    postRootCovarianceReciprocalPairEnergy (1, 7) <
      (∑ mn ∈ postRootCovarianceFixedParentChildFiber 35 (1, 7),
        postRootCovarianceReciprocalPairAmplitude mn) ^ 2 := by
  rcases ownerReturn_mu_values with ⟨h1,_h2,_h3,_h5,h7,_h14,_h21,_h35⟩
  rw [ownerReturn_fibre_diagonal_energy,ownerReturn_fibre_signed_amplitude]
  norm_num [postRootCovarianceReciprocalPairEnergy,
    postRootCovarianceReciprocalPairAmplitude,realMoebiusStep,h1,h7]

#print axioms ownerReturnSignedReciprocalOutgoing_eq
#print axioms ownerReturn_pair_unweight
#print axioms ownerReturn_signed_square_eq_diagonal_add_cross
#print axioms ownerReturn_parent_one_seven_at_35
#print axioms ownerReturn_actual_diagonal_contracts_but_signed_square_expands

end RHLean.Proof
