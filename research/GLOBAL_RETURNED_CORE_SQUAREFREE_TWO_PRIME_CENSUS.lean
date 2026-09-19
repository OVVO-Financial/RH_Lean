import Mathlib

/-!
# Exact squarefree two-prime intersection census

This file keeps the two-prime count on the literal nonzero Möbius carrier.
There is no density estimate and no probabilistic input here.

For distinct primes `q,s`, multiplication by `q*s` identifies the squarefree
physical sites `n <= X` carrying both prime coordinates with cofactors

  m <= X / (q*s)

that are squarefree and relatively prime to `q*s`.

Thus the familiar `6/pi^2` squarefree density is not inserted as an assumption:
the finite carrier is first rewritten exactly into its squarefree cofactor
coordinate. Any later asymptotic density estimate can be applied to that
literal carrier.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The actual nonzero-Möbius sites on `[1,X]` carrying both prime coordinates. -/
def lowOwnerTwoPrimeMobiusIntersectionCarrier
    (X q s : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n =>
    μ n ≠ 0 ∧ q ∣ n ∧ s ∣ n

/-- The same physical population written directly as squarefree sites. -/
def lowOwnerTwoPrimeSquarefreeIntersectionCarrier
    (X q s : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n =>
    Squarefree n ∧ q ∣ n ∧ s ∣ n

/-- Cofactors remaining after removing the two distinct prime coordinates. -/
def lowOwnerTwoPrimeSquarefreeCofactorCarrier
    (X q s : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (X / (q * s))).filter fun m =>
    Squarefree m ∧ IsRelPrime (q * s) m

@[simp] theorem mem_lowOwnerTwoPrimeMobiusIntersectionCarrier
    {X q s n : ℕ} :
    n ∈ lowOwnerTwoPrimeMobiusIntersectionCarrier X q s ↔
      1 ≤ n ∧ n ≤ X ∧ μ n ≠ 0 ∧ q ∣ n ∧ s ∣ n := by
  simp [lowOwnerTwoPrimeMobiusIntersectionCarrier, and_assoc]

@[simp] theorem mem_lowOwnerTwoPrimeSquarefreeIntersectionCarrier
    {X q s n : ℕ} :
    n ∈ lowOwnerTwoPrimeSquarefreeIntersectionCarrier X q s ↔
      1 ≤ n ∧ n ≤ X ∧ Squarefree n ∧ q ∣ n ∧ s ∣ n := by
  simp [lowOwnerTwoPrimeSquarefreeIntersectionCarrier, and_assoc]

@[simp] theorem mem_lowOwnerTwoPrimeSquarefreeCofactorCarrier
    {X q s m : ℕ} :
    m ∈ lowOwnerTwoPrimeSquarefreeCofactorCarrier X q s ↔
      1 ≤ m ∧ m ≤ X / (q * s) ∧ Squarefree m ∧ IsRelPrime (q * s) m := by
  simp [lowOwnerTwoPrimeSquarefreeCofactorCarrier, and_assoc]

/-- Nonzero Möbius support is exactly squarefree support. -/
theorem moebius_ne_zero_iff_squarefree {n : ℕ} :
    μ n ≠ 0 ↔ Squarefree n :=
  ArithmeticFunction.moebius_ne_zero_iff_squarefree

/-- The literal nonzero-Möbius intersection carrier is the squarefree carrier. -/
theorem lowOwnerTwoPrimeMobiusIntersectionCarrier_eq_squarefree
    (X q s : ℕ) :
    lowOwnerTwoPrimeMobiusIntersectionCarrier X q s =
      lowOwnerTwoPrimeSquarefreeIntersectionCarrier X q s := by
  ext n
  simp [moebius_ne_zero_iff_squarefree]

/-- Distinct prime coordinates themselves form a squarefree product. -/
theorem squarefree_two_distinct_primes
    {q s : ℕ} (hq : q.Prime) (hs : s.Prime) (hqs : q ≠ s) :
    Squarefree (q * s) := by
  have hqNot : ¬ q ∣ s := by
    intro hdiv
    exact hqs ((Nat.prime_dvd_prime_iff_eq hq hs).mp hdiv)
  exact squarefree_mul_iff.mpr
    ⟨hq.isRelPrime_iff_not_dvd.mpr hqNot, hq.squarefree, hs.squarefree⟩

/-- Removing the two distinct prime coordinates leaves exactly a squarefree
cofactor relatively prime to their product. -/
theorem squarefree_twoPrime_mul_cofactor_iff
    {q s m : ℕ} (hq : q.Prime) (hs : s.Prime) (hqs : q ≠ s) :
    Squarefree (q * s * m) ↔
      Squarefree m ∧ IsRelPrime (q * s) m := by
  have hqsSq : Squarefree (q * s) :=
    squarefree_two_distinct_primes hq hs hqs
  constructor
  · intro h
    have hsplit := squarefree_mul_iff.mp h
    exact ⟨hsplit.2.2, hsplit.1⟩
  · rintro ⟨hmSq, hrel⟩
    exact squarefree_mul_iff.mpr ⟨hrel, hqsSq, hmSq⟩

/-- Multiplication by `q*s` carries precisely the squarefree cofactor carrier
onto the physical two-prime squarefree intersection carrier. -/
theorem mul_twoPrime_mem_squarefreeIntersection_iff_mem_cofactor
    {X q s m : ℕ} (hq : q.Prime) (hs : s.Prime) (hqs : q ≠ s) :
    q * s * m ∈ lowOwnerTwoPrimeSquarefreeIntersectionCarrier X q s ↔
      m ∈ lowOwnerTwoPrimeSquarefreeCofactorCarrier X q s := by
  have hprodPos : 0 < q * s := Nat.mul_pos hq.pos hs.pos
  constructor
  · intro hm
    rcases mem_lowOwnerTwoPrimeSquarefreeIntersectionCarrier.mp hm with
      ⟨hm1, hmX, hmSq, _hqdiv, _hsdiv⟩
    have hmPos : 0 < m := by
      by_contra hz
      have hm0 : m = 0 := by omega
      subst m
      simp at hm1
    have hmLe : m ≤ X / (q * s) := by
      apply (Nat.le_div_iff_mul_le hprodPos).2
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmX
    have hsplit :=
      (squarefree_twoPrime_mul_cofactor_iff hq hs hqs).mp hmSq
    exact mem_lowOwnerTwoPrimeSquarefreeCofactorCarrier.mpr
      ⟨Nat.succ_le_iff.mpr hmPos, hmLe, hsplit.1, hsplit.2⟩
  · intro hm
    rcases mem_lowOwnerTwoPrimeSquarefreeCofactorCarrier.mp hm with
      ⟨_hm1, hmLe, hmSq, hrel⟩
    have hmPos : 0 < m := by omega
    have hX : q * s * m ≤ X := by
      have h := (Nat.le_div_iff_mul_le hprodPos).1 hmLe
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    have hSq : Squarefree (q * s * m) :=
      (squarefree_twoPrime_mul_cofactor_iff hq hs hqs).2 ⟨hmSq, hrel⟩
    have h1 : 1 ≤ q * s * m := by
      exact Nat.succ_le_iff.mpr (Nat.mul_pos hprodPos hmPos)
    refine mem_lowOwnerTwoPrimeSquarefreeIntersectionCarrier.mpr
      ⟨h1, hX, hSq, ?_, ?_⟩
    · exact ⟨s * m, by ring⟩
    · exact ⟨q * m, by ring⟩

/-- **Exact finite squarefree census.** The physical two-prime intersection
population has exactly the cardinality of the squarefree coprime cofactor
population below `X/(q*s)`. -/
theorem card_lowOwnerTwoPrimeSquarefreeCofactor_eq_intersection
    {X q s : ℕ} (hq : q.Prime) (hs : s.Prime) (hqs : q ≠ s) :
    (lowOwnerTwoPrimeSquarefreeCofactorCarrier X q s).card =
      (lowOwnerTwoPrimeSquarefreeIntersectionCarrier X q s).card := by
  classical
  have hprodPos : 0 < q * s := Nat.mul_pos hq.pos hs.pos
  refine Finset.card_bij (fun m _hm => q * s * m) ?_ ?_ ?_
  · intro m hm
    exact (mul_twoPrime_mem_squarefreeIntersection_iff_mem_cofactor
      hq hs hqs).2 hm
  · intro m₁ _hm₁ m₂ _hm₂ hmul
    exact Nat.eq_of_mul_eq_mul_left hprodPos hmul
  · intro n hn
    rcases mem_lowOwnerTwoPrimeSquarefreeIntersectionCarrier.mp hn with
      ⟨_hn1, _hnX, _hnSq, hqn, hsn⟩
    have hcop : q.Coprime s := by
      rw [hq.coprime_iff_not_dvd]
      intro hdiv
      exact hqs ((Nat.prime_dvd_prime_iff_eq hq hs).mp hdiv)
    have hdiv : q * s ∣ n :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hqn hsn
    let m := n / (q * s)
    have hcancel : q * s * m = n := by
      unfold m
      exact Nat.mul_div_cancel' hdiv
    have hm : m ∈ lowOwnerTwoPrimeSquarefreeCofactorCarrier X q s := by
      apply (mul_twoPrime_mem_squarefreeIntersection_iff_mem_cofactor
        hq hs hqs).1
      rw [hcancel]
      exact hn
    exact ⟨m, hm, hcancel⟩

/-- The same exact census on the literal nonzero-Möbius carrier. -/
theorem card_lowOwnerTwoPrimeMobiusIntersection_eq_squarefreeCofactor
    {X q s : ℕ} (hq : q.Prime) (hs : s.Prime) (hqs : q ≠ s) :
    (lowOwnerTwoPrimeMobiusIntersectionCarrier X q s).card =
      (lowOwnerTwoPrimeSquarefreeCofactorCarrier X q s).card := by
  rw [lowOwnerTwoPrimeMobiusIntersectionCarrier_eq_squarefree]
  exact (card_lowOwnerTwoPrimeSquarefreeCofactor_eq_intersection hq hs hqs).symm

/-- Top-half prime coordinates have no two-prime squarefree intersection at all.
This is exact carrier emptiness, not a density estimate. -/
theorem lowOwnerTwoPrimeSquarefreeIntersectionCarrier_eq_empty_of_top
    {X q s : ℕ} (hq : q.Prime) (hs : s.Prime) (hqs : q ≠ s)
    (hqTop : X / 2 < q) :
    lowOwnerTwoPrimeSquarefreeIntersectionCarrier X q s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  rcases mem_lowOwnerTwoPrimeSquarefreeIntersectionCarrier.mp hn with
    ⟨_hn1, hnX, _hnSq, hqn, hsn⟩
  have hcop : q.Coprime s := by
    rw [hq.coprime_iff_not_dvd]
    intro hdiv
    exact hqs ((Nat.prime_dvd_prime_iff_eq hq hs).mp hdiv)
  have hdiv : q * s ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hqn hsn
  have hqsLe : q * s ≤ n := Nat.le_of_dvd (by omega) hdiv
  have h2q : X < 2 * q := by omega
  have h2le : 2 * q ≤ s * q := Nat.mul_le_mul_right q hs.two_le
  have hprod : X < q * s := by
    calc
      X < 2 * q := h2q
      _ ≤ s * q := h2le
      _ = q * s := by ring
  omega

end RHLean.Proof
