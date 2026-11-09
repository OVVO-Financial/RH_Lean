import Mathlib
import «research.FiniteDirectionalBudgetCosineBridge»
import RHLean.Arithmetic.PrimeCombFiniteDifferenceRecovery

/-!
# Square-root prime reconstruction of squarefree integers

Only primes through `Nat.sqrt X` appear in the primorial.  The residual
coprime to that primorial, if greater than one and at most `X`, is prime.

The divisor reconstruction must restrict the outer divisor to `d <= X`.
The unfiltered displayed Eq. (15) is false already at X=49.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open scoped ArithmeticFunction.Moebius BigOperators

def y (X : ℕ) : ℕ := Nat.sqrt X

def P_y (X : ℕ) : ℕ :=
  ∏ p ∈ primesUpTo (y X), p

private theorem P_y_ne_zero (X : ℕ) : P_y X ≠ 0 := by
  unfold P_y
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (prime_of_mem_primesUpTo hp).ne_zero

/-- Every prime not exceeding the square root divides the primorial. -/
theorem prime_dvd_P_y {X p : ℕ}
    (hp : Nat.Prime p) (hple : p ≤ y X) :
    p ∣ P_y X := by
  unfold P_y
  exact Finset.dvd_prod_of_mem id
    (mem_primesUpTo.mpr ⟨hp, hple⟩)

/-- A prime divisor of an integer coprime to the square-root primorial
must lie strictly above the square root. -/
private theorem prime_gt_root_of_coprime
    (X r p : ℕ) (hp : Nat.Prime p) (hpr : p ∣ r)
    (hc : Nat.Coprime r (P_y X)) :
    y X < p := by
  by_contra hnot
  have hple : p ≤ y X := Nat.le_of_not_gt hnot
  have hprod : p ∣ P_y X := prime_dvd_P_y hp hple
  have hpone : p ∣ 1 := by
    have h := Nat.dvd_gcd hpr hprod
    rw [show Nat.gcd r (P_y X) = 1 from hc] at h
    exact h
  exact hp.ne_one (Nat.dvd_one.mp hpone)

/-- A survivor beyond 1 is necessarily prime below X: if it were composite,
its least prime divisor would be no greater than sqrt X. -/
theorem coprime_root_survivor_is_prime
    (X r : ℕ) (hr : 1 < r) (hrX : r ≤ X)
    (hc : Nat.Coprime r (P_y X)) :
    Nat.Prime r ∧ y X < r := by
  by_cases hprime : Nat.Prime r
  · exact ⟨hprime,
      prime_gt_root_of_coprime X r r hprime (dvd_refl r) hc⟩
  · let p := r.minFac
    have hp : Nat.Prime p := by
      simpa [p] using
        (Nat.minFac_prime (by omega : r ≠ 1))
    have hpd : p ∣ r := by
      simpa [p] using Nat.minFac_dvd r
    have hpy : y X < p :=
      prime_gt_root_of_coprime X r p hp hpd hc
    have hpsq : p ^ 2 ≤ r := by
      simpa [p] using
        (Nat.minFac_sq_le_self (by omega : 0 < r) hprime)
    have hX : X < (y X + 1) ^ 2 := by
      simpa [y] using Nat.lt_succ_sqrt' X
    have hyy : (y X + 1) ^ 2 ≤ p ^ 2 :=
      Nat.pow_le_pow_left (by omega : y X + 1 ≤ p) 2
    omega

/-- Every squarefree integer at or below X splits into a divisor of the
square-root primorial and either 1 or a prime above sqrt X. -/
theorem squarefree_decomposition (X : ℕ) (n : ℕ)
    (hn : n ≤ X) (hsf : Squarefree n) :
    ∃ d r, d ∣ P_y X ∧ n = d * r ∧
      (r = 1 ∨ (Nat.Prime r ∧ y X < r)) := by
  have hn0 : n ≠ 0 := hsf.ne_zero
  let d := Nat.gcd n (P_y X)
  let r := n / d
  have hdn : d ∣ n := by
    dsimp [d]
    exact Nat.gcd_dvd_left n (P_y X)
  have hdp : d ∣ P_y X := by
    dsimp [d]
    exact Nat.gcd_dvd_right n (P_y X)
  have hprod : d * r = n := by
    dsimp [r]
    exact Nat.mul_div_cancel' hdn
  have hcop : Nat.Coprime r (P_y X) := by
    dsimp [r, d]
    exact Nat.coprime_div_gcd_of_squarefree hsf (P_y_ne_zero X)
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hrzero | hrpositive
    · rw [hrzero, mul_zero] at hprod
      exact False.elim (hn0 hprod.symm)
    · exact hrpositive
  have hrle : r ≤ X := by
    dsimp [r]
    exact (Nat.div_le_self n d).trans hn
  refine ⟨d, r, hdp, hprod.symm, ?_⟩
  by_cases hr1 : r = 1
  · exact Or.inl hr1
  · exact Or.inr
      (coprime_root_survivor_is_prime X r (by omega) hrle hcop)

-- Certifies the unique-small-prime-support mechanism underlying Eq. (15).
-- The signed finite C_X rewriting is stated separately once multiplicities
-- and the necessary d <= X truncation are checked.


/-! ## Exact finite Dirichlet sum reindexing (corrected Equation 15) -/

/-- The square-root prime wheel is the ordinary primorial, inclusive of the
prime at the square-root cutoff. -/
private theorem P_y_eq_primorial (X : ℕ) :
    P_y X = primorial (y X) := rfl

private theorem P_y_squarefree (X : ℕ) : Squarefree (P_y X) := by
  rw [P_y_eq_primorial]
  exact squarefree_primorial (y X)

private theorem largePrime_coprime_P_y (X r : ℕ)
    (hr : Nat.Prime r) (hy : y X < r) :
    Nat.Coprime r (P_y X) := by
  apply (hr.coprime_iff_not_dvd).mpr
  intro hrP
  have hrPrim : r ∣ primorial (y X) := by
    simpa only [P_y_eq_primorial] using hrP
  have hle : r ≤ y X := (Nat.Prime.dvd_primorial_iff hr).mp hrPrim
  omega

private def rootPrimeDivisors (X : ℕ) : Finset ℕ :=
  (P_y X).divisors.filter (fun d => d ≤ X)

private def rootPrimeRough (X d : ℕ) : Finset ℕ :=
  (Finset.range (X / d + 1)).filter
    (fun r => 1 < r ∧ Nat.Coprime r (P_y X))

private def rootPrimePairs (X : ℕ) : Finset (Σ _d : ℕ, ℕ) :=
  (rootPrimeDivisors X).sigma (rootPrimeRough X)

private def rootPrimeHighSource (X : ℕ) : Finset ℕ :=
  ((Finset.range (X + 1)).filter Squarefree).filter
    (fun n => ¬ n ∣ P_y X)

private theorem mem_rootPrimeDivisors {X d : ℕ} :
    d ∈ rootPrimeDivisors X ↔ d ∣ P_y X ∧ d ≤ X := by
  constructor
  · intro h
    obtain ⟨hd, hdX⟩ := Finset.mem_filter.mp h
    exact ⟨(Nat.mem_divisors.mp hd).1, hdX⟩
  · rintro ⟨hd, hdX⟩
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hd, P_y_ne_zero X⟩, hdX⟩

private theorem mem_rootPrimeRough {X d r : ℕ} :
    r ∈ rootPrimeRough X d ↔
      1 < r ∧ Nat.Coprime r (P_y X) ∧ r ≤ X / d := by
  constructor
  · intro h
    obtain ⟨hrange, hrgt, hc⟩ := Finset.mem_filter.mp h
    exact ⟨hrgt, hc, by have := Finset.mem_range.mp hrange; omega⟩
  · rintro ⟨hrgt, hc, hrub⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), ⟨hrgt, hc⟩⟩

private theorem rootPrimePair_to_high {X : ℕ}
    {dr : Σ _d : ℕ, ℕ} (hdr : dr ∈ rootPrimePairs X) :
    dr.1 * dr.2 ∈ rootPrimeHighSource X := by
  obtain ⟨hdD, hrR⟩ := Finset.mem_sigma.mp hdr
  obtain ⟨hdP, _hdX⟩ := mem_rootPrimeDivisors.mp hdD
  obtain ⟨hrgt, hrCoprime, hrub⟩ := mem_rootPrimeRough.mp hrR
  have hdpos : 0 < dr.1 :=
    Nat.pos_of_dvd_of_pos hdP (Nat.pos_of_ne_zero (P_y_ne_zero X))
  have hrX : dr.2 ≤ X := hrub.trans (Nat.div_le_self X dr.1)
  have hrPrime : Nat.Prime dr.2 :=
    (coprime_root_survivor_is_prime X dr.2 hrgt hrX hrCoprime).1
  have hCoprime : Nat.Coprime dr.1 dr.2 :=
    (hrCoprime.coprime_dvd_right hdP).symm
  have hdSF : Squarefree dr.1 :=
    (P_y_squarefree X).squarefree_of_dvd hdP
  have hSF : Squarefree (dr.1 * dr.2) :=
    Nat.squarefree_mul_iff.mpr ⟨hCoprime, hdSF, hrPrime.squarefree⟩
  have hprodX : dr.1 * dr.2 ≤ X := by
    have hm := (Nat.le_div_iff_mul_le hdpos).mp hrub
    simpa [Nat.mul_comm] using hm
  have hnP : ¬ dr.1 * dr.2 ∣ P_y X := by
    intro hprodP
    have hrD : dr.2 ∣ dr.1 * dr.2 := ⟨dr.1, by ring⟩
    have hrP : dr.2 ∣ P_y X := hrD.trans hprodP
    have hr1 : dr.2 ∣ 1 := by
      have hh := Nat.dvd_gcd (dvd_refl dr.2) hrP
      have hgg : Nat.gcd dr.2 (P_y X) = 1 := hrCoprime
      rw [hgg] at hh
      exact hh
    have hrOne : dr.2 = 1 := Nat.dvd_one.mp hr1
    omega
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hSF⟩, hnP⟩

private theorem rootPrimePair_injective (X : ℕ)
    {a b : Σ _d : ℕ, ℕ}
    (ha : a ∈ rootPrimePairs X) (hb : b ∈ rootPrimePairs X)
    (hprod : a.1 * a.2 = b.1 * b.2) : a = b := by
  obtain ⟨had, har⟩ := Finset.mem_sigma.mp ha
  obtain ⟨hbd, hbr⟩ := Finset.mem_sigma.mp hb
  obtain ⟨haP, _⟩ := mem_rootPrimeDivisors.mp had
  obtain ⟨hbP, _⟩ := mem_rootPrimeDivisors.mp hbd
  obtain ⟨_, haCoprime, _⟩ := mem_rootPrimeRough.mp har
  obtain ⟨_, hbCoprime, _⟩ := mem_rootPrimeRough.mp hbr
  have hAdDiv : a.1 ∣ b.1 * b.2 := by
    rw [← hprod]
    exact ⟨a.2, by ring⟩
  have hBdDiv : b.1 ∣ a.1 * a.2 := by
    rw [hprod]
    exact ⟨b.2, by ring⟩
  have hAdBd : a.1 ∣ b.1 :=
    ((hbCoprime.coprime_dvd_right haP).symm).dvd_of_dvd_mul_right hAdDiv
  have hBdAd : b.1 ∣ a.1 :=
    ((haCoprime.coprime_dvd_right hbP).symm).dvd_of_dvd_mul_right hBdDiv
  have hdeq : a.1 = b.1 := dvd_antisymm hAdBd hBdAd
  cases a with
  | mk d r =>
    cases b with
    | mk e t =>
      dsimp at hdeq hprod ⊢
      subst e
      have hdpos : 0 < d :=
        Nat.pos_of_dvd_of_pos haP (Nat.pos_of_ne_zero (P_y_ne_zero X))
      have hrt : r = t := mul_left_cancel₀ (Nat.ne_of_gt hdpos) hprod
      subst t
      rfl

private theorem highSource_to_rootPrimePair (X n : ℕ)
    (hn : n ∈ rootPrimeHighSource X) :
    ∃ dr ∈ rootPrimePairs X, dr.1 * dr.2 = n := by
  obtain ⟨hnS, hnNotDiv⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnrange, hsf⟩ := Finset.mem_filter.mp hnS
  have hnX : n ≤ X := by have h := Finset.mem_range.mp hnrange; omega
  obtain ⟨d, r, hdP, hprod, hcase⟩ :=
    squarefree_decomposition X n hnX hsf
  rcases hcase with hr1 | ⟨hrPrime, hrAbove⟩
  · exfalso
    apply hnNotDiv
    rw [hprod, hr1, mul_one]
    exact hdP
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos hdP (Nat.pos_of_ne_zero (P_y_ne_zero X))
  have hdDiv : d ∣ n := by
    rw [hprod]
    exact ⟨r, by ring⟩
  have hdX : d ≤ X :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hsf.ne_zero) hdDiv).trans hnX
  have hrCoprime : Nat.Coprime r (P_y X) :=
    largePrime_coprime_P_y X r hrPrime hrAbove
  have hrub : r ≤ X / d := by
    apply (Nat.le_div_iff_mul_le hdpos).mpr
    simpa [Nat.mul_comm, hprod] using hnX
  refine ⟨⟨d, r⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, hprod.symm⟩
  · exact mem_rootPrimeDivisors.mpr ⟨hdP, hdX⟩
  · exact mem_rootPrimeRough.mpr ⟨hrPrime.one_lt, hrCoprime, hrub⟩

private theorem finiteMobiusComplexTerm_largePrime
    (d r : ℕ) (s : ℂ)
    (hc : Nat.Coprime d r) (hr : Nat.Prime r) :
    finiteMobiusComplexTerm (d * r) s =
      -(finiteMobiusComplexTerm d s / (r : ℂ) ^ s) := by
  have hmu : μ (d * r) = -μ d := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
      ArithmeticFunction.moebius_apply_prime hr]
    ring
  have hp :
      ((d * r : ℕ) : ℂ) ^ s = (d : ℂ) ^ s * (r : ℂ) ^ s :=
    by simpa only [Nat.cast_mul] using Complex.natCast_mul_natCast_cpow d r s
  simp only [finiteMobiusComplexTerm, hmu, hp, Int.cast_neg,
    div_eq_mul_inv, mul_inv_rev]
  ring

private theorem rootPrimeHighSource_sum (X : ℕ) (s : ℂ) :
    (∑ n ∈ rootPrimeHighSource X, finiteMobiusComplexTerm n s) =
      -(∑ d ∈ rootPrimeDivisors X,
          ∑ r ∈ rootPrimeRough X d,
            finiteMobiusComplexTerm d s / (r : ℂ) ^ s) := by
  classical
  have hbij :
      (∑ dr ∈ rootPrimePairs X,
        -(finiteMobiusComplexTerm dr.1 s / (dr.2 : ℂ) ^ s)) =
      ∑ n ∈ rootPrimeHighSource X, finiteMobiusComplexTerm n s := by
    refine Finset.sum_bij (fun dr _hdr => dr.1 * dr.2)
      (fun dr hdr => rootPrimePair_to_high hdr)
      (fun a ha b hb heq => rootPrimePair_injective X ha hb heq)
      (fun n hn => by
        obtain ⟨dr, hdr, heq⟩ := highSource_to_rootPrimePair X n hn
        exact ⟨dr, hdr, heq⟩)
      ?_
    intro dr hdr
    obtain ⟨hdD, hrR⟩ := Finset.mem_sigma.mp hdr
    obtain ⟨hdP, _⟩ := mem_rootPrimeDivisors.mp hdD
    obtain ⟨hrgt, hrC, hrub⟩ := mem_rootPrimeRough.mp hrR
    have hrX : dr.2 ≤ X := hrub.trans (Nat.div_le_self X dr.1)
    have hrPrime : Nat.Prime dr.2 :=
      (coprime_root_survivor_is_prime X dr.2 hrgt hrX hrC).1
    have hc : Nat.Coprime dr.1 dr.2 :=
      (hrC.coprime_dvd_right hdP).symm
    exact (finiteMobiusComplexTerm_largePrime
      dr.1 dr.2 s hc hrPrime).symm
  calc
    _ = ∑ dr ∈ rootPrimePairs X,
        -(finiteMobiusComplexTerm dr.1 s / (dr.2 : ℂ) ^ s) := hbij.symm
    _ = _ := by
      unfold rootPrimePairs
      rw [Finset.sum_sigma]
      simp only [Finset.sum_neg_distrib]

/-- Exact square-root-prime reconstruction, including the mandatory
d <= X filter and residual primality encoded only as wheel coprimality. -/
theorem C_X_reconstruction (X : ℕ) (s : ℂ) :
    C_X X s =
      ∑ d ∈ ((P_y X).divisors.filter (fun d => d ≤ X)),
        ((((μ d : ℤ) : ℂ)) / (d : ℂ) ^ s) *
          (1 - ∑ r ∈ (Finset.range (X / d + 1)).filter
            (fun r => 1 < r ∧ Nat.Coprime r (P_y X)),
            1 / (r : ℂ) ^ s) := by
  classical
  let S : Finset ℕ := (Finset.range (X + 1)).filter Squarefree
  let D : Finset ℕ := rootPrimeDivisors X
  have hSF :
      C_X X s = ∑ n ∈ S, finiteMobiusComplexTerm n s := by
    unfold C_X
    change (∑ n ∈ Finset.range (X + 1), finiteMobiusComplexTerm n s) =
      ∑ n ∈ (Finset.range (X + 1)).filter Squarefree,
        finiteMobiusComplexTerm n s
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hn : Squarefree n
    · simp [hn]
    · simp [hn, finiteMobiusComplexTerm,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  have hSet : (S.filter (fun n => n ∣ P_y X)) = D := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnS, hnP⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnRange, _⟩ := Finset.mem_filter.mp hnS
      exact mem_rootPrimeDivisors.mpr
        ⟨hnP, by have h := Finset.mem_range.mp hnRange; omega⟩
    · intro hn
      obtain ⟨hnP, hnX⟩ := mem_rootPrimeDivisors.mp hn
      have hnpos : 0 < n :=
        Nat.pos_of_dvd_of_pos hnP (Nat.pos_of_ne_zero (P_y_ne_zero X))
      have hnSF : Squarefree n :=
        (P_y_squarefree X).squarefree_of_dvd hnP
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), hnSF⟩, hnP⟩
  have hSplit :
      (∑ n ∈ S, finiteMobiusComplexTerm n s) =
        (∑ d ∈ D, finiteMobiusComplexTerm d s) +
          (∑ n ∈ rootPrimeHighSource X, finiteMobiusComplexTerm n s) := by
    have hh := Finset.sum_filter_add_sum_filter_not
      (s := S) (p := fun n => n ∣ P_y X)
      (f := fun n => finiteMobiusComplexTerm n s)
    rw [hSet] at hh
    change (∑ d ∈ D, finiteMobiusComplexTerm d s) +
      (∑ n ∈ rootPrimeHighSource X, finiteMobiusComplexTerm n s) =
        ∑ n ∈ S, finiteMobiusComplexTerm n s at hh
    exact hh.symm
  calc
    C_X X s = ∑ n ∈ S, finiteMobiusComplexTerm n s := hSF
    _ = (∑ d ∈ D, finiteMobiusComplexTerm d s) +
        (∑ n ∈ rootPrimeHighSource X, finiteMobiusComplexTerm n s) :=
      hSplit
    _ = (∑ d ∈ D, finiteMobiusComplexTerm d s) -
          (∑ d ∈ D, ∑ r ∈ rootPrimeRough X d,
            finiteMobiusComplexTerm d s / (r : ℂ) ^ s) := by
      rw [rootPrimeHighSource_sum]
      ring
    _ = ∑ d ∈ D, finiteMobiusComplexTerm d s *
          (1 - ∑ r ∈ rootPrimeRough X d, 1 / (r : ℂ) ^ s) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [mul_sub, mul_one, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = _ := by
      rfl

-- Certifies Eq. (15) of the directional-Gram arithmetic note (with d ≤ X).
#print axioms C_X_reconstruction

end RHLean.Analysis
