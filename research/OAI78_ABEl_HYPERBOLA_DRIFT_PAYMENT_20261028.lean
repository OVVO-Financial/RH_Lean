import Mathlib
import «research.MOBIUS_INVERSION_GLOBAL_CANCELLATION»

/-!
# Exact hyperbola recombination of the original Abel historical drift

This is the complete ORIGINAL integer Möbius inversion at cutoff Q.
The truncated historical q-sum, the small-a cofactor prefix and the
terminal Q*M(r_Q) overlap must be retained TOGETHER.

This cancels the spurious singleton-cut drift loss. The remaining
physical floor phases and strict interior rows are not bounded here.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof
open RHLean.Analysis

/-- Original q>Q historical quotient sum, with exact small-a multiplicity.
    A hyperbola identity; no analytic Mertens bound or PNT is used. -/
theorem oai78Abel_tail_eq_small_cofactor_sum
    (N Q : ℕ) (hQ : 1 ≤ Q) (_hQN : Q ≤ N) :
    (∑ q ∈ Finset.Ioc Q N, mertensSummatoryInt (N / q)) =
      ∑ a ∈ Finset.Icc 1 (N / Q),
        (ArithmeticFunction.moebius a : ℤ) * ((N / a - Q : ℕ) : ℤ) := by
  have hswap : ∀ q a : ℕ,
      q ∈ Finset.Ioc Q N ∧ a ∈ Finset.Icc 1 (N / q) ↔
        a ∈ Finset.Icc 1 (N / Q) ∧ q ∈ Finset.Ioc Q (N / a) := by
    intro q a
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hqQ, hqN⟩, ha1, haN⟩
      have hq0 : 0 < q := by omega
      have hQ0 : 0 < Q := by omega
      have hqa : q * a ≤ N := by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq0).1 haN
      have hQa : Q * a ≤ N :=
        (Nat.mul_le_mul_right a (by omega : Q ≤ q)).trans hqa
      have haSmall : a ≤ N / Q :=
        (Nat.le_div_iff_mul_le hQ0).2 (by simpa [Nat.mul_comm] using hQa)
      have hqUp : q ≤ N / a :=
        (Nat.le_div_iff_mul_le (by omega : 0 < a)).2
          (by simpa [Nat.mul_comm] using hqa)
      exact ⟨⟨ha1, haSmall⟩, ⟨hqQ, hqUp⟩⟩
    · rintro ⟨⟨ha1, haSmall⟩, hqQ, hqUp⟩
      have hqa : q * a ≤ N :=
        (Nat.le_div_iff_mul_le (by omega : 0 < a)).1 hqUp
      have hqN : q ≤ N :=
        hqUp.trans (Nat.div_le_self _ _)
      have haUp : a ≤ N / q :=
        (Nat.le_div_iff_mul_le (by omega : 0 < q)).2
          (by simpa [Nat.mul_comm] using hqa)
      exact ⟨⟨hqQ, hqN⟩, ⟨ha1, haUp⟩⟩
  calc
    (∑ q ∈ Finset.Ioc Q N, mertensSummatoryInt (N / q)) =
        ∑ q ∈ Finset.Ioc Q N,
          ∑ a ∈ Finset.Icc 1 (N / q),
            (ArithmeticFunction.moebius a : ℤ) := by
              simp_rw [mertensSummatoryInt_eq_Icc]
    _ = ∑ a ∈ Finset.Icc 1 (N / Q),
          ∑ q ∈ Finset.Ioc Q (N / a),
            (ArithmeticFunction.moebius a : ℤ) :=
          Finset.sum_comm' (fun q a => (hswap q a).trans (and_comm))
    _ = ∑ a ∈ Finset.Icc 1 (N / Q),
          (ArithmeticFunction.moebius a : ℤ) * ((N / a - Q : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      ring

/-- All integer q-buckets are compensated by the complete Möbius inversion. -/
theorem oai78Abel_all_quotients_eq_one
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ q ∈ Finset.Icc 1 N, mertensSummatoryInt (N / q)) = 1 := by
  simpa only [mertensSummatoryInt_eq_Icc] using
    (sum_moebius_prefix_floor_div_eq_one N hN)

/-- Complete hyperbola identity: the apparent large historical head is
    compensated by its small-a prefix and terminal overlap Q*M(N/Q).
    This includes empty terminal buckets. -/
theorem oai78Abel_hyperbola_three_terms
    (N Q : ℕ) (hQ : 1 ≤ Q) (hQN : Q ≤ N) :
    (∑ q ∈ Finset.Ioc 1 Q, mertensSummatoryInt (N / q)) +
      (∑ a ∈ Finset.Icc 1 (N / Q),
        (ArithmeticFunction.moebius a : ℤ) * ((N / a : ℕ) : ℤ)) -
      (Q : ℤ) * mertensSummatoryInt (N / Q) =
      1 - mertensSummatoryInt N := by
  have htotal := oai78Abel_all_quotients_eq_one N (by omega)
  have hsplit1 := Finset.sum_Ioc_consecutive
    (f := fun q : ℕ => mertensSummatoryInt (N / q))
    (Nat.zero_le 1) (by omega : 1 ≤ N)
  have hsplit2 := Finset.sum_Ioc_consecutive
    (f := fun q : ℕ => mertensSummatoryInt (N / q))
    hQ hQN
  have hwhole :
      (∑ q ∈ Finset.Ioc 0 N, mertensSummatoryInt (N / q)) = 1 := by
    have he : Finset.Ioc 0 N = Finset.Icc 1 N := by
      ext q
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [he]
    exact htotal
  have htail := oai78Abel_tail_eq_small_cofactor_sum N Q hQ hQN
  have hfirst :
      (∑ q ∈ Finset.Ioc 0 1, mertensSummatoryInt (N / q)) =
        mertensSummatoryInt N := by simp
  have hcore :
      (∑ q ∈ Finset.Ioc 1 Q, mertensSummatoryInt (N / q)) +
        (∑ a ∈ Finset.Icc 1 (N / Q),
          (ArithmeticFunction.moebius a : ℤ) * ((N / a - Q : ℕ) : ℤ)) =
        1 - mertensSummatoryInt N := by
    rw [← hsplit1, ← hsplit2, hfirst, htail] at hwhole
    omega
  have hsmall :
      (∑ a ∈ Finset.Icc 1 (N / Q),
          (ArithmeticFunction.moebius a : ℤ) * ((N / a - Q : ℕ) : ℤ)) =
      (∑ a ∈ Finset.Icc 1 (N / Q),
          (ArithmeticFunction.moebius a : ℤ) * ((N / a : ℕ) : ℤ)) -
      (Q : ℤ) * mertensSummatoryInt (N / Q) := by
    have hnum : ∀ a ∈ Finset.Icc 1 (N / Q), Q ≤ N / a := by
      intro a ha
      have ha1 : 0 < a := (Finset.mem_Icc.mp ha).1
      have haLe : a ≤ N / Q := (Finset.mem_Icc.mp ha).2
      have hQa : a * Q ≤ N :=
        (Nat.le_div_iff_mul_le (by omega : 0 < Q)).1 haLe
      exact (Nat.le_div_iff_mul_le ha1).2
        (by simpa [Nat.mul_comm] using hQa)
    calc
      _ = ∑ a ∈ Finset.Icc 1 (N / Q),
          ((ArithmeticFunction.moebius a : ℤ) * ((N / a : ℕ) : ℤ) -
            (ArithmeticFunction.moebius a : ℤ) * (Q : ℤ)) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Nat.cast_sub (hnum a ha)]
              ring
      _ = (∑ a ∈ Finset.Icc 1 (N / Q),
            (ArithmeticFunction.moebius a : ℤ) * ((N / a : ℕ) : ℤ)) -
          (Q : ℤ) *
            (∑ a ∈ Finset.Icc 1 (N / Q),
              (ArithmeticFunction.moebius a : ℤ)) := by
                rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
                ring
      _ = _ := by rw [mertensSummatoryInt_eq_Icc]
  rw [hsmall] at hcore
  convert hcore using 1; ring

/-- No separately estimated R^(29/16) drift: the three original
    continuous Abel pieces combine to a SINGLE Mertens historical
    boundary. This lemma is rational even when b=0. -/
theorem oai78Abel_continuous_drift_exact
    (N Q L b : ℕ) (hQ : 1 ≤ Q) (hQN : Q ≤ N) :
    - ((L : ℚ) / (b : ℚ)) *
        (∑ q ∈ Finset.Ioc 1 Q,
          ((mertensSummatoryInt (N / q) : ℤ) : ℚ)) -
      ((L : ℚ) / (b : ℚ)) *
        (∑ a ∈ Finset.Icc 1 (N / Q),
          ((ArithmeticFunction.moebius a : ℤ) : ℚ) * ((N / a : ℕ) : ℚ)) +
      ((L : ℚ) / (b : ℚ)) * (Q : ℚ) *
        ((mertensSummatoryInt (N / Q) : ℤ) : ℚ) =
      ((L : ℚ) / (b : ℚ)) *
        (((mertensSummatoryInt N : ℤ) : ℚ) - 1) := by
  have h := oai78Abel_hyperbola_three_terms N Q hQ hQN
  have hRat :
      (∑ q ∈ Finset.Ioc 1 Q,
        (((mertensSummatoryInt (N / q) : ℤ) : ℚ))) +
      (∑ a ∈ Finset.Icc 1 (N / Q),
        (((ArithmeticFunction.moebius a : ℤ) : ℚ)) *
          (((N / a : ℕ) : ℚ))) -
      (Q : ℚ) * (((mertensSummatoryInt (N / Q) : ℤ) : ℚ)) =
      1 - (((mertensSummatoryInt N : ℤ) : ℚ)) := by
    have hc := congrArg (fun z : ℤ => (z : ℚ)) h
    simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul,
      Int.cast_sum, Int.cast_natCast, Int.cast_one] using hc
  linear_combination -((L : ℚ) / (b : ℚ)) * hRat

#print axioms oai78Abel_tail_eq_small_cofactor_sum
#print axioms oai78Abel_hyperbola_three_terms
#print axioms oai78Abel_continuous_drift_exact

end RHLean.Proof
