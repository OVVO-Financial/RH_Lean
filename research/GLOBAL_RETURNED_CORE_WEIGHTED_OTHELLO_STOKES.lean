import Mathlib
import RHLean.Proof.GlobalPrefixCarrierOthello

/-!
# Weighted Othello discrete Stokes identity

This file packages the exact weighted form of the global Othello pairing needed
by the returned-core signed telescope.

For a prime `p`, a finite carrier `S`, and an arbitrary scalar weight `f`, the
carrier toggle `tau_p` gives

  sum_{n in S} mu(n) f(n)
    = sum_{n in Esc_p(S)} mu(n) f(n)
      + 1/2 * sum_{n in Int_p(S)} mu(n) (f(n) - f(tau_p n)).

The factor `1/2` appears because the interior sum visits both points of every
moving two-cycle.  Fixed points are `p^2`-hits and therefore have zero Mobius
mass.  No absolute value, square, or estimate occurs.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Real-valued Mobius mass used only to state the weighted Othello identity
without importing any analytic layer. -/
def othelloRealMoebius (n : ℕ) : ℝ := ((μ n : ℤ) : ℝ)

/-- The carrier toggle reverses the real Mobius mass on every moving state. -/
theorem othelloRealMoebius_primeCarrierToggle
    {p n : ℕ} (hp : p.Prime) (hsq : ¬ p ^ 2 ∣ n) :
    othelloRealMoebius (primeCarrierToggle p n) =
      -othelloRealMoebius n := by
  unfold othelloRealMoebius
  rw [moebius_primeCarrierToggle hp hsq]
  norm_num

/-- **Weighted Othello / discrete integration by parts.**

The complete weighted signed mass is exactly an escape-face term plus one half
of the interior finite difference.  Same-branch interior states are paired
before any magnitude is taken. -/
theorem sum_weightedMoebius_eq_escape_add_half_interiorDifference
    {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ S, othelloRealMoebius n * f n) =
      (∑ n ∈ primeEscapePart p S, othelloRealMoebius n * f n) +
        (1 / 2 : ℝ) *
          ∑ n ∈ primeInteriorPart p S,
            othelloRealMoebius n *
              (f n - f (primeCarrierToggle p n)) := by
  let I := primeInteriorPart p S
  let E := primeEscapePart p S
  let tau := primeCarrierToggle p
  let muR := othelloRealMoebius

  have hmem : ∀ x ∈ I, tau x ∈ I := by
    intro x hx
    have hx' : x ∈ primeInteriorPart p S := by simpa [I] using hx
    obtain ⟨hxS, hmate⟩ := mem_primeInteriorPart.mp hx'
    have hback : tau (tau x) = x := by
      simpa [tau] using primeCarrierToggle_involutive hp x
    have hmem' : tau x ∈ primeInteriorPart p S := by
      apply mem_primeInteriorPart.mpr
      refine ⟨?_, ?_⟩
      · simpa [tau] using hmate
      · simpa [tau, hback] using hxS
    simpa [I] using hmem'

  have hinv : ∀ x ∈ I, tau (tau x) = x := by
    intro x _hx
    simpa [tau] using primeCarrierToggle_involutive hp x

  let g : ℕ → ℝ := fun x => muR x * (f x + f (tau x))

  have hneg : ∀ x ∈ I, tau x ≠ x → g (tau x) = -g x := by
    intro x hx hne
    have hsq : ¬ p ^ 2 ∣ x := by
      intro hsq
      apply hne
      simpa [tau] using primeCarrierToggle_of_sq_dvd hsq
    have hmu : muR (tau x) = -muR x := by
      simpa [muR, tau] using othelloRealMoebius_primeCarrierToggle hp hsq
    have hback : tau (tau x) = x := hinv x hx
    simp only [g]
    rw [hmu, hback]
    ring

  have hstable :
      (∑ x ∈ finiteOthelloStablePart I tau, g x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hfix : tau x = x := (Finset.mem_filter.mp hx).2
    have hsq : p ^ 2 ∣ x := by
      apply sq_dvd_of_primeCarrierToggle_eq_self hp
      simpa [tau] using hfix
    have hmu : μ x = 0 := by
      refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree ?_
      intro hsf
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp)
        (by simpa [pow_two] using hsq)
    simp [g, muR, othelloRealMoebius, hmu]

  have hzero : (∑ x ∈ I, g x) = 0 := by
    rw [sum_finiteOthelloRegion_eq_stable I tau g hmem hinv hneg]
    exact hstable

  have hplus :
      (∑ x ∈ I, muR x * f x) +
          (∑ x ∈ I, muR x * f (tau x)) = 0 := by
    calc
      (∑ x ∈ I, muR x * f x) +
          (∑ x ∈ I, muR x * f (tau x)) =
        ∑ x ∈ I, g x := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _hx
          simp only [g]
          ring
      _ = 0 := hzero

  have htranspose :
      (∑ x ∈ I, muR x * f (tau x)) =
        -(∑ x ∈ I, muR x * f x) := by
    linarith [hplus]

  have hdiff :
      (∑ x ∈ I, muR x * (f x - f (tau x))) =
        (∑ x ∈ I, muR x * f x) -
          (∑ x ∈ I, muR x * f (tau x)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]

  have hinterior :
      (∑ x ∈ I, muR x * f x) =
        (1 / 2 : ℝ) *
          ∑ x ∈ I, muR x * (f x - f (tau x)) := by
    rw [hdiff, htranspose]
    ring

  have hunion : I ∪ E = S := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_union.mp hn with h | h
      · exact (mem_primeInteriorPart.mp (by simpa [I] using h)).1
      · exact (mem_primeEscapePart.mp (by simpa [E] using h)).1
    · intro hn
      by_cases hm : tau n ∈ S
      · apply Finset.mem_union.mpr
        left
        have : n ∈ primeInteriorPart p S :=
          mem_primeInteriorPart.mpr ⟨hn, by simpa [tau] using hm⟩
        simpa [I] using this
      · apply Finset.mem_union.mpr
        right
        have : n ∈ primeEscapePart p S :=
          mem_primeEscapePart.mpr ⟨hn, by simpa [tau] using hm⟩
        simpa [E] using this

  have hdisj : Disjoint I E := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    have hInt : n ∈ primeInteriorPart p S := by simpa [I] using hn
    have hEsc : n ∈ primeEscapePart p S := by simpa [E] using hn'
    exact (mem_primeEscapePart.mp hEsc).2 (mem_primeInteriorPart.mp hInt).2

  change
    (∑ n ∈ S, muR n * f n) =
      (∑ n ∈ E, muR n * f n) +
        (1 / 2 : ℝ) *
          ∑ n ∈ I, muR n * (f n - f (tau n))
  calc
    (∑ n ∈ S, muR n * f n) =
        ∑ n ∈ I ∪ E, muR n * f n := by rw [hunion]
    _ = (∑ n ∈ I, muR n * f n) +
          ∑ n ∈ E, muR n * f n := Finset.sum_union hdisj
    _ = (∑ n ∈ E, muR n * f n) +
          (1 / 2 : ℝ) *
            ∑ n ∈ I, muR n * (f n - f (tau n)) := by
      rw [hinterior]
      ring

end RHLean.Proof
