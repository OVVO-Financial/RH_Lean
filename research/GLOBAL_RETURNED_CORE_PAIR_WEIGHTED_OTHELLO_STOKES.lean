import Mathlib
import «research.GLOBAL_RETURNED_CORE_WEIGHTED_OTHELLO_STOKES»

/-!
# Generic and pair-coordinate weighted Othello Stokes identities

The prime-carrier weighted identity is useful beyond a scalar integer carrier.
This file packages the abstract finite-involution form and then applies it to
the two coordinates of an arbitrary finite pair carrier.

For an involution `tau`, an antisymmetric signed weight `w` on moving states,
and zero weight on fixed states,

  sum_S w f
    = sum_Esc w f + 1/2 sum_Int w (f - f o tau).

Applying this first in the left coordinate and then, on the surviving interior,
in the right coordinate gives an exact two-dimensional discrete Stokes formula:

  pair mass
    = first escape face
      + 1/2 second escape face
      + 1/4 mixed interior finite difference.

Nothing is normed.  The escape faces are literal carrier failures, and the last
term is the Boolean mixed finite difference on complete pair orbits.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Escape part of an arbitrary finite carrier under a proposed involution. -/
def weightedOthelloEscapePart
    {α : Type*} (tau : α → α) (S : Finset α) : Finset α :=
  S.filter fun x => tau x ∉ S

/-- Interior part of an arbitrary finite carrier under a proposed involution. -/
def weightedOthelloInteriorPart
    {α : Type*} (tau : α → α) (S : Finset α) : Finset α :=
  S.filter fun x => tau x ∈ S

@[simp] theorem mem_weightedOthelloEscapePart
    {α : Type*} {tau : α → α} {S : Finset α} {x : α} :
    x ∈ weightedOthelloEscapePart tau S ↔ x ∈ S ∧ tau x ∉ S :=
  Finset.mem_filter

@[simp] theorem mem_weightedOthelloInteriorPart
    {α : Type*} {tau : α → α} {S : Finset α} {x : α} :
    x ∈ weightedOthelloInteriorPart tau S ↔ x ∈ S ∧ tau x ∈ S :=
  Finset.mem_filter

/-- **Generic weighted Othello / finite discrete integration by parts.** -/
theorem sum_weightedOthello_eq_escape_add_half_interiorDifference
    {α : Type*}
    (S : Finset α) (tau : α → α) (w f : α → ℝ)
    (hinv : ∀ x, tau (tau x) = x)
    (hflip : ∀ x, tau x ≠ x → w (tau x) = -w x)
    (hfixzero : ∀ x, tau x = x → w x = 0) :
    (∑ x ∈ S, w x * f x) =
      (∑ x ∈ weightedOthelloEscapePart tau S, w x * f x) +
        (1 / 2 : ℝ) *
          ∑ x ∈ weightedOthelloInteriorPart tau S,
            w x * (f x - f (tau x)) := by
  classical
  let I := weightedOthelloInteriorPart tau S
  let E := weightedOthelloEscapePart tau S

  have hmem : ∀ x ∈ I, tau x ∈ I := by
    intro x hx
    have hx' : x ∈ weightedOthelloInteriorPart tau S := by
      simpa [I] using hx
    obtain ⟨hxS, hmate⟩ := mem_weightedOthelloInteriorPart.mp hx'
    have hmem' : tau x ∈ weightedOthelloInteriorPart tau S := by
      apply mem_weightedOthelloInteriorPart.mpr
      exact ⟨hmate, by simpa [hinv x] using hxS⟩
    simpa [I] using hmem'

  have hinvI : ∀ x ∈ I, tau (tau x) = x := fun x _ => hinv x

  let g : α → ℝ := fun x => w x * (f x + f (tau x))

  have hneg : ∀ x ∈ I, tau x ≠ x → g (tau x) = -g x := by
    intro x hx hne
    have hback : tau (tau x) = x := hinvI x hx
    simp only [g]
    rw [hflip x hne, hback]
    ring

  have hstable :
      (∑ x ∈ finiteOthelloStablePart I tau, g x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hfix : tau x = x := (Finset.mem_filter.mp hx).2
    simp [g, hfixzero x hfix]

  have hzero : (∑ x ∈ I, g x) = 0 := by
    rw [sum_finiteOthelloRegion_eq_stable I tau g hmem hinvI hneg]
    exact hstable

  have hplus :
      (∑ x ∈ I, w x * f x) +
          (∑ x ∈ I, w x * f (tau x)) = 0 := by
    calc
      (∑ x ∈ I, w x * f x) +
          (∑ x ∈ I, w x * f (tau x)) =
        ∑ x ∈ I, g x := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _hx
          simp only [g]
          ring
      _ = 0 := hzero

  have htranspose :
      (∑ x ∈ I, w x * f (tau x)) =
        -(∑ x ∈ I, w x * f x) := by
    linarith [hplus]

  have hdiff :
      (∑ x ∈ I, w x * (f x - f (tau x))) =
        (∑ x ∈ I, w x * f x) -
          (∑ x ∈ I, w x * f (tau x)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]

  have hinterior :
      (∑ x ∈ I, w x * f x) =
        (1 / 2 : ℝ) *
          ∑ x ∈ I, w x * (f x - f (tau x)) := by
    rw [hdiff, htranspose]
    ring

  have hunion : I ∪ E = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with h | h
      · exact (mem_weightedOthelloInteriorPart.mp (by simpa [I] using h)).1
      · exact (mem_weightedOthelloEscapePart.mp (by simpa [E] using h)).1
    · intro hx
      by_cases hm : tau x ∈ S
      · apply Finset.mem_union.mpr
        left
        have : x ∈ weightedOthelloInteriorPart tau S :=
          mem_weightedOthelloInteriorPart.mpr ⟨hx, hm⟩
        simpa [I] using this
      · apply Finset.mem_union.mpr
        right
        have : x ∈ weightedOthelloEscapePart tau S :=
          mem_weightedOthelloEscapePart.mpr ⟨hx, hm⟩
        simpa [E] using this

  have hdisj : Disjoint I E := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hInt : x ∈ weightedOthelloInteriorPart tau S := by simpa [I] using hx
    have hEsc : x ∈ weightedOthelloEscapePart tau S := by simpa [E] using hx'
    exact (mem_weightedOthelloEscapePart.mp hEsc).2
      (mem_weightedOthelloInteriorPart.mp hInt).2

  change
    (∑ x ∈ S, w x * f x) =
      (∑ x ∈ E, w x * f x) +
        (1 / 2 : ℝ) *
          ∑ x ∈ I, w x * (f x - f (tau x))
  calc
    (∑ x ∈ S, w x * f x) =
        ∑ x ∈ I ∪ E, w x * f x := by rw [hunion]
    _ = (∑ x ∈ I, w x * f x) +
          ∑ x ∈ E, w x * f x := Finset.sum_union hdisj
    _ = (∑ x ∈ E, w x * f x) +
          (1 / 2 : ℝ) *
            ∑ x ∈ I, w x * (f x - f (tau x)) := by
      rw [hinterior]
      ring

/-- Toggle the first coordinate of a physical pair. -/
def pairPrimeCarrierToggleLeft (p : ℕ) (mn : ℕ × ℕ) : ℕ × ℕ :=
  (primeCarrierToggle p mn.1, mn.2)

/-- Toggle the second coordinate of a physical pair. -/
def pairPrimeCarrierToggleRight (p : ℕ) (mn : ℕ × ℕ) : ℕ × ℕ :=
  (mn.1, primeCarrierToggle p mn.2)

/-- Product Möbius sign on one ordered physical pair. -/
def othelloRealMoebiusPair (mn : ℕ × ℕ) : ℝ :=
  othelloRealMoebius mn.1 * othelloRealMoebius mn.2

/-- Left coordinate toggle is an involution. -/
theorem pairPrimeCarrierToggleLeft_involutive
    {p : ℕ} (hp : p.Prime) (mn : ℕ × ℕ) :
    pairPrimeCarrierToggleLeft p (pairPrimeCarrierToggleLeft p mn) = mn := by
  ext <;> simp [pairPrimeCarrierToggleLeft, primeCarrierToggle_involutive hp]

/-- Right coordinate toggle is an involution. -/
theorem pairPrimeCarrierToggleRight_involutive
    {p : ℕ} (hp : p.Prime) (mn : ℕ × ℕ) :
    pairPrimeCarrierToggleRight p (pairPrimeCarrierToggleRight p mn) = mn := by
  ext <;> simp [pairPrimeCarrierToggleRight, primeCarrierToggle_involutive hp]

private theorem othelloRealMoebius_eq_zero_of_toggle_fixed
    {p n : ℕ} (hp : p.Prime) (hfix : primeCarrierToggle p n = n) :
    othelloRealMoebius n = 0 := by
  have hsq : p ^ 2 ∣ n := sq_dvd_of_primeCarrierToggle_eq_self hp hfix
  have hmu : μ n = 0 := by
    refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree ?_
    intro hsf
    exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp)
      (by simpa [pow_two] using hsq)
  simp [othelloRealMoebius, hmu]

/-- Pair Möbius weight reverses under every moving left toggle. -/
theorem othelloRealMoebiusPair_left_flip
    {p : ℕ} (hp : p.Prime) (mn : ℕ × ℕ)
    (hne : pairPrimeCarrierToggleLeft p mn ≠ mn) :
    othelloRealMoebiusPair (pairPrimeCarrierToggleLeft p mn) =
      -othelloRealMoebiusPair mn := by
  have hfirst : primeCarrierToggle p mn.1 ≠ mn.1 := by
    intro h
    apply hne
    ext <;> simp [pairPrimeCarrierToggleLeft, h]
  have hsq : ¬ p ^ 2 ∣ mn.1 := by
    intro h
    exact hfirst (primeCarrierToggle_of_sq_dvd h)
  unfold othelloRealMoebiusPair pairPrimeCarrierToggleLeft
  simp only
  rw [othelloRealMoebius_primeCarrierToggle hp hsq]
  ring

/-- Pair Möbius weight reverses under every moving right toggle. -/
theorem othelloRealMoebiusPair_right_flip
    {p : ℕ} (hp : p.Prime) (mn : ℕ × ℕ)
    (hne : pairPrimeCarrierToggleRight p mn ≠ mn) :
    othelloRealMoebiusPair (pairPrimeCarrierToggleRight p mn) =
      -othelloRealMoebiusPair mn := by
  have hsecond : primeCarrierToggle p mn.2 ≠ mn.2 := by
    intro h
    apply hne
    ext <;> simp [pairPrimeCarrierToggleRight, h]
  have hsq : ¬ p ^ 2 ∣ mn.2 := by
    intro h
    exact hsecond (primeCarrierToggle_of_sq_dvd h)
  unfold othelloRealMoebiusPair pairPrimeCarrierToggleRight
  simp only
  rw [othelloRealMoebius_primeCarrierToggle hp hsq]
  ring

/-- Fixed left pair states carry zero pair Möbius weight. -/
theorem othelloRealMoebiusPair_left_fixed_zero
    {p : ℕ} (hp : p.Prime) (mn : ℕ × ℕ)
    (hfix : pairPrimeCarrierToggleLeft p mn = mn) :
    othelloRealMoebiusPair mn = 0 := by
  have hfirst : primeCarrierToggle p mn.1 = mn.1 := by
    exact congrArg Prod.fst hfix
  unfold othelloRealMoebiusPair
  rw [othelloRealMoebius_eq_zero_of_toggle_fixed hp hfirst, zero_mul]

/-- Fixed right pair states carry zero pair Möbius weight. -/
theorem othelloRealMoebiusPair_right_fixed_zero
    {p : ℕ} (hp : p.Prime) (mn : ℕ × ℕ)
    (hfix : pairPrimeCarrierToggleRight p mn = mn) :
    othelloRealMoebiusPair mn = 0 := by
  have hsecond : primeCarrierToggle p mn.2 = mn.2 := by
    exact congrArg Prod.snd hfix
  unfold othelloRealMoebiusPair
  rw [othelloRealMoebius_eq_zero_of_toggle_fixed hp hsecond, mul_zero]

/-- Left-coordinate escape face of an arbitrary pair carrier. -/
def pairPrimeLeftEscapePart (p : ℕ) (C : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  weightedOthelloEscapePart (pairPrimeCarrierToggleLeft p) C

/-- Left-coordinate interior of an arbitrary pair carrier. -/
def pairPrimeLeftInteriorPart (p : ℕ) (C : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  weightedOthelloInteriorPart (pairPrimeCarrierToggleLeft p) C

/-- After the left coordinate is paired, literal right-coordinate escape face
inside the surviving left interior. -/
def pairPrimeRightEscapeAfterLeft
    (p : ℕ) (C : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  weightedOthelloEscapePart (pairPrimeCarrierToggleRight p)
    (pairPrimeLeftInteriorPart p C)

/-- Complete two-coordinate interior after both pair toggles remain in the
successive carrier. -/
def pairPrimeTwoCoordinateInterior
    (p : ℕ) (C : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  weightedOthelloInteriorPart (pairPrimeCarrierToggleRight p)
    (pairPrimeLeftInteriorPart p C)

/-- **Two-coordinate weighted Othello Stokes identity.**

The first two terms are literal escape faces.  Only on the final interior does
the mixed Boolean finite difference appear.  This is the exact pair-coordinate
form intended for returned-core polarization carriers. -/
theorem sum_pairWeightedMoebius_eq_escapeFaces_add_quarter_mixedDifference
    {p : ℕ} (hp : p.Prime) (C : Finset (ℕ × ℕ))
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ C, othelloRealMoebiusPair mn * f mn) =
      (∑ mn ∈ pairPrimeLeftEscapePart p C,
        othelloRealMoebiusPair mn * f mn) +
      (1 / 2 : ℝ) *
        (∑ mn ∈ pairPrimeRightEscapeAfterLeft p C,
          othelloRealMoebiusPair mn *
            (f mn - f (pairPrimeCarrierToggleLeft p mn))) +
      (1 / 4 : ℝ) *
        ∑ mn ∈ pairPrimeTwoCoordinateInterior p C,
          othelloRealMoebiusPair mn *
            ((f mn - f (pairPrimeCarrierToggleLeft p mn)) -
              (f (pairPrimeCarrierToggleRight p mn) -
                f (pairPrimeCarrierToggleLeft p
                  (pairPrimeCarrierToggleRight p mn)))) := by
  let tauL := pairPrimeCarrierToggleLeft p
  let tauR := pairPrimeCarrierToggleRight p
  let w := othelloRealMoebiusPair
  let I := pairPrimeLeftInteriorPart p C
  let g : ℕ × ℕ → ℝ := fun mn => f mn - f (tauL mn)

  have hleft :=
    sum_weightedOthello_eq_escape_add_half_interiorDifference
      C tauL w f
      (pairPrimeCarrierToggleLeft_involutive hp)
      (othelloRealMoebiusPair_left_flip hp)
      (othelloRealMoebiusPair_left_fixed_zero hp)

  have hright :=
    sum_weightedOthello_eq_escape_add_half_interiorDifference
      I tauR w g
      (pairPrimeCarrierToggleRight_involutive hp)
      (othelloRealMoebiusPair_right_flip hp)
      (othelloRealMoebiusPair_right_fixed_zero hp)

  change
    (∑ mn ∈ C, w mn * f mn) =
      (∑ mn ∈ weightedOthelloEscapePart tauL C, w mn * f mn) +
      (1 / 2 : ℝ) *
        (∑ mn ∈ weightedOthelloEscapePart tauR I,
          w mn * (f mn - f (tauL mn))) +
      (1 / 4 : ℝ) *
        ∑ mn ∈ weightedOthelloInteriorPart tauR I,
          w mn *
            ((f mn - f (tauL mn)) -
              (f (tauR mn) - f (tauL (tauR mn))))
  change
    (∑ mn ∈ C, w mn * f mn) =
      (∑ mn ∈ weightedOthelloEscapePart tauL C, w mn * f mn) +
      (1 / 2 : ℝ) *
        (∑ mn ∈ weightedOthelloEscapePart tauR I, w mn * g mn) +
      (1 / 4 : ℝ) *
        ∑ mn ∈ weightedOthelloInteriorPart tauR I,
          w mn * (g mn - g (tauR mn))
  rw [hleft, hright]
  ring

end RHLean.Proof
