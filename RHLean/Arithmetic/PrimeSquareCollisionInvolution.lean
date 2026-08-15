import Mathlib
import RHLean.Arithmetic.PrimeSquareCollisionCRT
import RHLean.Arithmetic.PrimeWheelFiniteSystem

noncomputable section

open scoped BigOperators

namespace RHLean.Arithmetic

/-!
# Modular exponent-state involution for the nine collision classes

For each local prime comb there are three exponent states:

* `0`: no prime hit, with local value `+1`;
* `1`: first-power hit, with local value `-1`;
* `2`: square hit, with local value `0`.

The two-prime local state space is therefore `Fin 3 × Fin 3`, with exactly nine
labels.  The sign-reversing involution acts on the exponent state, not on the
primes and not by additive negation in the CRT modulus: it flips `0 <-> 1` in
the first coordinate and fixes the square-kill state `2`.

The CRT map below realizes these nine labels by the existing three-by-three
collision residue geometry.  The actual `R - 2H` frontier theorem will only
need to prove that its residue weight transforms by the same exponent-state
flip; `Finset.sum_involution` then performs the cancellation symbolically.
-/

/-- The three local prime-comb exponent states. -/
abbrev PrimeCombExponentState := Fin 3

/-- The nine two-prime exponent-state labels. -/
abbrev TwoPrimeCollisionState := PrimeCombExponentState × PrimeCombExponentState

/-- The exact local comb value attached to an exponent state. -/
def localPrimeCombStateValue (a : PrimeCombExponentState) : ℤ :=
  if a = 0 then 1 else if a = 1 then -1 else 0

/-- The exponent state read directly from divisibility by `p` and `p^2`. -/
def localPrimeExponentState (p n : ℕ) : PrimeCombExponentState :=
  if p ^ 2 ∣ n then 2 else if p ∣ n then 1 else 0

/-- `localPrimeComb` is exactly the three-state value map. -/
theorem localPrimeComb_eq_stateValue (p n : ℕ) :
    localPrimeComb p n =
      localPrimeCombStateValue (localPrimeExponentState p n) := by
  by_cases hsq : p ^ 2 ∣ n
  · simp [localPrimeComb, localPrimeExponentState,
      localPrimeCombStateValue, hsq]
  · by_cases hp : p ∣ n
    · simp [localPrimeComb, localPrimeExponentState,
        localPrimeCombStateValue, hsq, hp]
    · simp [localPrimeComb, localPrimeExponentState,
        localPrimeCombStateValue, hsq, hp]

/-- Flip first-power parity while leaving the square-kill state fixed. -/
def primeCombExponentFlip (a : PrimeCombExponentState) :
    PrimeCombExponentState :=
  if a = 0 then 1 else if a = 1 then 0 else 2

@[simp] theorem primeCombExponentFlip_involutive
    (a : PrimeCombExponentState) :
    primeCombExponentFlip (primeCombExponentFlip a) = a := by
  fin_cases a <;> simp [primeCombExponentFlip]

/-- The local comb value changes sign under the exponent-state flip.  The
square state is fixed only because its value is already zero. -/
@[simp] theorem localPrimeCombStateValue_flip
    (a : PrimeCombExponentState) :
    localPrimeCombStateValue (primeCombExponentFlip a) =
      -localPrimeCombStateValue a := by
  fin_cases a <;>
    simp [primeCombExponentFlip, localPrimeCombStateValue]

/-- The only fixed exponent state is the square-kill state. -/
theorem primeCombExponentFlip_eq_self_iff
    (a : PrimeCombExponentState) :
    primeCombExponentFlip a = a ↔ a = 2 := by
  fin_cases a <;> simp [primeCombExponentFlip]

/-- The modular exponent-state involution on the nine two-prime labels. -/
def collisionExponentStateInvolution
    (s : TwoPrimeCollisionState) : TwoPrimeCollisionState :=
  (primeCombExponentFlip s.1, s.2)

@[simp] theorem collisionExponentStateInvolution_involutive
    (s : TwoPrimeCollisionState) :
    collisionExponentStateInvolution
        (collisionExponentStateInvolution s) = s := by
  rcases s with ⟨a, b⟩
  simp [collisionExponentStateInvolution]

/-- Fixed points are exactly the three states whose first coordinate is a
square kill. -/
theorem collisionExponentStateInvolution_eq_self_iff
    (s : TwoPrimeCollisionState) :
    collisionExponentStateInvolution s = s ↔ s.1 = 2 := by
  rcases s with ⟨a, b⟩
  simp [collisionExponentStateInvolution,
    primeCombExponentFlip_eq_self_iff]

/-- There are exactly nine symbolic exponent-state labels. -/
theorem twoPrimeCollisionState_card :
    Fintype.card TwoPrimeCollisionState = 9 := by
  simp [TwoPrimeCollisionState, PrimeCombExponentState]

/-- The fixed-point set is tiny: exactly the three square-kill states in the
first coordinate. -/
def collisionExponentFixedPoints : Finset TwoPrimeCollisionState :=
  Finset.univ.filter (fun s => collisionExponentStateInvolution s = s)

/-- The non-fixed states on which sign-reversing pairing acts. -/
def collisionExponentPairedStates : Finset TwoPrimeCollisionState :=
  Finset.univ.filter (fun s => collisionExponentStateInvolution s ≠ s)

/-- The fixed-point computation is independent of `p,q` and contains only
three symbolic states. -/
theorem collisionExponentFixedPoints_card :
    collisionExponentFixedPoints.card = 3 := by
  native_decide

/-- A generic local product weight.  This is the algebraic model that the
signed `R - 2H` collision weight is expected to factor through. -/
def localPrimeCombPairWeight (s : TwoPrimeCollisionState) : ℤ :=
  localPrimeCombStateValue s.1 * localPrimeCombStateValue s.2

/-- The local product weight reverses sign under the modular exponent flip. -/
@[simp] theorem localPrimeCombPairWeight_involution
    (s : TwoPrimeCollisionState) :
    localPrimeCombPairWeight (collisionExponentStateInvolution s) =
      -localPrimeCombPairWeight s := by
  simp [localPrimeCombPairWeight, collisionExponentStateInvolution]

/-- Every fixed state has zero local weight because it contains a square kill. -/
theorem localPrimeCombPairWeight_eq_zero_of_fixed
    (s : TwoPrimeCollisionState)
    (hs : collisionExponentStateInvolution s = s) :
    localPrimeCombPairWeight s = 0 := by
  have hfirst : s.1 = 2 :=
    (collisionExponentStateInvolution_eq_self_iff s).mp hs
  simp [localPrimeCombPairWeight, localPrimeCombStateValue, hfirst]

/-- Symbolic cancellation of all nine local exponent states.  No numerical
residue evaluation occurs: `Finset.sum_involution` pairs the six non-fixed
states, and the three fixed square-kill states have weight zero. -/
theorem sum_localPrimeCombPairWeight_eq_zero :
    ∑ s : TwoPrimeCollisionState, localPrimeCombPairWeight s = 0 := by
  classical
  exact Finset.sum_involution
    (s := (Finset.univ : Finset TwoPrimeCollisionState))
    (f := localPrimeCombPairWeight)
    (fun s _hs => collisionExponentStateInvolution s)
    (fun s _hs => by
      rw [localPrimeCombPairWeight_involution]
      simp)
    (fun s _hs hne hfix =>
      hne (localPrimeCombPairWeight_eq_zero_of_fixed s hfix))
    (fun _s _hs => Finset.mem_univ _)
    (fun s _hs => collisionExponentStateInvolution_involutive s)

/-- Current-cell CRT offset attached to the first exponent-state label. -/
def currentCollisionStateOffset (a : PrimeCombExponentState) : ℕ :=
  a.1 + 1

/-- Next-cell CRT offset attached to the second exponent-state label. -/
def nextCollisionStateOffset (b : PrimeCombExponentState) : ℕ :=
  b.1 + 5

/-- CRT realization of a labelled exponent-state pair.  This is a modular
realization; the involution itself remains on the labels. -/
def collisionExponentStateResidue
    (p q : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2))
    (s : TwoPrimeCollisionState) :
    ZMod ((p ^ 2) * (q ^ 2)) :=
  (ZMod.chineseRemainder hcop).symm
    (collisionRoot (p ^ 2) (currentCollisionStateOffset s.1),
      collisionRoot (q ^ 2) (nextCollisionStateOffset s.2))

/-- Every labelled exponent state realizes one of the existing nine CRT
collision classes. -/
theorem collisionExponentStateResidue_mem
    (p q : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2))
    (s : TwoPrimeCollisionState) :
    collisionExponentStateResidue p q hcop s ∈
      collisionCRTResidues p q hcop := by
  rcases s with ⟨a, b⟩
  unfold collisionExponentStateResidue collisionCRTResidues
  apply Finset.mem_image.mpr
  refine ⟨(collisionRoot (p ^ 2) (currentCollisionStateOffset a),
    collisionRoot (q ^ 2) (nextCollisionStateOffset b)), ?_, rfl⟩
  apply Finset.mem_product.mpr
  constructor
  · fin_cases a <;>
      simp [currentCollisionStateOffset, currentCollisionRoots]
  · fin_cases b <;>
      simp [nextCollisionStateOffset, nextCollisionRoots]

/-- The nine symbolic states realized as a finite residue set. -/
def collisionExponentStateResidues
    (p q : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2)) :
    Finset (ZMod ((p ^ 2) * (q ^ 2))) :=
  Finset.univ.image (collisionExponentStateResidue p q hcop)

/-- The labelled realization is contained in the existing CRT collision set. -/
theorem collisionExponentStateResidues_subset
    (p q : ℕ) (hcop : Nat.Coprime (p ^ 2) (q ^ 2)) :
    collisionExponentStateResidues p q hcop ⊆
      collisionCRTResidues p q hcop := by
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨s, _hs, rfl⟩
  exact collisionExponentStateResidue_mem p q hcop s

end RHLean.Arithmetic
