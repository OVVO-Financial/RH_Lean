import Mathlib
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence
import RHLean.Proof.PrimeCombVisualizationDynamics

/-!
# Frozen rough-cofactor window behind first-owner wall fallout

The first-owner wall has already been reduced to one fresh owner and old born
partners `q <= K`.  Before inserting the wall-specific hypotheses, this file
isolates the exact finite object that appears after swapping the cofactor and
old-prime sums.

For a frozen prime universe `S` and cutoffs `A <= B`, the open/closed window

`A < P(t) <= B`

on Boolean faces has signed mass exactly

`F_S(B) - F_S(A)`.

Specializing `S = primesUpTo (q-1)`, `A = X_R/p`, and `B = X_R/q` gives the
rough cofactor window

`X_R/p < c <= X_R/q`, `P⁺(c) < q`.

The represented squarefree cofactors are also exposed as the image of the
window faces under `primeFaceProduct`; injectivity of products of distinct
prime coordinates shows that their ordinary Möbius sum is literally the same
frozen-window mass.

No estimate, asymptotic, PNT input, unrestricted Mertens replacement, or RH
input appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Boolean faces in one open/closed product window. -/
def frozenPrimeUniverseWindowFaces
    (S : Finset ℕ) (A B : ℕ) : Finset (Finset ℕ) :=
  S.powerset.filter fun t =>
    A < primeFaceProduct t ∧ primeFaceProduct t ≤ B

@[simp] theorem mem_frozenPrimeUniverseWindowFaces
    {S : Finset ℕ} {A B : ℕ} {t : Finset ℕ} :
    t ∈ frozenPrimeUniverseWindowFaces S A B ↔
      t ∈ S.powerset ∧ A < primeFaceProduct t ∧ primeFaceProduct t ≤ B := by
  simp [frozenPrimeUniverseWindowFaces]

/-- Signed alternating mass of one frozen product window. -/
def frozenPrimeUniverseWindowMass
    (S : Finset ℕ) (A B : ℕ) : ℤ :=
  ∑ t ∈ frozenPrimeUniverseWindowFaces S A B, booleanCubeSign t

/-- **Frozen mass difference = exact open/closed face window.** -/
theorem frozenPrimeUniverseWindowMass_eq_sub
    {S : Finset ℕ} {A B : ℕ} (hAB : A ≤ B) :
    frozenPrimeUniverseWindowMass S A B =
      frozenPrimeUniverseMass S B - frozenPrimeUniverseMass S A := by
  unfold frozenPrimeUniverseWindowMass frozenPrimeUniverseWindowFaces
  rw [Finset.sum_filter,
    frozenPrimeUniverseMass_eq_cutoffSum,
    frozenPrimeUniverseMass_eq_cutoffSum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hA : primeFaceProduct t ≤ A
  · have hB : primeFaceProduct t ≤ B := hA.trans hAB
    have hnot : ¬ A < primeFaceProduct t := Nat.not_lt.mpr hA
    simp [hA, hB, hnot]
  · have hAt : A < primeFaceProduct t := Nat.lt_of_not_ge hA
    by_cases hB : primeFaceProduct t ≤ B
    · simp [hA, hAt, hB]
    · simp [hA, hAt, hB]

/-- Square-root wall window faces for one old partner `q` and one fresh wall
owner `p`. -/
def squareRootLowPrimeOldPrimeWallWindowFaces
    (R p q : ℕ) : Finset (Finset ℕ) :=
  frozenPrimeUniverseWindowFaces
    (primesUpTo (q - 1))
    (squareRootEndpoint R / p)
    (squareRootEndpoint R / q)

/-- Their signed mass. -/
def squareRootLowPrimeOldPrimeWallWindowMass
    (R p q : ℕ) : ℤ :=
  frozenPrimeUniverseWindowMass
    (primesUpTo (q - 1))
    (squareRootEndpoint R / p)
    (squareRootEndpoint R / q)

/-- **The wall cofactor window is exactly a frozen `F_{q^-}` difference.** -/
theorem squareRootLowPrimeOldPrimeWallWindowMass_eq_frozenDifference
    {R p q : ℕ} (hq : q.Prime) (hqp : q ≤ p) :
    squareRootLowPrimeOldPrimeWallWindowMass R p q =
      frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / q) -
        frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / p) := by
  unfold squareRootLowPrimeOldPrimeWallWindowMass
  apply frozenPrimeUniverseWindowMass_eq_sub
  exact Nat.div_le_div_left hqp hq.pos

/-- Actual squarefree cofactors represented by the frozen wall window. -/
def squareRootLowPrimeOldPrimeWallWindowCofactors
    (R p q : ℕ) : Finset ℕ :=
  (squareRootLowPrimeOldPrimeWallWindowFaces R p q).image primeFaceProduct

/-- Products are injective on the wall-window face family because every
coordinate is prime. -/
theorem squareRootLowPrimeOldPrimeWallWindow_primeFaceProduct_injOn
    (R p q : ℕ) :
    Set.InjOn primeFaceProduct
      (↑(squareRootLowPrimeOldPrimeWallWindowFaces R p q)) := by
  intro t ht u hu hprod
  have htPow := (mem_frozenPrimeUniverseWindowFaces.mp ht).1
  have huPow := (mem_frozenPrimeUniverseWindowFaces.mp hu).1
  have htSub := Finset.mem_powerset.mp htPow
  have huSub := Finset.mem_powerset.mp huPow
  exact (primeFaceProduct_eq_iff
    (fun r hr => prime_of_mem_primesUpTo (htSub hr))
    (fun r hr => prime_of_mem_primesUpTo (huSub hr))).mp hprod

/-- The Möbius weight of every represented wall-window cofactor is its Boolean
face sign. -/
theorem squareRootLowPrimeOldPrimeWallWindow_moebius_eq_sign
    {R p q : ℕ} {t : Finset ℕ}
    (ht : t ∈ squareRootLowPrimeOldPrimeWallWindowFaces R p q) :
    μ (primeFaceProduct t) = booleanCubeSign t := by
  have htPow := (mem_frozenPrimeUniverseWindowFaces.mp ht).1
  have htSub := Finset.mem_powerset.mp htPow
  exact moebius_primeFaceProduct_eq_booleanCubeSign t
    (fun r hr => prime_of_mem_primesUpTo (htSub hr))

/-- **The ordinary Möbius sum of the represented rough cofactors equals the
frozen face-window mass exactly.** -/
theorem squareRootLowPrimeOldPrimeWallWindowCofactors_moebiusSum
    (R p q : ℕ) :
    (∑ c ∈ squareRootLowPrimeOldPrimeWallWindowCofactors R p q, μ c) =
      squareRootLowPrimeOldPrimeWallWindowMass R p q := by
  unfold squareRootLowPrimeOldPrimeWallWindowCofactors
    squareRootLowPrimeOldPrimeWallWindowMass
    frozenPrimeUniverseWindowMass
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    exact squareRootLowPrimeOldPrimeWallWindow_moebius_eq_sign ht
  · intro a ha b hb hab
    exact squareRootLowPrimeOldPrimeWallWindow_primeFaceProduct_injOn
      R p q ha hb hab

/-- **Integer rough-cofactor form of the horizontal recurrence window.** -/
theorem squareRootLowPrimeOldPrimeWallWindowCofactors_moebiusSum_eq_frozenDifference
    {R p q : ℕ} (hq : q.Prime) (hqp : q ≤ p) :
    (∑ c ∈ squareRootLowPrimeOldPrimeWallWindowCofactors R p q, μ c) =
      frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / q) -
        frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / p) := by
  rw [squareRootLowPrimeOldPrimeWallWindowCofactors_moebiusSum,
    squareRootLowPrimeOldPrimeWallWindowMass_eq_frozenDifference hq hqp]

end RHLean.Proof
