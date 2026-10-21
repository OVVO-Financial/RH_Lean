import Mathlib

/-!
# Polarized, pre-norm NNS fourth moments for the realified OAI marked row

The actual OAI marked source has row integrand
    ‖P_j(u) * P_k(u) * F.physicalProduct selected u‖²,  j+k ≤ 2.
Its correct fourth-degree polarization is
    |W(u)|² |P_j(u)|² |P_k(u)|²,
not |P_j P_k W|^4.

Theorems below establish all algebraic signs, unnormalized weighted row
identities, and the *character-twisted* Euler pair coefficient. They DO NOT
identify a generic finite atom array with the full OAI ideal source and
DO NOT prove a power-saving moment bound or a RH result.

The key source correction is W(T)-χ(p)*W(T∪{p}), not merely W(T)-W(T∪{p}).
-/

noncomputable section
open scoped BigOperators
namespace RHLean.MarkedRealNNS

def up (g : ℝ) : ℝ := max g 0
def down (g : ℝ) : ℝ := max (-g) 0

/-- The exact unnormalized zero-target UPM-minus-LPM equality. -/
theorem up_sub_down (g : ℝ) : up g - down g = g := by
  unfold up down
  rcases le_total 0 g with hg | hg
  · rw [max_eq_left hg, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right hg, max_eq_left (by linarith)]
    ring

/-- Eight sign quadrants: four in each coordinate of Phi. -/
def signedFace (x y : ℝ) : ℝ :=
  up x * up y + down x * down y -
    up x * down y - down x * up y

theorem signedFace_eq (x y : ℝ) : signedFace x y = x * y := by
  calc
    signedFace x y = (up x - down x) * (up y - down y) := by
      unfold signedFace
      ring
    _ = x * y := by rw [up_sub_down, up_sub_down]

/-- Actual normalized real Gram in the invertible Phi coordinates. -/
def phiGram (x y : ℝ × ℝ) : ℝ :=
  (x.1 * y.1 + x.2 * y.2) / 2

theorem phiGram_eq_signedFaces (x y : ℝ × ℝ) :
    phiGram x y = (signedFace x.1 y.1 + signedFace x.2 y.2) / 2 := by
  simp only [signedFace_eq, phiGram]

/-- The degree-two pre-norm energy identity for each derivative row. -/
theorem rowEnergy (E K P N : ℝ)
    (h : E = K + 2 * P - 2 * N) :
    E = K + 2 * (P - N) := by
  rw [h]
  ring

/-- Pure fourth moment: all four terms, including the negative LPM bill. -/
theorem pureFourth (E K P N : ℝ)
    (h : E = K + 2 * P - 2 * N) :
    E ^ 2 = K ^ 2 + 4 * K * P - 4 * K * N +
      4 * (P - N) ^ 2 := by
  rw [h]
  ring

/-- P1: EXACT polarized fourth moment for j+k<=2.
This is not an eighth-degree moment of the product Pj*Pk. -/
theorem polarizedFourth
    (Ej Ek Kj Pj Nj Kk Pk Nk : ℝ)
    (hj : Ej = Kj + 2 * Pj - 2 * Nj)
    (hk : Ek = Kk + 2 * Pk - 2 * Nk) :
    Ej * Ek =
      Kj * Kk +
        2 * (Kj * Pk + Kk * Pj) -
        2 * (Kj * Nk + Kk * Nj) +
        4 * (Pj - Nj) * (Pk - Nk) := by
  rw [hj, hk]
  ring

/-- Original varying, unnormalized physical row weights retained. -/
theorem weightedPolarizedFourth {ι : Type*}
    (rows : Finset ι) (w Ej Ek Kj Pj Nj Kk Pk Nk : ι → ℝ)
    (hj : ∀ u ∈ rows, Ej u = Kj u + 2 * Pj u - 2 * Nj u)
    (hk : ∀ u ∈ rows, Ek u = Kk u + 2 * Pk u - 2 * Nk u) :
    (∑ u ∈ rows, w u * (Ej u * Ek u)) =
      ∑ u ∈ rows, w u *
        (Kj u * Kk u +
          2 * (Kj u * Pk u + Kk u * Pj u) -
          2 * (Kj u * Nk u + Kk u * Nj u) +
          4 * (Pj u - Nj u) * (Pk u - Nk u)) := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [polarizedFourth (Ej u) (Ek u) (Kj u) (Pj u) (Nj u)
    (Kk u) (Pk u) (Nk u) (hj u hu) (hk u hu)]

/-- The known fourth-moment upper bound implies precisely this lower
bound on its already certified negative mixed payment; extracting the
inequality backward DOES NOT improve the original exponent. -/
theorem negativePaymentLower
    (M4 S A B Q upperBound : ℝ)
    (hMoment : M4 = S + 4 * A - 4 * B + 4 * Q)
    (hBound : M4 ≤ upperBound) :
    B ≥ A + S / 4 + Q - upperBound / 4 := by
  linarith

/-- Exact good-row contraction (conditionally useful for source-specific
analyses; it is not implied by PNT). -/
theorem goodRowEnergyLe
    (E K P N c : ℝ)
    (hE : E = K + 2 * P - 2 * N)
    (hGood : N - P ≥ ((1 - c) / 2) * K) :
    E ≤ c * K := by
  linarith

/-- CORRECT multiplicatively twisted Euler toggling.
The scalar weight difference alone is insufficient for nontrivial phase. -/
theorem twistedEulerPair
    (W0 W1 phase : ℂ) :
    W0 - phase * W1 =
      (W0 - W1) + (1 - phase) * W1 := by
  ring

/-- Character phase -1 defeats a constant-weight smooth pairing. -/
theorem noAutomaticSmoothGain (W : ℂ) :
    W - (-1 : ℂ) * W = 2 * W := by
  ring

/-- Ordinary logarithmic shifts for j<=2; the OAI logProfile
must be proved to have this form for each actual source. -/
theorem logarithmicShiftOne (l p : ℝ) :
    (l + p) - l = p := by ring

theorem logarithmicShiftTwo (l p : ℝ) :
    (l + p) ^ 2 - l ^ 2 = 2 * l * p + p ^ 2 := by ring

end RHLean.MarkedRealNNS

#print axioms RHLean.MarkedRealNNS.polarizedFourth
#print axioms RHLean.MarkedRealNNS.weightedPolarizedFourth
#print axioms RHLean.MarkedRealNNS.twistedEulerPair
