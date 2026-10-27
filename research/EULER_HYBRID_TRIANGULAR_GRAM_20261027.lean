import Mathlib
import «research.EULER_HYBRID_ABEL_GRAM_20261027»

/-!
# The triangular signed historical Gram of the exact Euler hyperbola

At X=R^2-1, the original bilinear form admits a triangular decomposition
Q_R=D_R+2B_R. D_R is nonnegative in integer arithmetic because the
hyperbola floor decreases with b, but B_R is SIGNED; we do not bound it.
The generic finite identity retains the terminal square at (N+1,N+1).
It vanishes only on the actual self-dual square-root horizon.

No finite-C, Mertens exponent improvement, or RH theorem is claimed.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- The actual historical diagonal square. -/
def eulerHybridDiagonal (R : ℕ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    mertensSummatory b ^ 2 *
      (eulerSelfDualFloor R b b -
        eulerSelfDualFloor R (b + 1) (b + 1))

/-- One off-diagonal signed historical/cofactor interaction.
The factor mu(b) is *not* replaced by a worst-case bounded sequence. -/
def eulerHybridStrictCross (R : ℕ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    (((μ b : ℤ) : ℂ)) *
      ∑ a ∈ Finset.Icc 1 (b - 1),
        mertensSummatory a *
          (eulerSelfDualFloor R a b -
            eulerSelfDualFloor R (a + 1) b)

/-- Finite summation by parts for an arbitrary cumulative sequence k.
The terminal boundary is essential. -/
private theorem eulerFiniteSquareAbel (N : ℕ)
    (k g : ℕ → ℂ) (hk0 : k 0 = 0) :
    (∑ b ∈ Finset.Icc 1 N,
      (k b - k (b - 1)) * g b) =
      (∑ b ∈ Finset.Icc 1 N,
        k b * (g b - g (b + 1))) + k N * g (N + 1) := by
  induction N with
  | zero => simp [hk0]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [ih, show N + 1 - 1 = N by omega]
      ring

/-- Generic symmetric finite square: the diagonal and both orientations
of every strict cross-pair. No arithmetic hypothesis is used. -/
private theorem eulerSymmetricFiniteSquare (N : ℕ)
    (c : ℕ → ℂ) (F : ℕ → ℕ → ℂ)
    (hF : ∀ a b, F a b = F b a) :
    (∑ b ∈ Finset.Icc 1 N,
      c b * (∑ a ∈ Finset.Icc 1 N, c a * F a b)) =
      (∑ b ∈ Finset.Icc 1 N, c b ^ 2 * F b b) +
      2 * ∑ b ∈ Finset.Icc 1 N,
        c b * (∑ a ∈ Finset.Icc 1 (b - 1), c a * F a b) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hswap :
          (∑ b ∈ Finset.Icc 1 N,
            c b * (c (N + 1) * F (N + 1) b)) =
          c (N + 1) *
            (∑ a ∈ Finset.Icc 1 N, c a * F a (N + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        rw [hF (N + 1) b]
        ring
      have hQ :
          (∑ b ∈ Finset.Icc 1 (N + 1),
            c b * (∑ a ∈ Finset.Icc 1 (N + 1), c a * F a b)) =
          (∑ b ∈ Finset.Icc 1 N,
            c b * (∑ a ∈ Finset.Icc 1 N, c a * F a b)) +
          2 * c (N + 1) *
            (∑ a ∈ Finset.Icc 1 N, c a * F a (N + 1)) +
          c (N + 1) ^ 2 * F (N + 1) (N + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp_rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, hswap]
        ring
      have hD :
          (∑ b ∈ Finset.Icc 1 (N + 1), c b ^ 2 * F b b) =
          (∑ b ∈ Finset.Icc 1 N, c b ^ 2 * F b b) +
            c (N + 1) ^ 2 * F (N + 1) (N + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      have hB :
          (∑ b ∈ Finset.Icc 1 (N + 1),
            c b * (∑ a ∈ Finset.Icc 1 (b - 1), c a * F a b)) =
          (∑ b ∈ Finset.Icc 1 N,
            c b * (∑ a ∈ Finset.Icc 1 (b - 1), c a * F a b)) +
          c (N + 1) *
            (∑ a ∈ Finset.Icc 1 N, c a * F a (N + 1)) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp [show N + 1 - 1 = N by omega]
      rw [hQ, hD, hB, ih]
      ring

/-- The square-endpoint diagonal corner is zero. -/
theorem eulerSelfDualFloor_root_corner_zero
    (R : ℕ) (hR : 2 ≤ R) :
    eulerSelfDualFloor R R R = 0 := by
  have hsq : 0 < R ^ 2 := by positivity
  have hlt : squareRootEndpoint R < R * R := by
    have h := Nat.sub_lt hsq (by norm_num : 0 < (1 : ℕ))
    simpa [squareRootEndpoint, pow_two] using h
  simp [eulerSelfDualFloor, Nat.div_eq_of_lt hlt]

/-- Original full historical bilinear floor form, with the diagonal and
signed triangular cross term exactly, on the true self-dual endpoint.
This is a finite identity and makes no quantitative claim for B_R. -/
theorem eulerSelfDualBilinear_eq_diagonal_add_signedStrictCross
    (R : ℕ) (hR : 2 ≤ R) :
    eulerSelfDualBilinear R =
      eulerHybridDiagonal R + 2 * eulerHybridStrictCross R := by
  let S := Finset.Icc 1 (R - 1)
  let f : ℕ → ℂ := fun b => (((μ b : ℤ) : ℂ))
  let F : ℕ → ℕ → ℂ := eulerSelfDualFloor R
  let M : ℕ → ℂ := mertensSummatory
  have hF : ∀ a b, F a b = F b a := by
    intro a b
    simp [F, eulerSelfDualFloor, Nat.mul_comm]
  have htop : R - 1 + 1 = R := by omega
  have hcorner : F R R = 0 := by
    exact eulerSelfDualFloor_root_corner_zero R hR
  have hM0 : M 0 = 0 := by
    simp [M]
  have hMstep (b : ℕ) (hb : 1 ≤ b) :
      M b ^ 2 - M (b - 1) ^ 2 =
        2 * M (b - 1) * f b + f b ^ 2 := by
    have hm := RHLean.Analysis.mertensSummatory_succ (b - 1)
    have hpred : b - 1 + 1 = b := by omega
    rw [hpred] at hm
    change M b = M (b - 1) + f b at hm
    rw [hm]
    ring
  have hdiag :
      eulerHybridDiagonal R =
        ∑ b ∈ S,
          (2 * M (b - 1) * f b + f b ^ 2) * F b b := by
    have habel :=
      eulerFiniteSquareAbel (R - 1) (fun b => M b ^ 2)
        (fun b => F b b) (by simp [hM0])
    rw [htop] at habel
    have hzero : M (R - 1) ^ 2 * F R R = 0 := by
      rw [hcorner]
      ring
    unfold eulerHybridDiagonal
    change (∑ b ∈ S, M b ^ 2 * (F b b - F (b + 1) (b + 1))) = _
    rw [hzero, add_zero] at habel
    calc
      (∑ b ∈ S, M b ^ 2 * (F b b - F (b + 1) (b + 1))) =
        ∑ b ∈ S, (M b ^ 2 - M (b - 1) ^ 2) * F b b :=
        habel.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hMstep b (Finset.mem_Icc.mp hb).1]
  have hcross :
      eulerHybridStrictCross R =
        ∑ b ∈ S,
          f b *
            ((∑ a ∈ Finset.Icc 1 (b - 1), f a * F a b) -
              M (b - 1) * F b b) := by
    unfold eulerHybridStrictCross
    apply Finset.sum_congr rfl
    intro b hb
    have hpred : b - 1 + 1 = b := by
      have hbb : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      omega
    have habel := RHLean.Analysis.sum_mertensSummatory_mul_forwardDifference
      (fun a => F a b) (b - 1)
    rw [hpred] at habel
    change
      (∑ a ∈ Finset.Icc 1 (b - 1),
        M a * (F a b - F (a + 1) b)) =
      (∑ a ∈ Finset.Icc 1 (b - 1), f a * F a b) -
        M (b - 1) * F b b at habel
    rw [habel]
  have hwhole :
      eulerSelfDualBilinear R =
        (∑ b ∈ S, f b ^ 2 * F b b) +
        2 * ∑ b ∈ S,
          f b * (∑ a ∈ Finset.Icc 1 (b - 1), f a * F a b) := by
    unfold eulerSelfDualBilinear
    change
      (∑ b ∈ S, f b * (∑ a ∈ S, f a * F a b)) = _
    exact eulerSymmetricFiniteSquare (R - 1) f F hF
  rw [hdiag, hcross]
  rw [hwhole]
  calc
    (∑ b ∈ S, f b ^ 2 * F b b) +
        2 * ∑ b ∈ S,
          f b * (∑ a ∈ Finset.Icc 1 (b - 1), f a * F a b) =
      ∑ b ∈ S,
        ((2 * M (b - 1) * f b + f b ^ 2) * F b b +
          2 * f b *
            ((∑ a ∈ Finset.Icc 1 (b - 1), f a * F a b) -
              M (b - 1) * F b b)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _hb
        ring
    _ = (∑ b ∈ S, (2 * M (b - 1) * f b + f b ^ 2) * F b b) +
        2 * ∑ b ∈ S,
          f b *
            ((∑ a ∈ Finset.Icc 1 (b - 1), f a * F a b) -
              M (b - 1) * F b b) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]

#print axioms eulerSelfDualBilinear_eq_diagonal_add_signedStrictCross

end RHLean.Proof
