import Mathlib
import RHLean.Analysis.FrozenSquareRunKernel
import RHLean.Proof.SquareRootCanonicalDowncrossFinalSeam

open scoped BigOperators

/-!
# Frozen square runs as differences of the canonical root-downcross frontier

The frozen square-run kernel already gives the exact signed mass of a forward
subdoubling square run,

`K(a,b) = M(a^2-1) - M((b+1)^2-1)`.

Independently, the canonical low-wheel involution gives at every square endpoint

`M(R^2-1) = M(R) - D_R`,

where `D_R = lowWheelCanonicalDowncrossLedger R` is the one signed adjacent
multiplicative root-downcross frontier.

Combining the two identities gives the exact run law

`K(a,b) = (M(a)-M(b+1)) + (D_{b+1}-D_a)`.

The lower-scale Mertens gap is harmless at run scale: its norm is at most the
root interval length `b+1-a`.  Consequently the frozen-kernel energy and the
energy of the *change* in the canonical downcross frontier differ by only one
linear run-length square.  This file proves that the resulting downcross-run
energy statement is exactly equivalent to the existing frozen-square-run,
global Mertens-energy, signed square-run, and primorial residual criteria.

This is deliberately a difference theorem.  No pointwise bound on `D_R` is
assumed, and no prime-gap lifetime model is used.  The remaining arithmetic
problem is therefore to control how the signed Euler frontier changes across a
subdoubling run, where the predecessor-cube / recursive-Go machinery can act
before any norm is taken.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Proof

/-- Change of the canonical adjacent root-downcross frontier across the square
run from root `a` to root `b+1`. -/
def canonicalDowncrossRunDifference (a b : ℕ) : ℂ :=
  lowWheelCanonicalDowncrossLedger (b + 1) -
    lowWheelCanonicalDowncrossLedger a

/-- **Exact square-run / downcross-difference identity.**

The only term between the frozen square-run kernel and the change in the
canonical downcross frontier is the ordinary lower-scale Mertens gap across the
root interval. -/
theorem frozenSquareRunKernel_eq_mertensGap_add_canonicalDowncrossRunDifference
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    frozenSquareRunKernel a b =
      (mertensSummatory a - mertensSummatory (b + 1)) +
        canonicalDowncrossRunDifference a b := by
  have hk := frozenSquareRunKernel_eq_squarePrefix_sub a b (by omega) hab hsub
  have hA := squarePrefixMertens_eq_mertens_sub_canonicalDowncross a ha
  have hBraw :=
    squarePrefixMertens_eq_mertens_sub_canonicalDowncross (b + 1) (by omega)
  have hB :
      squarePrefixMertens b =
        mertensSummatory (b + 1) - lowWheelCanonicalDowncrossLedger (b + 1) := by
    simpa using hBraw
  rw [hk, hA, hB]
  unfold canonicalDowncrossRunDifference
  ring

/-- Reverse form of the same exact identity. -/
theorem canonicalDowncrossRunDifference_eq_kernel_sub_mertensGap
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    canonicalDowncrossRunDifference a b =
      frozenSquareRunKernel a b -
        (mertensSummatory a - mertensSummatory (b + 1)) := by
  have h :=
    frozenSquareRunKernel_eq_mertensGap_add_canonicalDowncrossRunDifference
      a b ha hab hsub
  linear_combination h

/-- The lower-scale Mertens part of the exact run law costs at most the root
interval length. -/
theorem norm_mertensRunGap_le_rootLength
    (a b : ℕ) (hab : a ≤ b) :
    ‖mertensSummatory a - mertensSummatory (b + 1)‖ ≤
      (((b + 1 - a : ℕ) : ℝ)) := by
  have hgap := norm_mertensSummatory_sub_le a (b + 1) (by omega)
  have hneg :
      mertensSummatory a - mertensSummatory (b + 1) =
        -(mertensSummatory (b + 1) - mertensSummatory a) := by
    ring
  rw [hneg, norm_neg]
  exact hgap

private theorem norm_sq_add_le_two_downcrossBridge (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxy : 0 ≤ ‖x + y‖ := norm_nonneg (x + y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- One-sided energy comparison: the frozen kernel is controlled by the
frontier change plus one root-interval square. -/
theorem norm_frozenSquareRunKernel_sq_le_rootLength_add_downcrossDifference
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    ‖frozenSquareRunKernel a b‖ ^ 2 ≤
      2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 +
        2 * ‖canonicalDowncrossRunDifference a b‖ ^ 2 := by
  have hid :=
    frozenSquareRunKernel_eq_mertensGap_add_canonicalDowncrossRunDifference
      a b ha hab hsub
  have hadd := norm_sq_add_le_two_downcrossBridge
    (mertensSummatory a - mertensSummatory (b + 1))
    (canonicalDowncrossRunDifference a b)
  have hgap := norm_mertensRunGap_le_rootLength a b hab
  have hgap0 :
      0 ≤ ‖mertensSummatory a - mertensSummatory (b + 1)‖ := norm_nonneg _
  have hlen0 : 0 ≤ (((b + 1 - a : ℕ) : ℝ)) := by positivity
  have hgapSq :
      ‖mertensSummatory a - mertensSummatory (b + 1)‖ ^ 2 ≤
        (((b + 1 - a : ℕ) : ℝ)) ^ 2 := by
    nlinarith
  rw [hid]
  calc
    ‖(mertensSummatory a - mertensSummatory (b + 1)) +
        canonicalDowncrossRunDifference a b‖ ^ 2 ≤
      2 * ‖mertensSummatory a - mertensSummatory (b + 1)‖ ^ 2 +
        2 * ‖canonicalDowncrossRunDifference a b‖ ^ 2 := hadd
    _ ≤ 2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 +
        2 * ‖canonicalDowncrossRunDifference a b‖ ^ 2 := by
      nlinarith

/-- Reverse energy comparison: the change in the canonical frontier is
controlled by the frozen kernel plus the same root-interval square. -/
theorem norm_canonicalDowncrossRunDifference_sq_le_kernel_add_rootLength
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b)
    (hsub : (b + 1) ^ 2 ≤ 2 * a ^ 2) :
    ‖canonicalDowncrossRunDifference a b‖ ^ 2 ≤
      2 * ‖frozenSquareRunKernel a b‖ ^ 2 +
        2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 := by
  have hid :=
    canonicalDowncrossRunDifference_eq_kernel_sub_mertensGap
      a b ha hab hsub
  have hadd := norm_sq_add_le_two_downcrossBridge
    (frozenSquareRunKernel a b)
    (-(mertensSummatory a - mertensSummatory (b + 1)))
  have hgap := norm_mertensRunGap_le_rootLength a b hab
  have hgap0 :
      0 ≤ ‖mertensSummatory a - mertensSummatory (b + 1)‖ := norm_nonneg _
  have hlen0 : 0 ≤ (((b + 1 - a : ℕ) : ℝ)) := by positivity
  have hgapSq :
      ‖mertensSummatory a - mertensSummatory (b + 1)‖ ^ 2 ≤
        (((b + 1 - a : ℕ) : ℝ)) ^ 2 := by
    nlinarith
  rw [hid, sub_eq_add_neg]
  calc
    ‖frozenSquareRunKernel a b +
        -(mertensSummatory a - mertensSummatory (b + 1))‖ ^ 2 ≤
      2 * ‖frozenSquareRunKernel a b‖ ^ 2 +
        2 * ‖-(mertensSummatory a - mertensSummatory (b + 1))‖ ^ 2 := hadd
    _ = 2 * ‖frozenSquareRunKernel a b‖ ^ 2 +
        2 * ‖mertensSummatory a - mertensSummatory (b + 1)‖ ^ 2 := by
      rw [norm_neg]
    _ ≤ 2 * ‖frozenSquareRunKernel a b‖ ^ 2 +
        2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 := by
      nlinarith

/-- The root-interval square is below the physical endpoint to every exponent
`1+ε`, so it is genuinely lower order at the frozen-run energy scale. -/
private theorem rootLength_sq_le_endpoint_rpow
    (a b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((b + 1 - a : ℕ) : ℝ)) ^ 2 ≤
      Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by
  have hlenNat : b + 1 - a ≤ b + 1 := Nat.sub_le _ _
  have hlen :
      (((b + 1 - a : ℕ) : ℝ)) ≤ (((b + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hlenNat
  have hlen0 : 0 ≤ (((b + 1 - a : ℕ) : ℝ)) := by positivity
  have hroot0 : 0 ≤ (((b + 1 : ℕ) : ℝ)) := by positivity
  have hsq :
      (((b + 1 - a : ℕ) : ℝ)) ^ 2 ≤ (((b + 1 : ℕ) : ℝ)) ^ 2 := by
    nlinarith
  have hendpoint :
      (((b + 1 : ℕ) : ℝ)) ^ 2 = ((((b + 1) ^ 2 : ℕ) : ℝ)) := by
    norm_cast
  have hbaseNat : 1 ≤ (b + 1) ^ 2 := by positivity
  have hbase :
      (1 : ℝ) ≤ ((((b + 1) ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hbaseNat
  have hrpow := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (1 : ℝ) ≤ 1 + ε)
  calc
    (((b + 1 - a : ℕ) : ℝ)) ^ 2 ≤ (((b + 1 : ℕ) : ℝ)) ^ 2 := hsq
    _ = ((((b + 1) ^ 2 : ℕ) : ℝ)) := hendpoint
    _ ≤ Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by
      simpa using hrpow

/-- **RH-scale downcross-run seam.**  This asks only for the energy of the
change `D_{b+1}-D_a` on forward subdoubling runs.  It does not ask for any
pointwise bound on the absolute frontier `D_R`. -/
def CanonicalDowncrossRunDifferenceEnergyBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, 3 ≤ a → a ≤ b →
        (b + 1) ^ 2 < 2 * a ^ 2 →
        ‖canonicalDowncrossRunDifference a b‖ ^ 2 ≤
          C * Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)

/-- The downcross-run energy premise supplies the full frozen square-run energy
criterion.  Backward runs have zero frozen kernel; every forward strict
subdoubling run automatically starts at root at least `3`. -/
theorem frozenSquareRunEnergyBounded_of_canonicalDowncrossRunDifferenceEnergyBounded
    (hD : CanonicalDowncrossRunDifferenceEnergyBoundedStatement) :
    FrozenSquareRunEnergyBoundedStatement := by
  intro ε hε
  rcases hD ε hε with ⟨C, hC, hbound⟩
  refine ⟨2 + 2 * C, by positivity, ?_⟩
  intro a b hsub
  by_cases hab : a ≤ b
  · have hmono : (a + 1) ^ 2 ≤ (b + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have ha3 : 3 ≤ a := by
      by_contra hnot
      have ha2 : a ≤ 2 := by omega
      nlinarith
    have hlocal :=
      norm_frozenSquareRunKernel_sq_le_rootLength_add_downcrossDifference
        a b ha3 hab hsub.le
    have hDab := hbound a b ha3 hab hsub
    have hlen := rootLength_sq_le_endpoint_rpow a b hε
    let P : ℝ := Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)
    have hP0 : 0 ≤ P := by
      dsimp [P]
      exact Real.rpow_nonneg (by positivity) _
    have hDab' : ‖canonicalDowncrossRunDifference a b‖ ^ 2 ≤ C * P := by
      simpa [P] using hDab
    have hlen' : (((b + 1 - a : ℕ) : ℝ)) ^ 2 ≤ P := by
      simpa [P] using hlen
    calc
      ‖frozenSquareRunKernel a b‖ ^ 2 ≤
          2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 +
            2 * ‖canonicalDowncrossRunDifference a b‖ ^ 2 := hlocal
      _ ≤ 2 * P + 2 * (C * P) := by nlinarith
      _ = (2 + 2 * C) * P := by ring
      _ = (2 + 2 * C) *
          Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by rfl
  · have hba : b + 1 ≤ a := by omega
    rw [frozenSquareRunKernel_eq_zero_of_succ_le hba]
    have hP0 :
        0 ≤ Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) :=
      Real.rpow_nonneg (by positivity) _
    have hcoef : 0 ≤ 2 + 2 * C := by linarith
    have hrhs :
        0 ≤ (2 + 2 * C) *
          Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) :=
      mul_nonneg hcoef hP0
    simpa using hrhs

/-- Conversely, the frozen square-run criterion controls the energy of every
canonical downcross-frontier change on the same forward subdoubling window. -/
theorem canonicalDowncrossRunDifferenceEnergyBounded_of_frozenSquareRunEnergyBounded
    (hF : FrozenSquareRunEnergyBoundedStatement) :
    CanonicalDowncrossRunDifferenceEnergyBoundedStatement := by
  intro ε hε
  rcases hF ε hε with ⟨C, hC, hbound⟩
  refine ⟨2 * C + 2, by positivity, ?_⟩
  intro a b ha hab hsub
  have hlocal :=
    norm_canonicalDowncrossRunDifference_sq_le_kernel_add_rootLength
      a b ha hab hsub.le
  have hK := hbound a b hsub
  have hlen := rootLength_sq_le_endpoint_rpow a b hε
  let P : ℝ := Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact Real.rpow_nonneg (by positivity) _
  have hK' : ‖frozenSquareRunKernel a b‖ ^ 2 ≤ C * P := by
    simpa [P] using hK
  have hlen' : (((b + 1 - a : ℕ) : ℝ)) ^ 2 ≤ P := by
    simpa [P] using hlen
  calc
    ‖canonicalDowncrossRunDifference a b‖ ^ 2 ≤
        2 * ‖frozenSquareRunKernel a b‖ ^ 2 +
          2 * (((b + 1 - a : ℕ) : ℝ)) ^ 2 := hlocal
    _ ≤ 2 * (C * P) + 2 * P := by nlinarith
    _ = (2 * C + 2) * P := by ring
    _ = (2 * C + 2) *
        Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε) := by rfl

/-- The reconstructed seam is not merely sufficient: it is exactly the existing
frozen square-run energy criterion. -/
theorem canonicalDowncrossRunDifferenceEnergyBounded_iff_frozenSquareRunEnergyBounded :
    CanonicalDowncrossRunDifferenceEnergyBoundedStatement ↔
      FrozenSquareRunEnergyBoundedStatement := by
  constructor
  · exact frozenSquareRunEnergyBounded_of_canonicalDowncrossRunDifferenceEnergyBounded
  · exact canonicalDowncrossRunDifferenceEnergyBounded_of_frozenSquareRunEnergyBounded

/-- Hence controlling only changes of the signed canonical root-downcross
frontier is exactly the ordinary global Mertens-energy criterion. -/
theorem canonicalDowncrossRunDifferenceEnergyBounded_iff_mertensEnergyBounded :
    CanonicalDowncrossRunDifferenceEnergyBoundedStatement ↔
      MertensEnergyBoundedStatement := by
  exact canonicalDowncrossRunDifferenceEnergyBounded_iff_frozenSquareRunEnergyBounded.trans
    frozenSquareRunEnergyBounded_iff_mertensEnergyBounded

/-- Equivalent form on the repository's maximal signed square-run criterion. -/
theorem canonicalDowncrossRunDifferenceEnergyBounded_iff_squareRunEnergyBounded :
    CanonicalDowncrossRunDifferenceEnergyBoundedStatement ↔
      SquareRunEnergyBoundedStatement := by
  exact canonicalDowncrossRunDifferenceEnergyBounded_iff_frozenSquareRunEnergyBounded.trans
    frozenSquareRunEnergyBounded_iff_squareRunEnergyBounded

/-- Equivalent form on the synchronized primorial-wheel residual criterion. -/
theorem canonicalDowncrossRunDifferenceEnergyBounded_iff_primorialResidualBounded :
    CanonicalDowncrossRunDifferenceEnergyBoundedStatement ↔
      PrimeWheelResidualBoundedStatement primorialWheelFamily := by
  exact canonicalDowncrossRunDifferenceEnergyBounded_iff_frozenSquareRunEnergyBounded.trans
    frozenSquareRunEnergyBounded_iff_primorialResidualBounded

end RHLean.Analysis
