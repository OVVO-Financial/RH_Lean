import Mathlib
import RHLean.Proof.RecursivePrimeReplacement

/-!
# Complementary replacement fibre state

This module isolates the arithmetic state that survives the exact replacement
fibre dictionary.

For `X_R = R^2 - 1`, the complementary fibre coefficient

` t_R(z) = sum_{R <= n <= X_R, floor(X_R/n)=z} mu(n) `

is exactly a Mertens increment on the reciprocal hyperbola interval

` (floor(X_R/(z+1)), floor(X_R/z)] `.

The quotient kernel from `RecursivePrimeReplacement` is explicitly lower
triangular.  Composing the coefficient dictionary with the classical unit
Möbius renewal recovers only the ordinary complementary-tail partition

`sum_z t_R(z) = M(X_R) - M(R-1)`.

Accordingly, the endpoint recombination theorem in
`RecursivePrimeReplacement` is a consistency reconstruction, not an analytic
cancellation estimate.  The surviving state is the signed vector `t_R`; no
absolute value is taken on its individual fibres here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- Left endpoint of the complementary reciprocal fibre, inclusive. -/
def squareRootReplacementFibreLower (R z : ℕ) : ℕ :=
  squareRootEndpoint R / (z + 1) + 1

/-- Right endpoint of the complementary reciprocal fibre, inclusive. -/
def squareRootReplacementFibreUpper (R z : ℕ) : ℕ :=
  squareRootEndpoint R / z

/-- The quotient kernel has no mass above its diagonal. -/
theorem squareRootReplacementQuotientKernel_eq_zero_of_lt
    {z y : ℕ} (hzy : z < y) :
    squareRootReplacementQuotientKernel z y = 0 := by
  unfold squareRootReplacementQuotientKernel
  apply Finset.sum_eq_zero
  intro k _hk
  have hle : z / k ≤ z := Nat.div_le_self z k
  have hne : z / k ≠ y := by omega
  simp [hne]

/-- The diagonal coefficient of the quotient kernel is exactly one. -/
theorem squareRootReplacementQuotientKernel_self
    {z : ℕ} (hz : 1 ≤ z) :
    squareRootReplacementQuotientKernel z z = 1 := by
  classical
  unfold squareRootReplacementQuotientKernel
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 z := by simp [hz]
  calc
    (∑ k ∈ Finset.Icc 1 z, if z / k = z then (1 : ℂ) else 0) =
      ∑ k ∈ Finset.Icc 1 z, if k = 1 then (1 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hk1 : k = 1
        · subst k
          simp
        · have hkI := Finset.mem_Icc.mp hk
          have hk2 : 1 < k := by omega
          have hzpos : 0 < z := by omega
          have hlt : z / k < z := Nat.div_lt_self hzpos hk2
          have hne : z / k ≠ z := by omega
          simp [hk1, hne]
    _ = 1 := by simp [h1mem]

private theorem nat_div_eq_iff_reciprocal_interval
    {X n z : ℕ} (hn : 1 ≤ n) (hz : 1 ≤ z) :
    X / n = z ↔ X / (z + 1) < n ∧ n ≤ X / z := by
  have hnpos : 0 < n := by omega
  have hzpos : 0 < z := by omega
  have hzp : 0 < z + 1 := by omega
  constructor
  · intro hdiv
    have hlt : X / n < z + 1 := by omega
    have hxlt : X < (z + 1) * n :=
      (Nat.div_lt_iff_lt_mul hnpos).1 hlt
    have hlower : X / (z + 1) < n :=
      (Nat.div_lt_iff_lt_mul hzp).2 (by simpa [Nat.mul_comm] using hxlt)
    have hle : z ≤ X / n := by omega
    have hmul : z * n ≤ X :=
      (Nat.le_div_iff_mul_le hnpos).1 hle
    have hupper : n ≤ X / z :=
      (Nat.le_div_iff_mul_le hzpos).2 (by simpa [Nat.mul_comm] using hmul)
    exact ⟨hlower, hupper⟩
  · rintro ⟨hlower, hupper⟩
    have hmulUpper : n * z ≤ X :=
      (Nat.le_div_iff_mul_le hzpos).1 hupper
    have hzle : z ≤ X / n :=
      (Nat.le_div_iff_mul_le hnpos).2
        (by simpa [Nat.mul_comm] using hmulUpper)
    have hxlt : X < n * (z + 1) :=
      (Nat.div_lt_iff_lt_mul hzp).1 hlower
    have hlt : X / n < z + 1 :=
      (Nat.div_lt_iff_lt_mul hnpos).2
        (by simpa [Nat.mul_comm] using hxlt)
    omega

private theorem squareRoot_pred_mul_root_le_endpoint
    (R : ℕ) (hR : 2 ≤ R) :
    (R - 1) * R ≤ squareRootEndpoint R := by
  have hpred : R - 1 + 1 = R := by omega
  have hend : squareRootEndpoint R + 1 = R ^ 2 := by
    unfold squareRootEndpoint
    have hsq : 0 < R ^ 2 := by positivity
    omega
  nlinarith

/-- For every nonzero complementary quotient `z < R`, the reciprocal interval
already lies inside the physical tail `n >= R`; no extra clipping is needed. -/
theorem squareRoot_root_le_replacementFibreLower
    (R z : ℕ) (hR : 2 ≤ R) (hzR : z < R) :
    R ≤ squareRootReplacementFibreLower R z := by
  have hzr : z + 1 ≤ R := by omega
  have hmul : (R - 1) * (z + 1) ≤ (R - 1) * R :=
    Nat.mul_le_mul_left (R - 1) hzr
  have hbound : (R - 1) * (z + 1) ≤ squareRootEndpoint R :=
    hmul.trans (squareRoot_pred_mul_root_le_endpoint R hR)
  have hdiv : R - 1 ≤ squareRootEndpoint R / (z + 1) :=
    (Nat.le_div_iff_mul_le (by omega : 0 < z + 1)).2 hbound
  unfold squareRootReplacementFibreLower
  omega

/-- The hyperbola interval attached to `1 <= z < R` is nonempty. -/
theorem squareRoot_replacementFibreLower_le_upper
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    squareRootReplacementFibreLower R z ≤
      squareRootReplacementFibreUpper R z := by
  let X := squareRootEndpoint R
  have hzr : z + 1 ≤ R := by omega
  have hzpred : z ≤ R - 1 := by omega
  have hprod1 : z * (z + 1) ≤ (R - 1) * R :=
    Nat.mul_le_mul hzpred hzr
  have hprod : z * (z + 1) ≤ X := by
    dsimp [X]
    exact hprod1.trans (squareRoot_pred_mul_root_le_endpoint R hR)
  have hzq : z ≤ X / (z + 1) :=
    (Nat.le_div_iff_mul_le (by omega : 0 < z + 1)).2 hprod
  have hstep : (X / (z + 1) + 1) * z ≤
      (X / (z + 1)) * (z + 1) := by
    nlinarith
  have htoX : (X / (z + 1) + 1) * z ≤ X :=
    hstep.trans (Nat.div_mul_le_self X (z + 1))
  have hdiv : X / (z + 1) + 1 ≤ X / z :=
    (Nat.le_div_iff_mul_le (by omega : 0 < z)).2 htoX
  simpa [squareRootReplacementFibreLower,
    squareRootReplacementFibreUpper, X] using hdiv

/-- The physical reciprocal fibre is exactly its ordinary hyperbola interval. -/
theorem replacementTailFibre_mem_iff
    (R z n : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    (n ∈ Finset.Icc R (squareRootEndpoint R) ∧
        squareRootEndpoint R / n = z) ↔
      n ∈ Finset.Icc
        (squareRootReplacementFibreLower R z)
        (squareRootReplacementFibreUpper R z) := by
  have hroot := squareRoot_root_le_replacementFibreLower R z hR hzR
  constructor
  · rintro ⟨hnTail, hdiv⟩
    rcases Finset.mem_Icc.mp hnTail with ⟨hnR, _hnX⟩
    have hn1 : 1 ≤ n := by omega
    rcases (nat_div_eq_iff_reciprocal_interval hn1 hz).1 hdiv with
      ⟨hlower, hupper⟩
    apply Finset.mem_Icc.mpr
    constructor
    · unfold squareRootReplacementFibreLower
      omega
    · exact hupper
  · intro hnFiber
    rcases Finset.mem_Icc.mp hnFiber with ⟨hnLower, hnUpper⟩
    have hnR : R ≤ n := hroot.trans hnLower
    have hn1 : 1 ≤ n := by omega
    have hupperX :
        squareRootReplacementFibreUpper R z ≤ squareRootEndpoint R := by
      unfold squareRootReplacementFibreUpper
      exact Nat.div_le_self _ _
    have hnX : n ≤ squareRootEndpoint R := hnUpper.trans hupperX
    have hlower : squareRootEndpoint R / (z + 1) < n := by
      unfold squareRootReplacementFibreLower at hnLower
      omega
    have hdiv :=
      (nat_div_eq_iff_reciprocal_interval hn1 hz).2 ⟨hlower, hnUpper⟩
    exact ⟨Finset.mem_Icc.mpr ⟨hnR, hnX⟩, hdiv⟩

/-- The complementary fibre state is exactly the Mertens increment on its
reciprocal hyperbola interval. -/
theorem squareRootReplacementTailMoebiusCoefficient_eq_mertensIncrement
    (R z : ℕ) (hR : 2 ≤ R) (hz : 1 ≤ z) (hzR : z < R) :
    squareRootReplacementTailMoebiusCoefficient R z =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R / z) -
        RHLean.Analysis.mertensSummatory (squareRootEndpoint R / (z + 1)) := by
  classical
  let L := squareRootReplacementFibreLower R z
  let H := squareRootReplacementFibreUpper R z
  have hLH : L ≤ H := by
    dsimp [L, H]
    exact squareRoot_replacementFibreLower_le_upper R z hR hz hzR
  have hset :
      (Finset.Icc R (squareRootEndpoint R)).filter
          (fun n => squareRootEndpoint R / n = z) =
        Finset.Icc L H := by
    ext n
    simp only [Finset.mem_filter]
    rw [replacementTailFibre_mem_iff R z n hR hz hzR]
  have hdisj : Disjoint (Finset.Icc 1 (L - 1)) (Finset.Icc L H) := by
    rw [Finset.disjoint_left]
    intro n hnlo hnhi
    simp only [Finset.mem_Icc] at hnlo hnhi
    omega
  have hprefix : Finset.Icc 1 H =
      Finset.Icc 1 (L - 1) ∪ Finset.Icc L H := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hM :
      RHLean.Analysis.mertensSummatory H =
        RHLean.Analysis.mertensSummatory (L - 1) +
          ∑ n ∈ Finset.Icc L H, (((μ n : ℤ) : ℂ)) := by
    calc
      RHLean.Analysis.mertensSummatory H =
          ∑ n ∈ Finset.Icc 1 H, (((μ n : ℤ) : ℂ)) :=
        RHLean.Analysis.mertensSummatory_eq_sum_Icc _
      _ = (∑ n ∈ Finset.Icc 1 (L - 1), (((μ n : ℤ) : ℂ))) +
          ∑ n ∈ Finset.Icc L H, (((μ n : ℤ) : ℂ)) := by
            rw [hprefix, Finset.sum_union hdisj]
      _ = RHLean.Analysis.mertensSummatory (L - 1) +
          ∑ n ∈ Finset.Icc L H, (((μ n : ℤ) : ℂ)) := by
            rw [← RHLean.Analysis.mertensSummatory_eq_sum_Icc (L - 1)]
  unfold squareRootReplacementTailMoebiusCoefficient
  rw [← Finset.sum_filter, hset]
  have hsum :
      (∑ n ∈ Finset.Icc L H, (((μ n : ℤ) : ℂ))) =
        RHLean.Analysis.mertensSummatory H -
          RHLean.Analysis.mertensSummatory (L - 1) := by
    rw [hM]
    ring
  rw [hsum]
  dsimp [L, H]
  simp [squareRootReplacementFibreLower,
    squareRootReplacementFibreUpper]

/-- Summing the fibre state recovers exactly the ordinary complementary Mertens
tail.  This is a partition identity and carries no additional analytic saving. -/
theorem squareRootReplacementTailMoebius_sum_eq_complementaryMertensTail
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z) =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
        RHLean.Analysis.mertensSummatory (R - 1) :=
  sum_squareRootReplacementTailMoebiusCoefficient_eq_mertens_sub_pred R hR

/-- The composed dictionary-renewal endpoint reconstruction reduces to the
preceding complementary-tail partition.  The displayed endpoint equality is
therefore a consistency corollary, not a separate cancellation theorem. -/
theorem replacementDictionaryRenewal_reduces_to_tailPartition
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1 =
      (RHLean.Analysis.mertensSummatory (R - 1) - 1) +
        ∑ z ∈ Finset.range R,
          squareRootReplacementTailMoebiusCoefficient R z := by
  rw [squareRootReplacementTailMoebius_sum_eq_complementaryMertensTail R hR]
  ring

end RHLean.Proof
