import «research.SELBERG_MATCHED_PRODUCT_FACE»

open RHLean.Analysis
open scoped ArithmeticFunction.vonMangoldt BigOperators

example (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    (∑ n ∈ A, nativePNTSignedSecondSelbergKernel n * nativePNTError (N/n)) -
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N/a), if a*b ∈ A then
        Λ a * Λ b * nativePNTError ((N/a)/b) else 0) =
      -(∑ n ∈ A, Λ n * Real.log n * nativePNTError (N/n)) :=
  (selbergMatched_ordered N A hA).symm.trans (selbergMatched_eq_log N A)

example (N : ℕ) (p : ℕ) (hp : p.Prime) (hodd : 2 < p) :
    selbergMatchedMass N {2*p} = 0 := by
  simpa using selbergMatched_oddChildren N {p} (by simpa using And.intro hp hodd)

example (R : ℕ) (hR : 4 ≤ R) (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime ∧ 3*R ≤ 4*p ∧ p<R) :
    selbergMatchedMass (R^2-1) ((P ×ˢ P).image (fun z => z.1*z.2)) =
      ∑ p ∈ P, 2*(Real.log p)^2 := selbergMatched_schur R hR P hp

example (H : ℕ) (hH : 4 ≤ H) (P : ℕ → Finset ℕ)
    (hp : ∀ R ∈ Finset.Ico H (2*H), ∀ p ∈ P R, p.Prime ∧ 3*R ≤ 4*p ∧ p<R) :
    (∑ R ∈ Finset.Ico H (2*H), (max (selbergMatchedMass (R^2-1)
      ((P R ×ˢ P R).image (fun z => z.1*z.2)) / (Real.log ((R^2-1 : ℕ) : ℝ))^2) 0)^2) ≤
      (H : ℝ)^3 := selbergMatched_dyadic H hH P hp
