import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»

/-!
# Exact sharp rational shell to native deleted-norm convolution

The shell source is the TRUE integer Mobius on R^2 <= n < (R+1)^2.
Its sharp weight has bounded finite support, so the EXISTING native
vf919WeightedMobius_eq_excludedNormKernel theorem gives a fully exact
finite arithmetic expansion with the same physical site multiplicities.

This does not identify the constructed rational coefficients
vf919ExcludedNormCoefficients with actual Eisenstein ideal Mobius
norm-fibres. It does not estimate the resulting sums, discard
large-character divisors, invoke complete-residue orthogonality on
an incomplete annulus, or claim any uniform 7/8 bound.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Indicator of the exact half-open native shell [R^2,(R+1)^2). -/
def vf919NativeSquareShellSharpWeight (R n : ℕ) : ℂ :=
  if R ^ 2 ≤ n ∧ n < (R + 1) ^ 2 then 1 else 0

/-- The true shell source is supported below its actual upper endpoint.
There are no smooth-edge or Gaussian approximation errors here. -/
theorem vf919NativeSquareShellSharpWeight_supported (R n : ℕ)
    (hn : (R + 1) ^ 2 - 1 < n) :
    vf919NativeSquareShellSharpWeight R n = 0 := by
  unfold vf919NativeSquareShellSharpWeight
  have hnot : ¬ (R ^ 2 ≤ n ∧ n < (R + 1) ^ 2) := by
    intro h
    omega
  exact ite_eq_right hnot

/-- Fully exact native rational-to-constructed-norm coefficient identity
for the physical square shell. The weighted Mobius left-hand side is
the original sharp shell (not the Eisenstein integer-point count). -/
theorem vf919NativeSquareShell_exactExcludedNormExpansion
    (R : ℕ) (hR : 3 ≤ R) :
    (∑ n ∈ Finset.Icc 1 ((R + 1) ^ 2 - 1),
      (ArithmeticFunction.moebius n : ℂ) *
        vf919NativeSquareShellSharpWeight R n) =
      ∑ m ∈ Finset.Icc 1 ((R + 1) ^ 2 - 1),
        vf919ExcludedNormCoefficients m *
          vf919PhysicalHeckeKernel ((R + 1) ^ 2 - 1)
            (vf919NativeSquareShellSharpWeight R) m := by
  apply vf919WeightedMobius_eq_excludedNormKernel
  · have hlarge : 13 ≤ (R + 1) ^ 2 := by nlinarith
    omega
  · intro n hn
    exact vf919NativeSquareShellSharpWeight_supported R n hn

#print axioms vf919NativeSquareShellSharpWeight_supported
#print axioms vf919NativeSquareShell_exactExcludedNormExpansion

end RHLean.Analysis
