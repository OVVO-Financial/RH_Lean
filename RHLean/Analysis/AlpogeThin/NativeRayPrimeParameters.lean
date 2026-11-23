import Mathlib

/-!
# Native modulus parameters for geometric norm-prime selection

This is the literal ModAt condition used in Alpöge's short-norm suppliers.
It records the discriminant, divisibility and modulus size regime; it contains
no prime-count or short-interval estimate.

Source guide: Levent Alpöge's archive at
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AutomorphicArithmetic/ShortNorms/ShortNorm.lean, ModAt.
The archive states no license; attribution assigns none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace RHLean.Analysis.AlpogeThin.NativeRay

def ModAt (x eps : ℝ) (N d : ℕ) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 100 ≤ d ∧ 0 < N ∧ d ∣ N ∧
    Real.log N ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2

end RHLean.Analysis.AlpogeThin.NativeRay
