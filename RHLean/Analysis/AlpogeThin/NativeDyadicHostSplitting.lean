import RHLean.Analysis.AlpogeNativeQuadraticSplitting
import RHLean.Analysis.AlpogeThin.NativeDyadicHostRaw

/-!
# The quadratic splitting criterion on the SAME native host

The quadratic subfield is the literal `HostRaw.K = ℚ(sqd)` inside the actual
native fixed field, and `sqd` is its constructed d-Gauss root. The original
prime-count splitting criterion and ramified-prime count follow from the
actual quadratic supplier with no splitting or different-field premise.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/KcBase.lean`, `Der.splitK`, and
`src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/SplitK.lean`,
`{finrank_K,quad_K,ram_ncard}`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open NumberField IntermediateField Ideal

noncomputable section

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

/-- The actual generated quadratic subfield has rational degree two. -/
theorem nativeDyadicHostRaw_finrank_K
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    Module.finrank ℚ (nativeDyadicHostRaw e q d he hH).K = 2 := by
  let H := nativeDyadicHostRaw e q d he hH
  exact NativeQuadraticSplitting.finrank_K H.hyp.2.1.pos H.sqd_sq

theorem nativeDyadicHostRaw_quad_K
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    Algebra.IsQuadraticExtension ℚ (nativeDyadicHostRaw e q d he hH).K := by
  let H := nativeDyadicHostRaw e q d he hH
  exact NativeQuadraticSplitting.quad_K H.hyp.2.1.pos H.sqd_sq

/-- The exact original HostDer splitK clause for the same native subfield. -/
theorem nativeDyadicHostRaw_splitK
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ p : ℕ, p.Prime →
      ((primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 ↔
        (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1))) := by
  intro H p hp
  exact NativeQuadraticSplitting.clause H.hyp.2.1
    (by have := H.hyp.2.2.2.1; omega) H.sqd_sq p hp

/-- The same generated subfield has a single prime above d. -/
theorem nativeDyadicHostRaw_K_ram_ncard
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    (primesOver (span {(H.d : ℤ)}) (𝓞 H.K)).ncard = 1 := by
  let H := nativeDyadicHostRaw e q d he hH
  exact NativeQuadraticSplitting.ram_ncard H.hyp.2.1 H.sqd_sq

end RHLean.Analysis.AlpogeThin

end
