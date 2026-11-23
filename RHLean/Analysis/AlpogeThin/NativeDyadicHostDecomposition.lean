import RHLean.Analysis.AlpogeNativePrimeDecomposition
import RHLean.Analysis.AlpogeThin.NativeDyadicHostPrimes

/-!
# The original decomposition field on the actual native raw host

The native prime stabilizer theorem is transported through the existing
d,q-to-q,d equivalence. It supplies exactly `HostDer.decomp`, on the SAME
field and conductor; no derived-host record or decomposition premise is
introduced.

Source interface: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`ConjEMemHostFIff.lean`, `HostDer.decomp`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

/-- The original all-prime decomposition field, including ramified primes. -/
theorem nativeDyadicHostRaw_decomp
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime]
      [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      σ ∈ MulAction.stabilizer _ P ↔
        ∃ (u : (ZMod H.condN)ˣ) (k : ℕ),
          (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧
          H.gal σ = H.art u := by
  dsimp only
  intro l hl P hP hPl σ
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hnative := @alpogeNativeHostField_decomp_iff e q d _ _
    hq2 hd2 hqd l hl P hP hPl σ
  constructor
  · intro h
    obtain ⟨u, k, hu, hσ⟩ := hnative.mp h
    exact ⟨u, k, hu, congrArg (nativeDyadicFullHostEquiv e) hσ⟩
  · rintro ⟨u, k, hu, hσ⟩
    exact hnative.mpr
      ⟨u, k, hu, (nativeDyadicFullHostEquiv e).injective hσ⟩

end RHLean.Analysis.AlpogeThin

end
