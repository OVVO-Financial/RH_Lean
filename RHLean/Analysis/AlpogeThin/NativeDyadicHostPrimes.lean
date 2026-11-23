import RHLean.Analysis.AlpogeNativeHostPrimes
import RHLean.Analysis.AlpogeThin.NativeDyadicHostRaw

/-!
# Prime-ideal fields of the constructed original raw host

The actual native fixed-field inertia and Frobenius theorems are transported
through the explicit native d,q to source q,d sign equivalence. They have
the original `HostDer.inertia`, `HostDer.frob_any` and `HostDer.unramEF`
signatures on the already constructed `nativeDyadicHostRaw`. No `HostDer`
record, prime-ideal matching hypothesis, or replacement field is assumed.

Source interface: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`ConjEMemHostFIff.lean`, `Formalism.HC.HostDer`, with the proved suppliers
from `InertiaGaloisSymmetry/{CycLift,RootEqOfSubMem,CycGrp}.lean`.
The remaining derived-host fields, including decomposition and discriminant
bounds, remain separate obligations. The source archive/mirror states no
license; this notice preserves attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

/-- The exact original inertia field of `HostDer` for the constructed raw host. -/
theorem nativeDyadicHostRaw_inertia
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime]
      [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔
        ∃ u : (ZMod H.condN)ˣ,
          (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  dsimp only
  intro l hl P hP hPl σ
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hnative := @alpogeNativeHostField_inertia_iff e q d _ _
    hq2 hd2 hqd l hl P hP hPl σ
  constructor
  · intro h
    obtain ⟨u, hu, hσ⟩ := hnative.mp h
    exact ⟨u, hu, congrArg (nativeDyadicFullHostEquiv e) hσ⟩
  · rintro ⟨u, hu, hσ⟩
    exact hnative.mpr
      ⟨u, hu, (nativeDyadicFullHostEquiv e).injective hσ⟩

/-- The exact original all-prime Frobenius field of `HostDer`, including
its ramified-prime congruence and full inertia coset. -/
theorem nativeDyadicHostRaw_frob_any
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime]
      [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      IsArithFrobAt ℤ σ P ↔
        ∃ u : (ZMod H.condN)ˣ,
          (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  dsimp only
  intro l hl P hP hPl σ
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hnative := @alpogeNativeHostField_frob_iff e q d _ _
    hq2 hd2 hqd l hl P hP hPl σ
  constructor
  · intro h
    obtain ⟨u, hu, hσ⟩ := hnative.mp h
    exact ⟨u, hu, congrArg (nativeDyadicFullHostEquiv e) hσ⟩
  · rintro ⟨u, hu, hσ⟩
    exact hnative.mpr
      ⟨u, hu, (nativeDyadicFullHostEquiv e).injective hσ⟩

/-- The raw-host conjugation is the same automorphism already constructed
by restriction of the cyclotomic exponent `-1`. -/
theorem nativeDyadicHostRaw_conj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    (nativeDyadicHostRaw e q d he hH).conj = alpogeNativeHostConj e q d := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  apply (nativeDyadicHostRaw e q d he hH).gal.injective
  rw [HostRaw.conj, MulEquiv.apply_symm_apply]
  change (nativeDyadicFrame e).cc = nativeDyadicFullHostEquiv e
    (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd (alpogeNativeHostConj e q d))
  rw [alpogeNativeHostGalEquiv_conj e q d hq2 hd2 hqd hq4 hd4,
    nativeDyadicFullHostEquiv_cconj]

/-- The exact original `unramEF` field of `HostDer`, proved for every
nonzero prime of the actual ring of integers. -/
theorem nativeDyadicHostRaw_unramEF
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 H.E, H.conj • x - x ∈ P := by
  dsimp only
  intro P hP hP0
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  rw [nativeDyadicHostRaw_conj e q d he hH]
  exact alpogeNativeHostConj_unramEF e q d hq2 hd2 hqd hq4 hd4 P hP hP0

end RHLean.Analysis.AlpogeThin

end
