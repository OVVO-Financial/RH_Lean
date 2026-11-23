import RHLean.Analysis.AlpogeThin.NativeRayLevelPrime
import RHLean.Analysis.AlpogeThin.NativeDyadicHostSplitting
import RHLean.Analysis.AlpogeThin.NativeDyadicRayNorm

/-!
# A level prime and its integral norm element in the actual native host

The level-prime estimate is instantiated in the literal quadratic subfield
H.K = ℚ(H.sqd) of the constructed dyadic host. Its root is the existing
NativeQuadraticSplitting.bK H.sqd, and its rational degree two is already
proved for that same host. The resulting prime is then fed to the actual
integral ray-norm construction in H.E.

The threshold is uniform before the host, modulus and short window are chosen.
The original modulus N * (g₁ * g₂)^2 is unchanged. In particular N may be the
actual host conductor alpogeNativeHostN e q d = H.condN. The ModAt premise
contains only the original discriminant and modulus size regime; neither
prime existence nor an integral norm element is an input.

Source guide: Levent Alpöge's archive, inspected pin
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AutomorphicArithmetic/ShortNorms/levelPrimeN.lean` and
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLevChOfLevelPrime.lean`,
the latter's passage from the chosen level prime to normOne_host.
The algebraic construction is the existing native NativeDyadicRayNorm proof.
No source compiled artifact or terminal RH theorem is imported.
The archive states no license; attribution assigns none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open Formalism.HermitianLattices.ZeroFreeRegionGL2 (IsNormOne)

/-- The original specified short window contains an actual level prime and
an integral ray-norm element in the same constructed host. The field, root,
degree and norm-element suppliers are proved native constructions. -/
theorem nativeDyadicHostRaw_levelPrime_rayNormElement :
    ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
      ∀ cs CY : ℝ, 0 < cs → 0 < CY →
        ∃ x₀ : ℝ, ∀ x ≥ x₀,
          ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
            (he : 2 ≤ e) (hH : HostHyp q d) (N g₁ g₂ m : ℕ),
            NativeRay.ModAt x eps N d →
            1 ≤ g₁ → 1 ≤ g₂ →
            Real.log g₁ ≤ CY * x ^ eps → Real.log g₂ ≤ CY * x ^ eps →
            x ^ ((1 : ℝ) / 3) ≤ m →
            ∀ V Ts : ℝ, 1 ≤ V → V ≤ x ^ (12 : ℝ) →
              0 < Ts → cs * m * x ^ eps ≤ Real.log Ts →
              let H := nativeDyadicHostRaw e q d he hH
              ∃ (T : ℕ) (π : 𝓞 H.E),
                T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ (1 + 1 / V) * Ts ∧
                IsNormOne d (N * (g₁ * g₂) ^ 2) T ∧
                (π : H.E) ∈ H.K ∧
                (π : H.E) * H.conj (π : H.E) = (T : H.E) ∧
                π - 1 ∈ Ideal.span {((N * (g₁ * g₂) ^ 2 : ℕ) : 𝓞 H.E)} ∧
                T % (N * (g₁ * g₂) ^ 2) = 1 % (N * (g₁ * g₂) ^ 2) := by
  intro eps heps heps1 cs CY hcs hCY
  obtain ⟨x₀, hlevel⟩ := NativeRay.LevelPrime.levelPrimeN eps heps heps1 cs CY hcs hCY
  refine ⟨x₀, ?_⟩
  intro x hx e q d _ _ he hH N g₁ g₂ m hMod hg₁ hg₂ hlog₁ hlog₂ hm V Ts hV hVx hTs hlogTs
  let H := nativeDyadicHostRaw e q d he hH
  let r : H.K := NativeQuadraticSplitting.bK H.sqd
  have hr : r ^ 2 = -(d : H.K) := NativeQuadraticSplitting.bK_sq H.sqd_sq
  have htwo : Module.finrank ℚ H.K = 2 := nativeDyadicHostRaw_finrank_K e q d he hH
  obtain ⟨T, hT, hlo, hhi, hnorm⟩ :=
    hlevel x hx H.K N d g₁ g₂ m r hr htwo hMod hg₁ hg₂ hlog₁ hlog₂ hm V Ts hV hVx hTs hlogTs
  obtain ⟨⟨π, hπK, hπnorm, hπray⟩, hcong⟩ :=
    nativeDyadicHostRaw_exists_rayNormElement e q d he hH (N * (g₁ * g₂) ^ 2) T hnorm
  exact ⟨T, π, hT, hlo, hhi, hnorm, hπK, hπnorm, hπray, hcong⟩

end RHLean.Analysis.AlpogeThin

end
