import RHLean.Analysis.AlpogeThin.NativeRayHostLevelPrime
import RHLean.Analysis.AlpogeThin.NativeDyadicHostWindows

/-!
# Level primes at the actual selected dyadic-host conductor

The original PageN exponent and the SAME WinPair discharge ModAt for the
literal conductor alpogeNativeHostN e q d = H.condN. The discriminant lower
bound follows from the selected pair's own logarithmic lower window, and
the conductor estimate is the already proved native PageN estimate.

The level-prime theorem is then applied in that constructed host, with its
existing quadratic root and integral norm element. No field, discriminant,
conductor, prime-existence, or norm-element premise is added. The genuinely
geometric size conditions on g₁, g₂, m, V and Ts remain explicit.

Source guide: Levent Alpöge's archive at
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AutomorphicArithmetic/ShortNorms/ShortNorm.lean, ModAt;
src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean,
WinPair and PageN; and
src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLevChOfLevelPrime.lean.
This file composes the native reconstructed suppliers. No source compiled
artifact or terminal RH theorem is imported. The archive states no license;
attribution assigns none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField

namespace RHLean.Analysis.AlpogeThin

open Formalism.HermitianLattices.ZeroFreeRegionGL2 (IsNormOne)

/-- The selected prime pair itself supplies the native ray family's modest
discriminant cutoff. This fixed window threshold is uniform in eps. -/
theorem nativeWinPair_hundred_le_d
    {eps Y : ℝ} {q d : ℕ} (heps : 0 < eps)
    (hY : Real.exp 15 ≤ Y) (hpair : UpperTheory.Top.WinPair eps Y q d) :
    100 ≤ d := by
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 15)).trans hY
  have hlogY : 15 ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos 15) hY
    simpa only [Real.log_exp] using h
  have hpow : 1 ≤ Y ^ (eps / 5) := Real.one_le_rpow hY1 (by positivity)
  have hmul : Real.log Y ^ 2 ≤ Y ^ (eps / 5) * Real.log Y ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg _) hpow
  have hsq : 225 ≤ Real.log Y ^ 2 := by
    nlinarith [sq_nonneg (Real.log Y - 15)]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hpair.d_prime.pos
  have hlogd := Real.log_le_sub_one_of_pos hd0
  have hd100 : (100 : ℝ) ≤ d := by linarith [hpair.d_lo]
  exact_mod_cast hd100

/-- The literal selected host conductor satisfies every ModAt field. The
threshold is chosen before the selected primes and dyadic exponent. -/
theorem nativePageN_modAt_eventually
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1 / 52) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (Y : ℝ) (e q d : ℕ),
      Real.exp 15 ≤ Y → Y ≤ x →
      UpperTheory.Top.WinPair eps Y q d → UpperTheory.Top.PageN eps x e →
      NativeRay.ModAt x eps (alpogeNativeHostN e q d) d := by
  obtain ⟨x₀, hcond⟩ := nativePageN_conductor_eventually eps heps heps1
  refine ⟨x₀, fun x hx Y e q d hY hYx hpair hP => ?_⟩
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 15)).trans hY
  have hx0 : 0 ≤ x := (by linarith : (0 : ℝ) ≤ Y).trans hYx
  have hd4 : d % 4 = 3 := by have := hpair.d_mod; omega
  have hN : 0 < alpogeNativeHostN e q d := by
    unfold alpogeNativeHostN
    exact Nat.mul_pos (Nat.mul_pos (by positivity) hpair.q_prime.pos) hpair.d_prime.pos
  refine ⟨hpair.d_prime, hd4, nativeWinPair_hundred_le_d heps hY hpair,
    hN, alpogeNativeD_dvd_hostN e q d, ?_⟩
  calc
    Real.log (alpogeNativeHostN e q d : ℝ) ≤
        2 * x ^ (eps / 5) * Real.log x ^ 2 :=
      hcond x hx Y q d e hY1 hYx hpair hP
    _ ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2 := by
      nlinarith [mul_nonneg (Real.rpow_nonneg hx0 (eps / 5)) (sq_nonneg (Real.log x))]

/-- At the actual conductor of the SAME PageN/WinPair host, the specified
short window contains a level prime and its integral ray-norm element.
Both thresholds precede all selected host and geometric data. -/
theorem nativeSelectedDyadicHost_levelPrime_rayNormElement
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1 / 52)
    (cs CY : ℝ) (hcs : 0 < cs) (hCY : 0 < CY) :
    ∃ (x₀ : ℝ) (hx₀ : 2 ≤ x₀),
      ∀ (Y x : ℝ) (hx : x₀ ≤ x), Real.exp 15 ≤ Y → Y ≤ x →
        ∀ (e q d : ℕ) (hP : UpperTheory.Top.PageN eps x e)
          (hpair : UpperTheory.Top.WinPair eps Y q d) (g₁ g₂ m : ℕ),
          1 ≤ g₁ → 1 ≤ g₂ →
          Real.log g₁ ≤ CY * x ^ eps → Real.log g₂ ≤ CY * x ^ eps →
          x ^ ((1 : ℝ) / 3) ≤ m →
          ∀ V Ts : ℝ, 1 ≤ V → V ≤ x ^ (12 : ℝ) →
            0 < Ts → cs * m * x ^ eps ≤ Real.log Ts →
            let H := nativeDyadicHostRaw_of_pageN_winPair e heps (hx₀.trans hx) hP hpair
            ∃ (T : ℕ) (π : 𝓞 H.E),
              T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ (1 + 1 / V) * Ts ∧
              IsNormOne d (H.condN * (g₁ * g₂) ^ 2) T ∧
              (π : H.E) ∈ H.K ∧
              (π : H.E) * H.conj (π : H.E) = (T : H.E) ∧
              π - 1 ∈ Ideal.span {((H.condN * (g₁ * g₂) ^ 2 : ℕ) : 𝓞 H.E)} ∧
              T % (H.condN * (g₁ * g₂) ^ 2) = 1 % (H.condN * (g₁ * g₂) ^ 2) := by
  obtain ⟨xM, hmod⟩ := nativePageN_modAt_eventually eps heps heps1
  obtain ⟨xP, hprime⟩ :=
    nativeDyadicHostRaw_levelPrime_rayNormElement eps heps heps1 cs CY hcs hCY
  refine ⟨max (max xM xP) 2, le_max_right _ _, ?_⟩
  intro Y x hx hY hYx e q d hP hpair g₁ g₂ m hg₁ hg₂ hl₁ hl₂ hm V Ts hV hVx hTs hlTs
  have hxM : xM ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxP : xP ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
  let : Fact q.Prime := ⟨hpair.q_prime⟩
  let : Fact d.Prime := ⟨hpair.d_prime⟩
  exact hprime x hxP e q d (nativeDyadicPageN_two_le heps hx2 hP)
    (nativeDyadicHostHyp_of_winPair hpair) (alpogeNativeHostN e q d) g₁ g₂ m
    (hmod x hxM Y e q d hY hYx hpair hP) hg₁ hg₂ hl₁ hl₂ hm V Ts hV hVx hTs hlTs

end RHLean.Analysis.AlpogeThin

end
