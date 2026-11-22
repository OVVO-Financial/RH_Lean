import RHLean.Analysis.AlpogeThin.NativeDyadicCostWindows
import RHLean.Analysis.AlpogeThin.NativeDyadicHostWindows

/-!
# The complete scalar estimate on the constructed arithmetic size family

The dyadic exponent is chosen once by the original `PageN` construction.
The selected prime pair is chosen once for its original window. Their SAME
actual reciprocity host satisfies `SizeN`, the polynomial host bound and
the conductor bound; the latter two are no longer premises of the scalar
consumer. The original size regime then pays all analytic remainders.

What remains is exactly the literal geometric top excess divided by the
earned signal divisor, together with the original height/width/density
conditions that the actual geometric family must realize. No bound on
that geometric quantity, or existence of such a geometric family, is
assumed to be proved by this construction.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin

/-- Construct the native arithmetic size family and pay its complete analytic
remainder. The scalar source uses the exact chosen host and selected pair. -/
theorem nativeConstructedDyadicGzPayment
    (eps A : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) (hA : 1 ≤ A) :
    ∃ (exponent : ℝ → ℕ) (Y₀ x₀ : ℝ),
      (∀ x : ℝ, x₀ ≤ x →
        UpperTheory.Top.PageN eps x (exponent x) ∧
        x ^ (2 + 8 * eps - eps / 100) ≤
            (Fintype.card (AlpogeNativeDyadicH (exponent x)) : ℝ) ∧
        (Fintype.card (AlpogeNativeDyadicH (exponent x)) : ℝ) ≤
            x ^ (2 + 8 * eps + eps / 100)) ∧
      ∀ Y : ℝ, Y₀ ≤ Y →
        ∃ (q d : ℕ) (hG : UpperTheory.Top.PairGood 1 eps Y (Y ^ A) q d),
          letI : Fact q.Prime := ⟨hG.pair.q_prime⟩
          letI : Fact d.Prime := ⟨hG.pair.d_prime⟩
          ∀ x : ℝ, x₀ ≤ x → Y ≤ x →
            let e := exponent x
            let r := alpogeNativeRecMap e q d
            let D := alpogeNativeHostData e q d
            let ell := alpogeNativeCanonicalHostEll r
            ∀ (m : ℕ) (TT T2 : Finset (AlpogeNativeDyadicH e)),
              TT.Nonempty → T2.Nonempty → 0 < m →
              ∀ (a : AlpogeNativeDyadicH e → ℝ) (b h Amax beta : ℝ)
                (w : AlpogeNativeDyadicH e → Fin m →
                  AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
                0 < beta → beta ≤ b → 0 ≤ h →
                Real.exp (x ^ eps) ≤ b → h ≤ Real.exp (x ^ (eps / 4)) + 1 →
                (∀ t ∈ TT, 0 < a t) → (∀ t ∈ TT, a t ≤ Amax) →
                Amax / b ≤ x + 1 →
                x ^ (-eps) ≤ alpogeNativeProjectionDensity T2 →
                (∀ u j ρ, alpogeNativeInPhi ρ → beta ≤ w u j ρ) →
                (∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
                  b ≤ w u j ρ ∧ w u j ρ ≤ b + h) →
                (∀ (u : (⊤ : AddSubgroup (AlpogeNativeDyadicH e))) t,
                  t ∈ TT → ∀ (j : Fin m) g,
                  g ∈ (Finset.univ.filter
                      (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
                        ¬ alpogeNativeInPhi g)) \
                        alpogeNativeProjectionThickColours T2 u t →
                    Real.exp (x ^ (eps / 3)) / 3 ≤
                      a t / w u j (alpogeNativePartner t g)) →
                (∀ t ∈ TT, a t / b ∈ Set.Icc Y (Y ^ A)) →
                (1 / (TT.card : ℝ)) * ∑ t ∈ TT,
                    alpogeNativeGzArithmetic (a t / b) ≤
                  alpogeNativePhysicalSubgroupTopExcess
                      (⊤ : AddSubgroup (AlpogeNativeDyadicH e))
                      D.inertia D.frob ell (Nat.ceil (Amax / beta)) TT a w /
                    alpogeNativeProjectionDivisor TT T2 m b +
                  x ^ ((1 : ℝ) / 2 + eps) := by
  obtain ⟨exponent, xH, hhost⟩ := nativeDyadicHost_windows eps he he52
  obtain ⟨Y₁, xS, hsource⟩ :=
    nativeSelectedDyadicGzPayment_of_size_regime eps A 3 he he52 hA
  refine ⟨exponent, max Y₁ 1, max xH xS, ?_, ?_⟩
  · intro x hx
    obtain ⟨hP, hlo, hup, _hn, _hcond⟩ :=
      hhost x ((le_max_left _ _).trans hx)
    exact ⟨hP, hlo, hup⟩
  · intro Y hY
    have hY1 : 1 ≤ Y := (le_max_right _ _).trans hY
    obtain ⟨q, d, hG, hpaid⟩ := hsource Y ((le_max_left _ _).trans hY)
    refine ⟨q, d, hG, ?_⟩
    let : Fact q.Prime := ⟨hG.pair.q_prime⟩
    let : Fact d.Prime := ⟨hG.pair.d_prime⟩
    intro x hx hYx
    obtain ⟨_hP, _hlo, _hup, hn, hcond⟩ :=
      hhost x ((le_max_left _ _).trans hx)
    have hn' : (2 : ℝ) ^ (exponent x) ≤ x ^ (3 : ℝ) := by
      simpa only [alpogeNativeDyadicH_card, Nat.cast_pow, Nat.cast_ofNat] using hn
    exact hpaid x ((le_max_right _ _).trans hx) (exponent x) hn'
      (hcond Y q d hY1 hYx hG.pair)

end RHLean.Analysis.AlpogeThin

end
