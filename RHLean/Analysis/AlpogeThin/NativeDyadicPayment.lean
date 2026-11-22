import RHLean.Analysis.AlpogeThin.NativeCftThin
import RHLean.Analysis.AlpogeNativeDyadicHostSize

/-!
# Complete character payment on the constructed native dyadic host

The selected primes, the actual CRT reciprocity map, all its primitive
characters and the native physical source are now one dependent witness.
The finite host is the original full dyadic quotient for every exponent e.
There is no free onto map, abstract thin estimate or conductor-divisibility
premise in this application. The geometric top-excess estimate and genuine
conductor/width size regime remain the exact construction obligations.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin

/-- The normalized thin bill on the actual dyadic host, with its proved
cardinality substituted. The multiplicity has already cancelled against
the earned divisor; the dyadic size, selected density and actual mean
height remain explicit. -/
theorem nativeDyadicThinBill_div_projectionDivisor
    (e : ℕ) (A0 : AddSubgroup (AlpogeNativeDyadicH e))
    (TT T2 : Finset (AlpogeNativeDyadicH e)) (m : ℕ)
    (a : AlpogeNativeDyadicH e → ℝ) (b θ : ℝ)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m) (hb : 0 < b) :
    nativeThinBill A0 TT T2 m a θ / alpogeNativeProjectionDivisor TT T2 m b =
      (8 * (2 : ℝ) ^ e - 4 * T2.card) * θ *
        ((∑ t ∈ TT, a t) / TT.card) / (b * (T2.card / (2 : ℝ) ^ e)) := by
  rw [nativeThinBill_div_projectionDivisor A0 TT T2 m a b θ hTT hT2 hm hb]
  simp only [alpogeNativeProjectionDensity, alpogeNativeDyadicH_card,
    Nat.cast_pow, Nat.cast_ofNat]

/-- The complete same-host character-source inequality for the actual native
dyadic residue construction. Q and the cutoff are inherited unchanged from
the complete native comparison. The thin bill is entirely evaluated by
`nativeThinBill_eq` and `nativeThinBill_div_projectionDivisor`.

The geometric family must now prove only its actual size/width hypotheses
and bound the literal geometric top excess; this theorem assumes no bound on
that excess and does not conclude a critical-scale estimate.
-/
theorem nativeSelectedDyadicCompleteProjection
    (eps A : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) (hA : 1 ≤ A) :
    ∃ Y₀ x₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∃ (q d : ℕ) (hG : UpperTheory.Top.PairGood 1 eps Y (Y ^ A) q d),
        letI : Fact q.Prime := ⟨hG.pair.q_prime⟩
        letI : Fact d.Prime := ⟨hG.pair.d_prime⟩
        ∀ x : ℝ, x₀ ≤ x → ∀ e : ℕ,
          Real.log (alpogeNativeHostN e q d) ≤
            2 * x ^ (eps / 5) * Real.log x ^ 2 →
          let r := alpogeNativeRecMap e q d
          let D := alpogeNativeHostData e q d
          let ell := alpogeNativeCanonicalHostEll r
          ∀ (A0 : AddSubgroup (AlpogeNativeDyadicH e))
            (m : ℕ) (TT T2 : Finset (AlpogeNativeDyadicH e)),
            TT.Nonempty → T2.Nonempty → 0 < m →
            (∀ s ∈ T2, s ∈ A0) →
            ∀ (a : AlpogeNativeDyadicH e → ℝ) (b h Amax beta : ℝ)
              (w : AlpogeNativeDyadicH e → Fin m →
                AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
              0 < beta → beta ≤ b → 0 ≤ h →
              (∀ t ∈ TT, 0 < a t) → (∀ t ∈ TT, a t ≤ Amax) →
              (∀ u j ρ, alpogeNativeInPhi ρ → beta ≤ w u j ρ) →
              (∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
                b ≤ w u j ρ ∧ w u j ρ ≤ b + h) →
              (∀ (u : A0) t, t ∈ TT → ∀ (j : Fin m) g,
                g ∈ (Finset.univ.filter
                    (fun g : AlpogeNativeE0 × AlpogeNativeDyadicH e =>
                      ¬ alpogeNativeInPhi g)) \
                      alpogeNativeProjectionThickColours T2 u t →
                  Real.exp (x ^ (eps / 3)) / 3 ≤
                    a t / w u j (alpogeNativePartner t g)) →
              alpogeNativeProjectedSignal A0
                  (alpogeNativeFrobInertiaGPsi D.inertia D.frob ell) TT a b ≤
                (alpogeNativePhysicalSubgroupTopExcess A0 D.inertia D.frob ell
                    (Nat.ceil (Amax / beta)) TT a w +
                  nativeThinBill A0 TT T2 m a (Real.exp (-(x ^ (eps / 8))))) /
                  alpogeNativeProjectionDivisor TT T2 m b +
                  4 * h * (Real.log 4 + 2) * (Amax / b) /
                    (b * alpogeNativeProjectionDensity T2) := by
  obtain ⟨Y₀, x₀, hpair⟩ := nativeSelectedCompleteProjection eps A he he52 hA
  refine ⟨Y₀, x₀, fun Y hY => ?_⟩
  obtain ⟨q, d, hG, hpaid⟩ := hpair Y hY
  refine ⟨q, d, hG, ?_⟩
  let : Fact q.Prime := ⟨hG.pair.q_prime⟩
  let : Fact d.Prime := ⟨hG.pair.d_prime⟩
  intro x hx e hlog
  have hq2 : q ≠ 2 := by have := hG.pair.q_mod; omega
  have hd2 : d ≠ 2 := by have := hG.pair.d_mod; omega
  have hqd : q ≠ d := by
    have := hG.pair.q_mod
    have := hG.pair.d_mod
    omega
  dsimp only
  intro A0 m TT T2 hTT hT2 hm hsubset a b h Amax beta w
    hbeta hbetab hh ha hAmax hwbeta hwthick hwthin
  have hsource := hpaid x hx (AlpogeNativeDyadicH e) (e + 2)
    (alpogeNativeHostN e q d) (dvd_refl _) hlog (alpogeNativeRecMap e q d)
    (alpogeNativeRecMap_surjective e q d hq2 hd2 hqd)
    A0 m TT T2 hTT hT2 hm hsubset a b h Amax beta w
    hbeta hbetab hh ha hAmax hwbeta hwthick hwthin
  simpa only [alpogeNativeHostData] using hsource

end RHLean.Analysis.AlpogeThin
