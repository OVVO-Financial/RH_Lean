import RHLean.Analysis.AlpogeThin.NativeDyadicThickCharacters

/-!
# The complete scalar source inequality on the constructed dyadic host

The same selected `PairGood` witness pays both the thin primitive responses
and the three nonprincipal thick characters. The complete physical top
excess, the earned divisor, the evaluated thin charge, and the freezing
charge are retained at the actual heights `a t / b`.

This is the native principal specialization of the character-payment step
in Levent Alpöge's (with Claude) `PrimitiveCosets/CoreGm.lean`, at source pin
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
It constructs no new bound on the physical top excess. Constructing the
compatible geometric witnesses and proving their complete normalized cost
small remains the precise open source obligation.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin

/-- The native scalar source inequality with every charge explicit. The
prime pair is selected once; the actual dyadic host, primitive character
payment and original Y-to-Y^A window use that same pair. The thin charge
has its proved host cardinality substituted, and no bound on either the
physical top excess or the final right-hand side is a premise. -/
theorem nativeSelectedDyadicGzPayment
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
          ∀ (m : ℕ) (TT T2 : Finset (AlpogeNativeDyadicH e)),
            TT.Nonempty → T2.Nonempty → 0 < m →
            ∀ (a : AlpogeNativeDyadicH e → ℝ) (b h Amax beta : ℝ)
              (w : AlpogeNativeDyadicH e → Fin m →
                AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ),
              0 < beta → beta ≤ b → 0 ≤ h →
              (∀ t ∈ TT, 0 < a t) → (∀ t ∈ TT, a t ≤ Amax) →
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
                (8 * (2 : ℝ) ^ e - 4 * T2.card) *
                  Real.exp (-(x ^ (eps / 8))) *
                  ((∑ t ∈ TT, a t) / TT.card) /
                    (b * (T2.card / (2 : ℝ) ^ e)) +
                4 * h * (Real.log 4 + 2) * (Amax / b) /
                  (b * alpogeNativeProjectionDensity T2) +
                (3 / (TT.card : ℝ)) * ∑ t ∈ TT,
                  (a t / b) ^ ((1 : ℝ) / 2 + eps / 2) := by
  obtain ⟨Y₀, x₀, hpair⟩ :=
    nativeSelectedDyadicCompleteProjection eps A he he52 hA
  refine ⟨Y₀, x₀, fun Y hY => ?_⟩
  obtain ⟨q, d, hG, hpaid⟩ := hpair Y hY
  refine ⟨q, d, hG, ?_⟩
  let : Fact q.Prime := ⟨hG.pair.q_prime⟩
  let : Fact d.Prime := ⟨hG.pair.d_prime⟩
  intro x hx e hlog
  dsimp only
  intro m TT T2 hTT hT2 hm a b h Amax beta w
    hbeta hbetab hh ha hAmax hwbeta hwthick hwthin hwindow
  have hb : 0 < b := hbeta.trans_le hbetab
  have hproj := hpaid x hx e hlog ⊤ m TT T2 hTT hT2 hm
    (fun _ _ => AddSubgroup.mem_top _) a b h Amax beta w
    hbeta hbetab hh ha hAmax hwbeta hwthick hwthin
  rw [add_div,
    nativeDyadicThinBill_div_projectionDivisor e ⊤ TT T2 m a b
      (Real.exp (-(x ^ (eps / 8)))) hTT hT2 hm hb] at hproj
  exact (nativePairGood_dyadicGz_average_le_projection e q d hG TT a b hwindow).trans
    (add_le_add hproj le_rfl)

end RHLean.Analysis.AlpogeThin
