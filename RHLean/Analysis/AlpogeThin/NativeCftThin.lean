import RHLean.Analysis.AlpogeThin.NativePrincipalThin
import RHLean.Analysis.AlpogeCompletePrimitiveASK
import RHLean.Analysis.AlpogeNativeCompleteSourcePayment
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# The proved thin estimate on the complete native Frobenius/inertia source

`nativePrincipalSelectedPairThin` constructs the selected primes and proves the
analytic estimate for all primitive conductors dividing `2^k*q*d`. This file
attaches it to the original native modular-unit source, with its actual
primitive logarithmic derivative and every ramified prime power.

Surjectivity of the same modular-unit map supplies the missing principal
identification: the primitive Dirichlet character is principal exactly when
the additive host character is zero. Without this condition the two source
definitions have different principal branches.

The last theorem pays the literal finite thin return at its original widths.
The source estimate is supplied by the selected-pair theorem, not assumed.
The actual host/cover construction must still supply its onto unit map,
modulus bound and thin-width scale. No bound on geometric ASK-MAIN is asserted.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace RHLean.Analysis.AlpogeThin

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- An onto unit map detects every nonzero additive character. -/
theorem nativeDirChar_eq_one_iff
    {N : ℕ}
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (hr : Function.Surjective r)
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) :
    alpogeNativeDirChar r ψ = 1 ↔ ψ = 0 := by
  constructor
  · intro h
    ext g
    obtain ⟨u, hu⟩ := hr (Multiplicative.ofAdd g)
    have hv := DFunLike.congr_fun h (u : ZMod N)
    rw [alpogeNativeDirChar_unit, MulChar.one_apply (Units.isUnit u)] at hv
    simpa only [hu, toAdd_ofAdd, AddChar.zero_apply] using hv
  · intro h
    subst ψ
    apply MulChar.ext
    intro u
    rw [alpogeNativeDirChar_unit, AddChar.zero_apply,
      MulChar.one_apply (Units.isUnit u)]

private theorem primitive_eq_one_iff
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h,
      DirichletCharacter.changeLevel_one]
  · intro h
    subst χ
    exact DirichletCharacter.primitiveCharacter_one

/-- Conductor reduction preserves the exact principal-host identification. -/
theorem nativePrimitive_eq_one_iff
    {N : ℕ} [NeZero N]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (hr : Function.Surjective r)
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) :
    (alpogeNativeDirChar r ψ).primitiveCharacter = 1 ↔ ψ = 0 :=
  (primitive_eq_one_iff (alpogeNativeDirChar r ψ)).trans
    (nativeDirChar_eq_one_iff r hr ψ)

/-- Exact complete-response equality at every real argument. The principal
constant, the primitive log derivative and all ramified terms agree. -/
theorem nativeCftGPsi_eq_nativeResponse
    {N : ℕ} [NeZero N] (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (hr : Function.Surjective r)
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (y : ℝ) :
    letI : NeZero (alpogeNativeDirChar r ψ).conductor :=
      ⟨DirichletCharacter.conductor_ne_zero _⟩
    alpogeNativeFrobInertiaGPsi
        (alpogeNativeCftData N q d r).inertia
        (alpogeNativeCftData N q d r).frob
        (alpogeNativeCanonicalHostEll r) ψ y =
      nativeResponse (alpogeNativeDirChar r ψ).primitiveCharacter y := by
  letI : NeZero (alpogeNativeDirChar r ψ).conductor :=
    ⟨DirichletCharacter.conductor_ne_zero _⟩
  rw [alpogeNativeCftGPsi_eq_primitiveGPsi]
  unfold alpogeNativeRealizedPrimitiveGPsi nativeResponse
  by_cases hψ : ψ = 0
  · rw [ite_eq_left hψ, ite_eq_left ((nativePrimitive_eq_one_iff r hr ψ).2 hψ)]
  · rw [ite_eq_right hψ,
      ite_eq_right (fun h => hψ ((nativePrimitive_eq_one_iff r hr ψ).1 h))]
    rfl

/-- The selected pair pays every character of the same onto native host.
Conductor divisibility and the logarithmic conductor bound are derived from
the actual modulus; the caller does not choose a second character family. -/
theorem nativeSelectedCftThin
    (eps A : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) (hA : 1 ≤ A) :
    ∃ Y₀ x₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∃ q d : ℕ, UpperTheory.Top.PairGood 1 eps Y (Y ^ A) q d ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H]
            (k N : ℕ) [NeZero N],
          N ∣ 2 ^ k * q * d →
          Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 →
          ∀ r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H),
            Function.Surjective r →
            ∀ (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (y : ℝ),
              Real.exp (x ^ (eps / 3)) / 3 ≤ y →
              ‖alpogeNativeFrobInertiaGPsi
                  (alpogeNativeCftData N q d r).inertia
                  (alpogeNativeCftData N q d r).frob
                  (alpogeNativeCanonicalHostEll r) ψ y‖ ≤
                y * Real.exp (-(x ^ (eps / 8))) := by
  obtain ⟨Y₀, x₀, hpair⟩ := nativePrincipalSelectedPairThin eps A he he52 hA
  refine ⟨Y₀, x₀, fun Y hY => ?_⟩
  obtain ⟨q, d, hG, hthin⟩ := hpair Y hY
  refine ⟨q, d, hG, ?_⟩
  intro x hx H _ _ _ k N _ hN hlog r hr ψ y hy
  let χ := alpogeNativeDirChar r ψ
  letI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero _⟩
  have hcN : χ.conductor ∣ N := DirichletCharacter.conductor_dvd_level χ
  have hcpos : (0 : ℝ) < χ.conductor := by
    exact_mod_cast Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ)
  have hcle : (χ.conductor : ℝ) ≤ N := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos N) hcN
  have hclog : Real.log χ.conductor ≤
      2 * x ^ (eps / 5) * Real.log x ^ 2 :=
    (Real.log_le_log hcpos hcle).trans hlog
  rw [nativeCftGPsi_eq_nativeResponse q d r hr ψ y]
  exact hthin x hx k χ.conductor χ.primitiveCharacter
    (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (hcN.trans hN) hclog y hy

/-- Every original width cancels against its own thin-response argument.
The character count is the actual finite dual cardinal, not a multiplicity
inserted into the geometric source. -/
theorem nativeThinColourTerm_norm_le
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (a θ : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (g : AlpogeNativeE0 × H)
    (hw : 0 < w (alpogeNativePartner t g))
    (hF : ∀ ψ, ‖F ψ (a / w (alpogeNativePartner t g))‖ ≤
      (a / w (alpogeNativePartner t g)) * θ) :
    ‖alpogeNativeProjectionColourTerm F a t w g‖ ≤
      (4 * (Fintype.card H : ℝ)) * a * θ := by
  have hterm : ∀ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
      ‖ψ (-g) * ((w (alpogeNativePartner t g) : ℂ) *
        F ψ (a / w (alpogeNativePartner t g)))‖ ≤ a * θ := by
    intro ψ
    rw [norm_mul, AddChar.norm_apply, one_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
    calc
      w (alpogeNativePartner t g) *
          ‖F ψ (a / w (alpogeNativePartner t g))‖ ≤
        w (alpogeNativePartner t g) *
          ((a / w (alpogeNativePartner t g)) * θ) :=
        mul_le_mul_of_nonneg_left (hF ψ) hw.le
      _ = a * θ := by field_simp [hw.ne']; ring
  unfold alpogeNativeProjectionColourTerm
  calc
    ‖∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
        ψ (-g) * ((w (alpogeNativePartner t g) : ℂ) *
          F ψ (a / w (alpogeNativePartner t g)))‖ ≤
      ∑ _ψ : AddChar (AlpogeNativeE0 × H) ℂ, a * θ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun ψ _ => hterm ψ)
    _ = (4 * (Fintype.card H : ℝ)) * a * θ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        AddChar.card_eq, Fintype.card_prod]
      norm_num [AlpogeNativeE0, Nat.cast_mul] <;> ring

/-- Bound the literal complement, retaining its actual number of colours.
All characters and original widths occur in the source on the left. -/
theorem nativeThinReturn_norm_le
    (F : AddChar (AlpogeNativeE0 × H) ℂ → ℝ → ℂ)
    (T2 : Finset H) (a θ : ℝ) (u t : H)
    (w : AlpogeNativeE0 × H → ℝ)
    (hw : ∀ g ∈ (Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
          alpogeNativeProjectionThickColours T2 u t,
      0 < w (alpogeNativePartner t g))
    (hF : ∀ g ∈ (Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
          alpogeNativeProjectionThickColours T2 u t,
      ∀ ψ, ‖F ψ (a / w (alpogeNativePartner t g))‖ ≤
        (a / w (alpogeNativePartner t g)) * θ) :
    ‖alpogeNativeProjectionThinReturn F T2 a u t w‖ ≤
      (((Finset.univ.filter
          (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
            alpogeNativeProjectionThickColours T2 u t).card : ℝ) /
        (alpogeNativePhiSet H).card *
        ((4 * (Fintype.card H : ℝ)) * a * θ) := by
  unfold alpogeNativeProjectionThinReturn
  rw [norm_mul]
  have hn : ‖(1 / ((alpogeNativePhiSet H).card : ℂ))‖ =
      1 / ((alpogeNativePhiSet H).card : ℝ) := by simp
  rw [hn]
  calc
    _ ≤ (1 / ((alpogeNativePhiSet H).card : ℝ)) *
        ∑ _g ∈ (Finset.univ.filter
          (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
            alpogeNativeProjectionThickColours T2 u t,
          ((4 * (Fintype.card H : ℝ)) * a * θ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun g hg =>
        nativeThinColourTerm_norm_le F a θ t w g (hw g hg) (hF g hg))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- The original signed thin source is quantitatively paid on the selected
native host. The prime pair and analytic estimate are constructed together;
only the actual modulus, onto-map and thin-scale geometry remain to attach. -/
theorem nativeSelectedCftThinReturn
    (eps A : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) (hA : 1 ≤ A) :
    ∃ Y₀ x₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∃ q d : ℕ, UpperTheory.Top.PairGood 1 eps Y (Y ^ A) q d ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H]
            (k N : ℕ) [NeZero N],
          N ∣ 2 ^ k * q * d →
          Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 →
          ∀ r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H),
            Function.Surjective r →
            ∀ (T2 : Finset H) (a : ℝ) (u t : H)
              (w : AlpogeNativeE0 × H → ℝ),
              (∀ g ∈ (Finset.univ.filter
                  (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
                    alpogeNativeProjectionThickColours T2 u t,
                0 < w (alpogeNativePartner t g)) →
              (∀ g ∈ (Finset.univ.filter
                  (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
                    alpogeNativeProjectionThickColours T2 u t,
                Real.exp (x ^ (eps / 3)) / 3 ≤
                  a / w (alpogeNativePartner t g)) →
              ‖alpogeNativeProjectionThinReturn
                  (alpogeNativeFrobInertiaGPsi
                    (alpogeNativeCftData N q d r).inertia
                    (alpogeNativeCftData N q d r).frob
                    (alpogeNativeCanonicalHostEll r)) T2 a u t w‖ ≤
                (((Finset.univ.filter
                    (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
                      alpogeNativeProjectionThickColours T2 u t).card : ℝ) /
                  (alpogeNativePhiSet H).card *
                  ((4 * (Fintype.card H : ℝ)) * a *
                    Real.exp (-(x ^ (eps / 8)))) := by
  obtain ⟨Y₀, x₀, hpair⟩ := nativeSelectedCftThin eps A he he52 hA
  refine ⟨Y₀, x₀, fun Y hY => ?_⟩
  obtain ⟨q, d, hG, hthin⟩ := hpair Y hY
  refine ⟨q, d, hG, ?_⟩
  intro x hx H _ _ _ k N _ hN hlog r hr T2 a u t w hw hy
  exact nativeThinReturn_norm_le _ T2 a _ u t w hw
    (fun g hg ψ => hthin x hx H k N hN hlog r hr ψ
      (a / w (alpogeNativePartner t g)) (hy g hg))

/-- Explicit finite thin bill after every original width has cancelled. It
keeps the true colour counts, the subgroup average, all top heights and m rows.
It contains no response function, logarithmic derivative or unknown norm. -/
def nativeThinBill
    (A0 : AddSubgroup H) (TT T2 : Finset H) (m : ℕ)
    (a : H → ℝ) (θ : ℝ) : ℝ :=
  (1 / (Fintype.card A0 : ℝ)) * ∑ u : A0, ∑ t ∈ TT, ∑ _j : Fin m,
    (((Finset.univ.filter
        (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
          alpogeNativeProjectionThickColours T2 u t).card : ℝ) /
      (alpogeNativePhiSet H).card * ((4 * (Fintype.card H : ℝ)) * a t * θ)

/-- Direct attachment to the existing complete native source consumer.

The selected pair supplies the complete thin estimate; it is not a new input
bound. The only unevaluated source quantity on the right is the actual
geometric top excess. Its divisor Q, the common cutoff and the movement bill
are exactly those previously derived on this same source and same widths.
All selection thresholds precede the varying finite host, modulus and cover.
-/
theorem nativeSelectedCompleteProjection
    (eps A : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) (hA : 1 ≤ A) :
    ∃ Y₀ x₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∃ q d : ℕ, UpperTheory.Top.PairGood 1 eps Y (Y ^ A) q d ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ (H : Type*) [AddCommGroup H] [Fintype H] [DecidableEq H]
            (k N : ℕ) [NeZero N],
          N ∣ 2 ^ k * q * d →
          Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 →
          ∀ r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H),
            Function.Surjective r →
            ∀ (A0 : AddSubgroup H) (m : ℕ) (TT T2 : Finset H),
              TT.Nonempty → T2.Nonempty → 0 < m →
              (∀ s ∈ T2, s ∈ A0) →
              ∀ (a : H → ℝ) (b h Amax beta : ℝ)
                (w : H → Fin m → AlpogeNativeE0 × H → ℝ),
                0 < beta → beta ≤ b → 0 ≤ h →
                (∀ t ∈ TT, 0 < a t) → (∀ t ∈ TT, a t ≤ Amax) →
                (∀ u j ρ, alpogeNativeInPhi ρ → beta ≤ w u j ρ) →
                (∀ u j ρ, ρ ∈ alpogeNativeThickPositiveSites T2 u →
                  b ≤ w u j ρ ∧ w u j ρ ≤ b + h) →
                (∀ (u : A0) t, t ∈ TT → ∀ (j : Fin m) g,
                  g ∈ (Finset.univ.filter
                      (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g)) \
                        alpogeNativeProjectionThickColours T2 u t →
                    Real.exp (x ^ (eps / 3)) / 3 ≤
                      a t / w u j (alpogeNativePartner t g)) →
                alpogeNativeProjectedSignal A0
                    (alpogeNativeFrobInertiaGPsi
                      (alpogeNativeCftData N q d r).inertia
                      (alpogeNativeCftData N q d r).frob
                      (alpogeNativeCanonicalHostEll r)) TT a b ≤
                  (alpogeNativePhysicalSubgroupTopExcess A0
                      (alpogeNativeCftData N q d r).inertia
                      (alpogeNativeCftData N q d r).frob
                      (alpogeNativeCanonicalHostEll r)
                      (Nat.ceil (Amax / beta)) TT a w +
                    nativeThinBill A0 TT T2 m a
                      (Real.exp (-(x ^ (eps / 8))))) /
                    alpogeNativeProjectionDivisor TT T2 m b +
                    4 * h * (Real.log 4 + 2) * (Amax / b) /
                      (b * alpogeNativeProjectionDensity T2) := by
  obtain ⟨Y₀, x₀, hpair⟩ := nativeSelectedCftThinReturn eps A he he52 hA
  refine ⟨Y₀, x₀, fun Y hY => ?_⟩
  obtain ⟨q, d, hG, hthin⟩ := hpair Y hY
  refine ⟨q, d, hG, ?_⟩
  intro x hx H _ _ _ k N _ hN hlog r hr A0 m TT T2
    hTT hT2ne hm hT2 a b h Amax beta w hbeta hbetab hh ha haA hw hthick hscale
  let F := alpogeNativeFrobInertiaGPsi
    (alpogeNativeCftData N q d r).inertia
    (alpogeNativeCftData N q d r).frob (alpogeNativeCanonicalHostEll r)
  have hthinBill : |alpogeNativeProjectionThinAverage A0 F TT T2 a w| ≤
      nativeThinBill A0 TT T2 m a (Real.exp (-(x ^ (eps / 8)))) := by
    unfold alpogeNativeProjectionThinAverage nativeThinBill
    rw [abs_mul, abs_of_nonneg (by positivity :
      0 ≤ 1 / (Fintype.card A0 : ℝ))]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro u _hu
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro t ht
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro j _hj
    apply (Complex.abs_re_le_norm _).trans
    apply hthin x hx H k N hN hlog r hr T2 (a t) u t (w u j)
    · intro g hg
      apply hbeta.trans_le (hw u j _ _)
      exact alpogeNativeFreezing_partner_inPhi t g
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hg).1).2
    · exact hscale u t ht j
  have hbase := alpogeNativeCompleteProjection_at_constructed_cutoff A0
    (alpogeNativeCftData N q d r).inertia
    (alpogeNativeCftData N q d r).frob (alpogeNativeCanonicalHostEll r)
    TT T2 hTT hT2ne hm hT2 a b h Amax beta w hbeta hbetab hh ha haA hw hthick
  apply hbase.trans
  apply add_le_add_right
  apply div_le_div_of_nonneg_right
  · have hlow := (abs_le.mp hthinBill).1
    change -nativeThinBill A0 TT T2 m a (Real.exp (-(x ^ (eps / 8)))) ≤
      alpogeNativeProjectionThinAverage A0
        (alpogeNativeFrobInertiaGPsi
          (alpogeNativeCftData N q d r).inertia
          (alpogeNativeCftData N q d r).frob
          (alpogeNativeCanonicalHostEll r)) TT T2 a w at hlow
    linarith
  · exact (alpogeNativeProjectionDivisor_pos TT T2 hTT hT2ne m hm b
      (hbeta.trans_le hbetab)).le

end RHLean.Analysis.AlpogeThin
