import RHLean.Geometry.NativeSquareHostRealization

/-!
# Actual base lattice and theta sections at the reduced square rank

The original native constructor works for every k with R+3 <= k. Apply it
to k=R^2 on the SAME PageN host and WinPair, using one half-different for all
theta sections. This realizes the actual rank R^2+R-1 rather than R^3-1.
The existing nonvanishing, positivity, automorphy, and fiber metric proofs
are retained without new geometric hypotheses.

This is a smaller actual base-space construction, not a proof of the
integral restriction/recovery gain, measured component mass or slope bound
at that rank. See AlpogeNativeQuadraticRecovery for the independent scalar
budget that permits the smaller k. No new geometric field is assigned an
arithmetic target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Pointwise

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC
open RHLean.Geometry RHLean.Geometry.NativeGeometricPeriods
open RHLean.Geometry.NativeTheta.AppellHumbert
open NativeRawHostPolarization

theorem nativeSquareReduced_chain_size (R : ℕ) (hR : 3 ≤ R) :
    R + 3 ≤ R ^ 2 := by
  calc
    R + 3 ≤ R + R := Nat.add_le_add_left hR R
    _ = 2 * R := by ring
    _ ≤ R * R := Nat.mul_le_mul_right R (by omega)
    _ = R ^ 2 := by ring

/-- Construct the actual reduced-rank base space and all its nonzero
theta sections on the original arithmetic host. -/
theorem nativeSquareHost_exists_lattice_theta_reduced
    (R e q d : ℕ) (hR : 3 ≤ R) (ε Y : ℝ) (hε : 0 < ε)
    (hPage : UpperTheory.Top.PageN ε ((R ^ 2 - 1 : ℕ) : ℝ) e)
    (hPair : UpperTheory.Top.WinPair ε Y q d) :
    letI : Fact q.Prime := ⟨hPair.q_prime⟩
    letI : Fact d.Prime := ⟨hPair.d_prime⟩
    let he : 2 ≤ e := nativeDyadicPageN_two_le hε
      ((show (2 : ℝ) ≤ 3 by norm_num).trans (nativeSquareHost_scale_ge_three R (by omega))) hPage
    let hH := nativeDyadicHostHyp_of_winPair hPair
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let k := R ^ 2
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E,
        H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      Module.finrank (𝓞 H.E) (prescribedLattice H.toHostRaw B k R) = R ^ 2 + R - 1 ∧
      Module.finrank ℤ (prescribedLattice H.toHostRaw B k R) =
        (R ^ 2 + R - 1) * (4 * 2 ^ e) ∧
      ∀ j : ℕ, 1 ≤ j → ∀ hj : j ≤ R,
        let hk := nativeSquareReduced_chain_size R hR
        let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k R j hk hj
        let P := prescribedPeriodMap H.toHostRaw B hB k R j
        ∃ Hm : Matrix (Fin ((cmTypeFinset H.toHostRaw).card * (k + R - 1)))
            (Fin ((cmTypeFinset H.toHostRaw).card * (k + R - 1))) ℂ,
          Hm.IsHermitian ∧ (∀ z, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
          (∀ v w, (hermForm Hm (P v) (P w)).im = D.EF v w) ∧
          ∃ θ : (Fin ((cmTypeFinset H.toHostRaw).card * (k + R - 1)) → ℂ) → ℂ,
            Differentiable ℂ θ ∧ θ ≠ 0 ∧
            (∀ v z, θ (z + P v) = factor D P Hm v z * θ z) ∧
            ∀ v z, fiberNormSq Hm (z + P v) (θ (z + P v)) =
              fiberNormSq Hm z (θ z) := by
  let _ : Fact q.Prime := ⟨hPair.q_prime⟩
  let _ : Fact d.Prime := ⟨hPair.d_prime⟩
  let he : 2 ≤ e := nativeDyadicPageN_two_le hε
    ((show (2 : ℝ) ≤ 3 by norm_num).trans (nativeSquareHost_scale_ge_three R (by omega))) hPage
  let hH := nativeDyadicHostHyp_of_winPair hPair
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let k := R ^ 2
  obtain ⟨B, hB, hcop, hinv, htheta⟩ :=
    nativeDyadicHost_exists_nonzeroThetaSections e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_, ?_, ?_⟩
  · change Module.finrank (𝓞 H.E)
      (twistedLattice H.toHostRaw B (k + R - 1)) = R ^ 2 + R - 1
    rw [twistedLattice_rank H.toHostRaw B hB] <;> rfl
  · change Module.finrank ℤ (twistedLattice H.toHostRaw B (k + R - 1)) =
      (R ^ 2 + R - 1) * (4 * 2 ^ e)
    rw [twistedLattice_rank_int H.toHostRaw B hB]
    have hdeg : Module.finrank ℚ H.E = 4 * 2 ^ e := by
      change Module.finrank ℚ (nativeDyadicHostRaw e q d he hH).E = 4 * 2 ^ e
      rw [nativeDyadicHostRaw_finrank_E, nativeDyadicFrame_ord]
    rw [hdeg] <;> rfl
  · intro j hj1 hj
    exact htheta k R (nativeSquareReduced_chain_size R hR) j hj1 hj


end RHLean.Analysis.AlpogeThin

end
