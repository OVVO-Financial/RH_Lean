import RHLean.Geometry.NativeThetaNonzeroSection

/-!
# Existing native lattice and theta constructors at the square-clock sizes

For `x = R^2 - 1`, the choices `m = R` and `k = x*R` are natural numbers
and satisfy the original geometric requirement `m+3 <= k`.  The prescribed
lattice has measured rank `R^3-1` over the actual ring of integers and
`(R^3-1)*(4*2^e)` over the integers.

One half-different is selected by the existing theta constructor on the
same `PageN` exponent and selected `WinPair`.  All rank calculations and
every theta section use that SAME ideal.  Its coprimality and Galois
invariance, and the original nonvanishing, automorphy, and invariant fiber
metric conclusions, are retained.  The ranks are consequences of the
literal inverse-ideal lattice and localization theorems, not assigned
fields in a new bundle.

This realizes the base lattice and analytic theta sections at the chosen
parameters.  It does not construct top/thick sets, localized measured
heights, integral section recovery, Petersson masses, or the physical
gain and global capacity estimates.
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

/-- The native square endpoint is already in the positive geometric scale
range as soon as `R >= 2`. -/
theorem nativeSquareHost_scale_ge_three (R : ℕ) (hR : 2 ≤ R) :
    (3 : ℝ) ≤ ((R ^ 2 - 1 : ℕ) : ℝ) := by
  have hs : 4 ≤ R ^ 2 := by nlinarith
  exact_mod_cast (show 3 ≤ R ^ 2 - 1 by omega)

/-- The explicit integer parameters satisfy the original prescribed-space
constructor's size condition. -/
theorem nativeSquareHost_chain_size (R : ℕ) (hR : 2 ≤ R) :
    R + 3 ≤ (R ^ 2 - 1) * R := by
  have hs : 4 ≤ R ^ 2 := by nlinarith
  have hN : 3 ≤ R ^ 2 - 1 := by omega
  have hm := Nat.mul_le_mul_right R hN
  nlinarith

/-- Exact dimension of the original prescribed lattice at `m=R`, `k=xR`. -/
theorem nativeSquareHost_chain_dimension (R : ℕ) (hR : 2 ≤ R) :
    (R ^ 2 - 1) * R + R - 1 = R ^ 3 - 1 := by
  have hs : 1 ≤ R ^ 2 := by nlinarith
  have hsum : (R ^ 2 - 1) * R + R = R ^ 3 := by
    calc
      (R ^ 2 - 1) * R + R = ((R ^ 2 - 1) + 1) * R := by ring
      _ = R ^ 2 * R := by rw [Nat.sub_add_cancel hs]
      _ = R ^ 3 := by ring
  rw [hsum]

/-- Construct the existing prescribed lattice and nonzero analytic theta
sections on the SAME selected pair and dyadic exponent, at `m=R`, `k=xR`.
The measured ranks and all original theta conclusions use one ideal `B`.
No recovery, norm-budget, or physical signed-source bound is assumed. -/
theorem nativeSquareHost_exists_lattice_theta
    (R e q d : ℕ) (hR : 2 ≤ R) (ε Y : ℝ) (hε : 0 < ε)
    (hPage : UpperTheory.Top.PageN ε ((R ^ 2 - 1 : ℕ) : ℝ) e)
    (hPair : UpperTheory.Top.WinPair ε Y q d) :
    letI : Fact q.Prime := ⟨hPair.q_prime⟩
    letI : Fact d.Prime := ⟨hPair.d_prime⟩
    let he : 2 ≤ e := nativeDyadicPageN_two_le hε
      ((show (2 : ℝ) ≤ 3 by norm_num).trans (nativeSquareHost_scale_ge_three R hR)) hPage
    let hH := nativeDyadicHostHyp_of_winPair hPair
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let k := (R ^ 2 - 1) * R
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E,
        H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      Module.finrank (𝓞 H.E) (prescribedLattice H.toHostRaw B k R) = R ^ 3 - 1 ∧
      Module.finrank ℤ (prescribedLattice H.toHostRaw B k R) =
        (R ^ 3 - 1) * (4 * 2 ^ e) ∧
      ∀ j : ℕ, 1 ≤ j → ∀ hj : j ≤ R,
        let hk := nativeSquareHost_chain_size R hR
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
  letI : Fact q.Prime := ⟨hPair.q_prime⟩
  letI : Fact d.Prime := ⟨hPair.d_prime⟩
  let he : 2 ≤ e := nativeDyadicPageN_two_le hε
    ((show (2 : ℝ) ≤ 3 by norm_num).trans (nativeSquareHost_scale_ge_three R hR)) hPage
  let hH := nativeDyadicHostHyp_of_winPair hPair
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let k := (R ^ 2 - 1) * R
  obtain ⟨B, hB, hcop, hinv, htheta⟩ :=
    nativeDyadicHost_exists_nonzeroThetaSections e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_, ?_, ?_⟩
  · change Module.finrank (𝓞 H.E)
      (twistedLattice H.toHostRaw B (k + R - 1)) = R ^ 3 - 1
    rw [twistedLattice_rank H.toHostRaw B hB]
    exact nativeSquareHost_chain_dimension R hR
  · change Module.finrank ℤ (twistedLattice H.toHostRaw B (k + R - 1)) =
      (R ^ 3 - 1) * (4 * 2 ^ e)
    rw [twistedLattice_rank_int H.toHostRaw B hB]
    have hdeg : Module.finrank ℚ H.E = 4 * 2 ^ e := by
      change Module.finrank ℚ (nativeDyadicHostRaw e q d he hH).E = 4 * 2 ^ e
      rw [nativeDyadicHostRaw_finrank_E, nativeDyadicFrame_ord]
    rw [hdeg]
    exact congrArg (fun z : ℕ => z * (4 * 2 ^ e))
      (nativeSquareHost_chain_dimension R hR)
  · intro j hj1 hj
    exact htheta k R (nativeSquareHost_chain_size R hR) j hj1 hj

end RHLean.Analysis.AlpogeThin

end
