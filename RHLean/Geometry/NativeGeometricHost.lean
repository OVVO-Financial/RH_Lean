import RHLean.Analysis.AlpogeNativeIntegralQuadraticRoot
import RHLean.Analysis.AlpogeNativeCMUnramified
import RHLean.Geometry.NativeHostThetaPolynomial

/-!
# The actual geometric host on the native CM field

This reconstructs the complete arithmetic `Geo.Tor.Host` record, including
the actual integral root, integral half-root, CM involution and unramified
extension over the maximal real subfield. Its complex root is the very same
one used to define the positive embedding rows of the native theta polynomial.
No field, root, integral element, involution or unramifiedness is assumed.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/`
`ToroidalCompactification/TwoWeightEqOneAddRoot.lean`,
`ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host`.
The record below retains every original field and its type. The source's
semiabelian schemes, polarization datum, levels and moduli are not part of
this arithmetic record and remain separate constructions.

The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

open NumberField

namespace RHLean.Geometry

open RHLean.Analysis

/-- The exact arithmetic fields of the original `Geo.Tor.Host` interface. -/
structure NativeGeometricHost (E : Type) [Field E] [NumberField E] [IsCMField E] where
  d : ℕ
  d_mod : d % 16 = 7
  d_prime : d.Prime
  rt : 𝓞 E
  rt_sq : rt ^ 2 = -(d : 𝓞 E)
  w0 : 𝓞 E
  two_weight_eq_one_add_root : 2 * w0 = 1 + rt
  bar : 𝓞 E ≃+* 𝓞 E
  bar_eq : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)
  unram : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)
  rt0 : ℂ
  sqrt_neg_disc_sq : rt0 ^ 2 = -(d : ℂ)

/-- The original root-selected complex signature of the geometric host. -/
def NativeGeometricHost.InPsi {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : NativeGeometricHost E) (τ : E →+* ℂ) : Prop :=
  τ (H.rt : E) = H.rt0

/-- The CM instance is supplied by the same actual native field construction. -/
theorem nativeDyadicGeometricCM
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hqd : q ≠ d) (hq4 : q % 4 = 3) (hd16 : d % 16 = 7) :
    IsCMField (alpogeNativeHostField e q d) :=
  alpogeNativeHostField_isCMField e q d (by omega) (by omega) hqd hq4 (by omega)

/-- Construct all fields of the original geometric host from the actual
native CM field and the original prime congruences. The complex root is
chosen once by `nativeDyadicThetaEmbedding`, preserving the theta signature. -/
def nativeDyadicGeometricHost
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hqd : q ≠ d) (hq4 : q % 4 = 3) (hd16 : d % 16 = 7) :
    let _ : IsCMField (alpogeNativeHostField e q d) :=
      nativeDyadicGeometricCM e q d hqd hq4 hd16
    NativeGeometricHost (alpogeNativeHostField e q d) := by
  let _ : IsCMField (alpogeNativeHostField e q d) :=
    nativeDyadicGeometricCM e q d hqd hq4 hd16
  have hd4 : d % 4 = 3 := by omega
  exact
    { d := d
      d_mod := hd16
      d_prime := Fact.out
      rt := alpogeNativeIntegralSqrtD e q d hd4
      rt_sq := alpogeNativeIntegralSqrtD_sq e q d hd4
      w0 := alpogeNativeIntegralHalfRoot e q d hd4
      two_weight_eq_one_add_root := alpogeNativeIntegralHalfRoot_two_mul e q d hd4
      bar := alpogeNativeIntegralBar e q d
      bar_eq := alpogeNativeIntegralBar_eq_complexConj e q d
      unram := alpogeNativeHostField_unramified e q d (by omega) (by omega) hqd hq4 hd4
      rt0 := nativeDyadicThetaEmbedding e q d (alpogeNativeSqrtD e q d)
      sqrt_neg_disc_sq := by
        rw [← map_pow, alpogeNativeSqrtD_sq e q d hd4, map_neg, map_natCast] }

/-- The constructed geometric host uses exactly the same signature as the
already constructed harmonic polynomial; no conjugate-signature transport
or independently chosen complex root is needed. -/
theorem nativeDyadicGeometricHost_inPsi
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hqd : q ≠ d) (hq4 : q % 4 = 3) (hd16 : d % 16 = 7)
    (τ : alpogeNativeHostField e q d →+* ℂ) :
    let _ : IsCMField (alpogeNativeHostField e q d) :=
      nativeDyadicGeometricCM e q d hqd hq4 hd16
    (nativeDyadicGeometricHost e q d hqd hq4 hd16).InPsi τ ↔
      nativeDyadicThetaPositive e q d τ := by
  rfl

/-- The chosen half-root and actual integral conjugation satisfy the
polarization identity on the complete constructed geometric host. -/
theorem nativeDyadicGeometricHost_weight_add_bar
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hqd : q ≠ d) (hq4 : q % 4 = 3) (hd16 : d % 16 = 7) :
    let _ : IsCMField (alpogeNativeHostField e q d) :=
      nativeDyadicGeometricCM e q d hqd hq4 hd16
    let H := nativeDyadicGeometricHost e q d hqd hq4 hd16
    H.w0 + H.bar H.w0 = 1 := by
  exact alpogeNativeIntegralHalfRoot_add_bar e q d (by omega) (by omega) hqd hq4 (by omega)

end RHLean.Geometry

end
