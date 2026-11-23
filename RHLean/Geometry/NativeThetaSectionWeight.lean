import RHLean.Geometry.NativeThetaSectionRealization
import RHLean.Geometry.NativeThetaJetFrame

/-!
# Triangular weight of the constructed native theta values

Both values below are the actual values constructed by effective faithfully
flat descent in NativeThetaSectionRealization. The frame coefficients lie
in the original base ring and are mapped into the same cover. Faithfulness
then transfers the proved formal-jet triangular identity back to those
values. The finite phase transitions are retained for both frames; no
weight conclusion or alternative value is supplied as a hypothesis.

This composes the native reconstructions of Alpöge's
`ShortThetaValueExistsUniqueNaturalOfLaws.lean` and
`InvariantOperatorValueTriangularChange.lean` at source
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The actual geometric chart, cover and germ instantiations, integrality,
cusp property and measured norm estimate remain separate requirements.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeTheta.SectionRealization

open JetEvaluation FormalCalculus

variable {T K S B Q J : Type} [Fintype T] [Field K] [Infinite K]
  [CommRing S] [CommRing B] [Algebra K S] [Algebra K B] [Algebra ℚ B]
  [Fintype Q] [Fintype J] {r : T → ℕ} {n d : ℕ}

/-- The native descended values carry the triangular weight of the same
harmonic polynomial, with coefficients in their original base ring. -/
theorem value_triangular
    (φ : S →ₐ[K] B) (hφ : φ.toRingHom.FaithfullyFlat)
    (β : K) (index N : ℕ) (w : Q → K) (hN : Odd N)
    (G : FormalGroup B d) (actW0 : Fin d → Series B 1 d) (h : Series B 2 d)
    (u u' : Row T r → Fin d → B)
    (germ : Q → J → Fin n → Series B 1 d)
    (hphase : ∀ (A : Type) [CommRing A] [Algebra K A] (ψ₁ ψ₂ : B →ₐ[K] A),
      ψ₁.comp φ = ψ₂.comp φ → PhaseTransport N ψ₁ ψ₂
        (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u)
        (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u))
    (hphase' : ∀ (A : Type) [CommRing A] [Algebra K A] (ψ₁ ψ₂ : B →ₐ[K] A),
      ψ₁.comp φ = ψ₂.comp φ → PhaseTransport N ψ₁ ψ₂
        (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u')
        (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u'))
    (cf : ∀ τ, Fin (r τ) → Fin (r τ) → S)
    (hcf : ∀ τ i j, i < j → cf τ i j = 0)
    (huu : ∀ τ i e, u' ⟨τ, i⟩ e = ∑ j, φ (cf τ i j) * u ⟨τ, j⟩ e)
    (hu : ∀ τ i, IsUnit (cf τ i i))
    (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) K) (hP : P ∈ HHa r n K cc isX a) :
    value φ hφ β index N w
        (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u')
        hN hphase' P =
      (∏ l : Row T r, cf l.1 l.2 l.2 ^ a l.1 l.2) *
        value φ hφ β index N w
          (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u)
          hN hphase P := by
  classical
  apply hφ.injective
  rw [map_mul, value_spec, value_spec]
  change shortValueOfFormalGerms β index N w G.F actW0 h u' germ P =
    φ (∏ l : Row T r, cf l.1 l.2 l.2 ^ a l.1 l.2) *
      shortValueOfFormalGerms β index N w G.F actW0 h u germ P
  simpa only [map_prod, map_pow] using
    JetFrame.shortValueOfFormalGerms_triangular β index N w G actW0 h u u' germ
      (fun τ i j => φ (cf τ i j))
      (fun τ i j hij => by simp [hcf τ i j hij]) huu
      (fun τ i => (hu τ i).map φ) cc isX a P hP

end RHLean.Geometry.NativeTheta.SectionRealization

end
