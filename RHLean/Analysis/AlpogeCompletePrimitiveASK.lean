import Mathlib
import RHLean.Analysis.AlpogePrimitiveDirichletFull

/-!
# COMPLETE physical ASK-MAIN = full primitive Dirichlet character source

This is the deepest exact arithmetic equivalence in Alpoge's analytic
construction. It does NOT assume a new character sum estimate:
all original signed coefficients, all inertia and ramified zero factors,
every Frobenius prime power, and all widths remain.

The source is the genuine cftData of a modular-unit r, rather than
an arbitrary pseudo-Frobenius field.
-/

noncomputable section
open Finset
namespace RHLean.Analysis

/-- The canonical Dirichlet side of the complete character source:
principal channel Gz, and for each nonprincipal ψ the *primitive*
Dirichlet χ induced by the actual modular-unit map. -/
def alpogeNativeRealizedPrimitiveGPsi
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (y : ℝ) : ℂ :=
  if ψ = 0 then (alpogeNativeGzArithmetic y : ℂ)
  else alpogeNativeRealizedGchi r ψ (ell ψ) y

/-- The entire Frobenius/inertia source is equal pointwise to the
Dirichlet source, including the *exceptional principal* channel. -/
theorem alpogeNativeCftGPsi_eq_primitiveGPsi
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) (y : ℝ) :
    alpogeNativeFrobInertiaGPsi
      (alpogeNativeCftData N q d r).inertia
      (alpogeNativeCftData N q d r).frob ell ψ y =
    alpogeNativeRealizedPrimitiveGPsi r ell ψ y := by
  classical
  by_cases hψ : ψ = 0
  · subst ψ
    rw [alpogeNativeFrobInertiaGPsi_principal]
    simp [alpogeNativeRealizedPrimitiveGPsi]
  · rw [alpogeNativeRealizedGPsi_eq_nativeGchi
        q d r ell ψ hψ y]
    simp [alpogeNativeRealizedPrimitiveGPsi, hψ]

/-- Full source in primitive Dirichlet coordinates; NO character is
discarded and no signed Frobenius/Schur return is separately bounded. -/
def alpogeNativeCompletePrimitiveDe
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) : ℂ := by
  classical
  exact (1 / ((alpogeNativePhiSet H).card : ℂ)) *
    ∑ g ∈ Finset.univ.filter
       (fun g : AlpogeNativeE0 × H => ¬ alpogeNativeInPhi g),
      ∑ ψ : AddChar (AlpogeNativeE0 × H) ℂ,
        starRingEnd ℂ (ψ g) *
        ((w (alpogeNativePartner t g) : ℝ) : ℂ) *
          alpogeNativeRealizedPrimitiveGPsi r ell ψ
            (a / w (alpogeNativePartner t g))

/-- The actual complete signed ASK complement is IDENTICALLY the
realized primitive-character De, even at every exceptional prime,
with exactly the original phase, width and sign. -/
theorem alpogeNativeCftDe_eq_completePrimitiveDe
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ) :
    alpogeNativeDe
      (alpogeNativeCftData N q d r).inertia
      (alpogeNativeCftData N q d r).frob ell a t w =
    alpogeNativeCompletePrimitiveDe r ell a t w := by
  unfold alpogeNativeDe alpogeNativeCompletePrimitiveDe
  congr 1
  apply Finset.sum_congr rfl
  intro g _hg
  apply Finset.sum_congr rfl
  intro ψ _hψ
  rw [alpogeNativeCftGPsi_eq_primitiveGPsi q d r ell ψ
    (a / w (alpogeNativePartner t g))]

/-- FULL physical ASK-MAIN, no principal or nonprincipal loss,
is exactly its primitive Dirichlet character signed De source.
Nothing analytic is postulated, and ALL original weights survive. -/
theorem alpogeNativeCftASK_sub_MAIN_eq_completePrimitiveDe
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ell : AddChar (AlpogeNativeE0 × H) ℂ → ℂ)
    (M : ℕ) (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hM : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (M : ℝ)) :
    alpogeNativeFullKernelASK
      (alpogeNativeCftData N q d r).inertia
      (alpogeNativeCftData N q d r).frob M a t w -
    alpogeNativeMAIN ell a w =
    alpogeNativeCompletePrimitiveDe r ell a t w := by
  calc
    _ = alpogeNativeDe
      (alpogeNativeCftData N q d r).inertia
      (alpogeNativeCftData N q d r).frob ell a t w :=
      alpogeNativeFullASK_sub_MAIN_eq_De _ _ ell M a t w ha hw hM
    _ = _ := alpogeNativeCftDe_eq_completePrimitiveDe q d r ell a t w

/-! ## No symbolic ell: actual primitive Dirichlet logarithmic derivative

Alpoge's An.logDerivativeAtOne is literally
  (deriv (DirichletCharacter.LFunction chi)) 1 / LFunction chi 1.
The chosen canonical ell below is exactly that expression for each
conductor-reduced chi induced by the genuine modular-unit host.
This closes the analytic DEFINITION of the centering channel; no
estimate on L'/L, nonvanishing, or GRH is presumed.
-/

/-- The authentic logarithmic-derivative constant at the primitive
conductor. The zero-character channel is not used by nonprincipal GPsi. -/
def alpogeNativeCanonicalHostEll
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (ψ : AddChar (AlpogeNativeE0 × H) ℂ) : ℂ := by
  letI : NeZero (alpogeNativeDirChar r ψ).conductor :=
    ⟨DirichletCharacter.conductor_ne_zero _⟩
  let χ := (alpogeNativeDirChar r ψ).primitiveCharacter
  exact deriv (DirichletCharacter.LFunction χ) 1 /
    DirichletCharacter.LFunction χ 1

/-- Completely specified SAME-host source: no arbitrary ell or
fictional Frobenius/ramified coefficient remains in ASK-MAIN. -/
theorem alpogeNativeCanonicalHostASK_sub_MAIN_eq_primitiveDe
    {N : ℕ} [NeZero N]
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (AlpogeNativeE0 × H))
    (M : ℕ) (a : ℝ) (t : H) (w : AlpogeNativeE0 × H → ℝ)
    (ha : 0 < a)
    (hw : ∀ ρ, alpogeNativeInPhi ρ → 0 < w ρ)
    (hM : ∀ ρ, alpogeNativeInPhi ρ → a / w ρ ≤ (M : ℝ)) :
    alpogeNativeFullKernelASK
      (alpogeNativeCftData N q d r).inertia
      (alpogeNativeCftData N q d r).frob M a t w -
    alpogeNativeMAIN (alpogeNativeCanonicalHostEll r) a w =
    alpogeNativeCompletePrimitiveDe
      r (alpogeNativeCanonicalHostEll r) a t w :=
  alpogeNativeCftASK_sub_MAIN_eq_completePrimitiveDe
    q d r (alpogeNativeCanonicalHostEll r) M a t w ha hw hM

end RHLean.Analysis
