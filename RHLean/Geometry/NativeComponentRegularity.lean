import RHLean.Geometry.NativeTwistedTraceDescent

/-!
# Component nonvanishing supplies the actual regular determinant

The section constructor proves nonvanishing at one chosen point of each
component. Those points must be tied to the minimal-prime components of the
actual reduced coefficient ring. Arbitrary finite evaluations are insufficient.

This file proves the ring-theoretic bridge explicitly: each evaluation kernel
contains its component prime, the component primes intersect in zero, and a
determinant nonzero at each chosen point is a non-zero-divisor. The same
determinant then supplies joint injectivity of the actual twisted-trace maps.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix

namespace RHLean.Geometry

/-- A reduced ring element nonzero at a point on each minimal-prime component
is regular. The component-kernel inclusions are retained as explicit data. -/
theorem nativeRegular_of_component_evaluations {R : Type} [CommRing R]
    [IsReduced R] (F : minimalPrimes R → Type) [∀ p, CommRing (F p)]
    (ev : ∀ p, R →+* F p)
    (hcomponent : ∀ p, p.val ≤ RingHom.ker (ev p))
    (u : R) (hu : ∀ p, ev p u ≠ 0) : u ∈ nonZeroDivisors R := by
  have hleft : ∀ f : R, u * f = 0 → f = 0 := by
    intro f hf
    have hmem : f ∈ sInf (minimalPrimes R) := by
      apply Ideal.mem_sInf.mpr
      intro P hP
      let p : minimalPrimes R := ⟨P, hP⟩
      have huP : u ∉ P := by
        intro hm
        exact hu p (RingHom.mem_ker.mp (hcomponent p hm))
      have hprod : u * f ∈ P := hf ▸ P.zero_mem
      exact (hP.isPrime.mem_or_mem hprod).resolve_left huP
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
    change f ∈ nilradical R at hmem
    rw [nilradical_eq_zero] at hmem
    exact (Ideal.mem_bot).mp hmem
  rw [mem_nonZeroDivisors_iff]
  exact ⟨hleft, fun f hf => hleft f (by rwa [mul_comm])⟩

/-- Matrix evaluation commutes with its determinant, so the finite component
determinants constructed by the regular-section algorithm pay regularity. -/
theorem nativeMatrixDet_regular_of_component_evaluations
    {R I : Type} [CommRing R] [IsReduced R] [Fintype I] [DecidableEq I]
    (F : minimalPrimes R → Type) [∀ p, CommRing (F p)]
    (ev : ∀ p, R →+* F p)
    (hcomponent : ∀ p, p.val ≤ RingHom.ker (ev p))
    (A : Matrix I I R) (hdet : ∀ p, (A.map (ev p)).det ≠ 0) :
    A.det ∈ nonZeroDivisors R := by
  apply nativeRegular_of_component_evaluations F ev hcomponent A.det
  intro p
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  exact hdet p

/-- Attach the regularity witness to the exact original character trace.
The maps use the same section `u` whose component determinants were checked. -/
theorem nativeTwistedTrace_injective_of_componentDet
    {H K R : Type} [Group H] [Fintype H] [DecidableEq H]
    [Field K] [CommRing R] [Algebra K R] [IsReduced R]
    (st : H → R →ₐ[K] R) (h1 : ∀ x, st 1 x = x)
    (hmul : ∀ h h' x, st (h * h') x = st h' (st h x))
    (χ : H →* Kˣ) (u : R)
    (F : minimalPrimes R → Type) [∀ p, CommRing (F p)]
    (ev : ∀ p, R →+* F p)
    (hcomponent : ∀ p, p.val ≤ RingHom.ker (ev p))
    (hdet : ∀ p, (Matrix.of fun h g : H => ev p (st (h * g) u)).det ≠ 0) :
    ∀ f : R,
      (∀ h, ∑ g : H, (((χ g)⁻¹ : Kˣ) : K) • st g (f * st h u) = 0) →
      f = 0 := by
  have hreg : (Matrix.of fun h g : H => st (h * g) u).det ∈
      nonZeroDivisors R :=
    nativeMatrixDet_regular_of_component_evaluations F ev hcomponent _ hdet
  exact (NativeAlgebraicDescent.twistedTrace_equivariant_and_injective_of_groupDet
    H K R st h1 hmul χ u hreg).2.1

end RHLean.Geometry
