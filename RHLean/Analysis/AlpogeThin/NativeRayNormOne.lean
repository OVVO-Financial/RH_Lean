import RHLean.Analysis.AlpogeNativeQuadraticIntegerBasis
import RHLean.Analysis.AlpogeThin.NativeRayIdealCounts
import RHLean.Analysis.AlpogeThin.NativeRayIdealLattice
import RHLean.Analysis.AlpogeThin.NativeDyadicRayNorm

/-!
# The actual identity ray coefficient supplies native NormOne coordinates

The SAME ray-class ideal has a generator congruent to one modulo M. Its
coordinates in the native quadratic integral basis compute its actual ideal
norm, and hence give the already defined `IsNormOne` predicate. The result
holds at every natural norm; primality is only needed by later consumers.

Source guide: Levent Alpöge's archive, inspected pin
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean`,
`exists_gen`, `normOne_span`, and the last conjunct of `lamRay_props`.
This reconstruction uses the existing native principal-ideal norm-square
identity, so it imports no source zeta theorem. The archive states no license;
attribution assigns none.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open NumberField
open scoped Classical

namespace RHLean.Analysis.AlpogeThin.NativeRay.NormOne

open Formalism.HermitianLattices.ZeroFreeRegionGL2

variable {K : Type} [Field K] [NumberField K]

theorem exists_generator_absNorm_formula {d : ℕ} (hp : d.Prime)
    (hd : d % 4 = 3) {r : K} (hr : r ^ 2 = -(d : K))
    (h2 : Module.finrank ℚ K = 2) :
    ∃ w : 𝓞 K, (∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * w) ∧
      ∀ a b : ℤ,
        (Ideal.absNorm (Ideal.span {(a : 𝓞 K) + b * w}) : ℤ) * 4 =
          (2 * a + b) ^ 2 + (d : ℤ) * b ^ 2 := by
  obtain ⟨w, bar, hw, _, hgen, hemb, σ, hσr⟩ :=
    NativeQuadraticIntegers.ringOfIntegers_sqrt_neg_three_mod_four
      d (Irreducible.squarefree hp) hd K h2 r hr
  letI : IsTotallyComplex K :=
    ⟨fun v => InfinitePlace.isComplex_iff.mpr (hemb v.embedding).1⟩
  have hσw : σ (w : K) = (1 + Complex.I * Real.sqrt d) / 2 := by
    have h := congrArg σ hw
    rw [map_mul, map_add, map_one, map_ofNat, hσr] at h
    linear_combination h / 2
  refine ⟨w, hgen, fun a b => ?_⟩
  have hn := IdealLattice.normSq_eq h2 σ ((a : 𝓞 K) + b * w)
  have hval : σ (((a : 𝓞 K) + b * w : 𝓞 K) : K) =
      ((a + b / 2 : ℝ) : ℂ) + ((b * Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
    have hc : (((a : 𝓞 K) + b * w : 𝓞 K) : K) = a + b * (w : K) := by simp
    rw [hc, map_add, map_mul, map_intCast, map_intCast, hσw]
    push_cast
    ring
  rw [hval, Complex.sq_norm, Complex.normSq_add_mul_I] at hn
  have hs : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hreal : (Ideal.absNorm (Ideal.span {(a : 𝓞 K) + b * w}) : ℝ) * 4 =
      (2 * (a : ℝ) + b) ^ 2 + d * (b : ℝ) ^ 2 := by
    linear_combination -4 * hn + (b : ℝ) ^ 2 * hs
  exact_mod_cast hreal

/-- A congruent-to-one generator yields the literal pre-existing norm
predicate, with the factor four and both original congruences retained. -/
theorem isNormOne_span {d M : ℕ} (hp : d.Prime) (hd : d % 4 = 3)
    {r : K} (hr : r ^ 2 = -(d : K)) (h2 : Module.finrank ℚ K = 2)
    {π : 𝓞 K} (hπ : π - 1 ∈ Ideal.span {(M : 𝓞 K)}) :
    IsNormOne d M (Ideal.absNorm (Ideal.span {π})) := by
  obtain ⟨w, hgen, hnorm⟩ := exists_generator_absNorm_formula hp hd hr h2
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hπ
  obtain ⟨a, b, rfl⟩ := hgen z
  have e : π = ((1 + M * a : ℤ) : 𝓞 K) + ((M * b : ℤ) : 𝓞 K) * w := by
    push_cast
    linear_combination -hz
  have hn := hnorm (1 + M * a) (M * b)
  rw [← e] at hn
  apply (NativeRawHostRayNorm.isNormOne_iff_halfRootCoordinates
    d M (Ideal.absNorm (Ideal.span {π})) hd).mpr
  refine ⟨2 * (1 + M * a) + M * b, M * b, ?_, ⟨b, rfl⟩, ⟨a, by ring⟩⟩
  simpa only [mul_comm (4 : ℤ)] using hn.symm

/-- Nonzero mass supplies an actual ideal in the identity ray class. Its
existing native class equivalence constructs the generator; no analytic
prime-existence or hypothetical norm witness is used. -/
theorem isNormOne_of_lamRay_ne_zero {d M : ℕ} (hp : d.Prime)
    (hd : d % 4 = 3) {r : K} (hr : r ^ 2 = -(d : K))
    (h2 : Module.finrank ℚ K = 2) (D : RayData K M) (n : ℕ)
    (hn : lamRay D 1 n ≠ 0) : IsNormOne d M n := by
  have hne : (idealsIn D 1 n).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    apply hn
    unfold lamRay
    rw [h0, finsum_mem_empty]
  obtain ⟨I, hI0, hIc, hIn, hIcl⟩ := hne
  have hB : D.cls (1 : Ideal (𝓞 K)) = (1 : D.G)⁻¹ := by
    simpa only [inv_one] using D.cls_one
  obtain ⟨π, hπ, hspan⟩ :=
    (IdealLattice.cls_iff D (1 : D.G) 1 I isCoprime_one_left
      one_ne_zero hB hIc hI0).mp hIcl
  have hspan' : Ideal.span {π} = I := by simpa only [mul_one] using hspan
  rw [← hIn, ← hspan']
  exact isNormOne_span hp hd hr h2 hπ

end RHLean.Analysis.AlpogeThin.NativeRay.NormOne

end
