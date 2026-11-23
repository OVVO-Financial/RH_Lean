import RHLean.Geometry.NativeCMQuadraticOrder
import RHLean.Geometry.NativeDerivedGeometricHost
import RHLean.Analysis.AlpogeNativeQuadraticIntegerBasis
import RHLean.Analysis.AlpogeNativeQuadraticSplitting

/-!
# The Serre coefficient order is the actual quadratic ring of integers

The geometric order is the literal subalgebra Z[w0] of O_E. The arithmetic
finite-degree calculation uses O_K, where K is the literal subfield Q(sqd)
of the same E. This file identifies those rings, with their inclusions in
O_E and their half-root generators. No abstract quadratic field or second
choice of coefficient lattice intervenes.

The construction reuses the already native integral-basis proof in
`AlpogeNativeQuadraticIntegerBasis` and the degree-two proof in
`AlpogeNativeQuadraticSplitting`. Their source attribution is retained in
those files. All maps below are the actual number-field inclusion maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField

namespace RHLean.Geometry.NativeCM

open RHLean.Analysis

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- The quadratic field generated inside the same host by its integral root. -/
abbrev quadraticField (G : NativeGeometricHost E) : IntermediateField ℚ E :=
  ℚ⟮(G.rt : E)⟯

def quadraticFieldRoot (G : NativeGeometricHost E) : quadraticField G :=
  ⟨G.rt, IntermediateField.mem_adjoin_simple_self ℚ (G.rt : E)⟩

theorem quadraticFieldRoot_sq (G : NativeGeometricHost E) :
    quadraticFieldRoot G ^ 2 = -(G.d : quadraticField G) := by
  apply Subtype.ext
  exact_mod_cast G.rt_sq

theorem quadraticField_finrank (G : NativeGeometricHost E) :
    Module.finrank ℚ (quadraticField G) = 2 := by
  apply NativeQuadraticSplitting.finrank_K G.d_prime.pos
  exact_mod_cast G.rt_sq

private theorem exists_quadratic_integer_generator (G : NativeGeometricHost E) :
    ∃ w : 𝓞 (quadraticField G),
      2 * (w : quadraticField G) = 1 + quadraticFieldRoot G ∧
      ∀ a : 𝓞 (quadraticField G), ∃ m n : ℤ, a = m + n * w := by
  exact NativeQuadraticIntegers.exists_integer_generator_of_sq_eq_neg
    (quadraticField_finrank G) G.d_prime.squarefree
    (by have := G.d_mod; omega) (quadraticFieldRoot_sq G)

/-- The integral half-root in the literal quadratic subfield. -/
def quadraticIntegerGenerator (G : NativeGeometricHost E) : 𝓞 (quadraticField G) :=
  Classical.choose (exists_quadratic_integer_generator G)

theorem quadraticIntegerGenerator_spec (G : NativeGeometricHost E) :
    2 * (quadraticIntegerGenerator G : quadraticField G) =
        1 + quadraticFieldRoot G ∧
      ∀ a : 𝓞 (quadraticField G), ∃ m n : ℤ,
        a = m + n * quadraticIntegerGenerator G :=
  Classical.choose_spec (exists_quadratic_integer_generator G)

/-- The integral-basis generator is the geometric generator in O_E. -/
@[simp] theorem quadraticIntegerGenerator_image (G : NativeGeometricHost E) :
    algebraMap (𝓞 (quadraticField G)) (𝓞 E) (quadraticIntegerGenerator G) = G.w0 := by
  apply RingOfIntegers.coe_injective
  have h1 := congrArg (fun a : quadraticField G => (a : E))
    (quadraticIntegerGenerator_spec G).1
  have h2 := congrArg (fun a : 𝓞 E => (a : E)) G.two_weight_eq_one_add_root
  push_cast at h1 h2
  change (2 : E) *
    ((algebraMap (𝓞 (quadraticField G)) (𝓞 E) (quadraticIntegerGenerator G) : 𝓞 E) : E) =
      1 + (G.rt : E) at h1
  linear_combination (1 / 2 : E) * h1 - (1 / 2 : E) * h2

theorem quadraticInteger_image_mem_order (G : NativeGeometricHost E)
    (a : 𝓞 (quadraticField G)) :
    algebraMap (𝓞 (quadraticField G)) (𝓞 E) a ∈ OK G := by
  obtain ⟨m, n, ha⟩ := (quadraticIntegerGenerator_spec G).2 a
  rw [ha, map_add, map_mul, map_intCast, map_intCast, quadraticIntegerGenerator_image]
  exact coord_mem G m n

/-- Restrict the actual inclusion O_K -> O_E to its exact image Z[w0]. -/
def quadraticIntegersToOrder (G : NativeGeometricHost E) :
    𝓞 (quadraticField G) →+* OK G where
  toFun a := ⟨algebraMap (𝓞 (quadraticField G)) (𝓞 E) a,
    quadraticInteger_image_mem_order G a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

theorem quadraticIntegersToOrder_bijective (G : NativeGeometricHost E) :
    Function.Bijective (quadraticIntegersToOrder G) := by
  constructor
  · intro a b hab
    apply RingOfIntegers.coe_injective
    apply (algebraMap (quadraticField G) E).injective
    exact congrArg (fun x : OK G => ((x : 𝓞 E) : E)) hab
  · intro a
    obtain ⟨m, n, ha⟩ := exists_coord G a.property
    refine ⟨(m : 𝓞 (quadraticField G)) + n * quadraticIntegerGenerator G, ?_⟩
    apply Subtype.ext
    change algebraMap (𝓞 (quadraticField G)) (𝓞 E)
      ((m : 𝓞 (quadraticField G)) + n * quadraticIntegerGenerator G) = (a : 𝓞 E)
    rw [map_add, map_mul, map_intCast, map_intCast, quadraticIntegerGenerator_image]
    exact ha.symm

/-- The actual Serre order, identified with the full quadratic ring of integers. -/
def orderIntegerRingEquiv (G : NativeGeometricHost E) :
    OK G ≃+* 𝓞 (quadraticField G) :=
  (RingEquiv.ofBijective (quadraticIntegersToOrder G)
    (quadraticIntegersToOrder_bijective G)).symm

/-- The identification commutes with the original inclusion in O_E. -/
@[simp] theorem orderIntegerRingEquiv_inclusion (G : NativeGeometricHost E) (a : OK G) :
    algebraMap (𝓞 (quadraticField G)) (𝓞 E) (orderIntegerRingEquiv G a) = (a : 𝓞 E) :=
  congrArg Subtype.val ((RingEquiv.ofBijective (quadraticIntegersToOrder G)
    (quadraticIntegersToOrder_bijective G)).apply_symm_apply a)

@[simp] theorem orderIntegerRingEquiv_generator (G : NativeGeometricHost E) :
    orderIntegerRingEquiv G (wK G) = quadraticIntegerGenerator G := by
  apply RingOfIntegers.coe_injective
  apply (algebraMap (quadraticField G) E).injective
  change ((algebraMap (𝓞 (quadraticField G)) (𝓞 E)
    (orderIntegerRingEquiv G (wK G)) : 𝓞 E) : E) =
      ((algebraMap (𝓞 (quadraticField G)) (𝓞 E)
        (quadraticIntegerGenerator G) : 𝓞 E) : E)
  rw [orderIntegerRingEquiv_inclusion, quadraticIntegerGenerator_image]

/-- In particular the original scalar action on any O_E-module is unchanged. -/
theorem orderIntegerRingEquiv_smul (G : NativeGeometricHost E)
    {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (a : OK G) (x : M) :
    algebraMap (𝓞 (quadraticField G)) (𝓞 E) (orderIntegerRingEquiv G a) • x = a • x := by
  rw [orderIntegerRingEquiv_inclusion]

end RHLean.Geometry.NativeCM

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM

/-- The coefficient order in the native Serre construction is the literal
ring of integers used by the same host's relative different and finite degree. -/
def nativeDyadicCMOrderEquiv
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    OK (nativeDyadicGeometricHostOfDerived e q d he hH) ≃+* 𝓞 H.K := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  exact orderIntegerRingEquiv (nativeDyadicGeometricHostOfDerived e q d he hH)

/-- Both coefficient-ring descriptions have exactly the same inclusion in O_E. -/
theorem nativeDyadicCMOrderEquiv_inclusion
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    ∀ a : OK (nativeDyadicGeometricHostOfDerived e q d he hH),
      algebraMap (𝓞 H.K) (𝓞 H.E) (nativeDyadicCMOrderEquiv e q d he hH a) =
        (a : 𝓞 H.E) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  exact fun a => orderIntegerRingEquiv_inclusion
    (nativeDyadicGeometricHostOfDerived e q d he hH) a

/-- The matched generator is the same half of one plus HostRaw.sqd. -/
theorem nativeDyadicCMOrderEquiv_generator
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    2 * ((nativeDyadicCMOrderEquiv e q d he hH (wK G) : 𝓞 H.K) : H.K) =
      1 + ⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ H.sqd⟩ := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  change 2 * (orderIntegerRingEquiv G (wK G) : quadraticField G) =
    1 + quadraticFieldRoot G
  rw [orderIntegerRingEquiv_generator]
  exact (quadraticIntegerGenerator_spec G).1

end RHLean.Analysis.AlpogeThin

end
