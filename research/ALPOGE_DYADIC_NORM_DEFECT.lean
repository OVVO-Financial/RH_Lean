import RHLean.Analysis.AlpogeNNSCohomologicalCRPayment

/-!
# The integral norm defect at two

For an involution on the actual module, the two eigenlengths overcount by
the length of the fixed module modulo the norm image. No division by two,
finite-length hypothesis, or subtraction of infinite lengths is needed.
The concrete lifts show why the action on two-torsion cannot price this
quotient exactly. No estimate on a family of Selmer groups is assumed.
-/

namespace RHLean.Analysis

section Norm

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The norm of the involution, valued in its actual fixed submodule. -/
def nativeDyadicNorm (f : Module.End R M) (hf : ∀ x, f (f x) = x) :
    M →ₗ[R] ↥(f.eigenspace 1) :=
  (LinearMap.id + f).codRestrict _ fun x => by
    apply Module.End.mem_eigenspace_iff.mpr
    change f (x + f x) = (1 : R) • (x + f x)
    rw [map_add, hf, one_smul, add_comm]

private theorem dyadicNorm_ker (f : Module.End R M) (hf : ∀ x, f (f x) = x) :
    LinearMap.ker (nativeDyadicNorm f hf) = f.eigenspace (-1) := by
  ext x
  rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff, neg_one_smul]
  constructor
  · intro h
    have hz : x + f x = 0 := congrArg Subtype.val h
    calc
      f x = -x + (x + f x) := by abel
      _ = -x := by rw [hz, add_zero]
  · intro h
    apply Subtype.ext
    change x + f x = 0
    rw [h, add_neg_cancel]

private theorem dyadicNorm_on_fixed (f : Module.End R M) (hf : ∀ x, f (f x) = x)
    (x : f.eigenspace 1) : nativeDyadicNorm f hf x.val = (2 : R) • x := by
  apply Subtype.ext
  change (x : M) + f x = (2 : R) • (x : M)
  rw [Module.End.mem_eigenspace_iff.mp x.property, one_smul, two_smul]

private theorem dyadicLength_ker_range {B : Type*} [AddCommGroup B] [Module R B]
    (g : M →ₗ[R] B) : Module.length R M =
      Module.length R (LinearMap.ker g) + Module.length R (LinearMap.range g) := by
  let K := LinearMap.ker g
  calc
    Module.length R M = Module.length R K + Module.length R (M ⧸ K) :=
      Module.length_eq_add_of_exact K.subtype K.mkQ K.subtype_injective
        K.mkQ_surjective (LinearMap.exact_subtype_mkQ K)
    _ = _ := congrArg (Module.length R K + ·) g.quotKerEquivRange.length_eq

/-- Exact additive ledger, also meaningful at infinite length. -/
theorem nativeDyadicNorm_length (f : Module.End R M) (hf : ∀ x, f (f x) = x) :
    Module.length R (f.eigenspace 1) + Module.length R (f.eigenspace (-1)) =
      Module.length R M + Module.length R
        (↥(f.eigenspace 1) ⧸ LinearMap.range (nativeDyadicNorm f hf)) := by
  let I := LinearMap.range (nativeDyadicNorm f hf)
  have hp := Module.length_eq_add_of_exact I.subtype I.mkQ I.subtype_injective
    I.mkQ_surjective (LinearMap.exact_subtype_mkQ I)
  have hm := dyadicLength_ker_range (nativeDyadicNorm f hf)
  rw [dyadicNorm_ker] at hm
  rw [hp, hm]
  ac_rfl

/-- Twice every class in the counting defect is zero. -/
theorem nativeDyadicNorm_two_smul (f : Module.End R M) (hf : ∀ x, f (f x) = x)
    (z : ↥(f.eigenspace 1) ⧸ LinearMap.range (nativeDyadicNorm f hf)) :
    (2 : R) • z = 0 := by
  let I := LinearMap.range (nativeDyadicNorm f hf)
  obtain ⟨x, rfl⟩ := I.mkQ_surjective z
  rw [← map_smul]
  exact (Submodule.Quotient.mk_eq_zero I).mpr ⟨x.val, dyadicNorm_on_fixed f hf x⟩

/-- Only fixed two-torsion is charged in the upper bound, not all of M[2]. -/
theorem nativeDyadicNorm_fixedTorsion_bound (f : Module.End R M)
    (hf : ∀ x, f (f x) = x) :
    Module.length R (f.eigenspace 1) + Module.length R (f.eigenspace (-1)) ≤
      Module.length R M + Module.length R
        (LinearMap.ker ((2 : R) • (LinearMap.id : Module.End R ↥(f.eigenspace 1)))) := by
  let d := (2 : R) • (LinearMap.id : Module.End R ↥(f.eigenspace 1))
  let n := nativeDyadicNorm f hf
  have hsub : LinearMap.range d ≤ LinearMap.range n := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x.val, dyadicNorm_on_fixed f hf x⟩
  have him : Module.length R (LinearMap.range d) ≤ Module.length R (LinearMap.range n) := by
    simpa only [Module.length_submodule] using Order.height_mono hsub
  have hm := dyadicLength_ker_range (nativeDyadicNorm f hf)
  rw [dyadicNorm_ker] at hm
  calc
    _ = (Module.length R (LinearMap.ker d) + Module.length R (LinearMap.range d)) +
        Module.length R (f.eigenspace (-1)) :=
      congrArg (· + Module.length R (f.eigenspace (-1))) (dyadicLength_ker_range d)
    _ ≤ (Module.length R (LinearMap.ker d) + Module.length R (LinearMap.range n)) +
        Module.length R (f.eigenspace (-1)) := add_le_add (add_le_add le_rfl him) le_rfl
    _ = _ := by
      rw [hm]
      let a := Module.length R (LinearMap.ker d)
      let b := Module.length R (LinearMap.range n)
      let q := Module.length R (f.eigenspace (-1))
      change (a + b) + q = (q + b) + a
      exact (add_comm (a + b) q).trans
        ((congrArg (q + ·) (add_comm a b)).trans (add_assoc q b a).symm)

end Norm

/-- An integral lift of the identity on the two-torsion of (Z/4)^2. -/
def nativeDyadicModFourLift : Module.End (ZMod 4) (ZMod 4 × ZMod 4) :=
  let a := LinearMap.fst (ZMod 4) (ZMod 4) (ZMod 4)
  let b := LinearMap.snd (ZMod 4) (ZMod 4) (ZMod 4)
  (a + (2 : ZMod 4) • b).prod ((2 : ZMod 4) • a + (3 : ZMod 4) • b)

/-- The lift and the identity agree on two-torsion; the signed eigencounts
are (4,4) versus (16,4) on exactly the same 16-element module. -/
theorem nativeDyadicModFour_witness :
    (∀ x, nativeDyadicModFourLift (nativeDyadicModFourLift x) = x) ∧
    (∀ x, (2 : ZMod 4) • x = 0 → nativeDyadicModFourLift x = x) ∧
    (Finset.univ.filter (fun x => nativeDyadicModFourLift x = x)).card = 4 ∧
    (Finset.univ.filter (fun x => nativeDyadicModFourLift x = -x)).card = 4 ∧
    Fintype.card (ZMod 4 × ZMod 4) = 16 ∧
    (Finset.univ.filter (fun x : ZMod 4 × ZMod 4 => x = -x)).card = 4 := by
  decide

end RHLean.Analysis

#print axioms RHLean.Analysis.nativeDyadicNorm_length
#print axioms RHLean.Analysis.nativeDyadicNorm_two_smul
#print axioms RHLean.Analysis.nativeDyadicNorm_fixedTorsion_bound
#print axioms RHLean.Analysis.nativeDyadicModFour_witness
