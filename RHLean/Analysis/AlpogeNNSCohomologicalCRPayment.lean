import Mathlib
import RHLean.Analysis.AlpogeNNSMatchedSelbergKernel
import RHLean.Analysis.PartialMomentSchurTarget

/-!
# Native NNS C-to-R decomposition and the exact cohomology-length ledger

The map (a,b) -> (a+b,a-b) is invertible over any ring in which
2 is a unit. Applied to a cohomology module stable under an involution,
it identifies that module exactly with the + and - eigenspaces.
Consequently its module length is the SUM of the two eigenlengths,
without an additional index or covolume charge at odd residue primes.

This is the exact algebraic portion of Alpoge's genuine Sha length
split, not an import of the result or an assumption about cohomology.
It can be instantiated with an actual Selmer submodule and conjugation
once those have been built inside RH_Lean.

The native NNS Schur covariance CANNOT alone bound the sum of
nonnegative cohomology lengths: a constant sample has zero centered
covariance but positive first moment. More decisively, the exact
K2 - ordered Lambda convolution match cancels the apparently negative
principal rank-one mode: it is not available as a credit against Sha.

This file does not assert the nontrivial uniform VVle / VWin upper
bound on the ACTUAL global Selmer groups. The original growth theorem
requires that estimate at the same fields, twists and windows.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Exact C-to-R length conservation under a genuine involution.
The two image modules are the s and -s eigenparts inside the given
source submodule N; there are no surrogate finite-dimensional ranks.

Every equality is an algebraic consequence of f^2=1 and 2 invertible.
-/
theorem nativeNNSCohomologyLength_split
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (h2 : IsUnit (2 : R))
    (N : Submodule R M) (f : Module.End R M)
    (hN : ∀ x ∈ N, f x ∈ N)
    (hf : ∀ x, f (f x) = x) (s : R) (hs : s * s = 1) :
    Module.length R N =
      Module.length R ↥(N ⊓ f.eigenspace s) +
        Module.length R ↥(N ⊓ f.eigenspace (-s)) := by
  set c : R := ↑h2.unit⁻¹ with hc_def
  have hc : (2 : R) * c = 1 := h2.mul_val_inv
  have eP : ∀ x : M, f (x + s • f x) = s • (x + s • f x) := by
    intro x
    rw [map_add, map_smul, hf, smul_add, smul_smul, hs, one_smul, add_comm]
  have eQ : ∀ x : M, f (x - s • f x) = (-s) • (x - s • f x) := by
    intro x
    rw [map_sub, map_smul, hf, smul_sub, smul_smul, neg_mul,
      hs, neg_smul, neg_smul, one_smul]
    abel
  have memP : ∀ x ∈ N, c • (x + s • f x) ∈ N ⊓ f.eigenspace s := fun x hx =>
    ⟨N.smul_mem c (N.add_mem hx (N.smul_mem s (hN x hx))),
      (f.eigenspace s).smul_mem c (Module.End.mem_eigenspace_iff.mpr (eP x))⟩
  have memQ : ∀ x ∈ N, c • (x - s • f x) ∈ N ⊓ f.eigenspace (-s) := fun x hx =>
    ⟨N.smul_mem c (N.sub_mem hx (N.smul_mem s (hN x hx))),
      (f.eigenspace (-s)).smul_mem c (Module.End.mem_eigenspace_iff.mpr (eQ x))⟩
  let toP : N →ₗ[R] ↥(N ⊓ f.eigenspace s) :=
    (c • (N.subtype + s • (f ∘ₗ N.subtype))).codRestrict _ (fun x => by
      simp only [LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.comp_apply, Submodule.coe_subtype]
      exact memP _ x.2)
  let toQ : N →ₗ[R] ↥(N ⊓ f.eigenspace (-s)) :=
    (c • (N.subtype - s • (f ∘ₗ N.subtype))).codRestrict _ (fun x => by
      simp only [LinearMap.smul_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, Submodule.coe_subtype]
      exact memQ _ x.2)
  let back : (↥(N ⊓ f.eigenspace s) × ↥(N ⊓ f.eigenspace (-s))) →ₗ[R] N :=
    (Submodule.inclusion inf_le_left).coprod (Submodule.inclusion inf_le_left)
  have h_forward : (toP.prod toQ) ∘ₗ back = LinearMap.id := by
    ext ⟨a, ha⟩
    all_goals simp [toP, toQ, back]
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (c • a) + hc • a
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (-(c • a))
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (-(c • a))
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (c • a) + hc • a
  have h_backward : back ∘ₗ (toP.prod toQ) = LinearMap.id := by
    ext ⟨x, hx⟩
    simp [toP, toQ, back]
    linear_combination (norm := module) hc • x
  rw [(LinearEquiv.ofLinear (toP.prod toQ) back
    h_forward h_backward).length_eq, Module.length_prod]

/-- For every ODD prime, the NNS C-to-R change of variables pays
zero module-length distortion over the ACTUAL p-adic integer ring.
The exceptional p=2 input is deliberately kept separate. -/
theorem nativeNNSOddPrimeCohomologyLength_split
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (N : Submodule ℤ_[p] M) (f : Module.End ℤ_[p] M)
    (hN : ∀ x ∈ N, f x ∈ N)
    (hf : ∀ x, f (f x) = x)
    (s : ℤ_[p]) (hs : s * s = 1) :
    Module.length ℤ_[p] N =
      Module.length ℤ_[p] ↥(N ⊓ f.eigenspace s) +
        Module.length ℤ_[p] ↥(N ⊓ f.eigenspace (-s)) := by
  have h2 : IsUnit (2 : ℤ_[p]) := by
    by_contra hn
    have hmem : (2 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      (IsLocalRing.mem_maximalIdeal _).mpr hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_ofNat] at hmem
    have hz : ((2 : ℕ) : ZMod p) = 0 := by simpa using hmem
    rw [ZMod.natCast_eq_zero_iff] at hz
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hz)
  exact nativeNNSCohomologyLength_split h2 N f hN hf s hs

/-- The MATCHED native Selberg band has NO free negative principal
rank-one credit to transfer into positive Sha lengths.  In the full
physical source the ordered prime-pair convolution restores it
exactly, leaving a nonnegative diagonal sum. -/
theorem nativeNNSMatchedBand_nonneg
    (m : ℕ) (ell : Fin m → ℝ) :
    0 ≤ alpogeNNSBandCharge m ell -
      alpogeNNSBandOrderedConvolutionCharge m ell := by
  rw [alpogeNNSBand_principalMode_cancels]
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (ell i))

/-- Definitive finite test of the wrong candidate implication:
even nonnegative 3-slot data can have Schur covariance exactly zero
and strictly positive FIRST moment.  So no universal scaling of
CENTERED NNS covariance can prove VVle's nonnegative first-moment bound.
This refutes a *particular shortcut*, not the possibility of a new
cohomological comparison using genuinely stronger data. -/
theorem nativeNNSCenteredSchur_cannot_pay_positive_lengths :
    ¬ ∃ C : ℝ, ∀ ell : Fin 3 → ℝ,
        (∀ i, 0 ≤ ell i) →
          (∑ i : Fin 3, ell i) ≤ C *
            alpogeNNSBandScaledSchur 3 ell := by
  rintro ⟨C, hC⟩
  have h := hC (fun _ : Fin 3 => 1) (by intro _; norm_num)
  norm_num [alpogeNNSBandScaledSchur] at h

end RHLean.Analysis
