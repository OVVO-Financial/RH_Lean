import RHLean.Geometry.NativeThetaFock
import Mathlib.Analysis.Fourier.ZMod

/-! Degree-sensitive restriction on the actual native Fock polynomials.
The level factor is applied to a homogeneous coefficient projection;
the finite dilation compensates it exactly. The Fourier operation is
the genuine cyclic transform on coefficient-valued sections. This
does not assert an economical preimage for the native ramified chain. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Classical
open MvPolynomial
open RHLean.Geometry.NativeTheta.Fock

namespace RHLean.Analysis.NativeLevelBranching

variable {S : Type*}

/-- Diagonal coefficient operation in the original factorial metric. -/
def reweight (u : (S →₀ ℕ) → ℂ) (P : MvPolynomial S ℂ) : MvPolynomial S ℂ :=
  ∑ a ∈ P.support, monomial a (u a * P.coeff a)

@[simp] theorem coeff_reweight (u : (S →₀ ℕ) → ℂ) (P : MvPolynomial S ℂ)
    (a : S →₀ ℕ) : (reweight u P).coeff a = u a * P.coeff a := by
  classical
  rw [reweight, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  by_cases ha : a ∈ P.support
  · simp only [ha, ite_true]
  · simp only [ha, ite_false, MvPolynomial.notMem_support_iff.mp ha, mul_zero]

theorem support_reweight (u : (S →₀ ℕ) → ℂ) (P : MvPolynomial S ℂ) :
    (reweight u P).support ⊆ P.support := by
  intro a ha
  by_contra hn
  exact (MvPolynomial.mem_support_iff.mp ha) (by
    rw [coeff_reweight, MvPolynomial.notMem_support_iff.mp hn, mul_zero])

/-- This is a genuine linear map, so finite Fourier sums can be
transported through it without coefficient or sign losses. -/
def reweightLinear (u : (S →₀ ℕ) → ℂ) :
    MvPolynomial S ℂ →ₗ[ℂ] MvPolynomial S ℂ where
  toFun := reweight u
  map_add' := by
    intro P Q
    ext a
    simp only [coeff_reweight, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]
  map_smul' := by
    intro c P
    ext a
    simp only [coeff_reweight, coeff_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem reweight_norm_le (u : (S →₀ ℕ) → ℂ) (P : MvPolynomial S ℂ)
    (k : ℝ) (hk : ∀ a, ‖u a‖ ≤ k) :
    fockNormSq (reweight u P) ≤ k^2 * fockNormSq P := by
  classical
  rw [fockNormSq_eq_sum_of_subset (support_reweight u P), fockNormSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [coeff_reweight, norm_mul]
  calc
    _ = ‖u a‖^2 * ((multiFactorial a : ℝ) * ‖P.coeff a‖^2) := by ring
    _ ≤ k^2 * ((multiFactorial a : ℝ) * ‖P.coeff a‖^2) := by
      gcongr
      exact hk a

/-- Retain the literal distinguished degree, with no rescaling of
the original Fock norm. -/
def restrictDegree (t : S) (h : ℕ) (v : ℂ) (P : MvPolynomial S ℂ) :=
  reweight (fun a => if a t = h then v⁻¹ ^ h else 0) P

/-- Dilation of the actual coefficient along the distinguished axis. -/
def dilate (t : S) (N : ℂ) (P : MvPolynomial S ℂ) :=
  reweight (fun a => N ^ (a t)) P

/-- The independent archimedean saving, valid for any embedded
norm element v satisfying the norm identity. -/
theorem restriction_norm (t : S) (h : ℕ) (v : ℂ)
    (P : MvPolynomial S ℂ) (N : ℝ) (hv : ‖v‖^2 = N) :
    fockNormSq (restrictDegree t h v P) ≤ N⁻¹ ^ h * fockNormSq P := by
  have hnorm : ‖v⁻¹ ^ h‖^2 = N⁻¹ ^ h := by
    rw [norm_pow, norm_inv, ← pow_mul, Nat.mul_comm h 2, pow_mul, inv_pow, hv]
  rw [← hnorm]
  apply reweight_norm_le
  intro a
  by_cases ha : a t = h
  · simp only [ha, ite_true, le_refl]
  · simp only [ha, ite_false, norm_zero, norm_nonneg]

/-- Exact counterpart of the finite-gauge identity: the degree h
dilation cancels the degree h pole, leaving the integral companion. -/
theorem restriction_dilate (t : S) (h : ℕ) (u v N : ℂ)
    (hv : v ≠ 0) (hN : u*v = N) (P : MvPolynomial S ℂ) :
    restrictDegree t h v (dilate t N P) =
      reweight (fun a => if a t = h then u^h else 0) P := by
  ext a
  simp only [restrictDegree, dilate, coeff_reweight]
  by_cases ha : a t = h
  · simp only [ha, ite_true]
    rw [← mul_assoc, ← mul_pow, ← hN]
    have he : v⁻¹ * (u*v) = u := by
      field_simp
    rw [he]
  · simp only [ha, ite_false, zero_mul]

/-- Finite integrality is measured on the same coefficients as the
real norm, rather than imposed by an assigned height. -/
theorem compensated_integral (t : S) (h : ℕ) (u v N : ℂ)
    (hv : v ≠ 0) (hN : u*v = N) (P : MvPolynomial S ℂ)
    (hu : IsIntegral ℤ u) (hP : ∀ a, IsIntegral ℤ (P.coeff a)) (a : S →₀ ℕ) :
    IsIntegral ℤ ((restrictDegree t h v (dilate t N P)).coeff a) := by
  rw [restriction_dilate t h u v N hv hN, coeff_reweight]
  split_ifs
  · exact (hu.pow h).mul (hP a)
  · rw [zero_mul]
    exact isIntegral_zero

/-- Genuine Fourier transport on cyclic residue labels with values in
the original polynomial space. The phase is not replaced by its norm. -/
theorem fourier_reweight (N : ℕ) [NeZero N] (u : (S →₀ ℕ) → ℂ)
    (f : ZMod N → MvPolynomial S ℂ) (j : ZMod N) :
    ZMod.dft (fun i => reweight u (f i)) j =
      reweight u (ZMod.dft f j) := by
  let L := reweightLinear u
  change ZMod.dft (fun i => L (f i)) j = L (ZMod.dft f j)
  simp only [ZMod.dft_apply, map_sum, map_smul]

/-- A pair of unnormalized Fourier operations pays precisely one
factor N, and reverses the original residue address. -/
theorem fourier_pair (N : ℕ) [NeZero N] (f : ZMod N → MvPolynomial S ℂ)
    (j : ZMod N) :
    ZMod.dft (ZMod.dft f) j = (N:ℂ) • f (-j) := by
  rw [ZMod.dft_dft]

/-- Full phase-sensitive pair transport through the measured degree
restriction. This is not an identification of Fourier with dilation. -/
theorem fourier_pair_restrict (N : ℕ) [NeZero N] (t : S) (h : ℕ) (v : ℂ)
    (f : ZMod N → MvPolynomial S ℂ) (j : ZMod N) :
    ZMod.dft (ZMod.dft (fun i => restrictDegree t h v (f i))) j =
      (N:ℂ) • restrictDegree t h v (f (-j)) := by
  exact fourier_pair N (fun i => restrictDegree t h v (f i)) j

/-- Coordinate exchange yields the mean finite degree, not the
maximum degree, when the actual retained index set has that symmetry. -/
theorem mean_degree {I J : Type*} [Fintype I] [Fintype J]
    (d : I → J → ℕ) (j : J) (a : ℕ)
    (hs : ∀ k : J, ∑ i, d i k = ∑ i, d i j)
    (hd : ∀ i, ∑ k, d i k = a) :
    Fintype.card J * (∑ i, d i j) = Fintype.card I * a := by
  calc
    _ = ∑ k : J, ∑ i, d i k := by simp_rw [hs]; simp
    _ = ∑ i : I, ∑ k, d i k := Finset.sum_comm
    _ = _ := by simp [hd]

end RHLean.Analysis.NativeLevelBranching
