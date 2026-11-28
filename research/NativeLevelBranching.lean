import RHLean.Geometry.NativeThetaFock
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

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

/-- The ramified residue sections given by the image of one minus the
action of a scalar unit on the cyclic addresses. -/
def ramifiedResidue {N : ℕ} (u : (ZMod N)ˣ) (f : ZMod N → MvPolynomial S ℂ)
    (j : ZMod N) : MvPolynomial S ℂ :=
  f j - f ((u : ZMod N) * j)

theorem dft_ramifiedResidue (N : ℕ) [NeZero N] (u : (ZMod N)ˣ)
    (f : ZMod N → MvPolynomial S ℂ) :
    ZMod.dft (ramifiedResidue u f) = ramifiedResidue u⁻¹ (ZMod.dft f) := by
  have h : ramifiedResidue u f = f - (fun j => f ((u : ZMod N) * j)) := rfl
  rw [h, map_sub]
  funext j
  change ZMod.dft f j - ZMod.dft (fun i => f ((u : ZMod N) * i)) j =
    ZMod.dft f j - ZMod.dft f ((↑(u⁻¹) : ZMod N) * j)
  rw [ZMod.dft_comp_unitMul]

/-- The cyclic source transform followed by inverse level dilation
on the source Fock grading. -/
def sourceFourier (N : ℕ) [NeZero N] (t : S)
    (f : ZMod N → MvPolynomial S ℂ) (j : ZMod N) : MvPolynomial S ℂ :=
  dilate t (N : ℂ)⁻¹ (ZMod.dft f j)

/-- One pair of the source transforms. -/
def pairedFourier (N : ℕ) [NeZero N] (t : S)
    (f : ZMod N → MvPolynomial S ℂ) : ZMod N → MvPolynomial S ℂ :=
  sourceFourier N t (sourceFourier N t f)

theorem coeff_pairedFourier (N : ℕ) [NeZero N] (t : S)
    (f : ZMod N → MvPolynomial S ℂ) (j : ZMod N) (a : S →₀ ℕ) :
    (pairedFourier N t f j).coeff a =
      (((N : ℂ)⁻¹) ^ (2 * a t) * (N : ℂ)) * (f (-j)).coeff a := by
  unfold pairedFourier sourceFourier
  rw [show ZMod.dft (fun i => dilate t (N : ℂ)⁻¹ (ZMod.dft f i)) j =
    dilate t (N : ℂ)⁻¹ (ZMod.dft (ZMod.dft f) j) from
      fourier_reweight N (fun b => ((N : ℂ)⁻¹) ^ (b t)) (ZMod.dft f) j,
    fourier_pair]
  simp only [dilate, coeff_reweight, coeff_smul, smul_eq_mul, two_mul, pow_add]
  ring

theorem coeff_pairedFourier_iterate (N : ℕ) [NeZero N] (t : S) (q : ℕ)
    (f : ZMod N → MvPolynomial S ℂ) (j : ZMod N) (a : S →₀ ℕ) :
    (((pairedFourier N t)^[q] f) j).coeff a =
      (((N : ℂ)⁻¹) ^ (2 * a t * q) * (N : ℂ) ^ q) *
        (f ((Neg.neg : ZMod N → ZMod N)^[q] j)).coeff a := by
  induction q generalizing j with
  | zero => simp
  | succ q ih =>
      rw [Function.iterate_succ_apply' (pairedFourier N t), coeff_pairedFourier, ih,
        Function.iterate_succ_apply (Neg.neg : ZMod N → ZMod N), Nat.mul_succ, pow_add,
        pow_succ (N : ℂ)]
      ring

/-- The Fourier pairs contribute one level factor per pair. A degree
coordinate therefore needs only the positive part of its remaining pole. -/
def pairedClearingDegree (t : S) (q : ℕ) (a : S →₀ ℕ) : ℕ :=
  (2 * a t * q + a t) - q

private theorem paired_clearing_scalar {z : ℂ} (hz : z ≠ 0) (r e q : ℕ) :
    (z⁻¹ ^ r * z ^ q) * z ^ (r + e - q) = z ^ e * z ^ (q - (r + e)) := by
  have he : q + (r + e - q) = r + (e + (q - (r + e))) := by omega
  calc
    _ = (z ^ r)⁻¹ * z ^ (q + (r + e - q)) := by rw [inv_pow, pow_add, mul_assoc]
    _ = _ := by
      rw [he, pow_add z r, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero r hz), one_mul, pow_add]

/-- Construct the preimage in the cyclic polynomial model. The seed
and its reflected output use the original coefficient lattice. -/
theorem pairedFourier_preimage (N : ℕ) [NeZero N] (t : S) (q : ℕ)
    (f : ZMod N → MvPolynomial S ℂ) :
    (pairedFourier N t)^[q]
      (fun j => reweight (fun a => (N : ℂ) ^ pairedClearingDegree t q a) (f j)) =
    fun j => dilate t (N : ℂ)
      (reweight (fun a => (N : ℂ) ^ (q - (2 * a t * q + a t)))
        (f ((Neg.neg : ZMod N → ZMod N)^[q] j))) := by
  funext j
  ext a
  rw [coeff_pairedFourier_iterate]
  simp only [dilate, coeff_reweight, pairedClearingDegree]
  rw [← mul_assoc, paired_clearing_scalar (NeZero.ne (N : ℂ)), mul_assoc]

/-- The degree-weighted clearing gives integral output at every residue
and in every coefficient, measured in the dilated source lattice. -/
theorem pairedFourier_integral_preimage (N : ℕ) [NeZero N] (t : S) (q : ℕ)
    (f : ZMod N → MvPolynomial S ℂ) (hf : ∀ j a, IsIntegral ℤ ((f j).coeff a)) :
    ∃ g : ZMod N → MvPolynomial S ℂ, (∀ j a, IsIntegral ℤ ((g j).coeff a)) ∧
      (pairedFourier N t)^[q]
        (fun j => reweight (fun a => (N : ℂ) ^ pairedClearingDegree t q a) (f j)) =
      fun j => dilate t (N : ℂ) (g j) := by
  refine ⟨_, ?_, pairedFourier_preimage N t q f⟩
  intro j a
  rw [coeff_reweight]
  exact ((isIntegral_natCast N).pow _).mul (hf _ a)

/-- On the same cleared rows, the high-degree restriction lands in
the integral coefficient lattice of the target. -/
theorem pairedFourier_restriction_integral (N : ℕ) [NeZero N] (t : S) (q h : ℕ)
    (u v : ℂ) (hv : v ≠ 0) (hN : u * v = N) (hu : IsIntegral ℤ u)
    (f : ZMod N → MvPolynomial S ℂ) (hf : ∀ j a, IsIntegral ℤ ((f j).coeff a))
    (j : ZMod N) (a : S →₀ ℕ) :
    IsIntegral ℤ ((restrictDegree t h v
      (((pairedFourier N t)^[q]
        (fun i => reweight (fun b => (N : ℂ) ^ pairedClearingDegree t q b) (f i))) j)).coeff a) := by
  obtain ⟨g, hg, hpair⟩ := pairedFourier_integral_preimage N t q f hf
  rw [hpair]
  exact compensated_integral t h u v N hv hN (g j) hu (hg j) a

/-- The paired preimage stays ramified under the same scalar unit.
The integral seed is transported before applying one minus the action. -/
theorem pairedFourier_ramified_preimage (N : ℕ) [NeZero N] (t : S) (q : ℕ)
    (u : (ZMod N)ˣ) (f : ZMod N → MvPolynomial S ℂ)
    (hf : ∀ j a, IsIntegral ℤ ((f j).coeff a)) :
    ∃ g : ZMod N → MvPolynomial S ℂ, (∀ j a, IsIntegral ℤ ((g j).coeff a)) ∧
      (pairedFourier N t)^[q]
        (fun j => reweight (fun a => (N : ℂ) ^ pairedClearingDegree t q a)
          (ramifiedResidue u f j)) =
      fun j => dilate t (N : ℂ) (ramifiedResidue u g j) := by
  let w : (S →₀ ℕ) → ℂ := fun a => (N : ℂ) ^ (q - (2 * a t * q + a t))
  let g := fun j => reweight w (f ((Neg.neg : ZMod N → ZMod N)^[q] j))
  have comm (r : ℕ) (j : ZMod N) :
      (Neg.neg : ZMod N → ZMod N)^[r] ((u : ZMod N) * j) =
        (u : ZMod N) * ((Neg.neg : ZMod N → ZMod N)^[r] j) := by
    induction r with
    | zero => rfl
    | succ r ih => simp only [Function.iterate_succ_apply', ih, mul_neg]
  refine ⟨g, ?_, ?_⟩
  · intro j a
    rw [show g j = reweight w (f ((Neg.neg : ZMod N → ZMod N)^[q] j)) from rfl,
      coeff_reweight]
    exact ((isIntegral_natCast N).pow _).mul (hf _ a)
  · rw [pairedFourier_preimage]
    funext j
    apply congrArg (dilate t (N : ℂ))
    ext a
    simp only [g, w, ramifiedResidue, coeff_reweight, coeff_sub, comm, mul_sub]

/-- The clearing determinant on the selected monomial coordinates.
The choice of coordinates is fixed when applying the Fourier pairs. -/
theorem pairedFourier_preimage_det {I : Type*} [Fintype I] [DecidableEq I]
    (N : ℕ) (t : S) (q : ℕ) (a : I → S →₀ ℕ) :
    (Matrix.diagonal (fun i => (N : ℤ) ^ pairedClearingDegree t q (a i))).det =
      (N : ℤ) ^ ∑ i, pairedClearingDegree t q (a i) := by
  rw [Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]

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

/-- The source preimage exponent is paid by the mean distinguished
degree on any retained list that has the stated column symmetry. -/
theorem pairedClearingDegree_sum_le_mean {I : Type*} [Fintype I] [Fintype S]
    (t : S) (q total : ℕ) (a : I → S →₀ ℕ)
    (hs : ∀ j : S, ∑ i, a i j = ∑ i, a i t)
    (hd : ∀ i, ∑ j, a i j = total) :
    Fintype.card S * (∑ i, pairedClearingDegree t q (a i)) ≤
      (2 * q + 1) * (Fintype.card I * total) := by
  have h : (∑ i, pairedClearingDegree t q (a i)) ≤
      (2 * q + 1) * (∑ i, a i t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ 2 * a i t * q + a i t := Nat.sub_le _ _
      _ = _ := by ring
  calc
    _ ≤ Fintype.card S * ((2 * q + 1) * (∑ i, a i t)) :=
      Nat.mul_le_mul_left _ h
    _ = (2 * q + 1) * (Fintype.card S * (∑ i, a i t)) := by ring
    _ = _ := by rw [mean_degree (fun i j => a i j) t total hs hd]

end RHLean.Analysis.NativeLevelBranching
