import «research.VF_919_OAI_EXACT_MARKED_RESCALED_LOCAL_20261019»
import «research.VF_919_NATIVE_SEXTIC_OWNER_PROJECTION_20261019»

/-!
# One physical occurrence at a time: OAI local compensation on native owner seats

This is a strictly finer source than a norm-grouped scalar integer: each
label is (rational prime p, Eisenstein-cofactor a+b*omega). Two labels with
the same p and norm remain separate. The actual original site is

    n = p * N(a+b*omega)

and its weight is RH_Lean's lowOwnerZeroFrequencyMobiusSite, with the
literal integer Moebius sign and original first-owner crossing weight.

At EVERY label, attach the ACTUAL OAI Part II local factor:
  A=etaInv*Qx; D=eta*v^(-1)*Qx^(-1); B=Qw; W=v*Qw;
  G = selected marked-minus-rescaled Euler correction;
  H = unselected Euler factor;
  u = v^(-1) is the true nonzero sextic phase in the good case.
The p|row zero-character branch has D=W=0 and no inverse of v.

The aggregate identity is an application of the exact OAI factor equality
to the ORIGINAL signed physical source BEFORE grouping by integer norm.
The Hermitian energy retains the selected/returned mixed covariance.

This is an algebraic SOURCE-WEIGHTED coupling. OAI's completed cubic-theta
physical probe is *not* identified with the native original Mobius source;
an analytic moment bound for one is not automatically a bound for the other.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Ideal label with the exact Eisenstein coordinate of its cofactor. -/
abbrev VF919OAIPhysicalIdealLabel := ℕ × (ℕ × (ℤ × ℤ))

/-- The second index is the SPLIT PRIME-IDEAL ROOT r (mod p), not an
    integer owner or a second rational prime. Distinct roots r,r' yield
    distinct phase labels even at identical rational n = p*N(a+b*omega). -/
def vf919OAIlabelSexticResidue
    (i : VF919OAIPhysicalIdealLabel) : ZMod i.1 :=
  vf919SplitSexticResidue i.1 (i.2.1 : ZMod i.1) i.2.2.1 i.2.2.2

/-- At x=317 the SAME p=19 and SAME Eisenstein cofactor alpha are
    present as two different split-prime-ideal labels: their phases
    must be kept separately, before projecting to integer n=133. -/
theorem vf919OAI_x317_split_ideal_labels_distinct :
    ((19, (7, ((-2 : ℤ), (-3 : ℤ)))) :
       VF919OAIPhysicalIdealLabel) ≠
      ((19, (11, ((-2 : ℤ), (-3 : ℤ)))) :
       VF919OAIPhysicalIdealLabel) := by
  decide

/-- Genuine finite-field sextic character residues for the above two
    distinct p=19 prime-ideal roots, reused from the native 317 proof. -/
theorem vf919OAI_x317_both_actual_sextic_residues :
    vf919OAIlabelSexticResidue
      (19, (7, ((-2 : ℤ), (-3 : ℤ)))) =
        (1 + (7 : ZMod 19)) ^ 5 ∧
    vf919OAIlabelSexticResidue
      (19, (11, ((-2 : ℤ), (-3 : ℤ)))) =
        (1 + (11 : ZMod 19)) ^ 5 := by
  simpa [vf919OAIlabelSexticResidue] using
    (vf919Sextic_x317_exactFourIdealPhases).1



/-- The physical integer Möbius owner charge: no artificial sign or
    norm-only character replaces RH_Lean's literal source occurrence. -/
def vf919OAIOriginalIdealLabeledSeat
    (R : ℕ) (i : VF919OAIPhysicalIdealLabel) : ℂ :=
  (RHLean.Proof.vf919SexticNativeAMPSite R i.1 i.2.2.1 i.2.2.2 : ℂ)

/-- The actual selected Euler correction at an ideal label, multiplied
    by the original integer physical site weight. -/
def vf919OAIGoodSelectedPhysicalSum
    (R : ℕ) (labels : Finset VF919OAIPhysicalIdealLabel)
    (etaInv Qx Qw v V E eta : VF919OAIPhysicalIdealLabel → ℂ) : ℂ :=
  ∑ i ∈ labels,
    vf919OAIOriginalIdealLabeledSeat R i *
      vf919OAIlocalG (etaInv i * Qx i) (Qw i)
        (V i) (v i * Qw i)
        (eta i * (v i)⁻¹ * (Qx i)⁻¹)
        (E i - eta i * (v i)⁻¹ * (Qx i)⁻¹)

/-- The full returned unselected leg, including the inverse sextic
    phase and the original source weight at EVERY label. -/
def vf919OAIGoodReturnedPhysicalSum
    (R : ℕ) (labels : Finset VF919OAIPhysicalIdealLabel)
    (etaInv Qx Qw v V E eta : VF919OAIPhysicalIdealLabel → ℂ) : ℂ :=
  ∑ i ∈ labels,
    vf919OAIOriginalIdealLabeledSeat R i * (v i)⁻¹ *
      vf919OAIlocalH
        (V i) (v i * Qw i)
        (eta i * (v i)⁻¹ * (Qx i)⁻¹)
        (vf919OAIlocalP
          (V i) (v i * Qw i)
          (eta i * (v i)⁻¹ * (Qx i)⁻¹) (E i))

/-- Exact compensated physical remainder on the same ideal-labelled seats.
    The true residual coefficient is the explicit OAI phase/error bracket. -/
def vf919OAIGoodResidualPhysicalSum
    (R : ℕ) (labels : Finset VF919OAIPhysicalIdealLabel)
    (etaInv Qx Qw v V E eta : VF919OAIPhysicalIdealLabel → ℂ) : ℂ :=
  ∑ i ∈ labels,
    vf919OAIOriginalIdealLabeledSeat R i *
      vf919OAIlocalError
        (etaInv i * Qx i) (Qw i) (v i)⁻¹
        (V i) (v i * Qw i)
        (eta i * (v i)⁻¹ * (Qx i)⁻¹) (E i)

/-- THE DIRECT PHYSICAL BRIDGE: OAI cancellation, one ideal-labelled
    integer Mobius occurrence at a time, all signs and distinct phases kept.
    Neither local term is bounded separately. -/
theorem vf919OAI_original_native_seat_term_by_term
    (R : ℕ) (labels : Finset VF919OAIPhysicalIdealLabel)
    (etaInv Qx Qw v V E eta : VF919OAIPhysicalIdealLabel → ℂ)
    (hEta : ∀ i ∈ labels, etaInv i * eta i = 1)
    (hv : ∀ i ∈ labels, v i ≠ 0)
    (hQx : ∀ i ∈ labels, Qx i ≠ 0)
    (hV : ∀ i ∈ labels, 1 - V i ≠ 0)
    (hW : ∀ i ∈ labels, 1 - v i * Qw i ≠ 0)
    (hD : ∀ i ∈ labels,
      1 - (eta i * (v i)⁻¹ * (Qx i)⁻¹) ≠ 0) :
    vf919OAIGoodSelectedPhysicalSum R labels etaInv Qx Qw v V E eta +
      vf919OAIGoodReturnedPhysicalSum R labels etaInv Qx Qw v V E eta =
      vf919OAIGoodResidualPhysicalSum R labels etaInv Qx Qw v V E eta := by
  unfold vf919OAIGoodSelectedPhysicalSum
    vf919OAIGoodReturnedPhysicalSum
    vf919OAIGoodResidualPhysicalSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hlocal :=
    vf919OAI_exact_good_character_compensation
      (etaInv i) (eta i) (v i) (Qx i) (Qw i) (V i) (E i)
      (hEta i hi) (hv i hi) (hQx i hi)
      (hV i hi) (hW i hi) (hD i hi)
  calc
    vf919OAIOriginalIdealLabeledSeat R i *
        vf919OAIlocalG (etaInv i * Qx i) (Qw i)
          (V i) (v i * Qw i)
          (eta i * (v i)⁻¹ * (Qx i)⁻¹)
          (E i - eta i * (v i)⁻¹ * (Qx i)⁻¹) +
      vf919OAIOriginalIdealLabeledSeat R i * (v i)⁻¹ *
        vf919OAIlocalH (V i) (v i * Qw i)
          (eta i * (v i)⁻¹ * (Qx i)⁻¹)
          (vf919OAIlocalP (V i) (v i * Qw i)
            (eta i * (v i)⁻¹ * (Qx i)⁻¹) (E i)) =
      vf919OAIOriginalIdealLabeledSeat R i *
        (vf919OAIlocalG (etaInv i * Qx i) (Qw i)
          (V i) (v i * Qw i)
          (eta i * (v i)⁻¹ * (Qx i)⁻¹)
          (E i - eta i * (v i)⁻¹ * (Qx i)⁻¹) +
        (v i)⁻¹ *
          vf919OAIlocalH (V i) (v i * Qw i)
            (eta i * (v i)⁻¹ * (Qx i)⁻¹)
            (vf919OAIlocalP (V i) (v i * Qw i)
              (eta i * (v i)⁻¹ * (Qx i)⁻¹) (E i))) := by ring
    _ = _ := by rw [hlocal]

/-- NO dropped covariance. This is the complete complex Gram of the
    two original signed physical legs, including their mixed cross term.
    Its equality with the compensated residual uses the theorem above. -/
theorem vf919OAI_original_native_seat_full_mixed_gram
    (R : ℕ) (labels : Finset VF919OAIPhysicalIdealLabel)
    (etaInv Qx Qw v V E eta : VF919OAIPhysicalIdealLabel → ℂ)
    (hEta : ∀ i ∈ labels, etaInv i * eta i = 1)
    (hv : ∀ i ∈ labels, v i ≠ 0)
    (hQx : ∀ i ∈ labels, Qx i ≠ 0)
    (hV : ∀ i ∈ labels, 1 - V i ≠ 0)
    (hW : ∀ i ∈ labels, 1 - v i * Qw i ≠ 0)
    (hD : ∀ i ∈ labels,
      1 - (eta i * (v i)⁻¹ * (Qx i)⁻¹) ≠ 0) :
    ‖vf919OAIGoodResidualPhysicalSum R labels etaInv Qx Qw v V E eta‖ ^ 2 =
      ‖vf919OAIGoodSelectedPhysicalSum R labels etaInv Qx Qw v V E eta‖ ^ 2 +
      ‖vf919OAIGoodReturnedPhysicalSum R labels etaInv Qx Qw v V E eta‖ ^ 2 +
      2 * (vf919OAIGoodSelectedPhysicalSum R labels etaInv Qx Qw v V E eta *
        star (vf919OAIGoodReturnedPhysicalSum R labels etaInv Qx Qw v V E eta)).re := by
  rw [← vf919OAI_original_native_seat_term_by_term R labels
    etaInv Qx Qw v V E eta hEta hv hQx hV hW hD]
  simpa only [Complex.sq_norm] using
    Complex.normSq_add
      (vf919OAIGoodSelectedPhysicalSum R labels etaInv Qx Qw v V E eta)
      (vf919OAIGoodReturnedPhysicalSum R labels etaInv Qx Qw v V E eta)

/-! ## Full source with OAI's CONTINUED holomorphic selected-prime factor

This is the actual version needed after contour continuation: 1-W can
vanish, so no raw P or H is inverted. Original native signed weights
and genuine distinct ideal labels remain on BOTH terms. -/

/-- The unselected return is the continued OAI correction, not the
    raw meromorphic factor. No division by an ill-defined local P. -/
def vf919OAIContinuedReturnedPhysicalSum
    (R : ℕ) (labels : Finset VF919OAIPhysicalIdealLabel)
    (etaInv Qx Qw v V E eta : VF919OAIPhysicalIdealLabel → ℂ) : ℂ :=
  ∑ i ∈ labels,
    vf919OAIOriginalIdealLabeledSeat R i * (v i)⁻¹ *
      vf919OAIcontinuedH (V i) (v i * Qw i)
        (eta i * (v i)⁻¹ * (Qx i)⁻¹)
        (E i - eta i * (v i)⁻¹ * (Qx i)⁻¹)

/-- Full original weighted integer-site termwise compensated identity
    with the precise OAI continued factor and complete residual E.
    Unlike the initial-Euler proof, NO (1-W) nonvanishing assumption. -/
theorem vf919OAI_original_native_continued_term_by_term
    (R : ℕ) (labels : Finset VF919OAIPhysicalIdealLabel)
    (etaInv Qx Qw v V E eta : VF919OAIPhysicalIdealLabel → ℂ)
    (hEta : ∀ i ∈ labels, etaInv i * eta i = 1)
    (hv : ∀ i ∈ labels, v i ≠ 0)
    (hQx : ∀ i ∈ labels, Qx i ≠ 0)
    (hV : ∀ i ∈ labels, 1 - V i ≠ 0)
    (hD : ∀ i ∈ labels,
      1 - eta i * (v i)⁻¹ * (Qx i)⁻¹ ≠ 0) :
    vf919OAIGoodSelectedPhysicalSum R labels etaInv Qx Qw v V E eta +
      vf919OAIContinuedReturnedPhysicalSum R labels etaInv Qx Qw v V E eta =
      vf919OAIGoodResidualPhysicalSum R labels etaInv Qx Qw v V E eta := by
  unfold vf919OAIGoodSelectedPhysicalSum
    vf919OAIContinuedReturnedPhysicalSum
    vf919OAIGoodResidualPhysicalSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hlocal :=
    vf919OAI_exact_continued_good_character
      (etaInv i) (eta i) (v i) (Qx i) (Qw i) (V i) (E i)
      (hEta i hi) (hv i hi) (hQx i hi) (hV i hi) (hD i hi)
  calc
    vf919OAIOriginalIdealLabeledSeat R i *
        vf919OAIlocalG (etaInv i * Qx i) (Qw i)
          (V i) (v i * Qw i)
          (eta i * (v i)⁻¹ * (Qx i)⁻¹)
          (E i - eta i * (v i)⁻¹ * (Qx i)⁻¹) +
      vf919OAIOriginalIdealLabeledSeat R i * (v i)⁻¹ *
        vf919OAIcontinuedH (V i) (v i * Qw i)
          (eta i * (v i)⁻¹ * (Qx i)⁻¹)
          (E i - eta i * (v i)⁻¹ * (Qx i)⁻¹) =
      vf919OAIOriginalIdealLabeledSeat R i *
        (vf919OAIlocalG (etaInv i * Qx i) (Qw i)
          (V i) (v i * Qw i)
          (eta i * (v i)⁻¹ * (Qx i)⁻¹)
          (E i - eta i * (v i)⁻¹ * (Qx i)⁻¹) +
        (v i)⁻¹ * vf919OAIcontinuedH (V i) (v i * Qw i)
          (eta i * (v i)⁻¹ * (Qx i)⁻¹)
          (E i - eta i * (v i)⁻¹ * (Qx i)⁻¹)) := by ring
    _ = _ := by rw [hlocal]

/-- Complete Hermitian covariance including the PLUS selected/returned
    cross bill: no absolute-value or independence error from continuation. -/
theorem vf919OAI_original_native_continued_full_gram
    (R : ℕ) (labels : Finset VF919OAIPhysicalIdealLabel)
    (etaInv Qx Qw v V E eta : VF919OAIPhysicalIdealLabel → ℂ)
    (hEta : ∀ i ∈ labels, etaInv i * eta i = 1)
    (hv : ∀ i ∈ labels, v i ≠ 0)
    (hQx : ∀ i ∈ labels, Qx i ≠ 0)
    (hV : ∀ i ∈ labels, 1 - V i ≠ 0)
    (hD : ∀ i ∈ labels,
      1 - eta i * (v i)⁻¹ * (Qx i)⁻¹ ≠ 0) :
    ‖vf919OAIGoodResidualPhysicalSum R labels etaInv Qx Qw v V E eta‖ ^ 2 =
      ‖vf919OAIGoodSelectedPhysicalSum R labels etaInv Qx Qw v V E eta‖ ^ 2 +
      ‖vf919OAIContinuedReturnedPhysicalSum R labels etaInv Qx Qw v V E eta‖ ^ 2 +
      2 * (vf919OAIGoodSelectedPhysicalSum R labels etaInv Qx Qw v V E eta *
        star (vf919OAIContinuedReturnedPhysicalSum R labels etaInv Qx Qw v V E eta)).re := by
  rw [← vf919OAI_original_native_continued_term_by_term R labels
    etaInv Qx Qw v V E eta hEta hv hQx hV hD]
  simpa only [Complex.sq_norm] using
    Complex.normSq_add
      (vf919OAIGoodSelectedPhysicalSum R labels etaInv Qx Qw v V E eta)
      (vf919OAIContinuedReturnedPhysicalSum R labels etaInv Qx Qw v V E eta)

#print axioms vf919OAI_original_native_continued_term_by_term
#print axioms vf919OAI_original_native_continued_full_gram

#print axioms vf919OAI_x317_split_ideal_labels_distinct
#print axioms vf919OAI_x317_both_actual_sextic_residues
#print axioms vf919OAI_original_native_seat_term_by_term
#print axioms vf919OAI_original_native_seat_full_mixed_gram

end RHLean.Analysis
