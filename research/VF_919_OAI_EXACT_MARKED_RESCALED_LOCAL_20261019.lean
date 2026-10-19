import «research.VF_MID_919_OAI_EXCLUDED_SIX_SIGNED_KERNEL»

/-!
# The actual OpenAI marked-minus-rescaled local Euler cancellation

Source: openai/math, The Quasi-Riemann Hypothesis (2026-09-30),
Part II, "The compensated probe" and "The local compensation and its errors",
equations (5.13), (5.13b), (5.13c), and the selected-local-operation.

We reproduce EVERY local term in complex arithmetic, in the native RH_Lean
toolchain, rather than replacing the construction by mu(3d)=-mu(d).

OAI notation at a selected *good* prime ideal p of norm Q:
  A = conj(eta(p))*Q^x
  B = Q^(-w)
  u = chi_p(row)^(-1), for p not dividing the row
  D = eta(p)*chi_p(row)^(-1)*Q^(-x)
  W = chi_p(row)*Q^(-w)
  V = the other local Euler variable
  E = Pstar + D (the local error, retaining all zero restrictions)
  Pstar = E - D
  P = (1-V)^(-1) + W/(1-W) + Pstar
  H = ((1-V)*(1-W)/(1-D))*P
  G = ((A-B)*(1-V)*(1-W)*Pstar - B*(1-V*W))/(1-D)

The TWO exact phase facts are A*D=u and u*W=B.
They are retained as explicit local parameters. The zero-extension p|row
has D=W=0 and is proved separately: no inverse of a zero character.

This formalizes OpenAI's exact local algebra, NOT its nontrivial
large-sieve/moment estimate, and does not identify its cubic-theta
completed source with a Möbius square shell. The final finite
source pairing below is RH_Lean's *actual* excluded-six rational/Hecke
four-site transport and preserves every individual physical weight.
-/

noncomputable section

namespace RHLean.Analysis

open scoped BigOperators

/-- OAI's local unrestricted completed series after extracting the scalar
    Euler quotient: P = (1-V)^(-1) + W/(1-W) + (E-D). -/
def vf919OAIlocalP (V W D E : ℂ) : ℂ :=
  (1 - V)⁻¹ + W / (1 - W) + (E - D)

/-- Its holomorphic unselected factor. This is not inverted at P=0. -/
def vf919OAIlocalH (V W D P : ℂ) : ℂ :=
  ((1 - V) * (1 - W) * P) / (1 - D)

/-- OAI's holomorphic marked-minus-rescaled factor, including the
    -B*(1-V*W) term and the actual restricted completed Pstar. -/
def vf919OAIlocalG (A B V W D Pstar : ℂ) : ℂ :=
  ((A - B) * (1 - V) * (1 - W) * Pstar -
    B * (1 - V * W)) / (1 - D)

/-- The *actual* phase-dependent remainder after scalar cancellation.
    In OAI, u = chi_p(row)^(-1) on good nonzero character rows. -/
def vf919OAIlocalError (A B u V W D E : ℂ) : ℂ :=
  ((1 - V) * (1 - W) / (1 - D)) *
    ((u - B) * (V / (1 - V) - D) +
      (A + u - B) * E)

/-- Exact 1/(1-V) and W/(1-W) contribution:
    (1-V)(1-W)[1/(1-V)+W/(1-W)] = 1-VW.
    Retains the complete Euler row, not a density approximation. -/
theorem vf919OAIlocalP_unrestricted_two_terms
    (V W : ℂ) (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) :
    (1 - V) * (1 - W) *
      ((1 - V)⁻¹ + W / (1 - W)) = 1 - V * W := by
  field_simp [hV, hW]
  <;> ring

/-- The full unrestricted row with the local error E and reciprocal D. -/
theorem vf919OAIlocalP_polynomial
    (V W D E : ℂ) (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) :
    (1 - V) * (1 - W) * vf919OAIlocalP V W D E =
      (1 - V * W) + (1 - V) * (1 - W) * (E - D) := by
  unfold vf919OAIlocalP
  have hbase := vf919OAIlocalP_unrestricted_two_terms V W hV hW
  calc
    (1 - V) * (1 - W) *
        ((1 - V)⁻¹ + W / (1 - W) + (E - D)) =
      (1 - V) * (1 - W) * ((1 - V)⁻¹ + W / (1 - W)) +
        (1 - V) * (1 - W) * (E - D) := by ring
    _ = _ := by rw [hbase]

/-- MARKED minus RESCALED, term by term, before any denominator division.
    This remains valid even when the unrestricted P equals zero. -/
theorem vf919OAImarkedMinusRescaled_numerator
    (A B V W D E : ℂ) (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) :
    (1 - V) * (1 - W) *
      (A * (E - D) - B * vf919OAIlocalP V W D E) =
      (A - B) * (1 - V) * (1 - W) * (E - D) -
        B * (1 - V * W) := by
  have hP := vf919OAIlocalP_polynomial V W D E hV hW
  calc
    (1 - V) * (1 - W) *
        (A * (E - D) - B * vf919OAIlocalP V W D E) =
      A * ((1 - V) * (1 - W) * (E - D)) -
        B * ((1 - V) * (1 - W) * vf919OAIlocalP V W D E) := by ring
    _ = A * ((1 - V) * (1 - W) * (E - D)) -
        B * ((1 - V * W) + (1 - V) * (1 - W) * (E - D)) := by
          rw [hP]
    _ = _ := by ring

/-- OAI's scalar cancellation on the physically unramified phase.
    Every one of A, B, u, V, W, D and E is present. This is polynomial,
    with no nonzero assumption on P, H, or the main row. -/
theorem vf919OAIphase_scalar_cancellation
    (A B u V W D E : ℂ)
    (hAD : A * D = u) (huW : u * W = B) :
    (A + u - B) * (1 - V) * (1 - W) * (E - D) +
      (u - B) * (1 - V * W) =
      (1 - W) *
        ((u - B) * (V - D * (1 - V)) +
          (A + u - B) * (1 - V) * E) := by
  have hu : u = A * D := hAD.symm
  have hB : B = A * D * W := by
    calc
      B = u * W := huW.symm
      _ = A * D * W := by rw [hu]
  rw [hu, hB]
  ring

/-- Exact numerator payment after adding the u*H return leg. All scalar
    prime terms and all E errors remain accounted for; no estimate here. -/
theorem vf919OAIlocalG_add_phaseH_numerator
    (A B u V W D E : ℂ)
    (hP : (1 - V) * (1 - W) * vf919OAIlocalP V W D E =
      (1 - V * W) + (1 - V) * (1 - W) * (E - D))
    (hAD : A * D = u) (huW : u * W = B) :
    ((A - B) * (1 - V) * (1 - W) * (E - D) -
        B * (1 - V * W)) +
      u * ((1 - V) * (1 - W) * vf919OAIlocalP V W D E) =
      (1 - W) *
        ((u - B) * (V - D * (1 - V)) +
          (A + u - B) * (1 - V) * E) := by
  rw [hP]
  calc
    ((A - B) * (1 - V) * (1 - W) * (E - D) -
      B * (1 - V * W)) +
      u * ((1 - V * W) + (1 - V) * (1 - W) * (E - D)) =
        (A + u - B) * (1 - V) * (1 - W) * (E - D) +
          (u - B) * (1 - V * W) := by ring
    _ = _ := vf919OAIphase_scalar_cancellation A B u V W D E hAD huW

/-- THE EXACT OAI IDENTITY (5.13b), in RH_Lean complex arithmetic.
    G + chi_p(row)^(-1)*H is the explicit phase-dependent remainder.
    The proof does not invert P or H and therefore does not lose zeros. -/
theorem vf919OAI_exact_local_compensation
    (A B u V W D E : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hD : 1 - D ≠ 0)
    (hAD : A * D = u) (huW : u * W = B) :
    vf919OAIlocalG A B V W D (E - D) +
        u * vf919OAIlocalH V W D (vf919OAIlocalP V W D E) =
      vf919OAIlocalError A B u V W D E := by
  have hP := vf919OAIlocalP_polynomial V W D E hV hW
  have hnum :=
    vf919OAIlocalG_add_phaseH_numerator A B u V W D E
      hP hAD huW
  unfold vf919OAIlocalG vf919OAIlocalH vf919OAIlocalError
  calc
    ((A - B) * (1 - V) * (1 - W) * (E - D) -
      B * (1 - V * W)) / (1 - D) +
      u * (((1 - V) * (1 - W) * vf919OAIlocalP V W D E) / (1 - D)) =
        (((A - B) * (1 - V) * (1 - W) * (E - D) -
          B * (1 - V * W)) +
          u * ((1 - V) * (1 - W) * vf919OAIlocalP V W D E)) /
          (1 - D) := by ring
    _ = ((1 - W) *
          ((u - B) * (V - D * (1 - V)) +
            (A + u - B) * (1 - V) * E)) / (1 - D) := by
          rw [hnum]
    _ = ((1 - V) * (1 - W) / (1 - D)) *
          ((u - B) * (V / (1 - V) - D) +
            (A + u - B) * E) := by
          field_simp [hV, hD]
          <;> ring

/-- The p|row zero-extension: W=D=0, so the nonunit character inverse
    does not exist. The selected row obeys G=A*(1-V)*E-B*H exactly. -/
theorem vf919OAI_zero_extended_mask
    (A B V E : ℂ) (hV : 1 - V ≠ 0) :
    vf919OAIlocalG A B V 0 0 E =
      A * (1 - V) * E -
        B * vf919OAIlocalH V 0 0 (vf919OAIlocalP V 0 0 E) := by
  have hP :=
    vf919OAIlocalP_polynomial V 0 0 E hV (by norm_num)
  unfold vf919OAIlocalG vf919OAIlocalH
  have hP' : (1 - V) * vf919OAIlocalP V 0 0 E =
      1 + (1 - V) * E := by
    simpa using hP
  rw [hP']
  ring

/-- A finite product of good-prime local compensated factors: every slot
    uses the SAME phase and zero-correct term as the OAI local identity. -/
theorem vf919OAI_exact_finite_good_prime_slots
    {ι : Type*} (slots : Finset ι)
    (A B u V W D E : ι → ℂ)
    (hV : ∀ p ∈ slots, 1 - V p ≠ 0)
    (hW : ∀ p ∈ slots, 1 - W p ≠ 0)
    (hD : ∀ p ∈ slots, 1 - D p ≠ 0)
    (hAD : ∀ p ∈ slots, A p * D p = u p)
    (huW : ∀ p ∈ slots, u p * W p = B p) :
    (∏ p ∈ slots,
      (vf919OAIlocalG (A p) (B p) (V p) (W p) (D p) (E p - D p) +
        u p * vf919OAIlocalH (V p) (W p) (D p)
          (vf919OAIlocalP (V p) (W p) (D p) (E p)))) =
      ∏ p ∈ slots, vf919OAIlocalError
        (A p) (B p) (u p) (V p) (W p) (D p) (E p) := by
  apply Finset.prod_congr rfl
  intro p hp
  exact vf919OAI_exact_local_compensation
    (A p) (B p) (u p) (V p) (W p) (D p) (E p)
    (hV p hp) (hW p hp) (hD p hp) (hAD p hp) (huW p hp)

/-- Each rational physical site keeps BOTH distinct marked and rescaled
    observables, the genuine four-shift excluded-(2,3) mask and all signs.
    This is the finite #919 coefficient pairing; it does NOT identify those
    two observables with OAI's cubic-theta source without a separate map. -/
theorem vf919OAI_marked_rescaled_physical_pairing
    (s : Finset (ℕ × ℕ)) (ns : Finset ℕ)
    (a chi : ℕ → ℝ) (marked rescaled : ℕ → ℝ)
    (hcover : ∀ x ∈ s,
      x.1 * x.2 ∈ ns ∧ 3 * (x.1 * x.2) ∈ ns ∧
      4 * (x.1 * x.2) ∈ ns ∧ 12 * (x.1 * x.2) ∈ ns) :
    (∑ n ∈ ns,
      vf919FiniteSixExcludedRationalCoefficient s a chi n *
        (marked n - rescaled n)) =
      ∑ x ∈ s, (a x.1 * chi x.2) *
        (vf919SixExcludedSiteWeight marked (x.1 * x.2) -
          vf919SixExcludedSiteWeight rescaled (x.1 * x.2)) := by
  rw [vf919FiniteSixExcludedRationalPairing_eq_Hecke
    s ns a chi (fun n => marked n - rescaled n) hcover]
  unfold vf919FiniteSixExcludedPairSource
  apply Finset.sum_congr rfl
  intro x _
  rw [vf919SixExcludedSiteWeight_sub]


/-! ## The ORIGINAL OpenAI subset expansion and unit-phase substitution -/

/-- Explicit source-faithful finite difference. OAI's subset J indexes
    the RESCALED slots, while the complement is MARKED. The alternating
    sign (-1)^|J| is never replaced with an unsigned incidence count. -/
theorem vf919OAI_original_subset_marked_minus_rescaled
    {ι : Type*} [DecidableEq ι]
    (slots : Finset ι) (marked rescaled : ι → ℂ) :
    (∑ J ∈ slots.powerset,
      (-1 : ℂ) ^ J.card *
        (∏ p ∈ slots \ J, marked p) *
        (∏ p ∈ J, rescaled p)) =
      ∏ p ∈ slots, (marked p - rescaled p) := by
  simpa using (Finset.prod_sub marked rescaled slots).symm

/-- Source equation (5.13c), but as a true selected-prime OPERATION
    rather than merely a definition of G. No inversion of P or H,
    so the identity survives their zeros and the full source mask. -/
theorem vf919OAI_selected_local_operation
    (A B V W D E : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hD : 1 - D ≠ 0) :
    (1 - V) * (1 - W) *
        (A * (E - D) - B * vf919OAIlocalP V W D E) =
      (1 - D) * vf919OAIlocalG A B V W D (E - D) := by
  rw [vf919OAImarkedMinusRescaled_numerator A B V W D E hV hW]
  unfold vf919OAIlocalG
  field_simp [hD]

/-- Derive both OAI phase equalities from unit character, zero-extended
    nonzero good-prime phase v, and nonzero complex norm power Q^x.
    etaInv is the conjugate of eta on unit characters; all products
    retain their original complex phases. -/
theorem vf919OAI_unit_character_phase_facts
    (etaInv eta v Qx Qw : ℂ)
    (hEta : etaInv * eta = 1) (hv : v ≠ 0) (hQx : Qx ≠ 0) :
    (etaInv * Qx) * (eta * v⁻¹ * Qx⁻¹) = v⁻¹ ∧
      v⁻¹ * (v * Qw) = Qw := by
  constructor
  · calc
      (etaInv * Qx) * (eta * v⁻¹ * Qx⁻¹) =
          (etaInv * eta) * (Qx * Qx⁻¹) * v⁻¹ := by ring
      _ = v⁻¹ := by simp [hEta, hQx]
  · field_simp [hv]
    <;> ring

/-- OpenAI (5.13b) with A, B, D, W and u INSTANTIATED from the
    ACTUAL character and norm-power expressions, not separately
    hypothesized zero-defect/dipole parameters. -/
theorem vf919OAI_exact_good_character_compensation
    (etaInv eta v Qx Qw V E : ℂ)
    (hEta : etaInv * eta = 1) (hv : v ≠ 0) (hQx : Qx ≠ 0)
    (hV : 1 - V ≠ 0) (hW : 1 - v * Qw ≠ 0)
    (hD : 1 - (eta * v⁻¹ * Qx⁻¹) ≠ 0) :
    vf919OAIlocalG
        (etaInv * Qx) Qw V (v * Qw)
        (eta * v⁻¹ * Qx⁻¹)
        (E - eta * v⁻¹ * Qx⁻¹) +
      v⁻¹ * vf919OAIlocalH
        V (v * Qw) (eta * v⁻¹ * Qx⁻¹)
        (vf919OAIlocalP V (v * Qw) (eta * v⁻¹ * Qx⁻¹) E) =
      vf919OAIlocalError
        (etaInv * Qx) Qw v⁻¹ V (v * Qw)
        (eta * v⁻¹ * Qx⁻¹) E := by
  obtain ⟨hAD, hBW⟩ :=
    vf919OAI_unit_character_phase_facts etaInv eta v Qx Qw hEta hv hQx
  exact vf919OAI_exact_local_compensation
    (etaInv * Qx) Qw v⁻¹ V (v * Qw)
    (eta * v⁻¹ * Qx⁻¹) E
    hV hW hD hAD hBW

#print axioms vf919OAI_original_subset_marked_minus_rescaled
#print axioms vf919OAI_selected_local_operation
#print axioms vf919OAI_unit_character_phase_facts
#print axioms vf919OAI_exact_good_character_compensation

#print axioms vf919OAIlocalP_unrestricted_two_terms
#print axioms vf919OAImarkedMinusRescaled_numerator
#print axioms vf919OAIphase_scalar_cancellation
#print axioms vf919OAIlocalG_add_phaseH_numerator
#print axioms vf919OAI_exact_local_compensation
#print axioms vf919OAI_zero_extended_mask
#print axioms vf919OAI_exact_finite_good_prime_slots
#print axioms vf919OAI_marked_rescaled_physical_pairing

end RHLean.Analysis
