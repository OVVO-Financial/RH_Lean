import Mathlib
import «research.VF_MID_ADVERSARIAL_PROOF_FUZZER»

/-!
# Structural owner-admissible escape class for the direct VF route

This file records the intended final logical architecture explicitly in Lean.

The admissible class is not defined by the desired von-Koch bound and is
not defined by a realized cancellation estimate. Instead it records the exact
well-founded escape law isolated by the adversarial proof fuzzer:

* finitely many base scales are not bad;
* every channel-threatening bad scale reproduces on a strict recursive VF
  child scale.

The fuzzer already proves that weak recurrence, perfect midpoint balance, and
the exact quadratic energy identity do not imply radial boundedness. The
strict-child reproduction law is the additional arithmetic structure which
kills every escaping adversary by strong induction.

For the honest prime-counting defect, the sole arithmetic obligation exposed
here is VFMidActualPrimeOwnerEscapeAdmissibleStatement.

Its intended proof is by the exact sieve/owner mechanics already developed in
the repository: physical VF seat reassembly, exact affine/Mobius decoding,
unique first owner, critical owner trichotomy, strict continuation to a smaller
state, and clipped outgoing contraction. No global prime-error cancellation
estimate belongs in the definition of admissibility.
-/

noncomputable section

namespace RHLean.Analysis

/-- A defect trajectory is structurally owner-admissible when some nonnegative
radial constant has finite base control and every bad scale reproduces on an
actual strict recursive VF child scale.

This is deliberately a descent law, not the desired radial bound itself. -/
def VFMidOwnerEscapeAdmissible (D : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    (∀ R : ℕ, R < 7 → ¬ VFMidSyntheticBadAt D K R) ∧
    (∀ R : ℕ, 7 ≤ R → VFMidSyntheticBadAt D K R →
      ∃ S : ℕ,
        VFMidRecursiveScaleStep R S ∧
          VFMidSyntheticBadAt D K S)

/-- Every structurally owner-admissible trajectory is radially bounded.

The proof is purely logical: once a bad scale must reproduce on a strict child,
strong induction forbids a minimal bad scale. -/
theorem vfMidSyntheticRadialBounded_of_ownerEscapeAdmissible
    {D : ℕ → ℝ}
    (h : VFMidOwnerEscapeAdmissible D) :
    VFMidSyntheticRadialBounded D := by
  rcases h with ⟨K, hK0, hsmall, hdesc⟩
  exact
    vfMidSyntheticRadialBounded_of_recursiveReproduction
      D K hK0 hsmall hdesc

/-- The deliberately amplified logic adversary from the fuzzer is not a member
of the structural admissible class. Thus the class is strictly stronger than
recurrence + midpoint balance + the formal quadratic energy identity. -/
theorem not_vfMidOwnerEscapeAdmissible_logicAdversary :
    ¬ VFMidOwnerEscapeAdmissible vfMidLogicAdversaryDefect := by
  intro h
  rcases h with ⟨K, hK0, hsmall, hdesc⟩
  exact
    (vfMidLogicAdversary_reproduction_must_fail K hK0 hsmall)
      hdesc

/-- The actual square-endpoint prime defect trajectory. -/
def vfMidActualPrimeEndpointDefect (R : ℕ) : ℝ :=
  vfMidPrimeError ((R : ℝ) ^ 2)

/-- Single structural arithmetic obligation for the admissible-class route.

This statement does not assume the desired radial bound. It says only that
the honest prime defect obeys the finite-base + strict-child reproduction law
of the structural admissible class.

The intended proof must come from exact sieve/owner identities, not from an
independent estimate of the realized prime-error cancellation. -/
def VFMidActualPrimeOwnerEscapeAdmissibleStatement : Prop :=
  VFMidOwnerEscapeAdmissible vfMidActualPrimeEndpointDefect

/-- Structural admissibility of the actual prime trajectory closes the direct
square-endpoint VF von-Koch target immediately. -/
theorem vfMidSquareEndpointVonKochBounded_of_actualPrimeOwnerEscapeAdmissible
    (h : VFMidActualPrimeOwnerEscapeAdmissibleStatement) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  have hbounded :
      VFMidSyntheticRadialBounded vfMidActualPrimeEndpointDefect :=
    vfMidSyntheticRadialBounded_of_ownerEscapeAdmissible h
  rw [vfMidActualPrimeEndpointDefect] at hbounded
  exact
    vfMidActualRadialBounded_iff_squareEndpoint.mp hbounded

/-- Expanded witness form of the actual-prime admissibility statement. This is
the exact interface which the physical owner tree must discharge. -/
theorem actualPrimeOwnerEscapeAdmissible_iff_exists_recursiveReproduction :
    VFMidActualPrimeOwnerEscapeAdmissibleStatement ↔
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ R : ℕ, R < 7 →
          ¬ VFMidSyntheticBadAt
            vfMidActualPrimeEndpointDefect K R) ∧
        (∀ R : ℕ, 7 ≤ R →
          VFMidSyntheticBadAt
            vfMidActualPrimeEndpointDefect K R →
          ∃ S : ℕ,
            VFMidRecursiveScaleStep R S ∧
              VFMidSyntheticBadAt
                vfMidActualPrimeEndpointDefect K S) := by
  rfl

end RHLean.Analysis
