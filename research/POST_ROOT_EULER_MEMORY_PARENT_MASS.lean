import Mathlib
import RHLean.Proof.PostRootPartnerEulerMemory

/-!
# Euler memory is exactly the current parent raw mass

The post-root memory law says that changing from the raw zero-factor update to
the cofactor-weighted reciprocal Euler update retains a `(1 - 1/p)` fraction of
the signed raw boundary on a complete prefix.

Before using completeness, the next-state difference has an even more concrete
form.  The two updates have the same survivor mass after the exact
raw-to-reciprocal coordinate change.  Their only difference is on the current
fresh-prime parents: the raw update gives those retained parents coefficient
zero, while the reciprocal update gives them the Euler coefficient
`1 - 1/p`.

Hence, for every evolved carrier (no completeness needed),

  EulerNext - RawNext
    = (1 - 1/p) * sum_{current parents} rawParentAmplitude.

This identifies the precise signed packet that must be reassembled with the
q^2 daughter column in the amplitude-first proof.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Raw amplitude carried by the current fresh-prime parent fibre of one evolved
zero-factor state. -/
def evolvedFreshPrimeRawParentMass
    (R p : ℕ) (qs : List ℕ) : ℂ :=
  let U0 := Finset.Icc 1 (squareRootEndpoint R)
  let U := squareRootCanonicalRoughAdaptiveCarrier qs U0
  let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
    (fun _ => (1 : ℂ))
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    a c * squareRootCanonicalRoughRawCorrelationSummand R c

/-- **Exact parent-mass form of Euler memory.**  The weighted reciprocal and raw
next states differ only on current parents; survivor amplitudes agree exactly
under the cofactor-weighted coordinate change. -/
theorem evolvedEulerNext_sub_rawNext_eq_eulerFactor_mul_parentMass
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hp : p.Prime) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier qs U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
      (fun _ => (1 : ℂ))
    let b := fun n : ℕ => (n : ℂ) * a n
    let nextU := squareRootCanonicalRoughAdaptiveNextCarrier p U
    squareRootCanonicalRoughAdaptiveWeightedMass R nextU
          (squareRootCanonicalRoughAdaptiveNextCoefficient p U b) -
        squareRootCanonicalRoughAdaptiveRawWeightedMass R nextU
          (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a) =
      (canonicalRoughEulerFactor p : ℂ) *
        evolvedFreshPrimeRawParentMass R p qs := by
  dsimp [evolvedFreshPrimeRawParentMass]
  let U0 : Finset ℕ := Finset.Icc 1 (squareRootEndpoint R)
  let U : Finset ℕ := squareRootCanonicalRoughAdaptiveCarrier qs U0
  let a : ℕ → ℂ := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
    (fun _ => (1 : ℂ))
  let b : ℕ → ℂ := fun n => (n : ℂ) * a n
  let parents := squareRootCanonicalRoughFreshPrimeParentsOn p U
  let survivors := squareRootCanonicalRoughFreshPrimeSurvivorsOn p U
  let nextU := squareRootCanonicalRoughAdaptiveNextCarrier p U

  have hweighted := adaptiveNext_weightedMass_eq_eulerParents_add_survivors
    R U b hp
  change squareRootCanonicalRoughAdaptiveWeightedMass R nextU
      (squareRootCanonicalRoughAdaptiveNextCoefficient p U b) =
    (canonicalRoughEulerFactor p : ℂ) *
      (∑ c ∈ parents,
        b c * squareRootCanonicalRoughCorrelationReciprocalSummand R c) +
      ∑ n ∈ survivors,
        b n * squareRootCanonicalRoughCorrelationReciprocalSummand R n at hweighted

  have hraw := adaptiveRawNext_weightedMass_eq_survivors R U a hp
  change squareRootCanonicalRoughAdaptiveRawWeightedMass R nextU
      (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a) =
    ∑ n ∈ survivors,
      a n * squareRootCanonicalRoughRawCorrelationSummand R n at hraw

  have hparentCoord :
      (∑ c ∈ parents,
        b c * squareRootCanonicalRoughCorrelationReciprocalSummand R c) =
      ∑ c ∈ parents,
        a c * squareRootCanonicalRoughRawCorrelationSummand R c := by
    apply Finset.sum_congr rfl
    intro c hc
    have hcParent : c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U := hc
    rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
      ⟨_hcU, hcpos, _hcrough, _hchild⟩
    dsimp [b]
    unfold squareRootCanonicalRoughRawCorrelationSummand
    calc
      (c : ℂ) * a c *
          squareRootCanonicalRoughCorrelationReciprocalSummand R c =
        a c * ((c : ℂ) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R c) := by ring
      _ = a c *
          (canonicalMoebiusWeight c *
            squareRootCanonicalRoughCofactorResponse R c) := by
        rw [natCast_mul_squareRootCanonicalRoughCorrelationReciprocalSummand
          R hcpos]

  have hsurvivorCoord :
      (∑ n ∈ survivors,
        b n * squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      ∑ n ∈ survivors,
        a n * squareRootCanonicalRoughRawCorrelationSummand R n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnU : n ∈ U := (Finset.mem_sdiff.mp hn).1
    have hnU0 : n ∈ U0 :=
      squareRootCanonicalRoughAdaptiveCarrier_subset qs U0 hnU
    have hnRange := Finset.mem_Icc.mp hnU0
    have hnpos : 0 < n := by omega
    dsimp [b]
    unfold squareRootCanonicalRoughRawCorrelationSummand
    calc
      (n : ℂ) * a n *
          squareRootCanonicalRoughCorrelationReciprocalSummand R n =
        a n * ((n : ℂ) *
          squareRootCanonicalRoughCorrelationReciprocalSummand R n) := by ring
      _ = a n *
          (canonicalMoebiusWeight n *
            squareRootCanonicalRoughCofactorResponse R n) := by
        rw [natCast_mul_squareRootCanonicalRoughCorrelationReciprocalSummand
          R hnpos]

  rw [hweighted, hraw, hparentCoord, hsurvivorCoord]
  ring

/-- On a complete descending prefix, the same parent mass equals the signed raw
boundary itself.  This follows by comparing the parent-mass identity above with
the already-compiled Euler memory law; the formulation deliberately keeps the
Euler factor visible rather than cancelling it. -/
theorem eulerFactor_mul_evolvedFreshPrimeRawParentMass_eq_eulerFactor_mul_boundary
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    (canonicalRoughEulerFactor p : ℂ) *
        evolvedFreshPrimeRawParentMass R p qs =
      (1 - (1 : ℂ) / (p : ℂ)) *
        (let U0 := Finset.Icc 1 (squareRootEndpoint R)
         let U := squareRootCanonicalRoughAdaptiveCarrier qs U0
         let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
           (fun _ => (1 : ℂ))
         squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a) := by
  have hparent :=
    evolvedEulerNext_sub_rawNext_eq_eulerFactor_mul_parentMass
      R qs hp
  have hmemory :=
    evolvedEulerNext_sub_rawNext_eq_one_sub_inv_mul_boundary
      R qs hR hp hcomplete
  dsimp at hparent hmemory ⊢
  rw [← hparent]
  exact hmemory

end RHLean.Proof
