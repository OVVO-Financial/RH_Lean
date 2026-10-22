import Mathlib
import «research.VF_919_NNS_LOW_HIGH_GATE_SPARSE_EXTENSION_20261021»

/-!
# Source-faithful finite admission and rational norm-fiber gate bridge

This is a NEW FINITE theorem on original labelled columns. It does NOT
identify OpenAI's physical source with a particular finite carrier: that
identification must be supplied and checked separately, especially in
the presence of multiple prime slots, ideal multiplicity, inert prime
ideals, row characters, conductor masks, and rescaled theta windows.

Mathematical content:
* two independent branch admission predicates partition the source into
  mutual, marked-only, rescaled-only (and absent) faces;
* already-signed full complex coefficients are retained, including the
  actual minus sign of the rescaled branch;
* the Hermitian cross energy is not discarded;
* the rational norm projection is a real FINITE MAP and its fiber sums
  are proved equal to the original column sum;
* the two Cauchy-Schwarz stages are PROVED, not assumed;
* the canonical low gate count from SignedCanonicalHeight is used ONLY
  when every projected rational pair meets its hypotheses.

No new bound on the high-height part, nor an OAI inverse/plain-moment
estimate, nor a 7/8 improvement, nor RH is claimed.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Proof
namespace CompensatedBoundaryCorrespondence

/-! ## One source, two independent branch masks -/

variable {ι : Type*}

def mutualFace (S : Finset ι) (M R : ι → Prop) : Finset ι :=
  S.filter (fun a => M a ∧ R a)

def markedOnlyFace (S : Finset ι) (M R : ι → Prop) : Finset ι :=
  S.filter (fun a => M a ∧ ¬ R a)

def rescaledOnlyFace (S : Finset ι) (M R : ι → Prop) : Finset ι :=
  S.filter (fun a => ¬ M a ∧ R a)

/-- The complex rescaled coefficient must ALREADY include its Euler
minus sign, power of the selected prime norm and Hecke phase. -/
def fullRowSource (S : Finset ι) (M R : ι → Prop)
    (marked rescaledSigned : ι → ℂ) : ℂ :=
  ∑ a ∈ S, ((if M a then marked a else 0) +
            (if R a then rescaledSigned a else 0))

def mutualRowSource (S : Finset ι) (M R : ι → Prop)
    (marked rescaledSigned : ι → ℂ) : ℂ :=
  ∑ a ∈ mutualFace S M R, (marked a + rescaledSigned a)

def unmatchedRowSource (S : Finset ι) (M R : ι → Prop)
    (marked rescaledSigned : ι → ℂ) : ℂ :=
  (∑ a ∈ markedOnlyFace S M R, marked a) +
    (∑ a ∈ rescaledOnlyFace S M R, rescaledSigned a)

/-- EXACT row source decomposition. No equality of masks or weights
has been assumed; the rescaled branch enters with its original sign. -/
theorem fullRowSource_eq_mutual_add_unmatched
    (S : Finset ι) (M R : ι → Prop)
    (marked rescaledSigned : ι → ℂ) :
    fullRowSource S M R marked rescaledSigned =
      mutualRowSource S M R marked rescaledSigned +
      unmatchedRowSource S M R marked rescaledSigned := by
  classical
  unfold fullRowSource mutualRowSource unmatchedRowSource
    mutualFace markedOnlyFace rescaledOnlyFace
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hm : M a <;> by_cases hr : R a <;>
    simp [hm, hr]

/-! ## Exact Hermitian row and detector Gram -/

theorem normSq_mutual_add_unmatched (A B : ℂ) :
    Complex.normSq (A + B) =
      Complex.normSq A + Complex.normSq B +
        2 * (A.re * B.re + A.im * B.im) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

theorem detectorEnergy_eq_mutual_boundary_Gram
    {ρ : Type*} (rows : Finset ρ) (D : ℝ)
    (A B : ρ → ℂ) :
    D⁻¹ * (∑ u ∈ rows, Complex.normSq (A u + B u)) =
      D⁻¹ * ∑ u ∈ rows,
        (Complex.normSq (A u) + Complex.normSq (B u) +
          2 * ((A u).re * (B u).re + (A u).im * (B u).im)) := by
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  exact normSq_mutual_add_unmatched (A u) (B u)

/-! ## Unconditional norm-fiber grouping: no aliasing of ideal labels -/

/-- Caution: inert prime ideals can have composite rational norm q=p^2,
but the pure factor-pair count can STILL apply. This example has
q=4, c=3, m=12, n=3, and Z=7/2 <=4. It does NOT license a
largest-rational-prime or Mobius-sign interpretation. -/
theorem compositePrimeNorm_geometric_gate_example :
    SignedHeight.Admissible 3 4 3 1 := by
  norm_num [SignedHeight.Admissible]

/-- The disjoint fibers of an ACTUAL finite map reassemble the original
labelled source exactly. This records multiplicity rather than collapsing
distinct ideal occurrences sharing one rational norm pair. -/
theorem sum_over_norm_fibers
    {α β γ : Type*} [AddCommMonoid γ]
    (S : Finset α) (f : α → β) (g : α → γ) :
    (∑ p ∈ S.image f, ∑ a ∈ S.filter (fun a => f a = p), g a) =
      ∑ a ∈ S, g a := by
  classical
  calc
    (∑ p ∈ S.image f, ∑ a ∈ S.filter (fun a => f a = p), g a) =
        ∑ p ∈ S.image f, ∑ a ∈ S, if f a = p then g a else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_filter]
    _ = ∑ a ∈ S, ∑ p ∈ S.image f,
           if f a = p then g a else 0 := by rw [Finset.sum_comm]
    _ = ∑ a ∈ S, g a := by
      apply Finset.sum_congr rfl
      intro a ha
      have hmem : f a ∈ S.image f := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simp [eq_comm, hmem]

/-- Finite Cauchy-Schwarz, proven without a statistical assumption. -/
theorem finiteComplex_energy_le
    {α : Type*} (S : Finset α) (z : α → ℂ) :
    ‖∑ a ∈ S, z a‖ ^ 2 ≤
      (S.card : ℝ) * ∑ a ∈ S, ‖z a‖ ^ 2 := by
  have hnorm : ‖∑ a ∈ S, z a‖ ≤ ∑ a ∈ S, ‖z a‖ :=
    norm_sum_le _ _
  have hsum : 0 ≤ ∑ a ∈ S, ‖z a‖ :=
    Finset.sum_nonneg (fun a ha => norm_nonneg (z a))
  have hfac : 0 ≤
      ((∑ a ∈ S, ‖z a‖) - ‖∑ a ∈ S, z a‖) *
      ((∑ a ∈ S, ‖z a‖) + ‖∑ a ∈ S, z a‖) :=
    mul_nonneg (sub_nonneg.mpr hnorm)
      (add_nonneg hsum (norm_nonneg _))
  have hsq : ‖∑ a ∈ S, z a‖ ^ 2 ≤
      (∑ a ∈ S, ‖z a‖) ^ 2 := by nlinarith [hfac]
  have hCS :
      (∑ a ∈ S, ‖z a‖) ^ 2 ≤
      (S.card : ℝ) * ∑ a ∈ S, ‖z a‖ ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq S
        (fun _ => (1 : ℝ)) (fun a => ‖z a‖))
  exact hsq.trans hCS

/-- TWO STAGES OF CAUCHY-SCHWARZ, BOTH DERIVED.

The finite index alpha can be a fully labelled prime/cofactor ideal pair,
with all original marked/rescaled tuple and phase labels retained.
The map f returns an ordered positive integer factor-pair (c,d),
q=c+d. The SignedHeight counting theorem is PURE GEOMETRY: q need
not be a rational prime. A Möbius largest-prime interpretation requires
separate proofs of q=P_plus(c*q), squarefreeness and the sign flip.

The visible admission hypothesis demands exactly the hypotheses of
SignedHeight.card_le, rather than inventing an identification with
an inert prime ideal of norm p^2 or an arbitrary OAI column.

The fiber multiplicity is its ACTUAL CARDINALITY, not an assumed
2*tau(c) bound. No independent randomness or weight restriction. -/
theorem normFiber_lowGate_bridge_unconditional
    {α : Type*} {n H : ℕ} (hn : 1 ≤ n)
    (S : Finset α) (f : α → ℕ × ℕ) (z : α → ℂ)
    (hCanon : ∀ a ∈ S,
       SignedHeight.Admissible n H (f a).1 (f a).2) :
    ‖∑ a ∈ S, z a‖ ^ 2 ≤
      ((H / n + 1 : ℕ) : ℝ) *
        ∑ p ∈ S.image f,
          ((S.filter (fun a => f a = p)).card : ℝ) *
            ∑ a ∈ S.filter (fun a => f a = p), ‖z a‖ ^ 2 := by
  classical
  let L : Finset (ℕ × ℕ) := S.image f
  let packet : (ℕ × ℕ) → ℂ :=
    fun p => ∑ a ∈ S.filter (fun a => f a = p), z a
  have hL : ∀ p ∈ L, SignedHeight.Admissible n H p.1 p.2 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
    exact hCanon a ha
  have hLow := NNSLowHighGateExtension.weightedCanonicalLow_energy_le
    hn L hL packet
  have hFiber (p : ℕ × ℕ) :
      ‖packet p‖ ^ 2 ≤
        ((S.filter (fun a => f a = p)).card : ℝ) *
          ∑ a ∈ S.filter (fun a => f a = p), ‖z a‖ ^ 2 := by
    exact finiteComplex_energy_le _ _
  have hSum :
      (∑ p ∈ L, ‖packet p‖ ^ 2) ≤
        ∑ p ∈ L,
          ((S.filter (fun a => f a = p)).card : ℝ) *
            ∑ a ∈ S.filter (fun a => f a = p), ‖z a‖ ^ 2 :=
    Finset.sum_le_sum (fun p hp => hFiber p)
  have hC : 0 ≤ ((H / n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hTop := mul_le_mul_of_nonneg_left hSum hC
  have hgroup : (∑ p ∈ L, packet p) = ∑ a ∈ S, z a := by
    dsimp [L, packet]
    calc
      (∑ p ∈ S.image f, ∑ a ∈ S.filter (fun a => f a = p), z a) =
          ∑ p ∈ S.image f, ∑ a ∈ S,
            if f a = p then z a else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_filter]
      _ = ∑ a ∈ S, ∑ p ∈ S.image f,
            if f a = p then z a else 0 := by rw [Finset.sum_comm]
      _ = ∑ a ∈ S, z a := by
        apply Finset.sum_congr rfl
        intro a ha
        have hmem : f a ∈ S.image f :=
          Finset.mem_image.mpr ⟨a, ha, rfl⟩
        simp [eq_comm, hmem]
  calc
    ‖∑ a ∈ S, z a‖ ^ 2 =
        ‖∑ p ∈ L, packet p‖ ^ 2 := by rw [hgroup]
    _ ≤ ((H / n + 1 : ℕ) : ℝ) *
        ∑ p ∈ L, ‖packet p‖ ^ 2 := hLow
    _ ≤ ((H / n + 1 : ℕ) : ℝ) *
        ∑ p ∈ L,
          ((S.filter (fun a => f a = p)).card : ℝ) *
            ∑ a ∈ S.filter (fun a => f a = p), ‖z a‖ ^ 2 := hTop

end CompensatedBoundaryCorrespondence
end RHLean.Proof

#print axioms RHLean.Proof.CompensatedBoundaryCorrespondence.fullRowSource_eq_mutual_add_unmatched
#print axioms RHLean.Proof.CompensatedBoundaryCorrespondence.normSq_mutual_add_unmatched
#print axioms RHLean.Proof.CompensatedBoundaryCorrespondence.detectorEnergy_eq_mutual_boundary_Gram
#print axioms RHLean.Proof.CompensatedBoundaryCorrespondence.sum_over_norm_fibers
#print axioms RHLean.Proof.CompensatedBoundaryCorrespondence.finiteComplex_energy_le
#print axioms RHLean.Proof.CompensatedBoundaryCorrespondence.normFiber_lowGate_bridge_unconditional
