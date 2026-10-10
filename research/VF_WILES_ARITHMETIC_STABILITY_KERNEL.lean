import Mathlib

/-!
# Wiles-style arithmetic owner stability: independent finite kernel

This Mathlib-only module proves a genuinely universal finite statement about
occurrence-preserving signed transport. Its class is defined by a local,
weight-preserving involution on individual occurrences, *not* by a global
prime-count error bound, a first-bad inequality, or an assumption of RH.

The local sector law is f(z) = 4*z - 2*|z|. A return involution preserves the
finite source carrier and reverses the exact signed, masked amplitude.
Consequently the FULL signed sum is nonpositive. Additional dissipative
sinks contribute negative squares. This is the elementary generic theorem,
not an assertion that the ACTUAL VF owner packet admits such a completion.

The open arithmetic problem is a term-by-term identification of the original
VF first-bad source plus its SIX genuinely clipped boundary sectors with a
packet of this kind. In particular, a fitted scalar sum-of-squares equality,
a future owner return, a repeated historical parent charge, or an arbitrary
new sink is NOT an acceptable arithmetic realization.

See VF_WILES_ARITHMETIC_STABILITY_PROOF_CONTRACT.md.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- The original signed local sign-reversal law, before summing over sites. -/
def vfWilesLocalSector (z : ℝ) : ℝ :=
  4 * z - 2 * |z|

theorem vfWilesLocalSector_mirror (z : ℝ) :
    vfWilesLocalSector z + vfWilesLocalSector (-z) = -4 * |z| := by
  unfold vfWilesLocalSector
  rw [abs_neg]
  ring

/-- A purely finite, independently specified arithmetic-combinatorial class.

The data consist of actual *occurrences* (not distinct owner values), an
involutive return on the SAME finite carrier, and antisymmetry of the signed
amplitude. Multiplicities, masks, and physical weights must be encoded in
the occurrence index and amplitude BEFORE a packet is constructed.

This is deliberately restrictive. The actual six-sector source has not
been proved to lie in this class; its raw boundary cells may demand a more
general Gram or spectral completion rather than literal involutive pairing.
-/
structure VFWilesReversibleCells (α : Type*) [DecidableEq α] where
  sites : Finset α
  mirror : α → α
  mirror_mem : ∀ i ∈ sites, mirror i ∈ sites
  mirror_involutive : ∀ i ∈ sites, mirror (mirror i) = i
  amplitude : α → ℝ
  amplitude_neg : ∀ i ∈ sites, amplitude (mirror i) = -amplitude i

/-- Exact occurrence-preserving reindexing under the involution. This is a
genuine finite Fubini/permutation identity, not a cancellation estimate. -/
theorem vfWilesReversibleCells_sum_mirror
    {α : Type*} [DecidableEq α] (c : VFWilesReversibleCells α) :
    (∑ i ∈ c.sites, c.amplitude (c.mirror i)) =
      ∑ i ∈ c.sites, c.amplitude i := by
  classical
  refine Finset.sum_bij (fun i _hi => c.mirror i) ?_ ?_ ?_ ?_
  · intro i hi
    exact c.mirror_mem i hi
  · intro i hi j hj h
    have h' := congrArg c.mirror h
    simpa [c.mirror_involutive i hi,
      c.mirror_involutive j hj] using h'
  · intro j hj
    exact ⟨c.mirror j, c.mirror_mem j hj,
      c.mirror_involutive j hj⟩
  · intro i _hi
    rfl

/-- The signed amplitude cancels on a closed, anti-phase finite orbit
system. There is no pointwise absolute-value bound here. -/
theorem vfWilesReversibleCells_amplitude_sum_zero
    {α : Type*} [DecidableEq α] (c : VFWilesReversibleCells α) :
    (∑ i ∈ c.sites, c.amplitude i) = 0 := by
  have hperm := vfWilesReversibleCells_sum_mirror c
  have hsign :
      (∑ i ∈ c.sites, c.amplitude (c.mirror i)) =
        -(∑ i ∈ c.sites, c.amplitude i) := by
    calc
      (∑ i ∈ c.sites, c.amplitude (c.mirror i)) =
          ∑ i ∈ c.sites, -(c.amplitude i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact c.amplitude_neg i hi
      _ = -(∑ i ∈ c.sites, c.amplitude i) := by
        simp
  linarith

/-- The genuine signed packet, not its unsigned or squared replacement. -/
def vfWilesReversibleSector
    {α : Type*} [DecidableEq α] (c : VFWilesReversibleCells α) : ℝ :=
  ∑ i ∈ c.sites, vfWilesLocalSector (c.amplitude i)

/-- Universal cancellation for ANY closed weighted anti-phase occurrence
system. The direction is forced by the local formula plus reindexing. -/
theorem vfWilesReversibleSector_eq_negative_absolute
    {α : Type*} [DecidableEq α] (c : VFWilesReversibleCells α) :
    vfWilesReversibleSector c =
      -2 * (∑ i ∈ c.sites, |c.amplitude i|) := by
  unfold vfWilesReversibleSector vfWilesLocalSector
  calc
    (∑ i ∈ c.sites, (4 * c.amplitude i - 2 * |c.amplitude i|)) =
        4 * (∑ i ∈ c.sites, c.amplitude i) -
          2 * (∑ i ∈ c.sites, |c.amplitude i|) := by
            simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = -2 * (∑ i ∈ c.sites, |c.amplitude i|) := by
          rw [vfWilesReversibleCells_amplitude_sum_zero c]
          ring

theorem vfWilesReversibleSector_nonpos
    {α : Type*} [DecidableEq α] (c : VFWilesReversibleCells α) :
    vfWilesReversibleSector c ≤ 0 := by
  rw [vfWilesReversibleSector_eq_negative_absolute]
  have hsum : 0 ≤ ∑ i ∈ c.sites, |c.amplitude i| := by
    apply Finset.sum_nonneg
    intro i _hi
    exact abs_nonneg _
  linarith

/-- The exact condition under which a physical zero mask is allowed to
commute with the return map. It is NOT automatic for OAI/Hecke tuple masks;
that compatibility is part of the open actual-arithmetic bridge. -/
def vfWilesSymmetricMask
    {α : Type*} [DecidableEq α]
    (c : VFWilesReversibleCells α)
    (keep : α → Prop) [DecidablePred keep]
    (hkeep : ∀ i ∈ c.sites, keep (c.mirror i) ↔ keep i) :
    VFWilesReversibleCells α where
  sites := c.sites
  mirror := c.mirror
  mirror_mem := c.mirror_mem
  mirror_involutive := c.mirror_involutive
  amplitude := fun i => if keep i then c.amplitude i else 0
  amplitude_neg := by
    intro i hi
    by_cases hk : keep i
    · have hm : keep (c.mirror i) := (hkeep i hi).mpr hk
      simp [hk, hm, c.amplitude_neg i hi]
    · have hm : ¬keep (c.mirror i) := by
        intro him
        exact hk ((hkeep i hi).mp him)
      simp [hk, hm]

/-- A mirror-invariant zero mask preserves finite signed packet stability,
with all physical coefficients kept on their original occurrences. -/
theorem vfWilesSymmetricMask_stable
    {α : Type*} [DecidableEq α]
    (c : VFWilesReversibleCells α)
    (keep : α → Prop) [DecidablePred keep]
    (hkeep : ∀ i ∈ c.sites, keep (c.mirror i) ↔ keep i) :
    vfWilesReversibleSector (vfWilesSymmetricMask c keep hkeep) ≤ 0 :=
  vfWilesReversibleSector_nonpos _

/-- A zero mask alone never increases the ordinary finite quadratic norm.
Unlike the signed sector theorem, this fact does not require mask symmetry;
it also does not give a SIGNED mixed owner-child estimate. -/
theorem vfWilesZeroMaskEnergy_le_original
    {α : Type*} (s : Finset α)
    (keep : α → Prop) [DecidablePred keep]
    (u : α → ℝ) :
    (∑ i ∈ s, (if keep i then u i else 0) ^ 2) ≤
      ∑ i ∈ s, (u i) ^ 2 := by
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hk : keep i
  · simp [hk]
  · simp [hk]
    positivity

/-- Independent negative-square sinks: their membership and signed weights
must also be established from real historical arithmetic, without fitting a
new square root to the aggregate first-bad excess. -/
def vfWilesDissipation
    {β : Type*} (sinks : Finset β) (amplitude : β → ℝ) : ℝ :=
  ∑ j ∈ sinks, (amplitude j) ^ 2

theorem vfWilesDissipation_nonneg
    {β : Type*} (sinks : Finset β) (amplitude : β → ℝ) :
    0 ≤ vfWilesDissipation sinks amplitude := by
  unfold vfWilesDissipation
  apply Finset.sum_nonneg
  intro j _hj
  positivity

/-- The universal signed stability theorem for the independent finite class.

This theorem makes NO reference to pi, Li, VF, a first-bad premise, or RH.
It follows from an occurrence pairing and nonnegative square energies.
-/
theorem vfWilesUniversalArithmeticPacketStability
    {α β : Type*} [DecidableEq α]
    (c : VFWilesReversibleCells α)
    (sinks : Finset β) (dissipationAmplitude : β → ℝ) :
    vfWilesReversibleSector c -
      vfWilesDissipation sinks dissipationAmplitude ≤ 0 := by
  have hpair := vfWilesReversibleSector_nonpos c
  have hsink := vfWilesDissipation_nonneg sinks dissipationAmplitude
  linarith

/-- Abstract Ribet-style trap: a POSITIVE physical first-bad ledger cannot
simultaneously have an occurrence-level representation by the class above.

The hypothesis hrepresentation is the major OPEN source-to-boundary arithmetic
identification. It must be established from real owner incidence, NOT by
postulating the inequality to be proved. -/
theorem vfWilesFirstBadContradiction_of_arithmeticRepresentation
    {α β : Type*} [DecidableEq α]
    (c : VFWilesReversibleCells α)
    (sinks : Finset β) (dissipationAmplitude : β → ℝ)
    (nativeSixSectorBudget : ℝ)
    (hfirstBadObstruction : 0 < nativeSixSectorBudget)
    (hrepresentation :
      nativeSixSectorBudget =
        vfWilesReversibleSector c -
          vfWilesDissipation sinks dissipationAmplitude) :
    False := by
  have hstable :=
    vfWilesUniversalArithmeticPacketStability c sinks dissipationAmplitude
  linarith

/-- Countercheck: unsigned or unpaired source atoms are NOT automatically
dissipative. This excludes an illicit universal all-state stability claim. -/
theorem vfWilesUnpairedCell_canBePositive :
    0 < vfWilesLocalSector (1 : ℝ) := by
  norm_num [vfWilesLocalSector]

/-- Countercheck against treating the OAI difference-of-rows polarization
as a sign estimate: opposed rows have POSITIVE signed interaction. -/
theorem vfWilesOpposedRows_canHavePositiveGram :
    0 < ((1 : ℝ) - (-1)) ^ 2 - (1 : ℝ) ^ 2 - (-1 : ℝ) ^ 2 := by
  norm_num

end RHLean.Analysis
