import Mathlib
import «research.VF_MID_DIRECT_COMPOSITE_DESCENT»

/-!
# Direct owner descent for the VF-mid discrepancy

This file stays entirely on the direct

  D_R = pi(R^2) - VF_mid(R^2)

architecture.

For one square band, every composite site has one unique least-prime owner
p <= R.  Reassembling by those owners gives an exact formula for the direct
band error

  e_R = P_R - V_R
      = 2R - V_R - sum_{p <= R prime} C_R(p),

where C_R(p) is the number of composites in the band whose least prime factor
is p.

Stripping the least-prime owner sends each owner fibre injectively to children
strictly below R^2.  If p^3 reaches the upper square, the child is already
prime.  Hence the only genuinely recursive owner fibres satisfy

  p^3 < (R+1)^2,

so the recursive owner scale is compressed from R to about R^(2/3).

No theta, psi, Li, Mertens, or asymptotic prime-distribution estimate enters
this reassembly.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- The literal sub-root prime owners available in the R-th square band. -/
def vfMidSquareBandOwnerPrimes (R : ℕ) : Finset ℕ :=
  (Finset.Icc 2 R).filter Nat.Prime

@[simp] theorem mem_vfMidSquareBandOwnerPrimes {R p : ℕ} :
    p ∈ vfMidSquareBandOwnerPrimes R ↔ p.Prime ∧ p ≤ R := by
  rw [vfMidSquareBandOwnerPrimes, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_hp2, hpR⟩, hp⟩
    exact ⟨hp, hpR⟩
  · rintro ⟨hp, hpR⟩
    exact ⟨⟨hp.two_le, hpR⟩, hp⟩

/-- Every composite in the square band maps to one of the sub-root owner
primes by its least prime factor. -/
theorem vfMidSquareBandComposite_minFac_mem_ownerPrimes
    {R n : ℕ} (hR : 2 ≤ R) (hn : n ∈ vfMidSquareBandComposites R) :
    n.minFac ∈ vfMidSquareBandOwnerPrimes R := by
  have hown : n ∈ vfMidSquareBandCompositeOwner R n.minFac := by
    exact Finset.mem_filter.mpr ⟨hn, rfl⟩
  have hdata :=
    vfMidSquareBandCompositeOwner_prime_le_root (hR := hR) hown
  exact mem_vfMidSquareBandOwnerPrimes.mpr ⟨hdata.1, hdata.2⟩

/-- **Exact owner Fubini.**  The composite population is the disjoint fibrewise
sum over its unique least-prime owners p <= R. -/
theorem vfMidSquareBandComposite_card_eq_sum_ownerCards
    (R : ℕ) (hR : 2 ≤ R) :
    (vfMidSquareBandComposites R).card =
      ∑ p ∈ vfMidSquareBandOwnerPrimes R,
        (vfMidSquareBandCompositeOwner R p).card := by
  let S : Finset ℕ := vfMidSquareBandComposites R
  let O : Finset ℕ := vfMidSquareBandOwnerPrimes R
  let owner : ℕ → ℕ := fun n => n.minFac
  have hmaps : ∀ n ∈ S, owner n ∈ O := by
    intro n hn
    exact vfMidSquareBandComposite_minFac_mem_ownerPrimes hR hn
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := S) (t := O) (g := owner) hmaps (fun _ => (1 : ℕ))
  have hraw :
      (∑ n ∈ S, (1 : ℕ)) =
        ∑ p ∈ O, ∑ n ∈ S with owner n = p, (1 : ℕ) :=
    hfiber.symm
  calc
    (vfMidSquareBandComposites R).card =
        ∑ n ∈ S, (1 : ℕ) := by
          rw [Finset.card_eq_sum_ones]
    _ = ∑ p ∈ O, ∑ n ∈ S with owner n = p, (1 : ℕ) := hraw
    _ = ∑ p ∈ vfMidSquareBandOwnerPrimes R,
          (vfMidSquareBandCompositeOwner R p).card := by
      dsimp [O, S, owner]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.card_eq_sum_ones]
      rfl

/-- **Direct owner expansion of the VF-mid band discrepancy.**

This is still exactly P_R - V_R; primality has merely been replaced by the
least-prime owner census of the complementary composites. -/
theorem vfMidSquareBandError_eq_ownerCards
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareBandError R =
      2 * (R : ℝ) - vfMidBandMass R -
        ∑ p ∈ vfMidSquareBandOwnerPrimes R,
          ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
  rw [vfMidSquareBandError_eq_compositeComplement]
  have hcard := vfMidSquareBandComposite_card_eq_sum_ownerCards R hR
  have hcardR :
      ((vfMidSquareBandComposites R).card : ℝ) =
        ∑ p ∈ vfMidSquareBandOwnerPrimes R,
          ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
    exact_mod_cast hcard
  rw [hcardR]
  ring

/-- Children obtained by stripping the least-prime owner from one composite
owner fibre. -/
def vfMidSquareBandCompositeOwnerChildren (R p : ℕ) : Finset ℕ :=
  (vfMidSquareBandCompositeOwner R p).image (fun n => n / p)

/-- Stripping a fixed owner is injective on its owner fibre. -/
theorem vfMidSquareBandCompositeOwner_child_injOn
    (R p : ℕ) :
    Set.InjOn (fun n => n / p) (vfMidSquareBandCompositeOwner R p : Set ℕ) := by
  intro a ha b hb hab
  have hma := vfMidSquareBandCompositeOwner_mul_div ha
  have hmb := vfMidSquareBandCompositeOwner_mul_div hb
  change a / p = b / p at hab
  rw [hab] at hma
  exact hma.symm.trans hmb

/-- Stripping preserves the exact cardinality of every owner fibre. -/
theorem vfMidSquareBandCompositeOwnerChildren_card
    (R p : ℕ) :
    (vfMidSquareBandCompositeOwnerChildren R p).card =
      (vfMidSquareBandCompositeOwner R p).card := by
  unfold vfMidSquareBandCompositeOwnerChildren
  exact Finset.card_image_iff.mpr
    (vfMidSquareBandCompositeOwner_child_injOn R p)

/-- Every stripped child lies strictly below the left square endpoint. -/
theorem vfMidSquareBandCompositeOwnerChildren_lt_square
    {R p m : ℕ} (hR : 3 ≤ R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    m < R ^ 2 := by
  rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
  exact vfMidSquareBandCompositeOwner_child_lt_square hR hn

/-- The direct band discrepancy reassembled entirely on descended child
populations below R^2. -/
theorem vfMidSquareBandError_eq_ownerChildren
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareBandError R =
      2 * (R : ℝ) - vfMidBandMass R -
        ∑ p ∈ vfMidSquareBandOwnerPrimes R,
          ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ) := by
  rw [vfMidSquareBandError_eq_ownerCards R hR]
  apply congrArg
    (fun x : ℝ => 2 * (R : ℝ) - vfMidBandMass R - x)
  apply Finset.sum_congr rfl
  intro p hp
  rw [vfMidSquareBandCompositeOwnerChildren_card]

/-- Owners whose stripped children are forced to be prime by the cubic
geometry. -/
def vfMidSquareBandTerminalOwners (R : ℕ) : Finset ℕ :=
  (vfMidSquareBandOwnerPrimes R).filter
    (fun p => (R + 1) ^ 2 ≤ p ^ 3)

/-- The genuinely recursive owner sector. -/
def vfMidSquareBandRecursiveOwners (R : ℕ) : Finset ℕ :=
  (vfMidSquareBandOwnerPrimes R).filter
    (fun p => p ^ 3 < (R + 1) ^ 2)

@[simp] theorem mem_vfMidSquareBandTerminalOwners {R p : ℕ} :
    p ∈ vfMidSquareBandTerminalOwners R ↔
      p ∈ vfMidSquareBandOwnerPrimes R ∧ (R + 1) ^ 2 ≤ p ^ 3 := by
  simp [vfMidSquareBandTerminalOwners]

@[simp] theorem mem_vfMidSquareBandRecursiveOwners {R p : ℕ} :
    p ∈ vfMidSquareBandRecursiveOwners R ↔
      p ∈ vfMidSquareBandOwnerPrimes R ∧ p ^ 3 < (R + 1) ^ 2 := by
  simp [vfMidSquareBandRecursiveOwners]

/-- Terminal and recursive owners partition the full sub-root owner set. -/
theorem vfMidSquareBand_terminal_recursive_partition (R : ℕ) :
    vfMidSquareBandTerminalOwners R ∪
        vfMidSquareBandRecursiveOwners R =
      vfMidSquareBandOwnerPrimes R := by
  ext p
  by_cases h : (R + 1) ^ 2 ≤ p ^ 3
  · simp [h, vfMidSquareBandTerminalOwners,
      vfMidSquareBandRecursiveOwners, Nat.not_lt.mpr h]
  · have hlt : p ^ 3 < (R + 1) ^ 2 := Nat.lt_of_not_ge h
    simp [h, hlt, vfMidSquareBandTerminalOwners,
      vfMidSquareBandRecursiveOwners]

/-- The terminal and recursive owner sectors are disjoint. -/
theorem vfMidSquareBand_terminal_recursive_disjoint (R : ℕ) :
    Disjoint (vfMidSquareBandTerminalOwners R)
      (vfMidSquareBandRecursiveOwners R) := by
  rw [Finset.disjoint_left]
  intro p hpT hpR
  have hT := (mem_vfMidSquareBandTerminalOwners.mp hpT).2
  have hR := (mem_vfMidSquareBandRecursiveOwners.mp hpR).2
  omega

/-- Every child in a terminal owner fibre is prime. -/
theorem vfMidSquareBand_terminalOwner_child_prime
    {R p m : ℕ} (hR : 2 ≤ R)
    (hp : p ∈ vfMidSquareBandTerminalOwners R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    m.Prime := by
  rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
  exact vfMidSquareBandCompositeOwner_child_prime_of_upperSquare_le_cube
    hR hn (mem_vfMidSquareBandTerminalOwners.mp hp).2

/-- **Terminal/recursive split of the direct band discrepancy.**

The first owner sum has prime children only.  Every genuinely composite child
has already been pushed into the recursive owner sector p^3 < (R+1)^2. -/
theorem vfMidSquareBandError_eq_terminal_add_recursive
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareBandError R =
      2 * (R : ℝ) - vfMidBandMass R -
        ∑ p ∈ vfMidSquareBandTerminalOwners R,
          ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ) -
        ∑ p ∈ vfMidSquareBandRecursiveOwners R,
          ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ) := by
  rw [vfMidSquareBandError_eq_ownerChildren R hR]
  have hpart := vfMidSquareBand_terminal_recursive_partition R
  have hdisj := vfMidSquareBand_terminal_recursive_disjoint R
  have hsum :
      (∑ p ∈ vfMidSquareBandOwnerPrimes R,
          ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ)) =
        (∑ p ∈ vfMidSquareBandTerminalOwners R,
            ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ)) +
          ∑ p ∈ vfMidSquareBandRecursiveOwners R,
            ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ) := by
    rw [← hpart, Finset.sum_union hdisj]
  rw [hsum]
  ring

/-- **Direct endpoint recurrence with cubic owner descent.**

This is the same exact D_(R+1)=D_R+e_R recurrence, now with e_R split into a
terminal prime-child sector and a genuinely recursive owner sector compressed
by p^3 < (R+1)^2. -/
theorem vfMidSquareEndpointError_succ_eq_ownerDescent
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareEndpointError (R + 1) =
      vfMidSquareEndpointError R +
        (2 * (R : ℝ) - vfMidBandMass R -
          ∑ p ∈ vfMidSquareBandTerminalOwners R,
            ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ) -
          ∑ p ∈ vfMidSquareBandRecursiveOwners R,
            ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ)) := by
  rw [vfMidSquareEndpointError_succ R hR,
    vfMidSquareBandError_eq_terminal_add_recursive R hR]

end RHLean.Analysis
