import Mathlib
import «research.GLOBAL_RETURNED_CORE_ARBITRARY_PRIME_FILTRATION»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION»
import «research.GLOBAL_RETURNED_CORE_DESCENDING_PAIR_OWNER»

/-!
# Signed Dirichlet polarization under arbitrary revealed-prime filtration

The carrier partition in `GLOBAL_RETURNED_CORE_ARBITRARY_PRIME_FILTRATION` is
independent of the site weight.  This file exposes that fact explicitly and then
instantiates it with the three Dirichlet coordinates of one first-owner cell.

For an arbitrary signed site `v`, revealing a fresh prime `r` gives the exact
quadratic identity

  E_v(S) = E_v(insert r S) + Cross_v(S,r).

Applying this simultaneously to incidence, base, and returned-child sites gives
an exact signed polarization filtration

  PiEnergy(S) = PiEnergy(insert r S) + PiCross(S,r).

This is the aggregate same-branch identity needed before any `2/9` estimate:
`PiEnergy(insert r S)` is the entire same-branch survivor, not an error term.
No square, absolute value, or contraction is introduced here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Revealed-signature pair mass for an arbitrary signed site. -/
def lowOwnerRevealedPairMassWith
    (R : ℕ) (S : Finset ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ mn ∈ lowOwnerRevealedPairCarrier R S,
    v mn.1 * v mn.2

/-- Fresh-coordinate crossing mass for an arbitrary signed site. -/
def lowOwnerRevealedCrossPairMassWith
    (R : ℕ) (S : Finset ℕ) (r : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ mn ∈ lowOwnerRevealedCrossPairCarrier R S r,
    v mn.1 * v mn.2

/-- **Weight-independent one-coordinate quadratic telescope.** -/
theorem lowOwnerRevealedPairMassWith_eq_insert_add_cross
    {R r : ℕ} {S : Finset ℕ}
    (hr : r.Prime) (hrS : r ∉ S) (v : ℕ → ℝ) :
    lowOwnerRevealedPairMassWith R S v =
      lowOwnerRevealedPairMassWith R (insert r S) v +
        lowOwnerRevealedCrossPairMassWith R S r v := by
  unfold lowOwnerRevealedPairMassWith lowOwnerRevealedCrossPairMassWith
  rw [lowOwnerRevealedPairCarrier_eq_sameBranch_union_cross,
    Finset.sum_union (lowOwnerRevealedSameBranch_disjoint_cross R S r),
    lowOwnerRevealedPairCarrier_insert_eq_sameBranch hr hrS]

/-- Restrict an arbitrary signed site to one full p-free lower-signature base
cell.  Zero extension lets the global revealed-pair carrier perform exact cell
Fubini without changing the carrier theorem. -/
def lowOwnerFirstOwnerCellRestrictedSite
    (R p : ℕ) (sig : Finset ℕ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n ∈ lowOwnerFirstOwnerBaseFiber R p sig then v n else 0

/-- Cell-restricted incidence site. -/
def lowOwnerFirstOwnerCellIncidenceSite
    (R p : ℕ) (sig : Finset ℕ) : ℕ → ℝ :=
  lowOwnerFirstOwnerCellRestrictedSite R p sig
    (lowOwnerFirstOwnerDirichletIncidenceSite R p)

/-- Cell-restricted base site. -/
def lowOwnerFirstOwnerCellBaseSite
    (R p : ℕ) (sig : Finset ℕ) : ℕ → ℝ :=
  lowOwnerFirstOwnerCellRestrictedSite R p sig
    (lowOwnerFirstOwnerDirichletBaseSite R)

/-- Cell-restricted returned-child site. -/
def lowOwnerFirstOwnerCellReturnedSite
    (R p : ℕ) (sig : Finset ℕ) : ℕ → ℝ :=
  lowOwnerFirstOwnerCellRestrictedSite R p sig
    (lowOwnerFirstOwnerDirichletReturnedChildSite R p)

/-- Signed polarization energy surviving the revealed coordinate set `S` inside
one first-owner cell. -/
def lowOwnerFirstOwnerRevealedPolarizationEnergy
    (R p : ℕ) (sig S : Finset ℕ) : ℝ :=
  lowOwnerRevealedPairMassWith R S
      (lowOwnerFirstOwnerCellIncidenceSite R p sig) -
    lowOwnerRevealedPairMassWith R S
      (lowOwnerFirstOwnerCellBaseSite R p sig) -
    lowOwnerRevealedPairMassWith R S
      (lowOwnerFirstOwnerCellReturnedSite R p sig)

/-- Signed polarization mass crossing one newly revealed owner coordinate. -/
def lowOwnerFirstOwnerRevealedPolarizationCrossMass
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) : ℝ :=
  lowOwnerRevealedCrossPairMassWith R S r
      (lowOwnerFirstOwnerCellIncidenceSite R p sig) -
    lowOwnerRevealedCrossPairMassWith R S r
      (lowOwnerFirstOwnerCellBaseSite R p sig) -
    lowOwnerRevealedCrossPairMassWith R S r
      (lowOwnerFirstOwnerCellReturnedSite R p sig)

/-- **Aggregate same-branch signed-cancellation identity.**

The two branch energies are not bounded separately.  Revealing `r` transports
the whole signed polarization to the surviving same-branch ledger at
`insert r S`; the only removed term is the signed r-crossing packet. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_eq_insert_add_cross
    {R p r : ℕ} {sig S : Finset ℕ}
    (hr : r.Prime) (hrS : r ∉ S) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig S =
      lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig (insert r S) +
        lowOwnerFirstOwnerRevealedPolarizationCrossMass R p sig S r := by
  unfold lowOwnerFirstOwnerRevealedPolarizationEnergy
    lowOwnerFirstOwnerRevealedPolarizationCrossMass
  rw [lowOwnerRevealedPairMassWith_eq_insert_add_cross
      hr hrS (lowOwnerFirstOwnerCellIncidenceSite R p sig),
    lowOwnerRevealedPairMassWith_eq_insert_add_cross
      hr hrS (lowOwnerFirstOwnerCellBaseSite R p sig),
    lowOwnerRevealedPairMassWith_eq_insert_add_cross
      hr hrS (lowOwnerFirstOwnerCellReturnedSite R p sig)]
  ring

/-- The current owner is not already in the strictly-larger revealed set. -/
theorem owner_not_mem_lowOwnerRevealedPrimesAbove
    (R r : ℕ) : r ∉ lowOwnerRevealedPrimesAbove R r := by
  simp [lowOwnerRevealedPrimesAbove]

/-- **Descending greatest-owner step.**  With every larger prime already
revealed, the exact same-branch survivor is obtained by inserting the current
owner `r`; the crossing term is precisely the greatest-fresh-owner packet. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_step
    {R p r : ℕ} {sig : Finset ℕ}
    (hr : r.Prime) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
          (insert r (lowOwnerRevealedPrimesAbove R r)) +
        lowOwnerFirstOwnerRevealedPolarizationCrossMass R p sig
          (lowOwnerRevealedPrimesAbove R r) r := by
  exact lowOwnerFirstOwnerRevealedPolarizationEnergy_eq_insert_add_cross
    hr (owner_not_mem_lowOwnerRevealedPrimesAbove R r)

end RHLean.Proof
