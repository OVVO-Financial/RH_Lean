import Mathlib
import RHLean.Proof.StableFarRenewalDyadicTwoShell

/-!
# Production global boundary for the centered stable-far renewal

The full returned-fibre theorem in StableFarRenewalDyadicTwoShell pairs the
actual centered renewal under e -> 2*e. Its owner-difference part is indexed
by odd parent cofactors and, after the owner-two fibre is separated, by returned
owners r != 2.

This file globalizes exactly that production carrier. No even returned
cofactor is inserted merely because the local two-shell predicate is meaningful
there.

Every nonzero production atom is transported from its q-square collision to

  q * r * e * p,

an honest squarefree physical site. The transport is globally injective,
preserves every pair product (two sign flips), and retains the two shell
orientations before any norm is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

def stableFarRenewalProductionTwoShellCarrier
    (R : ℕ) : Finset StableFarRenewalShellTag :=
  (stableFarRenewalTwoShellCarrier R).filter fun t =>
    t.2.1 ≠ 2 ∧ Odd t.2.2.1

@[simp] theorem mem_stableFarRenewalProductionTwoShellCarrier
    {R : ℕ} {t : StableFarRenewalShellTag} :
    t ∈ stableFarRenewalProductionTwoShellCarrier R ↔
      t ∈ stableFarRenewalTwoShellCarrier R ∧
      t.2.1 ≠ 2 ∧ Odd t.2.2.1 := by
  simp [stableFarRenewalProductionTwoShellCarrier]

theorem stableFarRenewalProductionTwoShellCarrier_data
    {R : ℕ} {t : StableFarRenewalShellTag}
    (ht : t ∈ stableFarRenewalProductionTwoShellCarrier R) :
    t.1 ∈ primesUpTo (R - 1) ∧
      t.2 ∈ lowWheelFarPrimeQ2DescendedTriples R ∧
      t.2.1 ≠ 2 ∧ Odd t.2.2.1 ∧
      (stableFarRenewalFirstCutShell
          R t.1 t.2.1 t.2.2.1 t.2.2.2 ∨
        stableFarRenewalSecondCrossShell
          R t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  have h := mem_stableFarRenewalProductionTwoShellCarrier.mp ht
  have hc := stableFarRenewalTwoShellCarrier_data h.1
  exact ⟨hc.1, hc.2.1, h.2.1, h.2.2, hc.2.2⟩

theorem stableFarRenewalProductionTransport_injOn
    (R : ℕ) :
    Set.InjOn stableFarRenewalTwoShellTransport
      (stableFarRenewalProductionTwoShellCarrier R :
        Set StableFarRenewalShellTag) := by
  intro a ha b hb hab
  exact stableFarRenewalTwoShellTransport_injOn R
    (by
      have hfin : a ∈ stableFarRenewalProductionTwoShellCarrier R := by
        simpa using ha
      exact Finset.mem_coe.mpr
        (mem_stableFarRenewalProductionTwoShellCarrier.mp hfin).1)
    (by
      have hfin : b ∈ stableFarRenewalProductionTwoShellCarrier R := by
        simpa using hb
      exact Finset.mem_coe.mpr
        (mem_stableFarRenewalProductionTwoShellCarrier.mp hfin).1)
    hab

def stableFarRenewalProductionImage (R : ℕ) : Finset ℕ :=
  (stableFarRenewalProductionTwoShellCarrier R).image
    stableFarRenewalTwoShellTransport

theorem stableFarRenewalProductionImage_subset_squarefreeShell
    {R : ℕ} (hR : 2 ≤ R) :
    stableFarRenewalProductionImage R ⊆
      orderedEulerCutSquarefreeShell R := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨t, ht, rfl⟩
  have htFull :
      t ∈ stableFarRenewalTwoShellCarrier R :=
    (mem_stableFarRenewalProductionTwoShellCarrier.mp ht).1
  exact stableFarRenewalTwoShellImage_subset_squarefreeShell hR
    (Finset.mem_image.mpr ⟨t, htFull, rfl⟩)

theorem stableFarRenewalProductionImage_card_eq_carrier
    (R : ℕ) :
    (stableFarRenewalProductionImage R).card =
      (stableFarRenewalProductionTwoShellCarrier R).card := by
  unfold stableFarRenewalProductionImage
  exact Finset.card_image_iff.mpr
    (stableFarRenewalProductionTransport_injOn R)

theorem stableFarRenewalProductionTransport_weight_eq_neg_returned
    {R : ℕ} {t : StableFarRenewalShellTag}
    (ht : t ∈ stableFarRenewalProductionTwoShellCarrier R) :
    canonicalMoebiusWeight (stableFarRenewalTwoShellTransport t) =
      -canonicalMoebiusWeight t.2.2.1 := by
  rcases t with ⟨q, ⟨r, ⟨e, p⟩⟩⟩
  rcases stableFarRenewalProductionTwoShellCarrier_data ht with
    ⟨hqOld, hy, _hrne, _heOdd, hshell⟩
  have hrq : r < q := by
    rcases hshell with hFirst | hSecond
    · exact hFirst.2.1
    · exact hSecond.2.1
  simpa [stableFarRenewalTwoShellTransport] using
    renewalTransportSite_weight_eq_neg_returned hy hqOld hrq

theorem stableFarRenewalProductionTransport_pairWeight_eq
    {R : ℕ} {a b : StableFarRenewalShellTag}
    (ha : a ∈ stableFarRenewalProductionTwoShellCarrier R)
    (hb : b ∈ stableFarRenewalProductionTwoShellCarrier R) :
    canonicalMoebiusWeight (stableFarRenewalTwoShellTransport a) *
        canonicalMoebiusWeight (stableFarRenewalTwoShellTransport b) =
      canonicalMoebiusWeight a.2.2.1 *
        canonicalMoebiusWeight b.2.2.1 := by
  rw [stableFarRenewalProductionTransport_weight_eq_neg_returned ha,
    stableFarRenewalProductionTransport_weight_eq_neg_returned hb]
  ring

def stableFarRenewalProductionFirstCutCarrier
    (R : ℕ) : Finset StableFarRenewalShellTag :=
  (stableFarRenewalProductionTwoShellCarrier R).filter fun t =>
    stableFarRenewalFirstCutShell R t.1 t.2.1 t.2.2.1 t.2.2.2

def stableFarRenewalProductionSecondCrossCarrier
    (R : ℕ) : Finset StableFarRenewalShellTag :=
  (stableFarRenewalProductionTwoShellCarrier R).filter fun t =>
    stableFarRenewalSecondCrossShell R t.1 t.2.1 t.2.2.1 t.2.2.2

@[simp] theorem mem_stableFarRenewalProductionFirstCutCarrier
    {R : ℕ} {t : StableFarRenewalShellTag} :
    t ∈ stableFarRenewalProductionFirstCutCarrier R ↔
      t ∈ stableFarRenewalProductionTwoShellCarrier R ∧
      stableFarRenewalFirstCutShell
        R t.1 t.2.1 t.2.2.1 t.2.2.2 := by
  simp [stableFarRenewalProductionFirstCutCarrier]

@[simp] theorem mem_stableFarRenewalProductionSecondCrossCarrier
    {R : ℕ} {t : StableFarRenewalShellTag} :
    t ∈ stableFarRenewalProductionSecondCrossCarrier R ↔
      t ∈ stableFarRenewalProductionTwoShellCarrier R ∧
      stableFarRenewalSecondCrossShell
        R t.1 t.2.1 t.2.2.1 t.2.2.2 := by
  simp [stableFarRenewalProductionSecondCrossCarrier]

theorem stableFarRenewalProductionFirstCut_disjoint_secondCross
    (R : ℕ) :
    Disjoint (stableFarRenewalProductionFirstCutCarrier R)
      (stableFarRenewalProductionSecondCrossCarrier R) := by
  rw [Finset.disjoint_left]
  intro t htFirst htSecond
  have hFirst :=
    (mem_stableFarRenewalProductionFirstCutCarrier.mp htFirst).2
  have hSecond :=
    (mem_stableFarRenewalProductionSecondCrossCarrier.mp htSecond).2
  exact hFirst.2.2.2.2 hSecond.2.2.1

theorem stableFarRenewalProductionTwoShellCarrier_eq_oriented_union
    (R : ℕ) :
    stableFarRenewalProductionTwoShellCarrier R =
      stableFarRenewalProductionFirstCutCarrier R ∪
        stableFarRenewalProductionSecondCrossCarrier R := by
  ext t
  simp only [Finset.mem_union,
    mem_stableFarRenewalProductionFirstCutCarrier,
    mem_stableFarRenewalProductionSecondCrossCarrier]
  constructor
  · intro ht
    have hdata := stableFarRenewalProductionTwoShellCarrier_data ht
    rcases hdata.2.2.2.2 with hFirst | hSecond
    · exact Or.inl ⟨ht, hFirst⟩
    · exact Or.inr ⟨ht, hSecond⟩
  · rintro (⟨ht, _⟩ | ⟨ht, _⟩)
    · exact ht
    · exact ht

def stableFarRenewalProductionCharge
    (R : ℕ) (t : StableFarRenewalShellTag) : ℂ :=
  ((stableFarRenewalOwnerIndicatorDifference
      R t.1 t.2.1 t.2.2.1 t.2.2.2 : ℤ) : ℂ) *
    canonicalMoebiusWeight t.2.2.1

def stableFarRenewalProductionFirstCutSites (R : ℕ) : Finset ℕ :=
  (stableFarRenewalProductionFirstCutCarrier R).image
    stableFarRenewalTwoShellTransport

def stableFarRenewalProductionSecondCrossSites (R : ℕ) : Finset ℕ :=
  (stableFarRenewalProductionSecondCrossCarrier R).image
    stableFarRenewalTwoShellTransport

theorem stableFarRenewalProductionFirstCutCharge_sum_eq_siteMass
    (R : ℕ) :
    (∑ t ∈ stableFarRenewalProductionFirstCutCarrier R,
        stableFarRenewalProductionCharge R t) =
      ∑ n ∈ stableFarRenewalProductionFirstCutSites R,
        canonicalMoebiusWeight n := by
  unfold stableFarRenewalProductionFirstCutSites
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rcases t with ⟨q, ⟨r, ⟨e, p⟩⟩⟩
    have hmem :=
      mem_stableFarRenewalProductionFirstCutCarrier.mp ht
    have hdata :=
      stableFarRenewalProductionTwoShellCarrier_data hmem.1
    unfold stableFarRenewalProductionCharge
      stableFarRenewalTwoShellTransport
    exact firstCutShell_indicator_weight_eq_transportWeight
      hdata.2.1 hmem.2
  · intro a ha b hb hab
    exact stableFarRenewalProductionTransport_injOn R
      (Finset.mem_coe.mpr
        ((mem_stableFarRenewalProductionFirstCutCarrier.mp ha).1))
      (Finset.mem_coe.mpr
        ((mem_stableFarRenewalProductionFirstCutCarrier.mp hb).1))
      hab

theorem stableFarRenewalProductionSecondCrossCharge_sum_eq_negSiteMass
    (R : ℕ) :
    (∑ t ∈ stableFarRenewalProductionSecondCrossCarrier R,
        stableFarRenewalProductionCharge R t) =
      ∑ n ∈ stableFarRenewalProductionSecondCrossSites R,
        -canonicalMoebiusWeight n := by
  unfold stableFarRenewalProductionSecondCrossSites
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rcases t with ⟨q, ⟨r, ⟨e, p⟩⟩⟩
    have hmem :=
      mem_stableFarRenewalProductionSecondCrossCarrier.mp ht
    have hdata :=
      stableFarRenewalProductionTwoShellCarrier_data hmem.1
    unfold stableFarRenewalProductionCharge
      stableFarRenewalTwoShellTransport
    exact secondCrossShell_indicator_weight_eq_neg_transportWeight
      hdata.2.1 hmem.2
  · intro a ha b hb hab
    exact stableFarRenewalProductionTransport_injOn R
      (Finset.mem_coe.mpr
        ((mem_stableFarRenewalProductionSecondCrossCarrier.mp ha).1))
      (Finset.mem_coe.mpr
        ((mem_stableFarRenewalProductionSecondCrossCarrier.mp hb).1))
      hab

def stableFarRenewalProductionSignedBoundaryMass (R : ℕ) : ℂ :=
  (∑ n ∈ stableFarRenewalProductionFirstCutSites R,
      canonicalMoebiusWeight n) +
    ∑ n ∈ stableFarRenewalProductionSecondCrossSites R,
      -canonicalMoebiusWeight n

theorem stableFarRenewalProductionCharge_sum_eq_signedBoundaryMass
    (R : ℕ) :
    (∑ t ∈ stableFarRenewalProductionTwoShellCarrier R,
        stableFarRenewalProductionCharge R t) =
      stableFarRenewalProductionSignedBoundaryMass R := by
  rw [stableFarRenewalProductionTwoShellCarrier_eq_oriented_union,
    Finset.sum_union
      (stableFarRenewalProductionFirstCut_disjoint_secondCross R)]
  unfold stableFarRenewalProductionSignedBoundaryMass
  rw [stableFarRenewalProductionFirstCutCharge_sum_eq_siteMass,
    stableFarRenewalProductionSecondCrossCharge_sum_eq_negSiteMass]

end RHLean.Proof
