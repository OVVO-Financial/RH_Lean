import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_OWNER_CUBE»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_INCIDENCE_CLOSURE»

/-!
# Virtual next-owner corners: admitted, clipped, or Dirichlet zero

A full fresh-owner square has two mixed corners.  The physical admitted child
fibre may contain only one of them.  The missing sibling must not be renamed as
an error term.

For an admitted p-parent `a` and a larger fresh prime `r`, the virtual site
`r*a` has exactly three possibilities:

1. `p*(r*a)` is still on the clock: `r*a` is an admitted parent in the same
   lower-p signature cell;
2. `r*a` is physical but its p-child is off the clock: it is exactly the named
   clipped p-base fibre in the same cell;
3. `r*a` itself is off the clock: every Dirichlet coefficient at that site is
   zero, so every polarization atom containing that coordinate vanishes.

This is the exact carrier completion needed to use the full owner cube without
adding a residual population.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Multiplying an admitted p-parent by a larger fresh prime stays in the same
admitted p-cell whenever the new p-child remains physical. -/
theorem lowOwnerFirstOwner_mul_larger_prime_mem_admittedBase
    {R p r a : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hra : ¬ r ∣ a)
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig)
    (hpraX : p * (r * a) ≤ squareRootEndpoint R) :
    r * a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig := by
  rcases Finset.mem_filter.mp ha with ⟨haBase, _hpaX⟩
  rcases Finset.mem_filter.mp haBase with ⟨haCar, hbase⟩
  rcases Finset.mem_filter.mp haCar with ⟨haIcc, hmu⟩
  have haPos : 0 < a := Nat.succ_le_iff.mp (Finset.mem_Icc.mp haIcc).1
  have hraPos : 0 < r * a := Nat.mul_pos hr.pos haPos
  have hraX : r * a ≤ squareRootEndpoint R := by
    have hle : r * a ≤ p * (r * a) := by
      calc
        r * a = 1 * (r * a) := by simp
        _ ≤ p * (r * a) := Nat.mul_le_mul_right (r * a) hp.one_le
    exact hle.trans hpraX
  have hmuRA : realMoebiusStep (r * a) ≠ 0 := by
    rw [realMoebiusStep_mul_prime_eq_neg hr hra]
    exact neg_ne_zero.mpr hmu
  have hcarRA : r * a ∈ lowOwnerNonzeroMobiusCarrier R :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hraPos, hraX⟩, hmuRA⟩
  have hsigRA : squarefreeLowerPrimeSignature p (r * a) = sig := by
    rw [squarefreeLowerPrimeSignature_mul_larger_prime hr hpr haPos, hbase.1]
  have hpnr : ¬ p ∣ r := by
    intro hdiv
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hdiv
    exact (ne_of_lt hpr) heq
  have hpra : ¬ p ∣ r * a := by
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with h | h
    · exact hpnr h
    · exact hbase.2 h
  have hbaseRA : r * a ∈ lowOwnerFirstOwnerBaseFiber R p sig :=
    Finset.mem_filter.mpr ⟨hcarRA, ⟨hsigRA, hpra⟩⟩
  exact Finset.mem_filter.mpr ⟨hbaseRA, hpraX⟩

/-- **Virtual-corner trichotomy.** -/
theorem lowOwnerFirstOwner_mul_larger_prime_admitted_or_clipped_or_outside
    {R p r a : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hra : ¬ r ∣ a)
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig) :
    r * a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig ∨
      r * a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig ∨
      squareRootEndpoint R < r * a := by
  by_cases hraX : r * a ≤ squareRootEndpoint R
  · by_cases hpraX : p * (r * a) ≤ squareRootEndpoint R
    · exact Or.inl
        (lowOwnerFirstOwner_mul_larger_prime_mem_admittedBase
          hp hr hpr hra ha hpraX)
    · have hclip : squareRootEndpoint R < p * (r * a) :=
        Nat.lt_of_not_ge hpraX
      exact Or.inr (Or.inl
        (lowOwnerFirstOwner_mul_larger_prime_mem_clippedBase
          hp hr hpr hra ha hraX hclip))
  · exact Or.inr (Or.inr (Nat.lt_of_not_ge hraX))

/-- If a virtual owner child is outside the physical clock, its base coefficient
vanishes. -/
theorem lowOwnerDirichletBaseCoefficient_eq_zero_of_outside
    {R n : ℕ} (hout : squareRootEndpoint R < n) :
    lowOwnerDirichletBaseCoefficient R n = 0 := by
  unfold lowOwnerDirichletBaseCoefficient
  exact lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hout

/-- Its returned p-child coefficient also vanishes. -/
theorem lowOwnerDirichletReturnedCoefficient_eq_zero_of_outside
    {R p n : ℕ} (hp : 1 ≤ p)
    (hout : squareRootEndpoint R < n) :
    lowOwnerDirichletReturnedCoefficient R p n = 0 := by
  have hnle : n ≤ p * n := by
    calc
      n = 1 * n := by simp
      _ ≤ p * n := Nat.mul_le_mul_right n hp
  have hout' : squareRootEndpoint R < p * n := hout.trans_le hnle
  unfold lowOwnerDirichletReturnedCoefficient
  exact lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hout'

/-- Hence the incidence coefficient vanishes as well. -/
theorem lowOwnerDirichletIncidenceCoefficient_eq_zero_of_outside
    {R p n : ℕ} (hp : 1 ≤ p)
    (hout : squareRootEndpoint R < n) :
    lowOwnerDirichletIncidenceCoefficient R p n = 0 := by
  unfold lowOwnerDirichletIncidenceCoefficient
  rw [lowOwnerDirichletBaseCoefficient_eq_zero_of_outside hout,
    lowOwnerDirichletReturnedCoefficient_eq_zero_of_outside hp hout]
  ring

/-- **Any polarization atom with an outside first coordinate is exactly zero.** -/
theorem lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_first_outside
    {R p a b : ℕ} (hp : 1 ≤ p)
    (hout : squareRootEndpoint R < a) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) = 0 := by
  rw [lowOwnerFirstOwnerDirichletPolarizationAtom_eq_scalar]
  rw [lowOwnerDirichletBaseCoefficient_eq_zero_of_outside hout,
    lowOwnerDirichletReturnedCoefficient_eq_zero_of_outside hp hout,
    lowOwnerDirichletIncidenceCoefficient_eq_zero_of_outside hp hout]
  ring

/-- Symmetric outside-coordinate vanishing. -/
theorem lowOwnerFirstOwnerDirichletPolarizationAtom_eq_zero_of_second_outside
    {R p a b : ℕ} (hp : 1 ≤ p)
    (hout : squareRootEndpoint R < b) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) = 0 := by
  rw [lowOwnerFirstOwnerDirichletPolarizationAtom_eq_scalar]
  rw [lowOwnerDirichletBaseCoefficient_eq_zero_of_outside hout,
    lowOwnerDirichletReturnedCoefficient_eq_zero_of_outside hp hout,
    lowOwnerDirichletIncidenceCoefficient_eq_zero_of_outside hp hout]
  ring

end RHLean.Proof
