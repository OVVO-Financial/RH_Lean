import RHLean.Proof.StableFarWallCrossingOwnerWindow

/-!
# Stable-far returned-fibre Fubini

Fix a returned owner `r` and far prime `p`.  An old owner `q > r` contributes
exactly those `r`-smooth squarefree cofactors `e` with

  q*r*e*p <= X_R < q^2*r*e*p.

Thus the fixed-q occurrence fibre is the frozen window

  X_R/(q^2*r*p) < e <= X_R/(q*r*p).

The point of this file is to perform the finite Fubini before any norm: every
occurrence is first summed with its Mobius sign into a complete frozen window,
and only then are the old owners summed.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Cofactors returning through one fixed old owner `q`. -/
def stableFarReturnedCrossingCofactors
    (R r p q : ℕ) : Finset ℕ :=
  squareRootLowPrimeGoSmoothCofactors r
      (squareRootEndpoint R / (q * r * p)) \
    squareRootLowPrimeGoSmoothCofactors r
      (squareRootEndpoint R / (q * q * r * p))

/-- The q^2 lower cutoff is contained in the q upper cutoff. -/
theorem stableFarReturnedCrossingCofactors_lower_subset_upper
    {R r p q : ℕ} (hr : r.Prime) (hp : p.Prime) (hq : q.Prime) :
    squareRootLowPrimeGoSmoothCofactors r
        (squareRootEndpoint R / (q * q * r * p)) ⊆
      squareRootLowPrimeGoSmoothCofactors r
        (squareRootEndpoint R / (q * r * p)) := by
  have hq1 : 1 ≤ q := hq.one_le
  have hden : q * r * p ≤ q * q * r * p := by
    have hqq : q ≤ q * q := by
      simpa using Nat.mul_le_mul_left q hq1
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (r * p) hqq
  have hdenPos : 0 < q * r * p :=
    Nat.mul_pos (Nat.mul_pos hq.pos hr.pos) hp.pos
  have hcut :
      squareRootEndpoint R / (q * q * r * p) ≤
        squareRootEndpoint R / (q * r * p) :=
    Nat.div_le_div_left hden hdenPos
  intro e he
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp he with
    ⟨he1, heCut, heSq, heRough⟩
  exact mem_squareRootLowPrimeGoSmoothCofactors.mpr
    ⟨he1, heCut.trans hcut, heSq, heRough⟩

/-- **One old-owner fibre is exactly one frozen-prefix difference.** -/
theorem stableFarReturnedCrossingCofactors_mass_eq_frozenWindow
    {R r p q : ℕ} (hr : r.Prime) (hp : p.Prime) (hq : q.Prime) :
    (∑ e ∈ stableFarReturnedCrossingCofactors R r p q, μ e) =
      frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootEndpoint R / (q * r * p)) -
        frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootEndpoint R / (q * q * r * p)) := by
  have hsub :=
    stableFarReturnedCrossingCofactors_lower_subset_upper
      (R := R) (r := r) (p := p) (q := q) hr hp hq
  have hsum := Finset.sum_sdiff hsub (f := fun e => μ e)
  have hUpper := frozenPrimeUniverseMass_eq_goSmoothCofactorSum
    (r := r) (Y := squareRootEndpoint R / (q * r * p)) hr
  have hLower := frozenPrimeUniverseMass_eq_goSmoothCofactorSum
    (r := r) (Y := squareRootEndpoint R / (q * q * r * p)) hr
  unfold stableFarReturnedCrossingCofactors
  rw [hUpper, hLower]
  exact (eq_sub_iff_add_eq).2 hsum

/-- Old owners which can occur at fixed returned coordinates `(r,p)`. -/
def stableFarReturnedOldOwners (R r p : ℕ) : Finset ℕ :=
  frozenPrimeUniverseHighPrimeSet r (squareRootEndpoint R / (r * p))

/-- Signed old-owner crossing column at fixed returned coordinates. -/
def stableFarReturnedCrossingColumn (R r p : ℕ) : ℤ :=
  ∑ q ∈ stableFarReturnedOldOwners R r p,
    ∑ e ∈ stableFarReturnedCrossingCofactors R r p q, μ e

/-- **Owner-first normal form.**  Every crossing occurrence has already been
summed with its Mobius sign before the old-owner sum is touched. -/
theorem stableFarReturnedCrossingColumn_eq_frozenWindows
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedCrossingColumn R r p =
      ∑ q ∈ stableFarReturnedOldOwners R r p,
        (frozenPrimeUniverseMass (primesUpTo (r - 1))
            (squareRootEndpoint R / (q * r * p)) -
          frozenPrimeUniverseMass (primesUpTo (r - 1))
            (squareRootEndpoint R / (q * q * r * p))) := by
  unfold stableFarReturnedCrossingColumn
  apply Finset.sum_congr rfl
  intro q hq
  exact stableFarReturnedCrossingCofactors_mass_eq_frozenWindow
    hr hp (mem_frozenPrimeUniverseHighPrimeSet.mp hq).1

/-- Descended returned cofactors at fixed coordinates `(r,p)`. -/
def stableFarReturnedDescendedCofactors
    (R r p : ℕ) : Finset ℕ :=
  squareRootLowPrimeGoSmoothCofactors r
    (squareRootEndpoint R / (r * r * p))

/-- Signed descended baseline at fixed returned coordinates. -/
def stableFarReturnedDescendedMass (R r p : ℕ) : ℤ :=
  ∑ e ∈ stableFarReturnedDescendedCofactors R r p, μ e

/-- The descended baseline is one frozen predecessor prefix. -/
theorem stableFarReturnedDescendedMass_eq_frozenPrefix
    {R r p : ℕ} (hr : r.Prime) :
    stableFarReturnedDescendedMass R r p =
      frozenPrimeUniverseMass (primesUpTo (r - 1))
        (squareRootEndpoint R / (r * r * p)) := by
  unfold stableFarReturnedDescendedMass stableFarReturnedDescendedCofactors
  symm
  exact frozenPrimeUniverseMass_eq_goSmoothCofactorSum hr

/-- Every fixed-q crossing window sits inside the common descended cofactor
carrier. -/
theorem stableFarReturnedCrossingCofactors_subset_descended
    {R r p q : ℕ} (hr : r.Prime) (hp : p.Prime)
    (hq : q ∈ stableFarReturnedOldOwners R r p) :
    stableFarReturnedCrossingCofactors R r p q ⊆
      stableFarReturnedDescendedCofactors R r p := by
  have hqData := mem_frozenPrimeUniverseHighPrimeSet.mp hq
  have hrleq : r ≤ q := hqData.2.1.le
  have hden : r * r * p ≤ q * r * p := by
    have hmul := Nat.mul_le_mul_right (r * p) hrleq
    simpa [Nat.mul_assoc] using hmul
  have hdenPos : 0 < r * r * p :=
    Nat.mul_pos (Nat.mul_pos hr.pos hr.pos) hp.pos
  have hcut :
      squareRootEndpoint R / (q * r * p) ≤
        squareRootEndpoint R / (r * r * p) :=
    Nat.div_le_div_left hden hdenPos
  intro e he
  have heUpper := (Finset.mem_sdiff.mp he).1
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp heUpper with
    ⟨he1, heCut, heSq, heRough⟩
  exact mem_squareRootLowPrimeGoSmoothCofactors.mpr
    ⟨he1, heCut.trans hcut, heSq, heRough⟩

/-- A fixed-q crossing fibre is exactly the filter it induces on the common
descended cofactor carrier. -/
theorem stableFarReturnedCrossingCofactors_eq_descended_filter
    {R r p q : ℕ} (hr : r.Prime) (hp : p.Prime)
    (hq : q ∈ stableFarReturnedOldOwners R r p) :
    stableFarReturnedCrossingCofactors R r p q =
      (stableFarReturnedDescendedCofactors R r p).filter fun e =>
        e ∈ stableFarReturnedCrossingCofactors R r p q := by
  ext e
  constructor
  · intro he
    exact Finset.mem_filter.mpr
      ⟨stableFarReturnedCrossingCofactors_subset_descended hr hp hq he, he⟩
  · intro he
    exact (Finset.mem_filter.mp he).2

/-- Number of old owners returning to one fixed cofactor. -/
def stableFarReturnedCrossingMultiplicity
    (R r p e : ℕ) : ℕ :=
  ((stableFarReturnedOldOwners R r p).filter fun q =>
    e ∈ stableFarReturnedCrossingCofactors R r p q).card

/-- **Finite Fubini onto returned cofactors.**  The owner occurrence column is
exactly the multiplicity-weighted signed cofactor column. -/
theorem stableFarReturnedCrossingColumn_eq_multiplicity
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedCrossingColumn R r p =
      ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        (stableFarReturnedCrossingMultiplicity R r p e : ℤ) * μ e := by
  unfold stableFarReturnedCrossingColumn
  calc
    (∑ q ∈ stableFarReturnedOldOwners R r p,
        ∑ e ∈ stableFarReturnedCrossingCofactors R r p q, μ e) =
      ∑ q ∈ stableFarReturnedOldOwners R r p,
        ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
          if e ∈ stableFarReturnedCrossingCofactors R r p q then μ e else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [← Finset.sum_filter]
            rw [← stableFarReturnedCrossingCofactors_eq_descended_filter hr hp hq]
    _ = ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        ∑ q ∈ stableFarReturnedOldOwners R r p,
          if e ∈ stableFarReturnedCrossingCofactors R r p q then μ e else 0 := by
            exact Finset.sum_comm
    _ = ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        (stableFarReturnedCrossingMultiplicity R r p e : ℤ) * μ e := by
          apply Finset.sum_congr rfl
          intro e _he
          rw [← Finset.sum_filter]
          simp [stableFarReturnedCrossingMultiplicity]

/-- Fixed returned-coordinate contribution after centering one genuine child
copy against every old crossing occurrence. -/
def stableFarReturnedCenteredMass (R r p : ℕ) : ℤ :=
  stableFarReturnedDescendedMass R r p -
    stableFarReturnedCrossingColumn R r p

/-- The centered returned mass is literally `1 - multiplicity` on each signed
cofactor. -/
theorem stableFarReturnedCenteredMass_eq_multiplicity
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedCenteredMass R r p =
      ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        (1 - (stableFarReturnedCrossingMultiplicity R r p e : ℤ)) * μ e := by
  unfold stableFarReturnedCenteredMass stableFarReturnedDescendedMass
  rw [stableFarReturnedCrossingColumn_eq_multiplicity hr hp,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  ring

/-- **Returned-fibre signed normal form.**  The opaque physical multiplicity
shape has become one frozen baseline minus a prime-indexed family of complete
frozen window differences. -/
theorem stableFarReturnedCenteredMass_eq_frozenPrefix_sub_windows
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedCenteredMass R r p =
      frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootEndpoint R / (r * r * p)) -
        ∑ q ∈ stableFarReturnedOldOwners R r p,
          (frozenPrimeUniverseMass (primesUpTo (r - 1))
              (squareRootEndpoint R / (q * r * p)) -
            frozenPrimeUniverseMass (primesUpTo (r - 1))
              (squareRootEndpoint R / (q * q * r * p))) := by
  unfold stableFarReturnedCenteredMass
  rw [stableFarReturnedDescendedMass_eq_frozenPrefix hr,
    stableFarReturnedCrossingColumn_eq_frozenWindows hr hp]

end RHLean.Proof
