import RHLean.Proof.StableFarWallCrossingOwnerWindow

/-!
# Stable-far returned-fibre Fubini

Fix a returned stable-far owner `r` and far prime `p`.  An old outer owner
`q > r` contributes exactly those `r`-smooth squarefree cofactors `e` for which

  q*r*e*p <= X_R < q^2*r*e*p.

Solving for `e` makes this one frozen predecessor window:

  X_R/(q^2*r*p) < e <= X_R/(q*r*p).

The signed mass of that complete occurrence fibre is therefore the difference
of two frozen `r^-` prefixes.  This file proves that identity first, before any
norm or estimate, and packages the q-first returned-fibre column for the next
finite Fubini step.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Cofactors returning through one fixed old owner `q`.  The set difference is
exactly the strict second-contact window at fixed returned coordinates `(r,p)`. -/
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
    exact Nat.mul_le_mul_right (r * p) hqq
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

/-- **One fixed returned crossing fibre is a frozen-prefix difference.** -/
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

/-- Old owners which can possibly occur at fixed returned `(r,p)` coordinates.
The actual strict-crossing cofactor window may be empty for some of them; that
is harmless because its signed mass is then zero. -/
def stableFarReturnedOldOwners (R r p : ℕ) : Finset ℕ :=
  frozenPrimeUniverseHighPrimeSet r (squareRootEndpoint R / (r * p))

/-- Signed q-first crossing column at fixed returned `(r,p)`. -/
def stableFarReturnedCrossingColumn (R r p : ℕ) : ℤ :=
  ∑ q ∈ stableFarReturnedOldOwners R r p,
    ∑ e ∈ stableFarReturnedCrossingCofactors R r p q, μ e

/-- **q-first returned-fibre normal form.**  Every crossing occurrence has been
summed with its Möbius sign before the old-owner sum is touched. -/
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
  have hqPrime := (mem_frozenPrimeUniverseHighPrimeSet.mp hq).1
  exact stableFarReturnedCrossingCofactors_mass_eq_frozenWindow hr hp hqPrime

/-- Descended child cofactors at fixed returned `(r,p)`. -/
def stableFarReturnedDescendedCofactors
    (R r p : ℕ) : Finset ℕ :=
  squareRootLowPrimeGoSmoothCofactors r
    (squareRootEndpoint R / (r * r * p))

/-- Signed descended baseline at fixed returned `(r,p)`. -/
def stableFarReturnedDescendedMass (R r p : ℕ) : ℤ :=
  ∑ e ∈ stableFarReturnedDescendedCofactors R r p, μ e

/-- The descended baseline is itself one frozen predecessor prefix. -/
theorem stableFarReturnedDescendedMass_eq_frozenPrefix
    {R r p : ℕ} (hr : r.Prime) :
    stableFarReturnedDescendedMass R r p =
      frozenPrimeUniverseMass (primesUpTo (r - 1))
        (squareRootEndpoint R / (r * r * p)) := by
  unfold stableFarReturnedDescendedMass stableFarReturnedDescendedCofactors
  symm
  exact frozenPrimeUniverseMass_eq_goSmoothCofactorSum hr

/-- The fixed returned-coordinate contribution after centering one genuine
child copy against every old crossing occurrence. -/
def stableFarReturnedCenteredMass (R r p : ℕ) : ℤ :=
  stableFarReturnedDescendedMass R r p -
    stableFarReturnedCrossingColumn R r p

/-- **Returned-fibre signed Fubini normal form.**  The opaque multiplicity field
has disappeared: one descended frozen prefix is paired with a prime-indexed
family of complete frozen window differences.  This is the exact object on
which the existing moving-boundary Euler telescope can act next. -/
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
