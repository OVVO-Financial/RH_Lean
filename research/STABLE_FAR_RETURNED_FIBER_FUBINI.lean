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
norm or estimate, and then identifies the arithmetic owner multiplicity with
the actual physical crossing multiplicity on every returned child.
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

/-- The arithmetic number of old owners returning to one fixed cofactor. -/
def stableFarReturnedCrossingMultiplicity
    (R r p e : ℕ) : ℕ :=
  ((stableFarReturnedOldOwners R r p).filter fun q =>
    e ∈ stableFarReturnedCrossingCofactors R r p q).card

/-- Every crossing-window cofactor is already a member of the descended
returned-child cofactor carrier. -/
theorem stableFarReturnedCrossingCofactors_subset_descended
    {R r p q : ℕ} (hr : r.Prime) (hp : p.Prime)
    (hq : q ∈ stableFarReturnedOldOwners R r p) :
    stableFarReturnedCrossingCofactors R r p q ⊆
      stableFarReturnedDescendedCofactors R r p := by
  have hqData := mem_frozenPrimeUniverseHighPrimeSet.mp hq
  have hrq : r < q := hqData.2.1
  have hrleq : r ≤ q := hrq.le
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

/-- A fixed q crossing fibre is the filter it induces on the common descended
cofactor carrier. -/
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

/-- **Finite Fubini of crossing occurrences onto returned cofactors.** -/
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
            rw [stableFarReturnedCrossingCofactors_eq_descended_filter hr hp hq,
              Finset.sum_filter]
    _ = ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        ∑ q ∈ stableFarReturnedOldOwners R r p,
          if e ∈ stableFarReturnedCrossingCofactors R r p q then μ e else 0 := by
            exact Finset.sum_comm
    _ = ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        (stableFarReturnedCrossingMultiplicity R r p e : ℤ) * μ e := by
          apply Finset.sum_congr rfl
          intro e he
          rw [← Finset.sum_filter]
          simp [stableFarReturnedCrossingMultiplicity]

/-- The fixed returned-coordinate contribution after centering one genuine
child copy against every old crossing occurrence. -/
def stableFarReturnedCenteredMass (R r p : ℕ) : ℤ :=
  stableFarReturnedDescendedMass R r p -
    stableFarReturnedCrossingColumn R r p

/-- The centered returned mass is literally the physical-looking coefficient
`1 - multiplicity` on each signed cofactor. -/
theorem stableFarReturnedCenteredMass_eq_multiplicity
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedCenteredMass R r p =
      ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        (1 - (stableFarReturnedCrossingMultiplicity R r p e : ℤ)) * μ e := by
  unfold stableFarReturnedCenteredMass stableFarReturnedDescendedMass
  rw [stableFarReturnedCrossingColumn_eq_multiplicity hr hp,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- **Returned-fibre signed Fubini normal form.**  The opaque multiplicity field
has disappeared: one descended frozen prefix is paired with a prime-indexed
family of complete frozen window differences. -/
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

/-! ## Identification with the actual stable-far physical multiplicity -/

/-- Every arithmetic descended cofactor produces an actual descended physical
returned child at `(r,(e,p))`. -/
theorem stableFarReturnedDescendedCofactor_mem_physical
    {R r p e : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p)
    (he : e ∈ stableFarReturnedDescendedCofactors R r p) :
    (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R := by
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp he with
    ⟨he1, heCut, heSq, heRough⟩
  have hdenPos : 0 < r * r * p :=
    Nat.mul_pos (Nat.mul_pos hr.pos hr.pos) hp.pos
  have hq2raw : (r * r * p) * e ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hdenPos).1 heCut
  have hq2 : r * r * e * p ≤ squareRootEndpoint R := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq2raw
  have hr1 : 1 ≤ r := hr.one_le
  have hbaseCut : r * e * p ≤ squareRootEndpoint R := by
    have hle : r * e * p ≤ r * r * e * p := by
      have h := Nat.mul_le_mul_right (r * e * p) hr1
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
    exact hle.trans hq2
  have hbase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
    lowWheelFarPrimeLowCofactorTriple_mem_of_data
      hr hrR he1 hp hpR heSq heRough hbaseCut
  exact Finset.mem_filter.mpr ⟨hbase, hq2⟩

/-- On a genuine returned cofactor, the explicit physical old-owner window is
exactly the arithmetic owner set filtered by the corresponding cofactor
window. -/
theorem lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_returnedFilter
    {R r p e : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p)
    (he : e ∈ stableFarReturnedDescendedCofactors R r p) :
    lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) =
      (stableFarReturnedOldOwners R r p).filter fun q =>
        e ∈ stableFarReturnedCrossingCofactors R r p q := by
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp he with
    ⟨he1, _heCut, heSq, heRough⟩
  have hRpos : 0 < R := hr.pos.trans hrR
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hne : R ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.ne_of_gt hRpos)
    simpa [pow_two] using Nat.pred_lt hne
  ext q
  constructor
  · intro hqPhys
    rcases Finset.mem_filter.mp hqPhys with
      ⟨hqOldRoot, hrq, hcut, hcross⟩
    have hqData := mem_primesUpTo.mp hqOldRoot
    have hdenPos : 0 < q * r * p :=
      Nat.mul_pos (Nat.mul_pos hqData.1.pos hr.pos) hp.pos
    have heUpperCut : e ≤ squareRootEndpoint R / (q * r * p) := by
      apply (Nat.le_div_iff_mul_le hdenPos).2
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcut
    have heUpper :
        e ∈ squareRootLowPrimeGoSmoothCofactors r
          (squareRootEndpoint R / (q * r * p)) :=
      mem_squareRootLowPrimeGoSmoothCofactors.mpr
        ⟨he1, heUpperCut, heSq, heRough⟩
    have heNotLower :
        e ∉ squareRootLowPrimeGoSmoothCofactors r
          (squareRootEndpoint R / (q * q * r * p)) := by
      intro heLower
      have heLowerCut :=
        (mem_squareRootLowPrimeGoSmoothCofactors.mp heLower).2.1
      have hden2Pos : 0 < q * q * r * p :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hqData.1.pos hqData.1.pos) hr.pos) hp.pos
      have hleRaw : (q * q * r * p) * e ≤ squareRootEndpoint R :=
        (Nat.le_div_iff_mul_le hden2Pos).1 heLowerCut
      have hle : q * q * r * e * p ≤ squareRootEndpoint R := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hleRaw
      exact (Nat.not_lt_of_ge hle) hcross
    have hcrossMem : e ∈ stableFarReturnedCrossingCofactors R r p q :=
      Finset.mem_sdiff.mpr ⟨heUpper, heNotLower⟩
    have hqrp : q * r * p ≤ squareRootEndpoint R := by
      have heOne : 1 ≤ e := he1
      have hle : q * r * p ≤ q * r * e * p := by
        have h := Nat.mul_le_mul_left (q * r) (Nat.mul_le_mul_right p heOne)
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
      exact hle.trans hcut
    have hqUpper : q ≤ squareRootEndpoint R / (r * p) := by
      have hrpPos : 0 < r * p := Nat.mul_pos hr.pos hp.pos
      apply (Nat.le_div_iff_mul_le hrpPos).2
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hqrp
    have hqReturned : q ∈ stableFarReturnedOldOwners R r p :=
      mem_frozenPrimeUniverseHighPrimeSet.mpr
        ⟨hqData.1, hrq, hqUpper⟩
    exact Finset.mem_filter.mpr ⟨hqReturned, hcrossMem⟩
  · intro hqArith
    rcases Finset.mem_filter.mp hqArith with ⟨hqReturned, heCross⟩
    rcases mem_frozenPrimeUniverseHighPrimeSet.mp hqReturned with
      ⟨hqPrime, hrq, hqUpper⟩
    rcases Finset.mem_sdiff.mp heCross with ⟨heUpper, heNotLower⟩
    have heUpperCut :=
      (mem_squareRootLowPrimeGoSmoothCofactors.mp heUpper).2.1
    have hdenPos : 0 < q * r * p :=
      Nat.mul_pos (Nat.mul_pos hqPrime.pos hr.pos) hp.pos
    have hcutRaw : (q * r * p) * e ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hdenPos).1 heUpperCut
    have hcut : q * r * e * p ≤ squareRootEndpoint R := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcutRaw
    have hden2Pos : 0 < q * q * r * p :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hqPrime.pos hqPrime.pos) hr.pos) hp.pos
    have hcross : squareRootEndpoint R < q * q * r * e * p := by
      by_contra hnot
      have hle : q * q * r * e * p ≤ squareRootEndpoint R := Nat.le_of_not_gt hnot
      have hleRaw : (q * q * r * p) * e ≤ squareRootEndpoint R := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hle
      have heLowerCut : e ≤ squareRootEndpoint R / (q * q * r * p) :=
        (Nat.le_div_iff_mul_le hden2Pos).2 hleRaw
      have heLower :
          e ∈ squareRootLowPrimeGoSmoothCofactors r
            (squareRootEndpoint R / (q * q * r * p)) :=
        mem_squareRootLowPrimeGoSmoothCofactors.mpr
          ⟨he1, heLowerCut, heSq, heRough⟩
      exact heNotLower heLower
    have hqrp : q * r * p ≤ squareRootEndpoint R := by
      have heOne : 1 ≤ e := he1
      have hle : q * r * p ≤ q * r * e * p := by
        have h := Nat.mul_le_mul_left (q * r) (Nat.mul_le_mul_right p heOne)
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
      exact hle.trans hcut
    have hqR : q < R := by
      by_contra hnot
      have hRq : R ≤ q := Nat.le_of_not_gt hnot
      have hRp : R ≤ p := by omega
      have hRR : R * R ≤ q * p := Nat.mul_le_mul hRq hRp
      have hrOne : 1 ≤ r := hr.one_le
      have hqp : q * p ≤ q * r * p := by
        have h := Nat.mul_le_mul_left q (Nat.mul_le_mul_right p hrOne)
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
      exact (Nat.not_lt_of_ge (hRR.trans (hqp.trans hqrp))) hXlt
    exact Finset.mem_filter.mpr
      ⟨mem_primesUpTo.mpr ⟨hqPrime, Nat.le_pred_of_lt hqR⟩,
        hrq, hcut, hcross⟩

/-- Therefore the arithmetic multiplicity is exactly the repository's physical
crossing multiplicity on every actual returned child. -/
theorem lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_returnedMultiplicity
    {R r p e : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p)
    (he : e ∈ stableFarReturnedDescendedCofactors R r p) :
    lowWheelFarPrimeQ2CrossingNextMultiplicity R (r, (e, p)) =
      stableFarReturnedCrossingMultiplicity R r p e := by
  have hy := stableFarReturnedDescendedCofactor_mem_physical hr hrR hp hpR he
  rw [lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_ownerSet_card hy,
    lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_returnedFilter hr hrR hp hpR he]
  rfl

/-- Integer form of the actual physical centered returned fibre. -/
def stableFarReturnedPhysicalCenteredMassInt (R r p : ℕ) : ℤ :=
  ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
    (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R (r, (e, p)) : ℤ)) * μ e

/-- **Physical/arithmetic returned-fibre bridge.**  After signed Fubini, the
actual stable-far multiplicity field is exactly the frozen-prefix/window object
above.  No coefficient norm or occurrence count remains. -/
theorem stableFarReturnedPhysicalCenteredMassInt_eq_centeredMass
    {R r p : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p) :
    stableFarReturnedPhysicalCenteredMassInt R r p =
      stableFarReturnedCenteredMass R r p := by
  rw [stableFarReturnedCenteredMass_eq_multiplicity hr hp]
  unfold stableFarReturnedPhysicalCenteredMassInt
  apply Finset.sum_congr rfl
  intro e he
  rw [lowWheelFarPrimeQ2CrossingNextMultiplicity_eq_returnedMultiplicity
    hr hrR hp hpR he]

end RHLean.Proof
