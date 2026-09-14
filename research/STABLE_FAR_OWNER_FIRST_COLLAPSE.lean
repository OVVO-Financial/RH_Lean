import RHLean.Proof.LowWheelCanonicalSqrtDenseContraction
import RHLean.Proof.SquareRootPredecessorPrimeCells
import RHLean.Proof.StableFarWallSignedReassembly

/-!
# Stable-far owner-first returned-window collapse

The returned-fibre Fubini developed after #691-#693 organizes strict crossings
by the returned owner. Here we reverse that Fubini order and keep one old
crossing owner `q` and one far-prime coordinate `p` fixed.

For every returned prime `r < q`, the crossing cofactors occupy the frozen
window

`F_{r^-}(X/(q^2*p*r), X/(q*p*r)]`.

Summing these windows over all returned owners is not a new multiplicity
problem. The existing high-window Euler telescope consumes the complete
`r < q` chronology exactly. The residue is the empty-prime unit window minus
the single moving parent state `F_q(X/(q*p))`.

The second section identifies the resulting q-smooth window with the literal
strict-crossing physical cofactor fibre. No norm, absolute value, asymptotic
input, or Mertens estimate is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- **Owner-first collapse of every nonunit returned window.**

At fixed old owner `q` and far-prime coordinate `p`, summing all returned-owner
windows `r < q` telescopes exactly to the unit window minus the moving
`q`-boundary. This is the arithmetic identity behind the occurrence-level
statement that the unit return and all nonunit returns recombine before any
energy is taken. -/
theorem stableFar_ownerFirst_returnedWindows_eq_unitWindow_sub_parent
    (X q p : ℕ) (hq : q.Prime) (hp : p.Prime) :
    (∑ r ∈ frozenPrimeUniverseHighPrimeSet 1 (q - 1),
      frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
        (X / (q * q * p * r)) (X / (q * p * r))) =
      frozenPrimeUniverseWindowMass (primesUpTo 1)
        (X / (q * q * p)) (X / (q * p)) -
      frozenPrimeUniverseMass (primesUpTo q) (X / (q * p)) := by
  have h1q : 1 ≤ q - 1 := by omega
  let A : ℕ := X / (q * q * p)
  let B : ℕ := X / (q * p)
  have hqq : q ≤ q * q := by
    simpa using Nat.mul_le_mul_left q hq.one_le
  have hden : q * p ≤ q * q * p := by
    exact Nat.mul_le_mul_right p hqq
  have hdenPos : 0 < q * p := Nat.mul_pos hq.pos hp.pos
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact Nat.div_le_div_left hden hdenPos
  have htel :=
    frozenPrimeUniverse_highWindow_telescope 1 (q - 1) A B h1q hAB
  have hBdiv : B / q = A := by
    dsimp [A, B]
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor q B hq
  unfold predecessorPrimeMass at hstep
  rw [hBdiv] at hstep
  have hwindow :
      frozenPrimeUniverseWindowMass (primesUpTo (q - 1)) A B =
        frozenPrimeUniverseMass (primesUpTo q) B := by
    rw [frozenPrimeUniverseWindowMass_eq_sub hAB]
    exact hstep.symm
  rw [hwindow] at htel
  simpa [A, B, Nat.div_div_eq_div_mul, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using htel

/-! ## The same collapse on the literal physical crossing fibre -/

/-- Whole low cofactors `d` on the strict q^2 crossing at fixed old owner `q`
and fixed far prime `p`.  The upper prefix is exactly the first-contact cutoff;
the deleted lower prefix is exactly the q^2-descended half. -/
def stableFarOldOwnerCrossingCofactors
    (R q p : ℕ) : Finset ℕ :=
  squareRootLowPrimeGoSmoothCofactors q
      (squareRootEndpoint R / (q * p)) \
    squareRootLowPrimeGoSmoothCofactors q
      (squareRootEndpoint R / (q * q * p))

/-- The q^2 lower prefix is contained in the first-contact prefix. -/
theorem stableFarOldOwnerCrossingCofactors_lower_subset_upper
    {R q p : ℕ} (hq : q.Prime) (hp : p.Prime) :
    squareRootLowPrimeGoSmoothCofactors q
        (squareRootEndpoint R / (q * q * p)) ⊆
      squareRootLowPrimeGoSmoothCofactors q
        (squareRootEndpoint R / (q * p)) := by
  have hqq : q ≤ q * q := by
    simpa using Nat.mul_le_mul_left q hq.one_le
  have hden : q * p ≤ q * q * p := Nat.mul_le_mul_right p hqq
  have hdenPos : 0 < q * p := Nat.mul_pos hq.pos hp.pos
  have hcut :
      squareRootEndpoint R / (q * q * p) ≤
        squareRootEndpoint R / (q * p) :=
    Nat.div_le_div_left hden hdenPos
  intro d hd
  rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hd with
    ⟨hd1, hdCut, hdSq, hdRough⟩
  exact mem_squareRootLowPrimeGoSmoothCofactors.mpr
    ⟨hd1, hdCut.trans hcut, hdSq, hdRough⟩

/-- The arithmetic q-smooth window is exactly the literal strict-crossing
physical triple fibre at fixed `(q,p)`. -/
theorem mem_stableFarOldOwnerCrossingCofactors_iff_crossingTriple
    {R q p d : ℕ} (hq : q.Prime) (hqR : q < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p) :
    d ∈ stableFarOldOwnerCrossingCofactors R q p ↔
      (q, (d, p)) ∈ lowWheelFarPrimeQ2CrossingTriples R := by
  constructor
  · intro hd
    rcases Finset.mem_sdiff.mp hd with ⟨hUpper, hNotLower⟩
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hUpper with
      ⟨hd1, hdCut, hdSq, hdRough⟩
    have hdenPos : 0 < q * p := Nat.mul_pos hq.pos hp.pos
    have hcutRaw : d * (q * p) ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hdenPos).1 hdCut
    have hcut : q * d * p ≤ squareRootEndpoint R := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcutRaw
    have hbase : (q, (d, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
      lowWheelFarPrimeLowCofactorTriple_mem_of_data
        hq hqR hd1 hp hpR hdSq hdRough hcut
    have hden2Pos : 0 < q * q * p :=
      Nat.mul_pos (Nat.mul_pos hq.pos hq.pos) hp.pos
    have hcross : squareRootEndpoint R < q * q * d * p := by
      by_contra hnot
      have hle : q * q * d * p ≤ squareRootEndpoint R :=
        Nat.le_of_not_gt hnot
      have hleRaw : d * (q * q * p) ≤ squareRootEndpoint R := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hle
      have hdLowerCut : d ≤ squareRootEndpoint R / (q * q * p) :=
        (Nat.le_div_iff_mul_le hden2Pos).2 hleRaw
      have hLower :
          d ∈ squareRootLowPrimeGoSmoothCofactors q
            (squareRootEndpoint R / (q * q * p)) :=
        mem_squareRootLowPrimeGoSmoothCofactors.mpr
          ⟨hd1, hdLowerCut, hdSq, hdRough⟩
      exact hNotLower hLower
    exact Finset.mem_filter.mpr ⟨hbase, hcross⟩
  · intro ht
    rcases Finset.mem_filter.mp ht with ⟨hbase, hcross⟩
    rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
      ⟨_hq, _hqR, hd1, _hp, _hpR, hdSq, hdRough, hcut⟩
    have hdenPos : 0 < q * p := Nat.mul_pos hq.pos hp.pos
    have hcutRaw : d * (q * p) ≤ squareRootEndpoint R := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcut
    have hdUpperCut : d ≤ squareRootEndpoint R / (q * p) :=
      (Nat.le_div_iff_mul_le hdenPos).2 hcutRaw
    have hUpper :
        d ∈ squareRootLowPrimeGoSmoothCofactors q
          (squareRootEndpoint R / (q * p)) :=
      mem_squareRootLowPrimeGoSmoothCofactors.mpr
        ⟨hd1, hdUpperCut, hdSq, hdRough⟩
    have hden2Pos : 0 < q * q * p :=
      Nat.mul_pos (Nat.mul_pos hq.pos hq.pos) hp.pos
    have hNotLower :
        d ∉ squareRootLowPrimeGoSmoothCofactors q
          (squareRootEndpoint R / (q * q * p)) := by
      intro hLower
      have hdLowerCut :=
        (mem_squareRootLowPrimeGoSmoothCofactors.mp hLower).2.1
      have hleRaw : d * (q * q * p) ≤ squareRootEndpoint R :=
        (Nat.le_div_iff_mul_le hden2Pos).1 hdLowerCut
      have hle : q * q * d * p ≤ squareRootEndpoint R := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hleRaw
      exact (Nat.not_lt_of_ge hle) hcross
    exact Finset.mem_sdiff.mpr ⟨hUpper, hNotLower⟩

/-- The exact signed crossing-cofactor mass at fixed `(q,p)`. -/
def stableFarOldOwnerCrossingCofactorMass
    (R q p : ℕ) : ℤ :=
  ∑ d ∈ stableFarOldOwnerCrossingCofactors R q p, μ d

/-- **Physical owner-first parent collapse.**  The complete signed strict
crossing cofactor fibre at fixed old owner `q` and far prime `p` is exactly the
admitted-q parent state at cutoff `X_R/(q*p)`. -/
theorem stableFarOldOwnerCrossingCofactorMass_eq_parent
    {R q p : ℕ} (hq : q.Prime) (hp : p.Prime) :
    stableFarOldOwnerCrossingCofactorMass R q p =
      frozenPrimeUniverseMass (primesUpTo q)
        (squareRootEndpoint R / (q * p)) := by
  have hsub := stableFarOldOwnerCrossingCofactors_lower_subset_upper
    (R := R) (q := q) (p := p) hq hp
  have hsum := Finset.sum_sdiff hsub (f := fun d => μ d)
  have hUpper := frozenPrimeUniverseMass_eq_goSmoothCofactorSum
    (r := q) (Y := squareRootEndpoint R / (q * p)) hq
  have hLower := frozenPrimeUniverseMass_eq_goSmoothCofactorSum
    (r := q) (Y := squareRootEndpoint R / (q * q * p)) hq
  have hBdiv :
      (squareRootEndpoint R / (q * p)) / q =
        squareRootEndpoint R / (q * q * p) := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor
      q (squareRootEndpoint R / (q * p)) hq
  unfold predecessorPrimeMass at hstep
  rw [hBdiv] at hstep
  unfold stableFarOldOwnerCrossingCofactorMass
    stableFarOldOwnerCrossingCofactors
  rw [hUpper, hLower]
  have hdiff :
      (∑ d ∈ squareRootLowPrimeGoSmoothCofactors q
          (squareRootEndpoint R / (q * p)) \
        squareRootLowPrimeGoSmoothCofactors q
          (squareRootEndpoint R / (q * q * p)), μ d) =
        frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / (q * p)) -
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / (q * q * p)) := by
    exact (eq_sub_iff_add_eq).2 hsum
  rw [hdiff]
  exact hstep.symm

end RHLean.Proof
