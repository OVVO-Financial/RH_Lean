import Mathlib
import RHLean.Analysis.PhysicalCenteredDistinguishedPrimeOperator
import RHLean.Analysis.MertensEnergyRHForward
import RHLean.Proof.HeightShellGram

/-!
# Global centered distinguished-prime Gram

The fixed-prime scalar contraction theorem has no useful uniform gap.  The
remaining object in the centered distinguished-prime architecture must therefore
retain the signed interaction between distinct distinguished primes until after
the full prime sum is assembled.

This module does exactly that.

* `centeredDistinguishedPrimeSet R` is the canonical transport-prime range
  `R < q <= R^2 - 1`.
* `physicalCenteredDistinguishedPrimeChannel R q` is the physical centered
  operator of `PhysicalCenteredDistinguishedPrimeOperator` on that range and is
  exactly zero off it.
* `globalPhysicalCenteredDistinguishedPrimeOperator R` is the coefficientwise
  finite sum of those physical channels.  The reconstruction theorem is exact.
* `centeredCrossQGram` is the weighted Hermitian interaction of two complete
  centered channel outputs.  No absolute value occurs in its definition.
* `globalCenteredDistinguishedPrimeEnergyAt` is the weighted energy after the
  complete `q`-sum has been assembled.
* the exact Gram theorem expands that energy into the signed diagonal plus the
  complete `q < q'` off-diagonal interaction.

The analytic estimate is deliberately only a named proposition.  A separate
exact Mertens-reconstruction structure records the remaining arithmetic bridge
needed before that proposition can feed the protected Mertens-to-RH theorem.
No estimate, orthogonality assumption, or triangle-inequality replacement is
introduced here.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace RHLean.Analysis

open RestrictedPrimeTransitionOperator
open RHLean.Proof

/-- Canonical distinguished transport primes at square-root scale `R`. -/
def centeredDistinguishedPrimeSet (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime

/-- The zero operator in the certified thirteen-coefficient class. -/
def zeroRestrictedPrimeTransitionOperator : RestrictedPrimeTransitionOperator where
  inactiveInactive := 0
  inactiveToActive := fun _ => 0
  activeToInactive := fun _ => 0

@[simp] theorem zeroRestrictedPrimeTransitionOperator_action
    (x : SignedPrimeHitState → ℂ) (s : SignedPrimeHitState) :
    zeroRestrictedPrimeTransitionOperator.action x s = 0 := by
  rcases s with _ | s
  · simp [zeroRestrictedPrimeTransitionOperator,
      RestrictedPrimeTransitionOperator.action,
      RestrictedPrimeTransitionOperator.activeInputForm]
  · rfl

/-- Total fixed-`q` centered channel: physical on the canonical transport-prime
set and exactly zero elsewhere.  This lets the global Gram be indexed by an
ordinary natural-number range without adding any nonphysical term. -/
def physicalCenteredDistinguishedPrimeChannel
    (R q : ℕ) : RestrictedPrimeTransitionOperator :=
  if hq : q ∈ centeredDistinguishedPrimeSet R then
    let hfilter := Finset.mem_filter.mp hq
    let hIoc := Finset.mem_Ioc.mp hfilter.1
    physicalCenteredDistinguishedPrimeOperator R q hfilter.2 hIoc.1
  else
    zeroRestrictedPrimeTransitionOperator

@[simp] theorem physicalCenteredDistinguishedPrimeChannel_eq_zero_of_not_mem
    (R q : ℕ) (hq : q ∉ centeredDistinguishedPrimeSet R) :
    physicalCenteredDistinguishedPrimeChannel R q =
      zeroRestrictedPrimeTransitionOperator := by
  simp [physicalCenteredDistinguishedPrimeChannel, hq]

/-- Every canonical transport prime lies in the natural range ending at the
complete-square endpoint. -/
theorem centeredDistinguishedPrimeSet_subset_range (R : ℕ) :
    centeredDistinguishedPrimeSet R ⊆
      Finset.range (squareRootEndpoint R + 1) := by
  intro q hq
  have hIoc := (Finset.mem_filter.mp hq).1
  have hqX := (Finset.mem_Ioc.mp hIoc).2
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hqX)

/-- Coefficientwise finite sum in the restricted operator class. -/
def restrictedPrimeOperatorSum
    (S : Finset ℕ)
    (A : ℕ → RestrictedPrimeTransitionOperator) :
    RestrictedPrimeTransitionOperator where
  inactiveInactive := ∑ q ∈ S, (A q).inactiveInactive
  inactiveToActive := fun t => ∑ q ∈ S, (A q).inactiveToActive t
  activeToInactive := fun s => ∑ q ∈ S, (A q).activeToInactive s

/-- The global physical centered operator at scale `R`. -/
def globalPhysicalCenteredDistinguishedPrimeOperator
    (R : ℕ) : RestrictedPrimeTransitionOperator :=
  restrictedPrimeOperatorSum (centeredDistinguishedPrimeSet R)
    (physicalCenteredDistinguishedPrimeChannel R)

/-- **Exact global reconstruction.**  The global centered operator is the
coefficientwise sum over all and only the physical transport primes
`R < q <= R^2 - 1`.  No norm or absolute value has been taken. -/
theorem globalPhysicalCenteredDistinguishedPrimeOperator_reconstruction
    (R : ℕ) :
    globalPhysicalCenteredDistinguishedPrimeOperator R =
      restrictedPrimeOperatorSum (centeredDistinguishedPrimeSet R)
        (physicalCenteredDistinguishedPrimeChannel R) := rfl

@[simp] theorem globalPhysicalCenteredDistinguishedPrimeOperator_inactiveInactive
    (R : ℕ) :
    (globalPhysicalCenteredDistinguishedPrimeOperator R).inactiveInactive =
      ∑ q ∈ centeredDistinguishedPrimeSet R,
        (physicalCenteredDistinguishedPrimeChannel R q).inactiveInactive := rfl

@[simp] theorem globalPhysicalCenteredDistinguishedPrimeOperator_inactiveToActive
    (R : ℕ) (t : PrimeActiveLabel) :
    (globalPhysicalCenteredDistinguishedPrimeOperator R).inactiveToActive t =
      ∑ q ∈ centeredDistinguishedPrimeSet R,
        (physicalCenteredDistinguishedPrimeChannel R q).inactiveToActive t := rfl

@[simp] theorem globalPhysicalCenteredDistinguishedPrimeOperator_activeToInactive
    (R : ℕ) (s : PrimeActiveLabel) :
    (globalPhysicalCenteredDistinguishedPrimeOperator R).activeToInactive s =
      ∑ q ∈ centeredDistinguishedPrimeSet R,
        (physicalCenteredDistinguishedPrimeChannel R q).activeToInactive s := rfl

/-- One output coordinate of one centered fixed-prime action. -/
def centeredDistinguishedPrimeActionCoordinateShell
    (R : ℕ) (x : SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) (q : ℕ) : ℂ :=
  (physicalCenteredDistinguishedPrimeChannel R q).action x s

/-- One output coordinate after the entire distinguished-prime family has been
assembled.  The natural range contains no extra contribution because the shell
is exactly zero off `centeredDistinguishedPrimeSet R`. -/
def globalCenteredDistinguishedPrimeActionCoordinate
    (R : ℕ) (x : SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) : ℂ :=
  heightShellSum
    (centeredDistinguishedPrimeActionCoordinateShell R x s)
    (squareRootEndpoint R + 1)

/-- The coordinate-level action is exactly the sum over the canonical physical
prime set.  This is the action form of the global reconstruction theorem. -/
theorem globalCenteredDistinguishedPrimeActionCoordinate_reconstruction
    (R : ℕ) (x : SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) :
    globalCenteredDistinguishedPrimeActionCoordinate R x s =
      ∑ q ∈ centeredDistinguishedPrimeSet R,
        (physicalCenteredDistinguishedPrimeChannel R q).action x s := by
  classical
  unfold globalCenteredDistinguishedPrimeActionCoordinate heightShellSum
    centeredDistinguishedPrimeActionCoordinateShell
  symm
  apply Finset.sum_subset (centeredDistinguishedPrimeSet_subset_range R)
  intro q hqRange hqNot
  rw [physicalCenteredDistinguishedPrimeChannel_eq_zero_of_not_mem R q hqNot]
  exact zeroRestrictedPrimeTransitionOperator_action x s

/-- Complete global centered action, assembled before any energy is taken. -/
def globalCenteredDistinguishedPrimeAction
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    SignedPrimeHitState → ℂ :=
  fun s => globalCenteredDistinguishedPrimeActionCoordinate R x s

/-- Weighted Hermitian cross interaction of two centered fixed-prime channels.
This is `⟨A^c_{R,q} x, W A^c_{R,q'} x⟩` for the diagonal inactive/active
Lyapunov weight `W`.  It is intentionally complex-valued and signed. -/
def centeredCrossQGram
    (w : RestrictedPrimeLyapunovWeights)
    (R q q' : ℕ)
    (x : SignedPrimeHitState → ℂ) : ℂ :=
  (w.inactive : ℂ) *
      star ((physicalCenteredDistinguishedPrimeChannel R q).action x none) *
        (physicalCenteredDistinguishedPrimeChannel R q').action x none +
    (w.active : ℂ) *
      ∑ s : PrimeActiveLabel,
        star ((physicalCenteredDistinguishedPrimeChannel R q).action x (some s)) *
          (physicalCenteredDistinguishedPrimeChannel R q').action x (some s)

/-- Exact sparse coefficient expansion of the cross-`q` Gram.  In particular,
the centered inactive-to-active linear forms from different primes interact
*before* any magnitude is taken. -/
theorem centeredCrossQGram_eq_sparseAction
    (w : RestrictedPrimeLyapunovWeights)
    (R q q' : ℕ)
    (x : SignedPrimeHitState → ℂ) :
    centeredCrossQGram w R q q' x =
      (w.inactive : ℂ) *
        star ((physicalCenteredDistinguishedPrimeChannel R q).inactiveInactive *
            x none +
          (physicalCenteredDistinguishedPrimeChannel R q).activeInputForm x) *
        ((physicalCenteredDistinguishedPrimeChannel R q').inactiveInactive *
            x none +
          (physicalCenteredDistinguishedPrimeChannel R q').activeInputForm x) +
      (w.active : ℂ) *
        ∑ s : PrimeActiveLabel,
          star ((physicalCenteredDistinguishedPrimeChannel R q).activeToInactive s *
              x none) *
            ((physicalCenteredDistinguishedPrimeChannel R q').activeToInactive s *
              x none) := by
  rfl

/-- Energy of the fully reconstructed centered family at one input.  The full
prime sum is formed first, and only then are coordinate norms taken. -/
def globalCenteredDistinguishedPrimeEnergyAt
    (w : RestrictedPrimeLyapunovWeights)
    (R : ℕ) (x : SignedPrimeHitState → ℂ) : ℝ :=
  restrictedPrimeLyapunov w (globalCenteredDistinguishedPrimeAction R x)

/-- Coordinate-first diagonal part of the exact global Gram. -/
def globalCenteredDistinguishedPrimeDiagonalEnergyAt
    (w : RestrictedPrimeLyapunovWeights)
    (R : ℕ) (x : SignedPrimeHitState → ℂ) : ℝ :=
  w.inactive *
      heightShellDiagonalEnergy
        (centeredDistinguishedPrimeActionCoordinateShell R x none)
        (squareRootEndpoint R + 1) +
    w.active *
      ∑ s : PrimeActiveLabel,
        heightShellDiagonalEnergy
          (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
          (squareRootEndpoint R + 1)

/-- Coordinate-first off-diagonal part.  It is still signed; no absolute value
has been applied. -/
def globalCenteredDistinguishedPrimeOffDiagonalGramAt
    (w : RestrictedPrimeLyapunovWeights)
    (R : ℕ) (x : SignedPrimeHitState → ℂ) : ℝ :=
  w.inactive *
      heightShellOffDiagonalGram (𝕜 := ℂ)
        (centeredDistinguishedPrimeActionCoordinateShell R x none)
        (squareRootEndpoint R + 1) +
    w.active *
      ∑ s : PrimeActiveLabel,
        heightShellOffDiagonalGram (𝕜 := ℂ)
          (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
          (squareRootEndpoint R + 1)

/-- **Exact signed global Gram identity.**  This is the structural theorem that
must precede every analytic estimate in this architecture. -/
theorem globalCenteredDistinguishedPrimeEnergyAt_eq_diagonal_add_offDiagonal
    (w : RestrictedPrimeLyapunovWeights)
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeEnergyAt w R x =
      globalCenteredDistinguishedPrimeDiagonalEnergyAt w R x +
        2 * globalCenteredDistinguishedPrimeOffDiagonalGramAt w R x := by
  unfold globalCenteredDistinguishedPrimeEnergyAt restrictedPrimeLyapunov
    globalCenteredDistinguishedPrimeAction
    globalCenteredDistinguishedPrimeActionCoordinate
    globalCenteredDistinguishedPrimeDiagonalEnergyAt
    globalCenteredDistinguishedPrimeOffDiagonalGramAt
  rw [energy_sum_heightShells (𝕜 := ℂ)]
  simp_rw [energy_sum_heightShells (𝕜 := ℂ)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The off-diagonal coordinate form is exactly the `q < q'` sum of the real
parts of the complex cross-prime Gram entries. -/
theorem globalCenteredDistinguishedPrimeOffDiagonalGramAt_eq_crossQ
    (w : RestrictedPrimeLyapunovWeights)
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeOffDiagonalGramAt w R x =
      ∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
        ∑ q ∈ Finset.range q',
          (centeredCrossQGram w R q q' x).re := by
  classical
  unfold globalCenteredDistinguishedPrimeOffDiagonalGramAt
    heightShellOffDiagonalGram shellReInner centeredCrossQGram
    centeredDistinguishedPrimeActionCoordinateShell
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q' hq'
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [map_add, map_mul, map_mul, map_sum]
  norm_num
  ring

/-- A scalar complex self-product has real part equal to squared norm. -/
private theorem re_star_mul_self_eq_norm_sq (z : ℂ) :
    (star z * z).re = ‖z‖ ^ 2 := by
  have hcast : (((‖z‖ ^ 2 : ℝ) : ℂ)) = star z * z := by
    calc
      (((‖z‖ ^ 2 : ℝ) : ℂ)) = (Complex.normSq z : ℂ) := by
        rw [Complex.normSq_eq_norm_sq]
      _ = Complex.conj z * z := Complex.normSq_eq_conj_mul_self
      _ = star z * z := rfl
  have hre := congrArg Complex.re hcast
  simpa using hre.symm

/-- The diagonal coordinate form is exactly the sum of the self-Gram entries. -/
theorem globalCenteredDistinguishedPrimeDiagonalEnergyAt_eq_crossQ
    (w : RestrictedPrimeLyapunovWeights)
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeDiagonalEnergyAt w R x =
      ∑ q ∈ Finset.range (squareRootEndpoint R + 1),
        (centeredCrossQGram w R q q x).re := by
  classical
  unfold globalCenteredDistinguishedPrimeDiagonalEnergyAt
    heightShellDiagonalEnergy centeredCrossQGram
    centeredDistinguishedPrimeActionCoordinateShell
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [map_add, map_mul, map_mul, map_sum]
  norm_num
  simp_rw [re_star_mul_self_eq_norm_sq]
  ring

/-- **Requested `q,q'` expansion.**  Every off-diagonal interaction is retained
with its sign.  In particular there is no triangle inequality between the
physical channel sum and this identity. -/
theorem globalCenteredDistinguishedPrimeEnergyAt_eq_crossQGram
    (w : RestrictedPrimeLyapunovWeights)
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeEnergyAt w R x =
      (∑ q ∈ Finset.range (squareRootEndpoint R + 1),
        (centeredCrossQGram w R q q x).re) +
      2 *
        (∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
          ∑ q ∈ Finset.range q',
            (centeredCrossQGram w R q q' x).re) := by
  rw [globalCenteredDistinguishedPrimeEnergyAt_eq_diagonal_add_offDiagonal,
    globalCenteredDistinguishedPrimeDiagonalEnergyAt_eq_crossQ,
    globalCenteredDistinguishedPrimeOffDiagonalGramAt_eq_crossQ]

/-- **Open analytic proposition.**  For a chosen physical input family and
nonnegative Lyapunov weight, the complete signed centered-prime energy has the
critical square-root exponent.  This is a proposition only; no estimate is
asserted or assumed by the module. -/
def CenteredDistinguishedPrimeGlobalGramBoundedStatement
    (w : RestrictedPrimeLyapunovWeights)
    (x : ℕ → SignedPrimeHitState → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        globalCenteredDistinguishedPrimeEnergyAt w R (x R) ≤
          C * Real.rpow (R : ℝ) (2 + ε)

/-- Exact arithmetic reconstruction required to connect a chosen global
centered-operator realization to the repository's square-prefix Mertens field.
This is intentionally a structure of theorem data rather than an axiom. -/
structure CenteredDistinguishedPrimeMertensReconstruction
    (w : RestrictedPrimeLyapunovWeights)
    (x : ℕ → SignedPrimeHitState → ℂ) : Prop where
  energy_eq_squarePrefix :
    ∀ n : ℕ, 1 ≤ n →
      globalCenteredDistinguishedPrimeEnergyAt w (n + 1) (x (n + 1)) =
        ‖squarePrefixMertens n‖ ^ 2

/-- Once the exact Mertens reconstruction is supplied, the open global Gram
bound is already the protected square-prefix energy criterion. -/
theorem squarePrefixEnergyBounded_of_centeredDistinguishedPrimeGlobalGram
    {w : RestrictedPrimeLyapunovWeights}
    {x : ℕ → SignedPrimeHitState → ℂ}
    (hrecon : CenteredDistinguishedPrimeMertensReconstruction w x)
    (hgram : CenteredDistinguishedPrimeGlobalGramBoundedStatement w x) :
    SquarePrefixEnergyBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hgram ε hε
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [squarePrefixMertens, squarePrefixEndpoint, mertensSummatory]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hR : 2 ≤ n + 1 := by omega
    rw [← hrecon.energy_eq_squarePrefix n hn1]
    exact hbound (n + 1) hR

/-- Protected terminal: an exact physical Mertens reconstruction plus the
signed global cross-`q` Gram bound implies Mathlib's Riemann hypothesis through
the repository's existing square-prefix and Mertens continuation chain. -/
theorem riemannHypothesis_of_centeredDistinguishedPrimeGlobalGram
    {w : RestrictedPrimeLyapunovWeights}
    {x : ℕ → SignedPrimeHitState → ℂ}
    (hrecon : CenteredDistinguishedPrimeMertensReconstruction w x)
    (hgram : CenteredDistinguishedPrimeGlobalGramBoundedStatement w x) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  apply mertensEnergyBounded_of_squarePrefixEnergyBounded
  exact squarePrefixEnergyBounded_of_centeredDistinguishedPrimeGlobalGram
    hrecon hgram

end RHLean.Analysis
