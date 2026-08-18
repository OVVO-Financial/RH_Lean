import Mathlib
import RHLean.Analysis.MertensZetaIdentityContinuation
import RHLean.Analysis.PhysicalCenteredDistinguishedPrimeOperator
import RHLean.Analysis.SquarePrefixMertensBridge
import RHLean.Proof.HeightShellGram

/-!
# The forward Mertens-energy implication to the Riemann hypothesis

The preceding Mertens layers construct a holomorphic continuation `F` on
`Re(s) > 1/2` and prove

`riemannZeta s * F s = 1`

there away from the pole `s = 1`.  Hence zeta is zero-free strictly to the
right of the critical line.

To exclude a nontrivial zero strictly to the left, this file uses the completed
Riemann zeta function.  Mathlib's exact zero set for `Gammaℝ` says that the
Archimedean factor vanishes only at nonpositive even integers.  The zero at
`s = 0` is excluded by `zeta(0) = -1/2`, while the negative even points are
exactly the trivial-zero locus already excluded by Mathlib's definition of RH.
Thus a nontrivial zeta zero gives a completed-zeta zero; the completed functional
equation reflects it to `1-s`, contradicting right-half-plane zero-freeness.

The second half of the file records the centered distinguished-prime global
Gram route.  It first reconstructs the complete physical prime family exactly,
then expands the global energy into all diagonal and signed cross-prime terms.
No absolute value is taken before the `q,q'` sum is assembled.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace RHLean.Analysis

open Complex
open RestrictedPrimeTransitionOperator
open RHLean.Proof

/-- The propagated reciprocal identity immediately rules out zeta zeros
strictly to the right of the critical line. -/
theorem riemannZeta_ne_zero_of_half_lt_re
    (hM : MertensEnergyBoundedStatement) {s : ℂ}
    (hs : (1 : ℝ) / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hprod :=
    riemannZeta_mul_mertensMellinContinuation_eq_one_of_half_lt_re
      hM hs hs1
  rw [hz, zero_mul] at hprod
  exact zero_ne_one hprod

/-- At a nontrivial candidate zero, the completed-zeta Archimedean factor is
nonzero.  Mathlib identifies its zero set exactly with the nonpositive even
integers. -/
private theorem GammaR_ne_zero_of_not_trivial
    {s : ℂ} (hs0 : s ≠ 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    Gammaℝ s ≠ 0 := by
  intro hGamma
  rcases Gammaℝ_eq_zero_iff.mp hGamma with ⟨n, hn⟩
  cases n with
  | zero =>
      apply hs0
      simpa using hn
  | succ n =>
      apply htriv
      refine ⟨n, ?_⟩
      simpa [Nat.cast_succ] using hn

/-- The repository's squared Mertens-energy criterion implies Mathlib's formal
Riemann hypothesis, with no caller-supplied classical Mertens/RH criterion. -/
theorem riemannHypothesis_of_mertensEnergy
    (hM : MertensEnergyBoundedStatement) :
    RiemannHypothesis := by
  intro s hz hnontriv hs1
  by_cases hcrit : s.re = (1 : ℝ) / 2
  · exact hcrit
  have hnotRight : ¬(1 : ℝ) / 2 < s.re := by
    intro hright
    exact (riemannZeta_ne_zero_of_half_lt_re hM hright hs1) hz
  have hleft : s.re < (1 : ℝ) / 2 := by
    exact lt_of_le_of_ne (le_of_not_gt hnotRight) hcrit
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hGamma : Gammaℝ s ≠ 0 :=
    GammaR_ne_zero_of_not_trivial hs0 hnontriv
  have hcompleted : completedRiemannZeta s = 0 := by
    have hdef := riemannZeta_def_of_ne_zero hs0
    have hdiv : completedRiemannZeta s / Gammaℝ s = 0 := by
      rw [← hdef, hz]
    simpa [hGamma] using hdiv
  have hrefCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub s, hcompleted]
  have href0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    exact (sub_eq_zero.mp h).symm
  have hrefZeta : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero href0, hrefCompleted]
    simp
  have hrefRe : (1 : ℝ) / 2 < (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  have href1 : 1 - s ≠ 1 := by
    intro h
    exact hs0 (sub_eq_self.mp h)
  exfalso
  exact (riemannZeta_ne_zero_of_half_lt_re hM hrefRe href1) hrefZeta

/-! ## Global centered distinguished-prime reconstruction -/

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
set and exactly zero elsewhere. -/
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

/-- **Exact global reconstruction.**  This is
`A_R^c = sum_{R<q<=R^2-1, q prime} A^c_{R,q}` coefficient-for-coefficient,
before any norm is taken. -/
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
assembled.  The natural range adds no nonphysical contribution. -/
def globalCenteredDistinguishedPrimeActionCoordinate
    (R : ℕ) (x : SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) : ℂ :=
  heightShellSum
    (centeredDistinguishedPrimeActionCoordinateShell R x s)
    (squareRootEndpoint R + 1)

/-- Action-level exact reconstruction over the canonical physical prime set. -/
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

/-- Unit-weight global energy after the complete `q`-sum is assembled. -/
def globalCenteredDistinguishedPrimeEnergyAt
    (R : ℕ) (x : SignedPrimeHitState → ℂ) : ℝ :=
  ‖globalCenteredDistinguishedPrimeAction R x none‖ ^ 2 +
    ∑ s : PrimeActiveLabel,
      ‖globalCenteredDistinguishedPrimeAction R x (some s)‖ ^ 2

/-- The complex cross-prime Gram entry
`G_R(q,q') = <A^c_{R,q}x, A^c_{R,q'}x>`.  This is signed and no absolute value
appears in its definition. -/
def centeredCrossQGram
    (R q q' : ℕ)
    (x : SignedPrimeHitState → ℂ) : ℂ :=
  restrictedPrimeStateInner
    ((physicalCenteredDistinguishedPrimeChannel R q).action x)
    ((physicalCenteredDistinguishedPrimeChannel R q').action x)

/-- Exact sparse coefficient expansion of one cross-`q` Gram entry. -/
theorem centeredCrossQGram_eq_sparseAction
    (R q q' : ℕ)
    (x : SignedPrimeHitState → ℂ) :
    centeredCrossQGram R q q' x =
      star ((physicalCenteredDistinguishedPrimeChannel R q).inactiveInactive *
          x none +
        (physicalCenteredDistinguishedPrimeChannel R q).activeInputForm x) *
      ((physicalCenteredDistinguishedPrimeChannel R q').inactiveInactive *
          x none +
        (physicalCenteredDistinguishedPrimeChannel R q').activeInputForm x) +
      ∑ s : PrimeActiveLabel,
        star ((physicalCenteredDistinguishedPrimeChannel R q).activeToInactive s *
            x none) *
          ((physicalCenteredDistinguishedPrimeChannel R q').activeToInactive s *
            x none) := by
  rfl

/-- Coordinate-first diagonal part of the exact global Gram. -/
def globalCenteredDistinguishedPrimeDiagonalEnergyAt
    (R : ℕ) (x : SignedPrimeHitState → ℂ) : ℝ :=
  heightShellDiagonalEnergy
      (centeredDistinguishedPrimeActionCoordinateShell R x none)
      (squareRootEndpoint R + 1) +
    ∑ s : PrimeActiveLabel,
      heightShellDiagonalEnergy
        (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
        (squareRootEndpoint R + 1)

/-- Coordinate-first signed off-diagonal part. -/
def globalCenteredDistinguishedPrimeOffDiagonalGramAt
    (R : ℕ) (x : SignedPrimeHitState → ℂ) : ℝ :=
  heightShellOffDiagonalGram (𝕜 := ℂ)
      (centeredDistinguishedPrimeActionCoordinateShell R x none)
      (squareRootEndpoint R + 1) +
    ∑ s : PrimeActiveLabel,
      heightShellOffDiagonalGram (𝕜 := ℂ)
        (centeredDistinguishedPrimeActionCoordinateShell R x (some s))
        (squareRootEndpoint R + 1)

/-- Exact global energy identity before rewriting the two pieces as `q,q'`
Gram sums. -/
theorem globalCenteredDistinguishedPrimeEnergyAt_eq_diagonal_add_offDiagonal
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeEnergyAt R x =
      globalCenteredDistinguishedPrimeDiagonalEnergyAt R x +
        2 * globalCenteredDistinguishedPrimeOffDiagonalGramAt R x := by
  unfold globalCenteredDistinguishedPrimeEnergyAt
    globalCenteredDistinguishedPrimeAction
    globalCenteredDistinguishedPrimeActionCoordinate
    globalCenteredDistinguishedPrimeDiagonalEnergyAt
    globalCenteredDistinguishedPrimeOffDiagonalGramAt
  rw [energy_sum_heightShells (𝕜 := ℂ)]
  simp_rw [energy_sum_heightShells (𝕜 := ℂ)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Real part of a complex self-product is squared norm. -/
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

/-- Diagonal coordinate energy is exactly the sum of the self-Gram entries. -/
theorem globalCenteredDistinguishedPrimeDiagonalEnergyAt_eq_crossQ
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeDiagonalEnergyAt R x =
      ∑ q ∈ Finset.range (squareRootEndpoint R + 1),
        (centeredCrossQGram R q q x).re := by
  classical
  unfold globalCenteredDistinguishedPrimeDiagonalEnergyAt
    heightShellDiagonalEnergy centeredCrossQGram restrictedPrimeStateInner
    centeredDistinguishedPrimeActionCoordinateShell
  simp_rw [map_add, map_sum]
  simp_rw [re_star_mul_self_eq_norm_sq]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

/-- The coordinate off-diagonal form is exactly the nested `q < q'` sum of
real cross-prime Gram entries. -/
theorem globalCenteredDistinguishedPrimeOffDiagonalGramAt_eq_crossQ
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeOffDiagonalGramAt R x =
      ∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
        ∑ q ∈ Finset.range q',
          (centeredCrossQGram R q q' x).re := by
  classical
  unfold globalCenteredDistinguishedPrimeOffDiagonalGramAt
    heightShellOffDiagonalGram shellReInner centeredCrossQGram
    restrictedPrimeStateInner
    centeredDistinguishedPrimeActionCoordinateShell
  simp_rw [map_add, map_sum]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ s : PrimeActiveLabel,
        ∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
          ∑ q ∈ Finset.range q',
            (star ((physicalCenteredDistinguishedPrimeChannel R q).action x (some s)) *
              (physicalCenteredDistinguishedPrimeChannel R q').action x (some s)).re) =
      ∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
        ∑ s : PrimeActiveLabel,
          ∑ q ∈ Finset.range q',
            (star ((physicalCenteredDistinguishedPrimeChannel R q).action x (some s)) *
              (physicalCenteredDistinguishedPrimeChannel R q').action x (some s)).re := by
          rw [Finset.sum_comm]
    _ =
      ∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
        ∑ q ∈ Finset.range q',
          ∑ s : PrimeActiveLabel,
            (star ((physicalCenteredDistinguishedPrimeChannel R q).action x (some s)) *
              (physicalCenteredDistinguishedPrimeChannel R q').action x (some s)).re := by
          apply Finset.sum_congr rfl
          intro q' hq'
          rw [Finset.sum_comm]

/-- **Exact requested cross-`q` expansion.**  Every off-diagonal interaction is
part of the main signed object; no triangle inequality has replaced it. -/
theorem globalCenteredDistinguishedPrimeEnergyAt_eq_crossQGram
    (R : ℕ) (x : SignedPrimeHitState → ℂ) :
    globalCenteredDistinguishedPrimeEnergyAt R x =
      (∑ q ∈ Finset.range (squareRootEndpoint R + 1),
        (centeredCrossQGram R q q x).re) +
      2 *
        (∑ q' ∈ Finset.range (squareRootEndpoint R + 1),
          ∑ q ∈ Finset.range q',
            (centeredCrossQGram R q q' x).re) := by
  rw [globalCenteredDistinguishedPrimeEnergyAt_eq_diagonal_add_offDiagonal,
    globalCenteredDistinguishedPrimeDiagonalEnergyAt_eq_crossQ,
    globalCenteredDistinguishedPrimeOffDiagonalGramAt_eq_crossQ]

/-- **Open analytic proposition.**  The physical input family is an explicit
parameter until its exact Mertens reconstruction is proved. -/
def CenteredDistinguishedPrimeGlobalGramBoundedStatement
    (x : ℕ → SignedPrimeHitState → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R : ℕ, 2 ≤ R →
        globalCenteredDistinguishedPrimeEnergyAt R (x R) ≤
          C * Real.rpow (R : ℝ) (2 + ε)

/-- Exact arithmetic bridge required to identify a chosen global centered input
with the repository's square-prefix Mertens energy.  This records theorem data,
not an axiom or an assumed estimate. -/
structure CenteredDistinguishedPrimeMertensReconstruction
    (x : ℕ → SignedPrimeHitState → ℂ) : Prop where
  energy_eq_squarePrefix :
    ∀ n : ℕ, 1 ≤ n →
      globalCenteredDistinguishedPrimeEnergyAt (n + 1) (x (n + 1)) =
        ‖squarePrefixMertens n‖ ^ 2

/-- Once exact Mertens reconstruction is supplied, the global Gram bound is the
protected square-prefix energy criterion. -/
theorem squarePrefixEnergyBounded_of_centeredDistinguishedPrimeGlobalGram
    {x : ℕ → SignedPrimeHitState → ℂ}
    (hrecon : CenteredDistinguishedPrimeMertensReconstruction x)
    (hgram : CenteredDistinguishedPrimeGlobalGramBoundedStatement x) :
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

/-- Protected terminal: exact physical reconstruction plus the signed global
cross-`q` Gram bound implies Mathlib's Riemann hypothesis through the existing
square-prefix and Mertens continuation chain. -/
theorem riemannHypothesis_of_centeredDistinguishedPrimeGlobalGram
    {x : ℕ → SignedPrimeHitState → ℂ}
    (hrecon : CenteredDistinguishedPrimeMertensReconstruction x)
    (hgram : CenteredDistinguishedPrimeGlobalGramBoundedStatement x) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mertensEnergy
  apply mertensEnergyBounded_of_squarePrefixEnergyBounded
  exact squarePrefixEnergyBounded_of_centeredDistinguishedPrimeGlobalGram
    hrecon hgram

end RHLean.Analysis