import Mathlib
import RHLean.Analysis.DeterministicTGreenKuboComparison
import RHLean.Proof.MiddlePrimeFibreCollapse

open scoped BigOperators

/-!
# Covariance capacity: record descent, and what support exhaustion still owes

`DeterministicTGreenKuboComparison` isolates the one-sided arithmetic frontier

```text
MertensPositiveLagUpperBoundedStatement :
  for every eps > 0, positiveLagPairSum K <= C * K ^ (1 + eps)
```

and proves it gives the protected Mertens energy criterion.  That target is the
right one, and it is worth being precise about its strength: the pair sum runs
over `binom(K,2)` pairs, so the trivial deterministic bound is `O(K^2)`.  A
bound `O(K)` would already give `M(x) = O(sqrt x)` outright.  What RH scale
needs is only `K^(1+eps)`, which is still a full power below the trivial bound.

Two things are recorded here.

## 1. Record descent

The excursion coordinate

```text
excursion(delta, K) = positiveLagPairSum K / K ^ (1 + delta)
```

is supercritical at `K` when it reaches `1`.  `MertensCovarianceDescentStatement`
says every supercritical scale is forced by a strictly smaller supercritical
scale.  Since the scales are natural numbers, that alone forbids a *minimal*
supercritical excursion, hence any supercritical excursion at all, hence gives
the one-sided frontier statement and the Mertens energy criterion.

This is deliberately a descent on the *signed aggregate covariance itself*.  It
never bounds `|C|` by a count of surviving pairs, and it allows every
intermediate signed correction to oscillate arbitrarily; only the normalized
excursion at the two scales is compared.

## 2. What the support-only route still owes

`MiddlePrimeFibreCollapse.norm_mertensSummatory_le_primeProductFrontierCard`
gives the exact support bound `‖M(X)‖ <= F(X, ell)` after Euler parent/child
pairing, and hence a covariance capacity `F (F - 1) / 2`.  That is RH strength
exactly when the exposed frontier is itself of square-root size, which is what
`PrimeProductFrontierRootScaleStatement` asks for and what the theorem below
converts into the energy criterion.

It is stated as a hypothesis because it is measured to be false for the raw
prime cube: the minimising pivot is `ell = 2`, whose frontier is the squarefree
part of the top-half window `(X/2, X]`, and its cardinality tends to
`(2/pi^2) X`.  A linear frontier gives capacity of order `X^2`, a full power
above the target.  See `scripts/CumulativeOthelloBoundary/frontier_capacity.py`.

So support exhaustion alone cannot close the argument, and the next theorem has
to be a signed multi-face statement, not another cardinality statement.

## 3. The two arrows, and why a frontier bound alone closes nothing

Two covariance objects are in play and must not be conflated.

* The **global** integer-order Green--Kubo covariance
  `C(x+1) = sum over 1 <= a < b <= x of mu a * mu b`, which is
  `realMertensPositiveLagPairSum`, and which satisfies the exact square
  expansion with diagonal `x - Z(x)`, `Z` counting the Moebius zeros.
* The **hierarchical Euler frontier** covariance of the terminal-correction
  coordinate, whose worst case over arbitrary deeper sign oscillation is what
  `MiddlePrimeFibreCollapse` bounds by
  `(|G_R| + D_R)^2 - (N_mid + N_top + D_R)` over 2.

No theorem yet identifies or dominates the first by the second.  So the critical
path is two arrows, not one:

```text
Euler frontier covariance  -->  global C(x)  -->  C(x) <= x^(1+eta).
```

`CovarianceEnvelopeDominates` and `CovarianceEnvelopeRootScale` below name the
two arrows for an arbitrary envelope `E`, and
`mertensEnergyBounded_of_covarianceEnvelope` proves that *both together* — and
only both together — give the energy criterion.  A frontier route supplies a
candidate `E`; until it is proved to dominate the global pair sum, however sharp
its own capacity bound is, it bounds a different object.

Two thresholds also should not be conflated.  Crossing the literal `sqrt x` line
is `C(x+1) > Z(x)/2`, and `Z(x)/2 ~ (1 - 6/pi^2) x / 2 ~ 0.196 x`; that is the
threshold of the *false* Mertens conjecture, so no global bound of that shape can
be true.  The RH threshold is the strictly weaker `C(x) <= x^(1+o(1))`, and an
RH-violating excursion of exponent `eps` needs `C(x+1)` of order
`x^(1+2 eps)` — a fixed power above the target, not a constant factor.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## The normalized covariance excursion -/

/-- Aggregate positive-lag covariance at scale `K`, normalized by the critical
power `K ^ (1 + delta)`.  Reaching `1` is exactly being supercritical. -/
def mertensCovarianceExcursion (δ : ℝ) (K : ℕ) : ℝ :=
  realMertensPositiveLagPairSum K / Real.rpow (K : ℝ) (1 + δ)

/-- **No minimal supercritical covariance excursion.**

Every scale whose normalized positive-lag covariance reaches the critical
exponent is forced by a strictly smaller scale that already does.  Nothing is
assumed about how the signed corrections behave in between, and no count of
surviving pairs appears. -/
def MertensCovarianceDescentStatement : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ K : ℕ, 1 ≤ K →
    1 ≤ mertensCovarianceExcursion δ K →
      ∃ d : ℕ, 1 ≤ d ∧ d < K ∧ 1 ≤ mertensCovarianceExcursion δ d

private theorem mertensCovarianceExcursion_lt_one_aux
    (h : MertensCovarianceDescentStatement) {δ : ℝ} (hδ : 0 < δ) :
    ∀ N K : ℕ, K ≤ N → 1 ≤ K → mertensCovarianceExcursion δ K < 1 := by
  intro N
  induction N with
  | zero =>
      intro K hKN hK
      exact absurd hKN (by omega)
  | succ N ih =>
      intro K hKN hK
      by_contra hge
      push_neg at hge
      obtain ⟨d, hd1, hdK, hdex⟩ := h δ hδ K hK hge
      exact absurd hdex (not_le.mpr (ih d (by omega) hd1))

/-- **Descent kills every supercritical scale.**  A well-founded descent on the
natural-number scale leaves no supercritical excursion anywhere. -/
theorem mertensCovarianceExcursion_lt_one_of_descent
    (h : MertensCovarianceDescentStatement) {δ : ℝ} (hδ : 0 < δ)
    (K : ℕ) (hK : 1 ≤ K) :
    mertensCovarianceExcursion δ K < 1 :=
  mertensCovarianceExcursion_lt_one_aux h hδ K K le_rfl hK

/-- **Record descent gives the one-sided arithmetic frontier.** -/
theorem mertensPositiveLagUpperBounded_of_covarianceDescent
    (h : MertensCovarianceDescentStatement) :
    MertensPositiveLagUpperBoundedStatement := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro K hK
  have hlt := mertensCovarianceExcursion_lt_one_of_descent h hε K hK
  have hKnat : 0 < K := hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKnat
  have hpos : 0 < Real.rpow (K : ℝ) (1 + ε) := Real.rpow_pos_of_pos hKpos _
  unfold mertensCovarianceExcursion at hlt
  rw [div_lt_one hpos] at hlt
  linarith

/-- **Record descent gives the protected Mertens energy criterion.** -/
theorem mertensEnergyBounded_of_covarianceDescent
    (h : MertensCovarianceDescentStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_positiveLagUpperBounded
    (mertensPositiveLagUpperBounded_of_covarianceDescent h)

/-! ## What the support-only frontier route would have to supply -/

/-- Some exposed Euler frontier is of square-root size.  This is exactly the
missing input that would make the support bound `‖M(X)‖ <= F` RH strength. -/
def PrimeProductFrontierRootScaleStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℕ, 2 ≤ X →
        ∃ ell : ℕ, ell ∈ primesUpTo X ∧
          (primeProductFrontierCard X ell : ℝ) ≤
            C * Real.rpow (((X + 1 : ℕ) : ℝ)) ((1 + ε) / 2)

private theorem one_le_rpow_succ_cast {ε : ℝ} (hε : 0 < ε) (X : ℕ) :
    (1 : ℝ) ≤ Real.rpow (((X + 1 : ℕ) : ℝ)) (1 + ε) := by
  have hbase : (1 : ℝ) ≤ (((X + 1 : ℕ) : ℝ)) := by
    have hone : (1 : ℕ) ≤ X + 1 := Nat.le_add_left 1 X
    exact_mod_cast hone
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (0 : ℝ) ≤ 1 + ε)
  simpa using h

private theorem rpow_half_sq {ε : ℝ} (B : ℝ) (hB : 0 ≤ B) :
    (Real.rpow B ((1 + ε) / 2)) ^ (2 : ℕ) = Real.rpow B (1 + ε) := by
  have hnat : (Real.rpow B ((1 + ε) / 2)) ^ (2 : ℕ) =
      Real.rpow (Real.rpow B ((1 + ε) / 2)) (((2 : ℕ) : ℝ)) :=
    (Real.rpow_natCast (Real.rpow B ((1 + ε) / 2)) 2).symm
  have hmul : Real.rpow B (((1 + ε) / 2) * ((2 : ℕ) : ℝ)) =
      Real.rpow (Real.rpow B ((1 + ε) / 2)) (((2 : ℕ) : ℝ)) :=
    Real.rpow_mul hB _ _
  have harg : ((1 + ε) / 2) * ((2 : ℕ) : ℝ) = 1 + ε := by
    push_cast
    ring
  rw [hnat, ← hmul, harg]

/-- **The exact requirement of the support-only route.**  A square-root-size
exposed Euler frontier converts the existing support bound into the Mertens
energy criterion.  Measured, the minimising frontier is linear in `X`, so this
hypothesis is where support exhaustion stops. -/
theorem mertensEnergyBounded_of_primeProductFrontierRootScale
    (h : PrimeProductFrontierRootScaleStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hfront⟩
  refine ⟨max (C ^ 2) 1, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro x
  have hBnn : (0 : ℝ) ≤ (((x + 1 : ℕ) : ℝ)) := by positivity
  have hone := one_le_rpow_succ_cast hε x
  by_cases hx : 2 ≤ x
  · obtain ⟨ell, hell, hcard⟩ := hfront x hx
    have hsupport := norm_mertensSummatory_le_primeProductFrontierCard hell
    have hle : ‖mertensSummatory x‖ ≤
        C * Real.rpow (((x + 1 : ℕ) : ℝ)) ((1 + ε) / 2) := hsupport.trans hcard
    have hsq := pow_le_pow_left₀ (norm_nonneg (mertensSummatory x)) hle 2
    have hexpand :
        (C * Real.rpow (((x + 1 : ℕ) : ℝ)) ((1 + ε) / 2)) ^ (2 : ℕ) =
          C ^ 2 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
      rw [mul_pow, rpow_half_sq (ε := ε) _ hBnn]
    rw [hexpand] at hsq
    have hmono : C ^ 2 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) ≤
        max (C ^ 2) 1 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
      have hrpow : (0 : ℝ) ≤ Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
        linarith
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hrpow
    exact hsq.trans hmono
  · have hgap := norm_mertensSummatory_sub_le 0 x (Nat.zero_le x)
    rw [mertensSummatory_zero, sub_zero, Nat.sub_zero] at hgap
    have hsmall : ‖mertensSummatory x‖ ≤ 1 := by
      have hxle : (x : ℝ) ≤ 1 := by
        have : x ≤ 1 := by omega
        exact_mod_cast this
      linarith
    have hsq := pow_le_pow_left₀ (norm_nonneg (mertensSummatory x)) hsmall 2
    have hone' : (1 : ℝ) ≤ max (C ^ 2) 1 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := by
      have hmax : (1 : ℝ) ≤ max (C ^ 2) 1 := le_max_right _ _
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ max (C ^ 2) 1 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) :=
            mul_le_mul hmax hone (by norm_num) (by linarith)
    calc ‖mertensSummatory x‖ ^ 2 ≤ (1 : ℝ) ^ (2 : ℕ) := hsq
      _ = 1 := one_pow 2
      _ ≤ max (C ^ 2) 1 * Real.rpow (((x + 1 : ℕ) : ℝ)) (1 + ε) := hone'

/-! ## The two arrows of the critical path -/

/-- **First arrow: the covariance bridge.**  A frontier route must dominate the
*global* integer-order Möbius covariance, not merely its own frontier
coordinate.  This is the step that puts the two covariance objects on one
carrier. -/
def CovarianceEnvelopeDominates (E : ℕ → ℝ) : Prop :=
  ∀ K : ℕ, 1 ≤ K → realMertensPositiveLagPairSum K ≤ E K

/-- **Second arrow: capacity.**  The envelope itself is of RH scale. -/
def CovarianceEnvelopeRootScale (E : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ K : ℕ, 1 ≤ K → E K ≤ C * Real.rpow (K : ℝ) (1 + ε)

/-- **Both arrows, and only both, close the covariance route.**

Domination without capacity bounds nothing, and capacity without domination
bounds a different object.  Together they give the one-sided arithmetic frontier
and hence the protected Mertens energy criterion. -/
theorem mertensPositiveLagUpperBounded_of_covarianceEnvelope
    {E : ℕ → ℝ} (hdom : CovarianceEnvelopeDominates E)
    (hscale : CovarianceEnvelopeRootScale E) :
    MertensPositiveLagUpperBoundedStatement := by
  intro ε hε
  rcases hscale ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro K hK
  exact (hdom K hK).trans (hbound K hK)

theorem mertensEnergyBounded_of_covarianceEnvelope
    {E : ℕ → ℝ} (hdom : CovarianceEnvelopeDominates E)
    (hscale : CovarianceEnvelopeRootScale E) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_positiveLagUpperBounded
    (mertensPositiveLagUpperBounded_of_covarianceEnvelope hdom hscale)

end RHLean.Analysis
