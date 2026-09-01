import Mathlib
import RHLean.Proof.PrefixCarrierOthelloWalls
import RHLean.Arithmetic.PrimorialWheelPrefixIdentity
import RHLean.Analysis.SquareWheelNesting

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# The Othello boundary of a wheel prefix and of a whole square run

The three cumulative coordinates of this project

```text
M(x),        R_k(x) = M(x) - M(L_k),        sum of Delta_j over a square run
```

are the same object read in three charts.  The global Othello theorem applies to
the carrier underneath all three, so each of them equals the signed mass of one
explicit boundary rather than a sum of local Möbius estimates.

This file installs the transport.

* `primorialWheelResidual_eq_wallMass` rewrites the pinned primorial-wheel
  residual — which the arithmetic certificate already identifies with the
  Mertens increment `M(x) - M(L_k)` — as the anchor wall plus the cutoff wall
  of the prefix carrier `(L_k, x]`.
* `sum_canonicalTotalIncrement_Ico_eq_runWallMass` does the same for an entire
  consecutive run of complete square blocks.  Two separate mechanisms are
  composed there and should not be confused.  The square times collapse by the
  **already-known telescope** `sum Delta_j = M(X_b) - M(X_{a-1})`, which is what
  removes the block count; what is left is then a cumulative arithmetic
  interval `(X_{a-1}, X_b]`, and the fixed-prime pairing reduces that interval
  to its two walls.  Nothing here is a survivor trajectory: the interval is not
  a space-time carrier, and no birth-to-capture cancellation is claimed.  That
  statement — an atom born and captured strictly inside a run costs zero
  whatever its lifetime — is proved separately, on the actual birth/death
  process, in `RHLean.Proof.LifetimeRunCancellation`.
* `mertensEnergyBounded_of_iteratedPrefixBoundaryBounded` states what is left to
  prove.  If some finite peel of distinguished primes leaves an iterated
  boundary of RH-scale population, the Mertens energy criterion follows — and
  hence, through the equivalences already in the repository, the pinned
  primorial-wheel residual criterion and the maximal signed square-run
  criterion.  The remaining problem is a multiplicity bound on a run boundary,
  not a statement about individual Möbius seats.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- The complete-square endpoint is monotone. -/
theorem squarePrefixEndpoint_mono {a b : ℕ} (hab : a ≤ b) :
    squarePrefixEndpoint a ≤ squarePrefixEndpoint b := by
  have hsquare : (a + 1) ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have ha := squarePrefixEndpoint_add_one a
  have hb := squarePrefixEndpoint_add_one b
  omega

/-! ## The wheel prefix -/

/-- **The pinned wheel residual is exactly the mass of its two walls.**

The residual is the raw seeded prefix minus twice its smooth core; the
arithmetic certificate makes it the Möbius mass of `(L_k, x]`; the global
Othello theorem then collapses that whole prefix onto its boundary. -/
theorem primorialWheelResidual_eq_wallMass
    {p : ℕ} (hp : p.Prime) (k : ℕ) {x : ℕ}
    (hx : x ≤ primorialBlockUpper k) :
    (primorialWheelSystem k).residual x =
      (∑ n ∈ primeCarrierAnchorWall p (primorialBlockLower k) x, μ n) +
        ∑ n ∈ primeCarrierCutoffWall p (primorialBlockLower k) x, μ n := by
  rw [primorialWheel_residual_eq_moebiusInterval k hx]
  exact sum_moebius_Ioc_eq_wallMass hp (primorialBlockLower k) x

/-- Population bound for the pinned wheel residual in terms of its boundary
alone. -/
theorem abs_primorialWheelResidual_le_wallCard
    {p : ℕ} (hp : p.Prime) (k : ℕ) {x : ℕ}
    (hx : x ≤ primorialBlockUpper k) :
    |(primorialWheelSystem k).residual x| ≤
      ((primorialBlockLower k : ℕ) : ℤ) + ((x - x / p : ℕ) : ℤ) := by
  rw [primorialWheel_residual_eq_moebiusInterval k hx]
  exact abs_sum_moebius_Ioc_le_wallCard hp (primorialBlockLower k) x

/-! ## A whole square run as one carrier -/

/-- A consecutive run of complete square blocks is the Möbius mass of the single
cumulative arithmetic interval `(X_{a-1}, X_b]`.  This is the pre-existing
square-prefix telescope, restated in interval form; it is where the block count
disappears. -/
theorem sum_canonicalTotalIncrement_Ico_eq_moebius_Ioc_cast
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    (∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j) =
      (((∑ n ∈ Finset.Ioc (squarePrefixEndpoint (a - 1))
          (squarePrefixEndpoint b), μ n : ℤ) : ℂ)) := by
  have hmono : squarePrefixEndpoint (a - 1) ≤ squarePrefixEndpoint b :=
    squarePrefixEndpoint_mono (by omega)
  calc (∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j)
      = squarePrefixMertens b - squarePrefixMertens (a - 1) :=
        sum_canonicalTotalIncrement_Ico_eq_squarePrefix_sub a b ha hab
    _ = mertensSummatory (squarePrefixEndpoint b) -
          mertensSummatory (squarePrefixEndpoint (a - 1)) := rfl
    _ = ∑ n ∈ Finset.Ioc (squarePrefixEndpoint (a - 1))
          (squarePrefixEndpoint b), (((μ n : ℤ) : ℂ)) :=
        (moebius_Ioc_cast_eq_mertens_sub hmono).symm
    _ = (((∑ n ∈ Finset.Ioc (squarePrefixEndpoint (a - 1))
          (squarePrefixEndpoint b), μ n : ℤ) : ℂ)) := by
        push_cast
        ring

/-- **Run-level wall identity.**

The whole signed square run equals the anchor wall at `X_{a-1}` plus the cutoff
wall at `X_b`.  The block count drops out at the first step, by the existing
square-prefix telescope; the pairing then acts on the resulting cumulative
interval.  The two steps are independent, and only the first one is about square
time. -/
theorem sum_canonicalTotalIncrement_Ico_eq_runWallMass
    {p : ℕ} (hp : p.Prime) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    (∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j) =
      (((∑ n ∈ primeCarrierAnchorWall p (squarePrefixEndpoint (a - 1))
          (squarePrefixEndpoint b), μ n : ℤ) : ℂ)) +
      (((∑ n ∈ primeCarrierCutoffWall p (squarePrefixEndpoint (a - 1))
          (squarePrefixEndpoint b), μ n : ℤ) : ℂ)) := by
  rw [sum_canonicalTotalIncrement_Ico_eq_moebius_Ioc_cast a b ha hab,
    sum_moebius_Ioc_eq_wallMass hp (squarePrefixEndpoint (a - 1))
      (squarePrefixEndpoint b)]
  push_cast
  ring

/-- The run is bounded by its boundary population alone. -/
theorem norm_sum_canonicalTotalIncrement_Ico_le_runWallCard
    {p : ℕ} (hp : p.Prime) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    ‖∑ j ∈ Finset.Ico a (b + 1), canonicalTotalIncrement j‖ ≤
      ((squarePrefixEndpoint (a - 1) : ℕ) : ℝ) +
        ((squarePrefixEndpoint b - squarePrefixEndpoint b / p : ℕ) : ℝ) := by
  rw [sum_canonicalTotalIncrement_Ico_eq_moebius_Ioc_cast a b ha hab,
    Complex.norm_intCast]
  have hbound := abs_sum_moebius_Ioc_le_wallCard hp
    (squarePrefixEndpoint (a - 1)) (squarePrefixEndpoint b)
  exact_mod_cast hbound

/-! ## What is left to prove -/

/-- **The iterated-boundary multiplicity target.**

For every cumulative prefix carrier `(0, x]` some finite peel of distinguished
primes leaves an Othello boundary whose population is of RH scale.  This is a
statement about one run boundary, not about individual Möbius values. -/
def IteratedPrefixBoundaryBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℕ, ∃ ps : List ℕ, (∀ p ∈ ps, Nat.Prime p) ∧
        ((iteratedPrimeEscapePart ps (Finset.Ioc 0 x)).card : ℝ) ^ 2 ≤
          C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε)

/-- The Mertens summatory function is the Möbius mass of its prefix carrier. -/
theorem mertensSummatory_eq_moebius_Ioc_cast (x : ℕ) :
    mertensSummatory x =
      (((∑ n ∈ Finset.Ioc 0 x, μ n : ℤ) : ℂ)) := by
  have hcast := moebius_Ioc_cast_eq_mertens_sub (Nat.zero_le x)
  rw [mertensSummatory_zero, sub_zero] at hcast
  rw [← hcast]
  push_cast
  ring

/-- **The reduction.**  An RH-scale multiplicity bound on the iterated Othello
boundary of the prefix carrier gives the Mertens energy criterion, and hence,
through the equivalences already recorded in this repository, the pinned
primorial-wheel residual criterion and the maximal signed square-run
criterion. -/
theorem mertensEnergyBounded_of_iteratedPrefixBoundaryBounded
    (h : IteratedPrefixBoundaryBoundedStatement) :
    MertensEnergyBoundedStatement := by
  intro ε hε
  rcases h ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro x
  obtain ⟨ps, hps, hcard⟩ := hbound x
  have habs := abs_sum_moebius_le_card_iteratedPrimeEscapePart ps hps
    (Finset.Ioc 0 x)
  have hnorm : ‖mertensSummatory x‖ ≤
      ((iteratedPrimeEscapePart ps (Finset.Ioc 0 x)).card : ℝ) := by
    rw [mertensSummatory_eq_moebius_Ioc_cast x, Complex.norm_intCast]
    exact_mod_cast habs
  calc ‖mertensSummatory x‖ ^ 2
      ≤ ((iteratedPrimeEscapePart ps (Finset.Ioc 0 x)).card : ℝ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ C * Real.rpow ((x + 1 : ℕ) : ℝ) (1 + ε) := hcard

end RHLean.Analysis
