import Mathlib
import RHLean.Analysis.EulerCRTRoughnessRecursion

/-!
# Exact prime-extension energy telescope

The amplitude recursion for adjoining one fresh prime is already exact:

```text
T_(pW)(x) = T_W(x) + T_(pW)(floor(x/p)).
```

This module squares that identity without discarding the cross term.  The
resulting one-prime energy increment is then iterated over an arbitrary
admissible ordered prime-extension chain.

Nothing analytic is asserted here.  In particular, the one-prime increment is
not assumed to have a sign.  The point is to preserve the complete signed
quadratic response so that future q^2 / boundary identifications can be made
before any inequality is taken.
-/

noncomputable section

namespace RHLean.Analysis

/-- Exact signed energy increment incurred when adjoining the fresh prime `p`
to the roughness wheel `W` at cutoff `x`.

Writing

```text
A = T_(pW)(x),   B = T_(pW)(floor(x/p)),
```

the parent amplitude is `A - B`, so this is exactly `B^2 - 2*A*B`. -/
def roughPrimeExtensionEnergyDefect (W p x : ℕ) : ℤ :=
  let A := roughMertens (p * W) x
  let B := roughMertens (p * W) (x / p)
  B ^ 2 - 2 * A * B

/-- **Exact one-prime energy law.**

No positivity, triangle inequality, or Cauchy step is used: the cross term is
retained literally. -/
theorem roughMertens_sq_prime_extension
    {W p : ℕ} (hp : p.Prime) (hpW : Squarefree (p * W)) (x : ℕ) :
    roughMertens W x ^ 2 =
      roughMertens (p * W) x ^ 2 +
        roughPrimeExtensionEnergyDefect W p x := by
  have h := roughMertens_prime_extension (W := W) hp hpW x
  have hrev :
      roughMertens W x =
        roughMertens (p * W) x -
          roughMertens (p * W) (x / p) := by
    linarith
  rw [hrev]
  unfold roughPrimeExtensionEnergyDefect
  ring

/-- The same one-prime law with the cross term displayed rather than packaged
as a defect. -/
theorem roughMertens_sq_prime_extension_expanded
    {W p : ℕ} (hp : p.Prime) (hpW : Squarefree (p * W)) (x : ℕ) :
    roughMertens W x ^ 2 =
      roughMertens (p * W) x ^ 2 +
        roughMertens (p * W) (x / p) ^ 2 -
        2 * roughMertens (p * W) x *
          roughMertens (p * W) (x / p) := by
  rw [roughMertens_sq_prime_extension hp hpW x]
  unfold roughPrimeExtensionEnergyDefect
  ring

/-- Wheel obtained by adjoining an ordered list of primes, one at a time. -/
def primeExtensionWheel : ℕ → List ℕ → ℕ
  | W, [] => W
  | W, p :: ps => primeExtensionWheel (p * W) ps

/-- Exact admissibility data needed at every step of an ordered prime-extension
chain.  Keeping this recursive avoids hiding any freshness/squarefreeness
obligation in the telescope theorem. -/
def PrimeExtensionChainAdmissible : ℕ → List ℕ → Prop
  | _, [] => True
  | W, p :: ps =>
      p.Prime ∧ Squarefree (p * W) ∧
        PrimeExtensionChainAdmissible (p * W) ps

/-- Sum of the exact signed one-prime energy increments along an ordered chain. -/
def roughPrimeExtensionEnergyDefectSum (W x : ℕ) : List ℕ → ℤ
  | [] => 0
  | p :: ps =>
      roughPrimeExtensionEnergyDefect W p x +
        roughPrimeExtensionEnergyDefectSum (p * W) x ps

/-- **Exact finite prime-extension energy telescope.**

For any admissible ordered chain, parent energy equals terminal-wheel energy
plus the signed sum of every one-prime quadratic increment.  This is the
general form of the finite identities visible at `x = 210` and `x = 317`. -/
theorem roughMertens_sq_primeExtensionChain
    {W x : ℕ} {ps : List ℕ}
    (hchain : PrimeExtensionChainAdmissible W ps) :
    roughMertens W x ^ 2 =
      roughMertens (primeExtensionWheel W ps) x ^ 2 +
        roughPrimeExtensionEnergyDefectSum W x ps := by
  induction ps generalizing W with
  | nil =>
      simp [primeExtensionWheel, roughPrimeExtensionEnergyDefectSum]
  | cons p ps ih =>
      simp only [PrimeExtensionChainAdmissible] at hchain
      rcases hchain with ⟨hp, hpW, htail⟩
      calc
        roughMertens W x ^ 2 =
            roughMertens (p * W) x ^ 2 +
              roughPrimeExtensionEnergyDefect W p x :=
          roughMertens_sq_prime_extension hp hpW x
        _ =
            (roughMertens (primeExtensionWheel (p * W) ps) x ^ 2 +
              roughPrimeExtensionEnergyDefectSum (p * W) x ps) +
              roughPrimeExtensionEnergyDefect W p x := by
          rw [ih htail]
        _ =
            roughMertens (primeExtensionWheel W (p :: ps)) x ^ 2 +
              roughPrimeExtensionEnergyDefectSum W x (p :: ps) := by
          simp [primeExtensionWheel, roughPrimeExtensionEnergyDefectSum]
          ring

/-- Equivalent difference form: the entire accumulated prime-extension response
is exactly the parent energy minus the terminal-wheel energy. -/
theorem roughPrimeExtensionEnergyDefectSum_eq_parent_sub_terminal
    {W x : ℕ} {ps : List ℕ}
    (hchain : PrimeExtensionChainAdmissible W ps) :
    roughPrimeExtensionEnergyDefectSum W x ps =
      roughMertens W x ^ 2 -
        roughMertens (primeExtensionWheel W ps) x ^ 2 := by
  have h := roughMertens_sq_primeExtensionChain
    (W := W) (x := x) (ps := ps) hchain
  linarith

/-- Rational-cast form, matching the repository's recursive Mertens-energy
currency. -/
theorem roughMertens_sq_primeExtensionChain_rat
    {W x : ℕ} {ps : List ℕ}
    (hchain : PrimeExtensionChainAdmissible W ps) :
    ((roughMertens W x : ℚ) ^ 2) =
      ((roughMertens (primeExtensionWheel W ps) x : ℚ) ^ 2) +
        (roughPrimeExtensionEnergyDefectSum W x ps : ℚ) := by
  exact_mod_cast
    roughMertens_sq_primeExtensionChain
      (W := W) (x := x) (ps := ps) hchain

end RHLean.Analysis
