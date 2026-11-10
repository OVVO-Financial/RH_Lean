import Mathlib

/-!
# Amplification exponent iteration: elementary, source-independent packet

This file formalizes the **algebraic** exponent mechanism behind the proposed
zero-log-amplification-to-Mertens-energy implication.  It neither assumes nor
proves the outstanding arithmetic one-step improvement.  In particular, the
`upgrade` hypothesis in `all_exponents_of_contracting_upgrade` must eventually
be instantiated from the exact Mobius square-endpoint and strict-history
`K_R` definitions in `SquareRootAmplificationLogGrowth.lean`.

No admitted proof holes or classical zeta/Pintz input is used.
-/

noncomputable section

namespace RHLean.Proof

/-- The square-endpoint transfer: a Mertens power `b` and an endpoint
amplification allowance `R^(2*eta)` give the candidate power
`(2*b+1)/4 + eta/2` for the full summatory function. -/
def amplificationNextExponent (b eta : ℝ) : ℝ :=
  (2 * b + 1) / 4 + eta / 2

/-- Exactly how much distance from the critical exponent remains. -/
theorem amplificationNextExponent_gap (b eta : ℝ) :
    amplificationNextExponent b eta - (1 / 2 : ℝ) =
      ((b - (1 / 2 : ℝ)) + eta) / 2 := by
  unfold amplificationNextExponent
  ring

/-- Taking the amplification allowance `eta=(b-1/2)/2` contracts the
remaining exponent gap by the fixed factor `3/4`. -/
theorem amplificationNextExponent_three_fourths (b : ℝ) :
    amplificationNextExponent b ((b - (1 / 2 : ℝ)) / 2) =
      (1 / 2 : ℝ) + (3 / 4 : ℝ) * (b - (1 / 2 : ℝ)) := by
  unfold amplificationNextExponent
  ring

/-- Any allowance strictly smaller than the current gap gives a real
improvement while staying above the critical exponent. -/
theorem amplificationNextExponent_strict_improvement
    {b eta : ℝ} (hb : (1 / 2 : ℝ) < b)
    (heta_nonneg : 0 <= eta)
    (heta_lt : eta < b - (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) < amplificationNextExponent b eta ∧
      amplificationNextExponent b eta < b := by
  constructor
  · unfold amplificationNextExponent
    linarith
  · unfold amplificationNextExponent
    linarith

/-- The concrete exponent sequence starting at `b=1`. -/
def amplificationIterateExponent (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) + (1 / 2 : ℝ) * (3 / 4 : ℝ) ^ n

@[simp] theorem amplificationIterateExponent_zero :
    amplificationIterateExponent 0 = 1 := by
  norm_num [amplificationIterateExponent]

theorem amplificationIterateExponent_half_lt (n : ℕ) :
    (1 / 2 : ℝ) < amplificationIterateExponent n := by
  have hp : 0 < (3 / 4 : ℝ) ^ n := pow_pos (by norm_num) n
  unfold amplificationIterateExponent
  linarith

/-- Each stage is the exact output of the selected one-step transfer. -/
theorem amplificationIterateExponent_succ (n : ℕ) :
    amplificationIterateExponent (n + 1) =
      amplificationNextExponent (amplificationIterateExponent n)
        ((amplificationIterateExponent n - (1 / 2 : ℝ)) / 2) := by
  rw [amplificationNextExponent_three_fourths]
  simp only [amplificationIterateExponent, pow_succ]
  ring

/-- The iterated gap goes to zero.  This is an elementary real-sequence
fact and does not consume any arithmetic estimate. -/
theorem amplificationIterateExponent_tendsto_half :
    Filter.Tendsto amplificationIterateExponent Filter.atTop
      (nhds (1 / 2 : ℝ)) := by
  have hpow : Filter.Tendsto (fun n : ℕ => (3 / 4 : ℝ) ^ n)
      Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hconst : Filter.Tendsto (fun _ : ℕ => (1 / 2 : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have hscaled : Filter.Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) * (3 / 4 : ℝ) ^ n)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [mul_zero] using hconst.mul hpow
  have hsum : Filter.Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) + (1 / 2 : ℝ) * (3 / 4 : ℝ) ^ n)
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
    simpa only [add_zero] using hconst.add hscaled
  simpa only [amplificationIterateExponent] using hsum

/-- General logical consumer for the amplification exponent mechanism.

`P b` stands for a genuine power-growth statement, e.g. a bound for the
actual Mertens function with every required constant and uniformity.

The only non-algebraic input is `upgrade`.  A proof of `upgrade` from the
actual zero-log amplification measure plus the square-endpoint interpolation
would turn this theorem into the desired Mertens-energy consumer.  This theorem
does *not* claim `upgrade` is known. -/
theorem all_exponents_of_contracting_upgrade
    (P : ℝ → Prop)
    (initial : P 1)
    (monotone : ∀ {a b : ℝ}, a ≤ b → P a → P b)
    (upgrade : ∀ b : ℝ, (1 / 2 : ℝ) < b → P b →
      P (amplificationNextExponent b ((b - (1 / 2 : ℝ)) / 2))) :
    ∀ b : ℝ, (1 / 2 : ℝ) < b → P b := by
  have hiter : ∀ n : ℕ, P (amplificationIterateExponent n) := by
    intro n
    induction n with
    | zero =>
        simpa using initial
    | succ n ih =>
        rw [amplificationIterateExponent_succ]
        exact upgrade (amplificationIterateExponent n)
          (amplificationIterateExponent_half_lt n) ih
  intro b hb
  have hnear : {x : ℝ | x < b} ∈ nhds (1 / 2 : ℝ) :=
    isOpen_Iio.mem_nhds hb
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      amplificationIterateExponent n < b :=
    amplificationIterateExponent_tendsto_half.eventually hnear
  obtain ⟨n, hn⟩ := hsmall.exists
  exact monotone hn.le (hiter n)

end RHLean.Proof
