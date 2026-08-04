import Mathlib

/-!
# Abstract energy recurrence

The stage-by-stage energy architecture supplies three ingredients:

```text
E_{j₀}            <= B x                       (base energy after 3, 5, 7)
E_{j+1}           <= A_j E_j + C_j x           (one further legal prime)
|Λ_n V_n|^2       <= D_n E_n                   (evaluation against the energy)
```

This module derives the exact iterated consequence

```text
E_n <= (∏_{r=j₀}^{n-1} A_r) B x  +  x ∑_{s=j₀}^{n-1} C_s ∏_{r=s+1}^{n-1} A_r
```

and hence

```text
|Λ_n V_n|^2 <= D_n x [ B ∏_{r} A_r + ∑_s C_s ∏_{r>s} A_r ].
```

It is pure algebra over `ℝ`: `A`, `C`, `D`, `B` and `x` are arbitrary, and the only
hypothesis beyond the three displayed inequalities is `0 ≤ A r`, which is what
lets the induction multiply through.  **No value of `A`, `B`, `C` or `D` is
asserted here, and no asymptotic specialization is made.**  In particular the
`D_n = 3^n` count and the range `n = O(log x / log log x)` are deliberately kept
outside this file: they belong to the analytic layer, and mixing them in would
turn an algebraic lemma into a conditional theorem.

The empirical status of the constants, recorded in
`research/TWO_ANCHOR_SLACK_COVERAGE.md`, is that on the tested post-`7` stages
`A_q^emp < 3.7`; the universal `(A, C)` inequality is open.
-/

noncomputable section

namespace RHLean.Proof

namespace EnergyRecurrence

/-- Accumulated inflation `∏_{r=s}^{n-1} A r` between two stages. -/
def inflation (A : ℕ → ℝ) (s n : ℕ) : ℝ := ∏ r ∈ Finset.Ico s n, A r

@[simp] theorem inflation_self (A : ℕ → ℝ) (s : ℕ) : inflation A s s = 1 := by
  simp [inflation]

theorem inflation_succ_top (A : ℕ → ℝ) {s n : ℕ} (h : s ≤ n) :
    inflation A s (n + 1) = inflation A s n * A n := by
  unfold inflation
  rw [Finset.prod_Ico_succ_top h]

theorem inflation_nonneg {A : ℕ → ℝ} (hA : ∀ r, 0 ≤ A r) (s n : ℕ) :
    0 ≤ inflation A s n :=
  Finset.prod_nonneg fun i _ => hA i

/-- The accumulated additive term `∑_{s=j₀}^{n-1} C s ∏_{r=s+1}^{n-1} A r`. -/
def additive (A C : ℕ → ℝ) (j₀ n : ℕ) : ℝ :=
  ∑ s ∈ Finset.Ico j₀ n, C s * inflation A (s + 1) n

@[simp] theorem additive_self (A C : ℕ → ℝ) (j₀ : ℕ) : additive A C j₀ j₀ = 0 := by
  simp [additive]

/-- The additive term satisfies the same one-stage recurrence as the energy. -/
theorem additive_succ_top (A C : ℕ → ℝ) {j₀ n : ℕ} (h : j₀ ≤ n) :
    additive A C j₀ (n + 1) = A n * additive A C j₀ n + C n := by
  unfold additive
  rw [Finset.sum_Ico_succ_top h, inflation_self]
  have hcongr : ∀ s ∈ Finset.Ico j₀ n,
      C s * inflation A (s + 1) (n + 1) = A n * (C s * inflation A (s + 1) n) := by
    intro s hs
    have hsn : s + 1 ≤ n := (Finset.mem_Ico.mp hs).2
    rw [inflation_succ_top A hsn]
    ring
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]
  ring

/-- **Iterated energy estimate.**  A base bound at stage `j₀` and a one-stage
affine recurrence give the exact closed form at every later stage. -/
theorem energy_le (A C E : ℕ → ℝ) (x B : ℝ) (j₀ : ℕ)
    (hA : ∀ r, 0 ≤ A r)
    (hbase : E j₀ ≤ B * x)
    (hstep : ∀ j, j₀ ≤ j → E (j + 1) ≤ A j * E j + C j * x) :
    ∀ n, j₀ ≤ n →
      E n ≤ inflation A j₀ n * (B * x) + additive A C j₀ n * x := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simpa using hbase
  | succ n hn ih =>
    have h1 : E (n + 1) ≤ A n * E n + C n * x := hstep n hn
    have h2 : A n * E n ≤
        A n * (inflation A j₀ n * (B * x) + additive A C j₀ n * x) :=
      mul_le_mul_of_nonneg_left ih (hA n)
    rw [inflation_succ_top A hn, additive_succ_top A C hn]
    nlinarith [h1, h2]

/-- The same estimate with the common factor `x` pulled out, in the shape the
proof programme states it. -/
theorem energy_le' (A C E : ℕ → ℝ) (x B : ℝ) (j₀ : ℕ)
    (hA : ∀ r, 0 ≤ A r)
    (hbase : E j₀ ≤ B * x)
    (hstep : ∀ j, j₀ ≤ j → E (j + 1) ≤ A j * E j + C j * x)
    (n : ℕ) (hn : j₀ ≤ n) :
    E n ≤ (B * inflation A j₀ n + additive A C j₀ n) * x := by
  have h := energy_le A C E x B j₀ hA hbase hstep n hn
  nlinarith [h]

/-- **Evaluation against the energy.**  Combining the iterated estimate with
`|Λ_n V_n|^2 ≤ D_n E_n` gives the closed form the programme targets. -/
theorem eval_le (A C E : ℕ → ℝ) (x B : ℝ) (j₀ : ℕ)
    (hA : ∀ r, 0 ≤ A r)
    (hbase : E j₀ ≤ B * x)
    (hstep : ∀ j, j₀ ≤ j → E (j + 1) ≤ A j * E j + C j * x)
    (n : ℕ) (hn : j₀ ≤ n) (lam D : ℝ) (hD : 0 ≤ D) (hlam : lam ≤ D * E n) :
    lam ≤ D * ((B * inflation A j₀ n + additive A C j₀ n) * x) := by
  have h := energy_le' A C E x B j₀ hA hbase hstep n hn
  have h' : D * E n ≤ D * ((B * inflation A j₀ n + additive A C j₀ n) * x) :=
    mul_le_mul_of_nonneg_left h hD
  linarith

/-! ## Uniform stage constants

The only collapse performed here is replacing each `A r` by a common upper bound.
It is still an inequality between finite products, not an asymptotic statement. -/

theorem inflation_le_pow {A : ℕ → ℝ} {a : ℝ} (hA : ∀ r, 0 ≤ A r) (hle : ∀ r, A r ≤ a)
    (s n : ℕ) : inflation A s n ≤ a ^ (n - s) := by
  unfold inflation
  calc ∏ r ∈ Finset.Ico s n, A r ≤ ∏ _r ∈ Finset.Ico s n, a :=
        Finset.prod_le_prod (fun i _ => hA i) (fun i _ => hle i)
    _ = a ^ (n - s) := by rw [Finset.prod_const, Nat.card_Ico]

end EnergyRecurrence

end RHLean.Proof
