import Mathlib
import RHLean.Analysis.CanonicalHighSectorCore

/-!
# Exact height-shell reconstruction

This Proof-side module isolates the algebraic step that must precede any
large-sieve or near-resonance conjecture.  For a finite weighted population it
expands the conjugate square of the total amplitude into

* diagonal energy;
* off-diagonal equal-height energy; and
* off-diagonal unequal-height energy.

An arbitrary shell labelling then partitions the unequal-height term exactly
into the finite set of shells that actually occur.  No analytic estimate is
assumed.  The final norm theorem records precisely how diagonal, equal-height,
and shell bounds combine to control the total amplitude.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace RHLean.Proof

variable {α κ : Type*}

/-- The weighted amplitude of a finite population. -/
def finiteAmplitude (s : Finset α) (w : α → ℂ) : ℂ :=
  ∑ x ∈ s, w x

/-- The full ordered-pair energy. -/
def totalPairEnergy (s : Finset α) (w : α → ℂ) : ℂ :=
  ∑ x ∈ s, ∑ y ∈ s, conj (w x) * w y

/-- The diagonal part of the ordered-pair energy. -/
def diagonalPairEnergy (s : Finset α) (w : α → ℂ) : ℂ :=
  ∑ x ∈ s, conj (w x) * w x

/-- Off-diagonal energy carried by pairs having exactly equal height. -/
def equalHeightOffDiagonalEnergy
    [DecidableEq α] (s : Finset α) (w : α → ℂ) (height : α → ℝ) : ℂ :=
  ∑ x ∈ s, ∑ y ∈ s,
    if x ≠ y ∧ height x = height y then conj (w x) * w y else 0

/-- Off-diagonal energy carried by pairs having unequal height. -/
def unequalHeightOffDiagonalEnergy
    [DecidableEq α] (s : Finset α) (w : α → ℂ) (height : α → ℝ) : ℂ :=
  ∑ x ∈ s, ∑ y ∈ s,
    if x ≠ y ∧ height x ≠ height y then conj (w x) * w y else 0

/-- The energy assigned to one height-difference shell.  The shell map is
arbitrary: later analytic work may choose dyadic, smooth, modular, or
problem-adapted shells. -/
def heightShellEnergy
    [DecidableEq α] [DecidableEq κ]
    (s : Finset α) (w : α → ℂ) (height : α → ℝ)
    (shell : α → α → κ) (k : κ) : ℂ :=
  ∑ x ∈ s, ∑ y ∈ s,
    if x ≠ y ∧ height x ≠ height y ∧ shell x y = k then
      conj (w x) * w y
    else 0

/-- The finite set of shell labels that actually occur among unequal-height
ordered pairs from `s`. -/
def activeHeightShells
    [DecidableEq α] [DecidableEq κ]
    (s : Finset α) (height : α → ℝ) (shell : α → α → κ) : Finset κ :=
  (((s.product s).filter fun p =>
      p.1 ≠ p.2 ∧ height p.1 ≠ height p.2).image fun p => shell p.1 p.2)

/-- The conjugate square of the finite amplitude is exactly the full
ordered-pair energy. -/
theorem conj_mul_finiteAmplitude_eq_totalPairEnergy
    (s : Finset α) (w : α → ℂ) :
    conj (finiteAmplitude s w) * finiteAmplitude s w = totalPairEnergy s w := by
  classical
  simp [finiteAmplitude, totalPairEnergy, Finset.mul_sum, Finset.sum_mul]

/-- Exact three-way partition of the total ordered-pair energy. -/
theorem totalPairEnergy_eq_diagonal_add_equal_add_unequal
    [DecidableEq α] (s : Finset α) (w : α → ℂ) (height : α → ℝ) :
    totalPairEnergy s w =
      diagonalPairEnergy s w +
        equalHeightOffDiagonalEnergy s w height +
          unequalHeightOffDiagonalEnergy s w height := by
  classical
  unfold totalPairEnergy diagonalPairEnergy
    equalHeightOffDiagonalEnergy unequalHeightOffDiagonalEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hxy : x = y
  · subst y
    simp
  · by_cases hh : height x = height y
    · simp [hxy, hh]
    · simp [hxy, hh]

/-- The unequal-height energy is exactly the sum over all active shells. -/
theorem unequalHeightOffDiagonalEnergy_eq_sum_active_shells
    [DecidableEq α] [DecidableEq κ]
    (s : Finset α) (w : α → ℂ) (height : α → ℝ)
    (shell : α → α → κ) :
    unequalHeightOffDiagonalEnergy s w height =
      ∑ k ∈ activeHeightShells s height shell,
        heightShellEnergy s w height shell k := by
  classical
  unfold unequalHeightOffDiagonalEnergy heightShellEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hxy : x = y
  · subst y
    simp
  · by_cases hh : height x = height y
    · simp [hh]
    · have hmem : shell x y ∈ activeHeightShells s height shell := by
        simp [activeHeightShells, hx, hy, hxy, hh]
      rw [Finset.sum_eq_single (shell x y)]
      · simp [hxy, hh]
      · intro k hk hne
        simp [hne]
      · exact hmem

/-- Exact shell reconstruction of the conjugate square. -/
theorem finiteAmplitude_shell_reconstruction
    [DecidableEq α] [DecidableEq κ]
    (s : Finset α) (w : α → ℂ) (height : α → ℝ)
    (shell : α → α → κ) :
    conj (finiteAmplitude s w) * finiteAmplitude s w =
      diagonalPairEnergy s w +
        equalHeightOffDiagonalEnergy s w height +
          ∑ k ∈ activeHeightShells s height shell,
            heightShellEnergy s w height shell k := by
  rw [conj_mul_finiteAmplitude_eq_totalPairEnergy]
  rw [totalPairEnergy_eq_diagonal_add_equal_add_unequal]
  rw [unequalHeightOffDiagonalEnergy_eq_sum_active_shells]

/-- Bounds for the diagonal, equal-height term, and every active shell combine
by the triangle inequality into a bound for the squared amplitude.  This is the
precise abstract implication that later analytic shell estimates must feed. -/
theorem norm_finiteAmplitude_sq_le_of_shell_bounds
    [DecidableEq α] [DecidableEq κ]
    (s : Finset α) (w : α → ℂ) (height : α → ℝ)
    (shell : α → α → κ)
    (diagonalBound equalHeightBound : ℝ) (shellBound : κ → ℝ)
    (hdiag : ‖diagonalPairEnergy s w‖ ≤ diagonalBound)
    (hequal : ‖equalHeightOffDiagonalEnergy s w height‖ ≤ equalHeightBound)
    (hshell : ∀ k ∈ activeHeightShells s height shell,
      ‖heightShellEnergy s w height shell k‖ ≤ shellBound k) :
    ‖finiteAmplitude s w‖ ^ 2 ≤
      diagonalBound + equalHeightBound +
        ∑ k ∈ activeHeightShells s height shell, shellBound k := by
  have hrecon := finiteAmplitude_shell_reconstruction s w height shell
  have hnorm :
      ‖finiteAmplitude s w‖ ^ 2 =
        ‖diagonalPairEnergy s w +
          equalHeightOffDiagonalEnergy s w height +
            ∑ k ∈ activeHeightShells s height shell,
              heightShellEnergy s w height shell k‖ := by
    rw [← hrecon]
    simp [norm_mul, pow_two]
  rw [hnorm]
  calc
    ‖diagonalPairEnergy s w + equalHeightOffDiagonalEnergy s w height +
        ∑ k ∈ activeHeightShells s height shell,
          heightShellEnergy s w height shell k‖
        ≤ ‖diagonalPairEnergy s w‖ +
            ‖equalHeightOffDiagonalEnergy s w height‖ +
              ‖∑ k ∈ activeHeightShells s height shell,
                heightShellEnergy s w height shell k‖ := by
          exact le_trans (norm_add_le _ _)
            (add_le_add_right (norm_add_le _ _) _)
    _ ≤ diagonalBound + equalHeightBound +
          ∑ k ∈ activeHeightShells s height shell,
            ‖heightShellEnergy s w height shell k‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ diagonalBound + equalHeightBound +
          ∑ k ∈ activeHeightShells s height shell, shellBound k := by
          gcongr
          exact Finset.sum_le_sum fun k hk => hshell k hk

/-- Canonical high-sector atoms, represented without collapsing the block
index.  Keeping `(j,m)` prevents any hidden identification between the real
source coordinate and the height coordinate. -/
def canonicalHighAtomSet (Λ : ℝ) (n : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (Finset.range (n + 1)).sigma fun j =>
    (canonicalSquareBlock j).filter fun m => IsCanonicalHighHeight Λ j m

/-- Möbius weight of a canonical high-sector atom. -/
def canonicalHighAtomWeight (p : Sigma fun _ : ℕ => ℕ) : ℂ :=
  canonicalMoebiusWeight p.2

/-- Doubled `2ab` height of a canonical high-sector atom. -/
def canonicalHighAtomHeight (p : Sigma fun _ : ℕ => ℕ) : ℝ :=
  canonicalHeightTwice p.2

/-- The atom representation sums to the existing canonical high prefix. -/
theorem finiteAmplitude_canonicalHighAtomSet_eq_canonicalHighPrefix
    (Λ : ℝ) (n : ℕ) :
    finiteAmplitude (canonicalHighAtomSet Λ n) canonicalHighAtomWeight =
      canonicalHighPrefix Λ n := by
  classical
  simp [finiteAmplitude, canonicalHighAtomSet, canonicalHighAtomWeight,
    canonicalHighPrefix, canonicalHighIncrement]

/-- Canonical specialization: every chosen shell map on high-sector atoms gives
an exact reconstruction of the current RH-equivalent high-sector square. -/
theorem canonicalHighPrefix_shell_reconstruction
    {κ : Type*} [DecidableEq κ]
    (Λ : ℝ) (n : ℕ)
    (shell : (Sigma fun _ : ℕ => ℕ) → (Sigma fun _ : ℕ => ℕ) → κ) :
    conj (canonicalHighPrefix Λ n) * canonicalHighPrefix Λ n =
      diagonalPairEnergy (canonicalHighAtomSet Λ n) canonicalHighAtomWeight +
        equalHeightOffDiagonalEnergy
          (canonicalHighAtomSet Λ n) canonicalHighAtomWeight canonicalHighAtomHeight +
          ∑ k ∈ activeHeightShells
              (canonicalHighAtomSet Λ n) canonicalHighAtomHeight shell,
            heightShellEnergy
              (canonicalHighAtomSet Λ n) canonicalHighAtomWeight
              canonicalHighAtomHeight shell k := by
  rw [← finiteAmplitude_canonicalHighAtomSet_eq_canonicalHighPrefix]
  exact finiteAmplitude_shell_reconstruction
    (canonicalHighAtomSet Λ n) canonicalHighAtomWeight canonicalHighAtomHeight shell

end RHLean.Proof
