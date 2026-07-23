import Mathlib

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RHLean.Analysis

/-- The ordered sum of the first `n` height-shell components. -/
def heightShellSum {E : Type*} [AddCommMonoid E]
    (shell : ℕ → E) (n : ℕ) : E :=
  ∑ i in Finset.range n, shell i

/-- The sum of the individual shell energies. -/
def heightShellDiagonalEnergy {E : Type*} [SeminormedAddCommGroup E]
    (shell : ℕ → E) (n : ℕ) : ℝ :=
  ∑ i in Finset.range n, ‖shell i‖ ^ 2

/-- The real part of the inner product, valid over real or complex scalars. -/
def shellReInner {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) : ℝ :=
  RCLike.re (inner 𝕜 x y)

/--
The exact off-diagonal height-shell Gram sum. The nested ranges enumerate every
ordered pair `i < j < n` exactly once.
-/
def heightShellOffDiagonalGram {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (shell : ℕ → E) (n : ℕ) : ℝ :=
  ∑ j in Finset.range n,
    ∑ i in Finset.range j, shellReInner (𝕜 := 𝕜) (shell i) (shell j)

/-- Appending one shell adds it to the full signed shell sum. -/
theorem heightShellSum_succ {E : Type*} [AddCommMonoid E]
    (shell : ℕ → E) (n : ℕ) :
    heightShellSum shell (n + 1) = heightShellSum shell n + shell n := by
  simpa [heightShellSum] using Finset.sum_range_succ shell n

/-- Appending one shell adds exactly its diagonal energy. -/
theorem heightShellDiagonalEnergy_succ {E : Type*} [SeminormedAddCommGroup E]
    (shell : ℕ → E) (n : ℕ) :
    heightShellDiagonalEnergy shell (n + 1) =
      heightShellDiagonalEnergy shell n + ‖shell n‖ ^ 2 := by
  simpa [heightShellDiagonalEnergy] using
    Finset.sum_range_succ (fun i => ‖shell i‖ ^ 2) n

/-- Appending shell `n` adds all and only the cross terms with earlier shells. -/
theorem heightShellOffDiagonalGram_succ
    {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (shell : ℕ → E) (n : ℕ) :
    heightShellOffDiagonalGram (𝕜 := 𝕜) shell (n + 1) =
      heightShellOffDiagonalGram (𝕜 := 𝕜) shell n +
        ∑ i in Finset.range n,
          shellReInner (𝕜 := 𝕜) (shell i) (shell n) := by
  simpa [heightShellOffDiagonalGram] using
    Finset.sum_range_succ
      (fun j => ∑ i in Finset.range j,
        shellReInner (𝕜 := 𝕜) (shell i) (shell j)) n

/-- Any shell's cross term with the first `n` shells expands term by term. -/
theorem shellReInner_heightShellSum_left
    {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (shell : ℕ → E) (m n : ℕ) :
    shellReInner (𝕜 := 𝕜) (heightShellSum shell n) (shell m) =
      ∑ i in Finset.range n,
        shellReInner (𝕜 := 𝕜) (shell i) (shell m) := by
  induction n with
  | zero =>
      simp [heightShellSum, shellReInner]
  | succ n ih =>
      rw [heightShellSum_succ]
      have ih' := ih
      unfold shellReInner at ih' ⊢
      rw [inner_add_left, RCLike.re.map_add, ih', Finset.sum_range_succ]

/--
Exact height-shell Gram identity. The full signed shell recombination remains
inside the norm, and every off-diagonal real inner product is retained.
-/
theorem energy_sum_heightShells
    {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (shell : ℕ → E) (n : ℕ) :
    ‖heightShellSum shell n‖ ^ 2 =
      heightShellDiagonalEnergy shell n +
        2 * heightShellOffDiagonalGram (𝕜 := 𝕜) shell n := by
  induction n with
  | zero =>
      simp [heightShellSum, heightShellDiagonalEnergy,
        heightShellOffDiagonalGram]
  | succ n ih =>
      rw [heightShellSum_succ, norm_add_sq, ih,
        heightShellDiagonalEnergy_succ,
        heightShellOffDiagonalGram_succ]
      have hcross :=
        shellReInner_heightShellSum_left (𝕜 := 𝕜) shell n n
      unfold shellReInner at hcross
      rw [hcross]
      ring

end RHLean.Analysis
