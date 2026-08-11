from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativeLambdaTwoGoodRecipMass_packed_blocks' in s
assert 'nativePNTGoodForwardRadius' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

/-! ## Integer good radii and quotient-block packing -/

/-- Integer radius corresponding to the PNT2 forward interval `h <= eps*t/8`. -/
def nativePNTGoodForwardRadius (t : ℕ) (eps : ℝ) : ℕ :=
  ⌊eps * (t : ℝ) / 8⌋₊

/-- The integer radius stays below the real PNT2 radius. -/
theorem nativePNTGoodForwardRadius_cast_le
    (t : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    ((nativePNTGoodForwardRadius t eps : ℕ) : ℝ) ≤
      eps * (t : ℝ) / 8 := by
  unfold nativePNTGoodForwardRadius
  exact Nat.floor_le (by positivity)

/-- For `eps <= 1`, the good radius is at most the base point.  This is the
coarse separation estimate used between consecutive geometric search blocks. -/
theorem nativePNTGoodForwardRadius_le_self
    (t : ℕ) (eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) :
    nativePNTGoodForwardRadius t eps ≤ t := by
  have hr := nativePNTGoodForwardRadius_cast_le t eps heps
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have hreal : eps * (t : ℝ) / 8 ≤ (t : ℝ) := by
    nlinarith
  have hcast : ((nativePNTGoodForwardRadius t eps : ℕ) : ℝ) ≤ (t : ℝ) :=
    hr.trans hreal
  exact_mod_cast hcast

/-- PNT2 expressed as an ordinary integer interval rather than a displacement
bound. -/
theorem nativePNTError_good_on_forward_radius
    (t : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (hforward : ∀ h : ℕ, (h : ℝ) ≤ eps * (t : ℝ) / 8 →
      |nativePNTError (t + h)| ≤ eps * ((t + h : ℕ) : ℝ)) :
    ∀ q ∈ Finset.Icc t (t + nativePNTGoodForwardRadius t eps),
      |nativePNTError q| ≤ eps * (q : ℝ) := by
  intro q hq
  have hqI := Finset.mem_Icc.mp hq
  let h := q - t
  have hhR : h ≤ nativePNTGoodForwardRadius t eps := by
    dsimp [h]
    omega
  have hhCast : (h : ℝ) ≤
      ((nativePNTGoodForwardRadius t eps : ℕ) : ℝ) := by
    exact_mod_cast hhR
  have hh : (h : ℝ) ≤ eps * (t : ℝ) / 8 :=
    hhCast.trans (nativePNTGoodForwardRadius_cast_le t eps heps)
  have heq : t + h = q := by
    dsimp [h]
    omega
  simpa [heq] using hforward h hh

/-- The combined PNT1/PNT2 theorem with its forward radius discretized. -/
theorem nativePNT_exists_good_radius_dyadic
    (A K : ℕ) (eps : ℝ)
    (hA : 3 ≤ A) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hlogA : 1 ≤ Real.log (A : ℝ))
    (htailA : 2200 ≤ eps * Real.log (A : ℝ))
    (hdownA : 1 < (eps / 4) * (2 * (A : ℝ) + 1))
    (hupA :
      Real.log ((A * 2 ^ K : ℕ) : ℝ) - 1 <
        (eps / 4) * (2 * (A : ℝ) + 1))
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        (eps / 4) * ((K : ℝ) * Real.log 2 - 1)) :
    ∃ t ∈ Finset.Icc A (A * 2 ^ K),
      |nativePNTError t| ≤ eps * (t : ℝ) / 4 ∧
        ∀ q ∈ Finset.Icc t (t + nativePNTGoodForwardRadius t eps),
          |nativePNTError q| ≤ eps * (q : ℝ) := by
  rcases nativePNT_exists_good_forward_dyadic
      A K eps hA heps heps1 hlogA htailA hdownA hupA hdepth with
    ⟨t, ht, hsmall, hforward⟩
  refine ⟨t, ht, hsmall, ?_⟩
  exact nativePNTError_good_on_forward_radius t eps heps.le hforward

/-- A separated family of good quotient intervals contributes the sum of all
its reciprocal `Lambda_2` block masses to the good-fibre compensation term. -/
theorem nativeLambdaTwoGoodRecipMass_packed_quotient_intervals
    (N J : ℕ) (beta : ℝ) (t H : ℕ → ℕ)
    (hbeta : 0 ≤ beta)
    (ht : ∀ j < J, 1 ≤ t j)
    (hgood : ∀ j < J, ∀ q ∈ Finset.Icc (t j) (t j + H j),
      |nativePNTError q| ≤ beta * (q : ℝ))
    (hsep : ∀ i j, i < j → j < J → t i + H i < t j) :
    (∑ j ∈ Finset.range J,
      nativeLambdaTwoRecipIntervalMass
        (N / (t j + H j + 1)) (N / t j)) ≤
      nativeLambdaTwoGoodRecipMass N beta := by
  let block : ℕ → Finset ℕ := fun j =>
    Finset.Icc (N / (t j + H j + 1) + 1) (N / t j)
  have hsub : ∀ j < J, block j ⊆ nativePNTGoodFiberSet N beta := by
    intro j hj
    dsimp [block]
    exact nativePNT_reciprocal_interval_subset_good
      N (t j) (H j) beta (ht j hj) hbeta (hgood j hj)
  have hdisj : ∀ i < J, ∀ j < J, i ≠ j → Disjoint (block i) (block j) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · dsimp [block]
      exact nativePNT_reciprocal_blocks_disjoint
        N (t i) (H i) (t j) (H j) (hsep i j hijlt hj)
    · dsimp [block]
      exact (nativePNT_reciprocal_blocks_disjoint
        N (t j) (H j) (t i) (H i) (hsep j i hjilt hi)).symm
  have hpacked := nativeLambdaTwoGoodRecipMass_packed_blocks
    N J beta block hsub hdisj
  simpa [block, nativeLambdaTwoRecipIntervalMass] using hpacked
'''
s = s.replace(marker, block + marker)
p.write_text(s)
