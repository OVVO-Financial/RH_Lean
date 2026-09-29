import Mathlib
import RHLean.Analysis.PrimeSieveQuotientPNTError
import RHLean.Proof.PrimeCombReciprocalBandCancellation

/-!
# The late-flip PNT split is the compiled PNT centering, shifted by one count

Research proposal under test.  After the primes through `y` have acted, every
prime `y < q <= x` performs the reciprocal-band update

`h(floor(x/q)) = 2 * (1 - M(floor(x/q)))`,

and `h(1) = 0`, so the top half `x/2 < q` is inert.  The proposal keeps the
root-stage field exact, replaces only the late-flip prime multiplicities by
logarithmic-integral density, and studies

`M(x) = (root field + Li model of the late flips) + eta`.

This file identifies both pieces with objects that were already compiled in
`PrimeSievePNTCentering` and `PrimeSieveQuotientPNTError`.  Writing `Disc(y,x)`
for the unweighted prime-count discrepancy `sum_{y<q<=x} (1_prime(q) - rho(q))`,
where `rho(q) = Li(q) - Li(q-1)`,

```text
eta(y,x)                  = 2 Disc(y,x) - 2 primeSievePNTError(y,x),
root field + Li model     = primeSievePNTCorrectedAllPlusMass(y,x) - 2 Disc(y,x).
```

So the proposed split is the repository's existing
`M = PNT-corrected all-plus mass - 2 * PNT error` split, with the single
unweighted discrepancy `2 Disc(y,x)` moved from the model side to the error
side.  The top half is inert in the late-flip operator (proved below), but its
primes remain in `Disc(y,x)` and in the exact root field.

Everything here is finite algebra.  No prime-number-theorem error term, no
bound on `eta`, and no bound on the model amplitude is asserted.  The finite
diagnostic in `research/LATE_FLIP_PNT_SPLIT_DIAGNOSTIC.md` measures both pieces
at the production endpoint `x = R^2 - 1`.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Complex prime count on `(y, x]`, as the prime-indicator sum. -/
def lateFlipPrimeCount (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x, RHLean.Analysis.primeSievePrimeIndicator q

/-- Complete late-flip correction: each prime `y < q <= x` applies the common
reciprocal-band update of its quotient band. -/
def lateFlipCorrection (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    RHLean.Analysis.primeSievePrimeIndicator q *
      primeCombReciprocalBandKernel (x / q)

/-- Root-stage field: the all-plus comb after the primes through `y`, with every
late prime seat already assigned its final sign `-1`.  Only the proper-multiple
channels of the late primes remain to be flipped. -/
def lateFlipRootField (y x : ℕ) : ℂ :=
  allPlusPrimeCombPrefixMass y x - 2 * lateFlipPrimeCount y x

/-- Logarithmic-integral model of the late-flip correction. -/
def lateFlipLiModel (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    RHLean.Analysis.primeSievePNTDensity q *
      primeCombReciprocalBandKernel (x / q)

/-- Exact effect of the actual late prime locations: `eta`. -/
def lateFlipPNTError (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    (RHLean.Analysis.primeSievePrimeIndicator q -
        RHLean.Analysis.primeSievePNTDensity q) *
      primeCombReciprocalBandKernel (x / q)

/-- Unweighted prime-count discrepancy on `(y, x]`. -/
def lateFlipPrimeCountDiscrepancy (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    (RHLean.Analysis.primeSievePrimeIndicator q -
      RHLean.Analysis.primeSievePNTDensity q)

private theorem lateFlip_mertensSummatory_one :
    RHLean.Analysis.mertensSummatory 1 = 1 := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]

/-! ## The inert top band -/

/-- The quotient-one band has zero late-flip update: `h(1) = 2 (1 - M(1)) = 0`. -/
theorem primeCombReciprocalBandKernel_one :
    primeCombReciprocalBandKernel 1 = 0 := by
  unfold primeCombReciprocalBandKernel
  rw [lateFlip_mertensSummatory_one, sub_self, mul_zero]

/-- Every coordinate in the top half `x/2 < q <= x` has quotient one, hence zero
late-flip update. -/
theorem primeCombReciprocalBandKernel_div_eq_zero_of_top
    {x q : ℕ} (hq : 0 < q) (hlow : x < 2 * q) (hhigh : q ≤ x) :
    primeCombReciprocalBandKernel (x / q) = 0 := by
  have h1 : 1 ≤ x / q := (Nat.le_div_iff_mul_le hq).2 (by simpa using hhigh)
  have h2 : x / q < 2 :=
    (Nat.div_lt_iff_lt_mul hq).2 (by simpa [Nat.mul_comm] using hlow)
  have hdiv : x / q = 1 := by omega
  rw [hdiv, primeCombReciprocalBandKernel_one]

/-- The smoothing error only sees the late primes below `x/2`: the top half
drops out of `eta` term by term. -/
theorem lateFlipPNTError_eq_lowerHalf
    {y x : ℕ} (hyx : y ≤ x / 2) :
    lateFlipPNTError y x =
      ∑ q ∈ Finset.Ioc y (x / 2),
        (RHLean.Analysis.primeSievePrimeIndicator q -
            RHLean.Analysis.primeSievePNTDensity q) *
          primeCombReciprocalBandKernel (x / q) := by
  have hsplit := Finset.sum_Ioc_consecutive
    (f := fun q : ℕ =>
      (RHLean.Analysis.primeSievePrimeIndicator q -
          RHLean.Analysis.primeSievePNTDensity q) *
        primeCombReciprocalBandKernel (x / q))
    hyx (Nat.div_le_self x 2)
  have htop :
      (∑ q ∈ Finset.Ioc (x / 2) x,
        (RHLean.Analysis.primeSievePrimeIndicator q -
            RHLean.Analysis.primeSievePNTDensity q) *
          primeCombReciprocalBandKernel (x / q)) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    rcases Finset.mem_Ioc.mp hq with ⟨hlow, hhigh⟩
    have hzero := primeCombReciprocalBandKernel_div_eq_zero_of_top
      (x := x) (q := q) (by omega) (by omega) hhigh
    rw [hzero, mul_zero]
  unfold lateFlipPNTError
  linear_combination htop - hsplit

/-! ## Exact reconstruction -/

/-- The late-flip correction is twice the late prime count minus twice the
compiled Mertens-weighted prime tail. -/
theorem lateFlipCorrection_eq_two_count_sub_two_primeTail (y x : ℕ) :
    lateFlipCorrection y x =
      2 * lateFlipPrimeCount y x - 2 * primeSieveMertensPrimeTail y x := by
  unfold lateFlipCorrection lateFlipPrimeCount primeSieveMertensPrimeTail
    primeCombReciprocalBandKernel RHLean.Analysis.primeSievePrimeIndicator
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> ring

/-- **Exact reconstruction.**  Past the square-root cutoff, Mertens is the root
field plus the complete late-flip correction. -/
theorem mertensSummatory_eq_lateFlipRootField_add_correction
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    RHLean.Analysis.mertensSummatory x =
      lateFlipRootField y x + lateFlipCorrection y x := by
  have hgap :=
    allPlusPrimeCombPrefixMass_sub_mertens_eq_two_mertensPrimeTail y x hroot
  rw [lateFlipCorrection_eq_two_count_sub_two_primeTail]
  unfold lateFlipRootField
  linear_combination -hgap

/-- The late-flip correction splits into its Li model and `eta`. -/
theorem lateFlipCorrection_eq_liModel_add_pntError (y x : ℕ) :
    lateFlipCorrection y x =
      lateFlipLiModel y x + lateFlipPNTError y x := by
  unfold lateFlipCorrection lateFlipLiModel lateFlipPNTError
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **The proposed split.**  Mertens is the model amplitude (root field plus Li
model) plus the exact location error `eta`. -/
theorem mertensSummatory_eq_lateFlipModel_add_pntError
    (y x : ℕ) (hroot : Nat.sqrt x < y) :
    RHLean.Analysis.mertensSummatory x =
      (lateFlipRootField y x + lateFlipLiModel y x) + lateFlipPNTError y x := by
  rw [mertensSummatory_eq_lateFlipRootField_add_correction y x hroot,
    lateFlipCorrection_eq_liModel_add_pntError]
  ring

/-! ## Bridge to the compiled PNT centering -/

/-- **`eta` is the compiled PNT error, shifted by one unweighted count.** -/
theorem lateFlipPNTError_eq_two_discrepancy_sub_two_pntError (y x : ℕ) :
    lateFlipPNTError y x =
      2 * lateFlipPrimeCountDiscrepancy y x -
        2 * RHLean.Analysis.primeSievePNTError y x := by
  unfold lateFlipPNTError lateFlipPrimeCountDiscrepancy
    RHLean.Analysis.primeSievePNTError primeCombReciprocalBandKernel
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The same bridge in reciprocal quotient-band coordinates: the weighted part
of `eta` is the compiled band sum of prime-count-minus-Li discrepancies
weighted by `M(d)`. -/
theorem lateFlipPNTError_eq_two_discrepancy_sub_two_reciprocalPNTError
    (y x : ℕ) :
    lateFlipPNTError y x =
      2 * lateFlipPrimeCountDiscrepancy y x -
        2 * RHLean.Analysis.primeSieveReciprocalPNTError y x := by
  rw [lateFlipPNTError_eq_two_discrepancy_sub_two_pntError,
    RHLean.Analysis.primeSievePNTError_eq_reciprocalPNTError]

/-- The Li model is twice the late Li mass minus twice the compiled PNT bulk. -/
theorem lateFlipLiModel_eq_two_density_sub_two_pntBulk (y x : ℕ) :
    lateFlipLiModel y x =
      2 * (∑ q ∈ Finset.Ioc y x, RHLean.Analysis.primeSievePNTDensity q) -
        2 * RHLean.Analysis.primeSievePNTBulk y x := by
  unfold lateFlipLiModel RHLean.Analysis.primeSievePNTBulk
    primeCombReciprocalBandKernel
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **The model amplitude is the compiled PNT-corrected all-plus mass, shifted by
the opposite unweighted count.**  The root field still carries the exact late
prime count, including the whole inert top half. -/
theorem lateFlipRootField_add_liModel_eq_pntCorrected_sub_two_discrepancy
    (y x : ℕ) :
    lateFlipRootField y x + lateFlipLiModel y x =
      RHLean.Analysis.primeSievePNTCorrectedAllPlusMass y x -
        2 * lateFlipPrimeCountDiscrepancy y x := by
  rw [lateFlipLiModel_eq_two_density_sub_two_pntBulk]
  unfold lateFlipRootField RHLean.Analysis.primeSievePNTCorrectedAllPlusMass
    lateFlipPrimeCountDiscrepancy lateFlipPrimeCount
  rw [Finset.sum_sub_distrib]
  ring

/-- The unweighted discrepancy is the late prime count minus its Li mass. -/
theorem lateFlipPrimeCountDiscrepancy_eq_count_sub_li
    {y x : ℕ} (hyx : y ≤ x) :
    lateFlipPrimeCountDiscrepancy y x =
      lateFlipPrimeCount y x -
        ((RHLean.Analysis.logarithmicIntegralFromTwo (x : ℝ) -
          RHLean.Analysis.logarithmicIntegralFromTwo (y : ℝ) : ℝ) : ℂ) := by
  unfold lateFlipPrimeCountDiscrepancy lateFlipPrimeCount
  rw [Finset.sum_sub_distrib, RHLean.Analysis.sum_primeSievePNTDensity_Ioc hyx]

/-! ## Production endpoint -/

private theorem lateFlip_squareRootEndpoint_sqrt_lt
    {R : ℕ} (hR : 1 ≤ R) :
    Nat.sqrt (squareRootEndpoint R) < R := by
  apply (Nat.sqrt_lt').2
  unfold squareRootEndpoint
  have hpos : 0 < R ^ 2 := by positivity
  omega

/-- At `X = R^2 - 1` with cutoff `R`, the proposal's model amplitude
`A = (B_root - M(R-1) + Q) + Hbar` and location error `eta` recombine to the
contract amplitude `G + Q = M(X) - M(R-1) + Q`, for any column value `Q`.
Hence `(A + eta)^2 - D` is exactly the contract's `FinalStokes`; the split
supplies no bound on either summand. -/
theorem squareRoot_lateFlipModel_add_pntError_eq_gap_add_column
    (R : ℕ) (hR : 1 ≤ R) (Q : ℂ) :
    (lateFlipRootField R (squareRootEndpoint R) -
          RHLean.Analysis.mertensSummatory (R - 1) + Q +
        lateFlipLiModel R (squareRootEndpoint R)) +
      lateFlipPNTError R (squareRootEndpoint R) =
      RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
        RHLean.Analysis.mertensSummatory (R - 1) + Q := by
  rw [mertensSummatory_eq_lateFlipModel_add_pntError R (squareRootEndpoint R)
    (lateFlip_squareRootEndpoint_sqrt_lt hR)]
  ring

end RHLean.Proof
