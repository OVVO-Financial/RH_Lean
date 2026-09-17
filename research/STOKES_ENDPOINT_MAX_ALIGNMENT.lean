import Mathlib
import RHLean.Analysis.PrimeWheelCoconductorTailBound
import RHLean.Analysis.SquareWheelQuadraticSampling

/-!
# Deterministic completed-period endpoint alignment bound

This file formalizes the harmonic mechanism suggested by the staggered-prime
superposition picture.

For a finite wheel `W` and a divisor period `p | W.modulus`, the canonical
frequency

  r_p = W.modulus / p  in ZMod W.modulus

has reduced additive conductor exactly `p`.  Thus the period-`p` wave on the
ambient wheel is represented without approximation by one additive character.

For two distinct prime periods `p,q`, the cross-frequency `r_p-r_q` is nonzero
and its reduced conductor divides `p*q`.  Every completed cross period therefore
cancels exactly.  The finite Dirichlet response at an arbitrary endpoint is
identical to the response on the residual incomplete period, and hence its norm
is at most `p*q`.

After reciprocal normalization by `1/p` and `1/q`, every off-diagonal pair has
maximum possible alignment at most one.  This is deterministic: no prime-spacing
probability, PNT input, or asymptotic equidistribution is used.
-/

noncomputable section
open scoped BigOperators
open AddChar

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Canonical additive frequency whose character has period `p` whenever
`p | W.modulus`. -/
def primePeriodFrequency
    (W : PrimeWheelFiniteSystem) (p : ℕ) : ZMod W.modulus :=
  (((W.modulus / p : ℕ) : ZMod W.modulus))

/-- The canonical period-`p` frequency has reduced conductor exactly `p`. -/
theorem reducedAdditiveConductor_primePeriodFrequency
    (W : PrimeWheelFiniteSystem) (p : ℕ)
    (hpmod : p ∣ W.modulus) :
    reducedAdditiveConductor (primePeriodFrequency W p) = p := by
  rw [reducedAdditiveConductor_eq_addOrderOf W]
  have hNne : W.modulus ≠ 0 := Nat.ne_of_gt W.modulus_pos
  unfold primePeriodFrequency
  rw [ZMod.addOrderOf_coe _ hNne]
  have hprod : p * (W.modulus / p) = W.modulus :=
    Nat.mul_div_cancel' hpmod
  have hquotdvd : W.modulus / p ∣ W.modulus := by
    refine ⟨p, ?_⟩
    simpa [Nat.mul_comm] using hprod.symm
  rw [Nat.gcd_eq_right_iff_dvd.mpr hquotdvd]
  have hquotpos : 0 < W.modulus / p :=
    Nat.pos_of_dvd_of_pos hquotdvd W.modulus_pos
  apply Nat.div_eq_of_eq_mul_right hquotpos
  simpa [Nat.mul_comm] using hprod.symm

/-- Distinct divisor periods give distinct canonical frequencies. -/
theorem primePeriodFrequency_ne_of_ne
    (W : PrimeWheelFiniteSystem) {p q : ℕ}
    (hpmod : p ∣ W.modulus) (hqmod : q ∣ W.modulus)
    (hpq : p ≠ q) :
    primePeriodFrequency W p ≠ primePeriodFrequency W q := by
  intro hfreq
  have hcond := congrArg
    (fun r : ZMod W.modulus => reducedAdditiveConductor r) hfreq
  change
    reducedAdditiveConductor (primePeriodFrequency W p) =
      reducedAdditiveConductor (primePeriodFrequency W q) at hcond
  rw [reducedAdditiveConductor_primePeriodFrequency W p hpmod,
    reducedAdditiveConductor_primePeriodFrequency W q hqmod] at hcond
  exact hpq hcond

/-- The cross-frequency conductor of two divisor periods divides the product
`p*q`.  Equivalently, every block of length `p*q` is a completed cross period. -/
theorem reducedAdditiveConductor_primePeriodDifference_dvd_mul
    (W : PrimeWheelFiniteSystem) {p q : ℕ}
    (hpmod : p ∣ W.modulus) (hqmod : q ∣ W.modulus) :
    reducedAdditiveConductor
        (primePeriodFrequency W p - primePeriodFrequency W q) ∣ p * q := by
  let rp := primePeriodFrequency W p
  let rq := primePeriodFrequency W q
  have hpord : addOrderOf rp = p := by
    rw [← reducedAdditiveConductor_eq_addOrderOf W]
    exact reducedAdditiveConductor_primePeriodFrequency W p hpmod
  have hqord : addOrderOf rq = q := by
    rw [← reducedAdditiveConductor_eq_addOrderOf W]
    exact reducedAdditiveConductor_primePeriodFrequency W q hqmod
  have hpzero : (p * q) • rp = 0 := by
    apply (addOrderOf_dvd_iff_nsmul_eq_zero).1
    rw [hpord]
    exact dvd_mul_right p q
  have hqzero : (p * q) • rq = 0 := by
    apply (addOrderOf_dvd_iff_nsmul_eq_zero).1
    rw [hqord]
    simp
  have hdiffzero : (p * q) • (rp - rq) = 0 := by
    rw [nsmul_sub, hpzero, hqzero, sub_zero]
  have horder : addOrderOf (rp - rq) ∣ p * q :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).2 hdiffzero
  rw [reducedAdditiveConductor_eq_addOrderOf W]
  exact horder

/-- Powers of one finite-wheel character depend only on the exponent modulo its
reduced additive conductor.  This is the algebraic deletion of completed
frequency periods. -/
theorem stokesStdAddChar_pow_eq_mod_reducedAdditiveConductor
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus) :
    ZMod.stdAddChar r ^ N =
      ZMod.stdAddChar r ^ (N % reducedAdditiveConductor r) := by
  let c : ℕ := reducedAdditiveConductor r
  have hcOrder : c = addOrderOf r := by
    dsimp [c]
    exact reducedAdditiveConductor_eq_addOrderOf W r
  have hcDvd : addOrderOf r ∣ c := by
    rw [hcOrder]
  have hcsmul : c • r = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).1 hcDvd
  have hpowc : ZMod.stdAddChar r ^ c = 1 := by
    calc
      ZMod.stdAddChar r ^ c = ZMod.stdAddChar (c • r) := by
        symm
        exact AddChar.map_nsmul_eq_pow
          (ZMod.stdAddChar : AddChar (ZMod W.modulus) ℂ) c r
      _ = ZMod.stdAddChar 0 := by rw [hcsmul]
      _ = 1 := AddChar.map_zero_eq_one _
  have hdecomp : N % c + c * (N / c) = N := Nat.mod_add_div N c
  calc
    ZMod.stdAddChar r ^ N =
        ZMod.stdAddChar r ^ (N % c + c * (N / c)) := by rw [hdecomp]
    _ = ZMod.stdAddChar r ^ (N % c) *
        ZMod.stdAddChar r ^ (c * (N / c)) := by rw [pow_add]
    _ = ZMod.stdAddChar r ^ (N % c) *
        (ZMod.stdAddChar r ^ c) ^ (N / c) := by rw [pow_mul]
    _ = ZMod.stdAddChar r ^ (N % c) := by rw [hpowc]; simp
    _ = ZMod.stdAddChar r ^
        (N % reducedAdditiveConductor r) := by rfl

/-- The finite Dirichlet response itself is unchanged after deleting all
completed conductor periods. -/
theorem stokesPrimeWheelDirichletKernel_eq_mod_reducedAdditiveConductor
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus) (hr : r ≠ 0) :
    primeWheelDirichletKernel W N r =
      primeWheelDirichletKernel W
        (N % reducedAdditiveConductor r) r := by
  rw [primeWheelDirichletKernel_eq_geom_of_ne_zero W N r hr,
    primeWheelDirichletKernel_eq_geom_of_ne_zero
      W (N % reducedAdditiveConductor r) r hr,
    stokesStdAddChar_pow_eq_mod_reducedAdditiveConductor W N r]

/-- After deleting all completed conductor periods, a nonzero Dirichlet response
is bounded by one residual conductor length. -/
theorem norm_primeWheelDirichletKernel_le_reducedConductor
    (W : PrimeWheelFiniteSystem) (N : ℕ)
    (r : ZMod W.modulus) (hr : r ≠ 0) :
    ‖primeWheelDirichletKernel W N r‖ ≤
      (reducedAdditiveConductor r : ℝ) := by
  rw [stokesPrimeWheelDirichletKernel_eq_mod_reducedAdditiveConductor W N r hr]
  have hlen := norm_primeWheelDirichletKernel_le_length W
    (N % reducedAdditiveConductor r) r
  have hcpos : 0 < reducedAdditiveConductor r := by
    rw [reducedAdditiveConductor_eq_addOrderOf W]
    exact addOrderOf_pos r
  have hmod : N % reducedAdditiveConductor r ≤ reducedAdditiveConductor r :=
    Nat.le_of_lt (Nat.mod_lt _ hcpos)
  exact hlen.trans (by exact_mod_cast hmod)

/-- **Maximum completed-period alignment bound.**

For two distinct prime periods embedded in the same wheel, the arbitrary finite
endpoint cross response has norm at most `p*q`. -/
theorem norm_primePeriodDifferenceDirichlet_le_mul
    (W : PrimeWheelFiniteSystem) (N : ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpmod : p ∣ W.modulus) (hqmod : q ∣ W.modulus) :
    ‖primeWheelDirichletKernel W N
        (primePeriodFrequency W p - primePeriodFrequency W q)‖ ≤
      ((p * q : ℕ) : ℝ) := by
  have hfreq :
      primePeriodFrequency W p - primePeriodFrequency W q ≠ 0 := by
    exact sub_ne_zero.mpr
      (primePeriodFrequency_ne_of_ne W hpmod hqmod hpq)
  have hcond := norm_primeWheelDirichletKernel_le_reducedConductor W N
    (primePeriodFrequency W p - primePeriodFrequency W q) hfreq
  have hdiv := reducedAdditiveConductor_primePeriodDifference_dvd_mul
    W hpmod hqmod
  have hle :
      reducedAdditiveConductor
          (primePeriodFrequency W p - primePeriodFrequency W q) ≤ p * q :=
    Nat.le_of_dvd (Nat.mul_pos hp.pos hq.pos) hdiv
  exact hcond.trans (by exact_mod_cast hle)

/-- Reciprocal normalization turns the worst possible off-diagonal alignment of
any distinct prime pair into an absolute unit bound. -/
theorem invPrime_mul_invPrime_mul_norm_primePeriodDifferenceDirichlet_le_one
    (W : PrimeWheelFiniteSystem) (N : ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpmod : p ∣ W.modulus) (hqmod : q ∣ W.modulus) :
    ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
        ‖primeWheelDirichletKernel W N
          (primePeriodFrequency W p - primePeriodFrequency W q)‖ ≤ 1 := by
  have h := norm_primePeriodDifferenceDirichlet_le_mul
    W N hp hq hpq hpmod hqmod
  have hw : 0 ≤ ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) := by
    positivity
  calc
    ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
        ‖primeWheelDirichletKernel W N
          (primePeriodFrequency W p - primePeriodFrequency W q)‖ ≤
      ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
        (((p * q : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h hw
    _ = 1 := by
      rw [Nat.cast_mul]
      field_simp [Nat.cast_ne_zero.mpr hp.ne_zero,
        Nat.cast_ne_zero.mpr hq.ne_zero]

end RHLean.Analysis
