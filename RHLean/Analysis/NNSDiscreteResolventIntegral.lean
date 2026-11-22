import Mathlib
import RHLean.Proof.FinitePartialMoments

/-!
# NNS discrete quadrature, integral mean values, and almost-sure convergence

These results are unconditional real-analytic infrastructure. They do NOT
assert that an RHLean arithmetic matrix presents actual global Sha groups.

* Finite UPM1-LPM1 quadrature is the signed Riemann sum, for every target.
* Adjacent left/right quadratures have an exact Abel boundary.
* The integral mean value theorem supplies an exact tag in each cell.
* An explicit deterministic error envelope implies almost-sure convergence
  for any measure on the tagging space (no independence needed).

See research/ALPOGE_NNS_RESOLVENT_DISCRETE_MVT_20261121.md for the
concrete real-resolvent integral and its certified error envelope.
-/

noncomputable section
open scoped BigOperators Interval
open MeasureTheory Filter

namespace RHLean.Analysis

/-- Degree-one NNS upper-minus-lower quadrature at an arbitrary target. -/
def nnsTaggedQuadrature (n : Nat) (step target : Real) (sample : Nat -> Real) : Real :=
  step *
    (upperPartialMass (Finset.range n) (fun j => sample j - target) -
      lowerPartialMass (Finset.range n) (fun j => sample j - target)) +
    (n : Real) * step * target

/-- Exact NNS quadrature equals the original signed Riemann sum. -/
theorem nnsTaggedQuadrature_eq_sum (n : Nat) (step target : Real)
    (sample : Nat -> Real) :
    nnsTaggedQuadrature n step target sample =
      step * (Finset.range n).sum sample := by
  unfold nnsTaggedQuadrature
  rw [upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum]
  unfold finiteSignedSum
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The NNS partial-moment target does not change the numerical integral. -/
theorem nnsTaggedQuadrature_target_independent (n : Nat) (step a b : Real)
    (sample : Nat -> Real) :
    nnsTaggedQuadrature n step a sample =
      nnsTaggedQuadrature n step b sample := by
  rw [nnsTaggedQuadrature_eq_sum, nnsTaggedQuadrature_eq_sum]

/-- Exact discrete Abel boundary: left versus right endpoint rules. -/
theorem nnsTaggedQuadrature_left_sub_right (n : Nat) (step target : Real)
    (sample : Nat -> Real) :
    nnsTaggedQuadrature n step target sample -
      nnsTaggedQuadrature n step target (fun j => sample (j + 1)) =
        step * (sample 0 - sample n) := by
  rw [nnsTaggedQuadrature_eq_sum, nnsTaggedQuadrature_eq_sum]
  have telescoping (k : Nat) :
      (Finset.range k).sum (fun j => sample j - sample (j + 1)) =
        sample 0 - sample k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    step * (Finset.range n).sum sample -
        step * (Finset.range n).sum (fun j => sample (j + 1)) =
        step * (Finset.range n).sum (fun j => sample j - sample (j + 1)) := by
          rw [Finset.sum_sub_distrib]
          ring
    _ = step * (sample 0 - sample n) := by rw [telescoping]

/-- The ordinary integral mean value theorem supplies an exact tag
for every continuous real cell kernel. -/
theorem nnsIntegralCell_mean_value (f : Real -> Real) (hf : Continuous f)
    (a b : Real) :
    Exists (fun c : Real => c ∈ Set.uIcc a b ∧
      (∫ x in a..b, f x) = (b - a) * f c) := by
  obtain ⟨c, hc, heq⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg
      (f := f) (g := fun _ => (1 : Real)) (a := a) (b := b)
      (μ := volume) hf.continuousOn intervalIntegrable_const
      (by intro _ _; norm_num)
  refine ⟨c, hc, ?_⟩
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using heq

/-- A deterministic uniform error bound that converges to zero yields
almost-sure convergence for *every* measure on the tag space.
The random objects here are numerical tags, not primes or Mobius values. -/
theorem nnsIntegral_uniformError_implies_ae_convergence
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (Q : Nat -> Omega -> Real) (I : Real) (err : Nat -> Real)
    (herr : Tendsto err atTop (nhds (0 : Real)))
    (hbound : ∀ omega, ∀ n, |Q n omega - I| ≤ err n) :
    ∀ᵐ omega ∂mu, Tendsto (fun n => Q n omega) atTop (nhds I) := by
  apply Filter.Eventually.of_forall
  intro omega
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero
    (fun n => norm_nonneg (Q n omega - I))
    (fun n => by simpa only [Real.norm_eq_abs] using hbound omega n)
    herr

end RHLean.Analysis
