import RHLean.Proof.StableFarWallRenewalDescent
import RHLean.Proof.CanonicalRoughAdaptiveWeightedIteration

/-!
# Stable-far crossings are adaptive four-corner cancellations

The stable-far q^2 renewal and the adaptive rough-prime descent are two
coordinates on the same arithmetic square.

A stripped far-wall triple has shape `(q,(d,p))` with

  q < R < p,
  P+(d) < q,
  q*d*p <= X_R.

Viewed at the low owner `q`, the far prime `p` is therefore a *strictly larger
physical extension* of the current child `d*q`.  The four corners

  d, d*q, d*p, d*q*p

all lie on the full raw carrier whenever the largest corner does.  In a
descending prime schedule, `p` is processed before `q`.  The already-compiled
four-corner theorem then zeroes the evolved raw coefficients of both `d` and
`d*q` at the `p` step, permanently through the rest of the schedule.

This is the cross-prime cancellation that ownerwise q^2 norms cannot see: the
far prime which defines the stable wall itself kills the coefficient mismatch
of the lower q-renewal before the q coordinate is processed.

No estimate, norm, or asymptotic input is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- **Far-wall four-corner coefficient kill.**

For every actual stripped stable-far triple, if a descending schedule is split
at its far prime and every earlier coordinate is still larger, then the raw
adaptive coefficients of the stripped parent `d` and low-prime child `d*q` are
both exactly zero after that split. -/
theorem lowWheelFarPrimeLowCofactorTriple_rawCoefficient_pair_eq_zero_at_farPrime
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeLowCofactorTriples R)
    (pre post : List ℕ)
    (hprePrime : ∀ r ∈ pre, r.Prime)
    (hpreLarger : ∀ r ∈ pre, t.2.2 < r) :
    squareRootCanonicalRoughAdaptiveRawCoefficient
        (pre ++ t.2.2 :: post)
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) t.2.1 = 0 ∧
      squareRootCanonicalRoughAdaptiveRawCoefficient
        (pre ++ t.2.2 :: post)
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) (t.2.1 * t.1) = 0 := by
  rcases lowWheelFarPrimeLowCofactorTriple_data ht with
    ⟨hq, hqR, hd1, hp, hpR, _hdsq, hdq, hcut⟩
  have hdpos : 0 < t.2.1 := by omega
  have hqp : t.1 < t.2.2 := by omega
  have hupper : (t.2.1 * t.1) * t.2.2 ≤ squareRootEndpoint R := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcut
  exact
    squareRootCanonicalRoughAdaptiveRawCoefficient_pair_eq_zero_of_larger_extension_split
      pre post hdpos hq hp hdq hqp hupper hprePrime hpreLarger

/-- The same cancellation applies in particular to every strict q^2 crossing
triple.  Crossing versus descended is irrelevant for the four-corner kill: the
single-insertion product `q*d*p <= X_R` already supplies the larger-prime
corner needed by the descending adaptive schedule. -/
theorem lowWheelFarPrimeQ2CrossingTriple_rawCoefficient_pair_eq_zero_at_farPrime
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeQ2CrossingTriples R)
    (pre post : List ℕ)
    (hprePrime : ∀ r ∈ pre, r.Prime)
    (hpreLarger : ∀ r ∈ pre, t.2.2 < r) :
    squareRootCanonicalRoughAdaptiveRawCoefficient
        (pre ++ t.2.2 :: post)
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) t.2.1 = 0 ∧
      squareRootCanonicalRoughAdaptiveRawCoefficient
        (pre ++ t.2.2 :: post)
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) (t.2.1 * t.1) = 0 := by
  exact lowWheelFarPrimeLowCofactorTriple_rawCoefficient_pair_eq_zero_at_farPrime
    (Finset.mem_filter.mp ht).1 pre post hprePrime hpreLarger

/-- Consequently every stable-far strict crossing carries a literal larger-prime
witness for the adaptive mismatch annihilation: its own far prime. -/
theorem lowWheelFarPrimeQ2CrossingTriple_has_larger_extension
    {R : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ lowWheelFarPrimeQ2CrossingTriples R) :
    squareRootCanonicalRoughHasPrimeExtensionAbove
      R t.1 (t.2.1 * t.1) := by
  have hdata := lowWheelFarPrimeLowCofactorTriple_data
    (Finset.mem_filter.mp ht).1
  rcases hdata with
    ⟨hq, hqR, hd1, hp, hpR, _hdsq, hdq, hcut⟩
  refine ⟨t.2.2, hp, ?_, ?_⟩
  · omega
  · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcut

end RHLean.Proof
