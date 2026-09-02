import Mathlib
import RHLean.Proof.CanonicalRoughTruncatedWheelDefectTelescope

/-!
# Many-prime telescope for truncated Euler-wheel defect shells

The fixed-partner theorem in `CanonicalRoughTruncatedWheelDefectTelescope`
identifies one physical defect shell, with its native `1/p`, as

```text
T_{P insert p}(N) - (1 - 1/p) * T_P(N).
```

The chronological orientation in the canonical rough compression processes the
larger prime first.  Therefore a shell created later at a smaller prime is
transported by every already-applied larger Euler factor.  This file records the
resulting exact telescope for an arbitrary duplicate-free list of prime
coordinates.

For a descending list `L = [p_k, ..., p_1]`, define recursively

```text
Ledger(N, p :: L)
  = (1 - 1/p) * Ledger(N, L)
    + (1/p) * (T_L(N) - T_L(N/p)).
```

Then, with no estimate at all,

```text
Ledger(N,L)
  = T_L(N) - EulerProduct(L) * T_empty(N).
```

For positive `N`, `T_empty(N)=1`, so the complete transported defect ledger is
literally the final truncated-wheel boundary

```text
T_L(N) - EulerProduct(L).
```

This is the quantitative structural replacement for the `(1-P) * Delta`
majorant: after the partner reindex, the physical defect shells telescope to one
final boundary profile instead of accumulating one normed error per prime.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Euler product of a chronological prime list, using the same factor as #540. -/
def canonicalRoughPrimeListEulerProduct : List ℕ → ℝ
  | [] => 1
  | p :: ps => canonicalRoughEulerFactor p * canonicalRoughPrimeListEulerProduct ps

@[simp] theorem canonicalRoughPrimeListEulerProduct_nil :
    canonicalRoughPrimeListEulerProduct [] = 1 := by
  rfl

@[simp] theorem canonicalRoughPrimeListEulerProduct_cons (p : ℕ) (ps : List ℕ) :
    canonicalRoughPrimeListEulerProduct (p :: ps) =
      canonicalRoughEulerFactor p * canonicalRoughPrimeListEulerProduct ps := by
  rfl

/-- The Finset Euler contraction factor agrees exactly with the chronological
list product whenever the list has no duplicate coordinates. -/
theorem primorialSignedContractionFactor_toFinset_eq_primeListEulerProduct
    (ps : List ℕ) (hnodup : ps.Nodup) :
    primorialSignedContractionFactor ps.toFinset =
      canonicalRoughPrimeListEulerProduct ps := by
  induction ps with
  | nil =>
      simp [primorialSignedContractionFactor,
        canonicalRoughPrimeListEulerProduct]
  | cons p ps ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hpNotList, htailNodup⟩
      have hpNot : p ∉ ps.toFinset := by
        simpa using hpNotList
      simp only [List.toFinset_cons, canonicalRoughPrimeListEulerProduct]
      unfold primorialSignedContractionFactor
      rw [Finset.prod_insert hpNot]
      have ih' := ih htailNodup
      unfold primorialSignedContractionFactor at ih'
      rw [ih']
      unfold canonicalRoughEulerFactor
      rfl

/-- Transported reciprocal shell ledger for one fixed truncation cutoff `N`.
The head of the list is the larger/earlier prime, exactly matching the transport
orientation in `squareRootCanonicalRoughTransportedDefectLedger`. -/
def primorialTruncatedTransportedShellLedger (N : ℕ) : List ℕ → ℝ
  | [] => 0
  | p :: ps =>
      canonicalRoughEulerFactor p *
          primorialTruncatedTransportedShellLedger N ps +
        (1 / (p : ℝ)) *
          (primorialTruncatedSignedReciprocalCube ps.toFinset N -
            primorialTruncatedSignedReciprocalCube ps.toFinset (N / p))

@[simp] theorem primorialTruncatedTransportedShellLedger_nil (N : ℕ) :
    primorialTruncatedTransportedShellLedger N [] = 0 := by
  rfl

/-- **Exact many-prime transported-shell telescope.**

The shell at each prime is converted by the fresh-prime truncated-wheel
recurrence into `new state - EulerFactor * old state`; the recursive transport
then cancels every intermediate state. -/
theorem primorialTruncatedTransportedShellLedger_eq_boundary
    (N : ℕ) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup) :
    primorialTruncatedTransportedShellLedger N ps =
      primorialTruncatedSignedReciprocalCube ps.toFinset N -
        canonicalRoughPrimeListEulerProduct ps *
          primorialTruncatedSignedReciprocalCube ∅ N := by
  induction ps with
  | nil =>
      simp [primorialTruncatedTransportedShellLedger,
        canonicalRoughPrimeListEulerProduct]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have htailPrime : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      rcases List.nodup_cons.mp hnodup with ⟨hpNotList, htailNodup⟩
      have hpNot : p ∉ ps.toFinset := by
        simpa using hpNotList
      have hstep :=
        primorialTruncatedSignedReciprocalCube_shell_div_prime_eq_insert_sub_euler
          (P := ps.toFinset) (p := p) (N := N) hpNot hp
      simp only [primorialTruncatedTransportedShellLedger,
        canonicalRoughPrimeListEulerProduct]
      rw [ih htailPrime htailNodup]
      rw [hstep]
      simp only [List.toFinset_cons]
      unfold canonicalRoughEulerFactor
      ring

/-- At every positive cutoff the empty truncated wheel is the unit state, so the
transported shell ledger is exactly `final truncated cube - full Euler product`. -/
theorem primorialTruncatedTransportedShellLedger_eq_truncated_sub_eulerProduct
    (N : ℕ) (ps : List ℕ) (hN : 1 ≤ N)
    (hprime : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup) :
    primorialTruncatedTransportedShellLedger N ps =
      primorialTruncatedSignedReciprocalCube ps.toFinset N -
        canonicalRoughPrimeListEulerProduct ps := by
  rw [primorialTruncatedTransportedShellLedger_eq_boundary N ps hprime hnodup,
    primorialTruncatedSignedReciprocalCube_empty N hN]
  ring

/-- If the final cutoff already contains the complete wheel, then even the final
boundary vanishes: the transported shell ledger is exactly zero. -/
theorem primorialTruncatedTransportedShellLedger_eq_zero_of_complete
    (N : ℕ) (ps : List ℕ) (hN : 1 ≤ N)
    (hprime : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup)
    (hcomplete : primorialWheelProduct ps.toFinset ≤ N) :
    primorialTruncatedTransportedShellLedger N ps = 0 := by
  rw [primorialTruncatedTransportedShellLedger_eq_truncated_sub_eulerProduct
    N ps hN hprime hnodup]
  have hfactor :=
    primorialTruncatedSignedReciprocalCube_eq_factor ps.toFinset N
      (by
        intro p hp
        exact hprime p (by simpa using hp)) hcomplete
  rw [hfactor,
    primorialSignedContractionFactor_toFinset_eq_primeListEulerProduct ps hnodup]
  ring

end RHLean.Proof
