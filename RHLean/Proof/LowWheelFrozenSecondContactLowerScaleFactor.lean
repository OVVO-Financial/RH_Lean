import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactGlobalTelescope

/-!
# Factor the strict frozen second-contact scale descent

Every frozen second-contact source already carries the smaller cutoff

`B = floor(X_R / (p * P(t))) < R`

and the cofactor exit shell

`c <= B < P+(c) * c`.

This module factors `c` by its canonical largest prime `q = P+(c)`.  Since the
existing frozen-cofactor arithmetic proves `q` is prime and `q ∣ c`, writing
`d = c / q` turns the exit shell into the literal second-contact shell

`q*d <= B < q^2*d`

at the strictly smaller cutoff `B < R`.

No sum, norm, asymptotic estimate, or cancellation hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- **Strict lower-scale second-contact factorization.**  Every frozen source
factors through its canonical largest cofactor prime into the same multiplicative
second-contact geometry at a strictly smaller numerical cutoff. -/
theorem lowWheelFrozenSecondContact_source_lowerScaleSecondContact
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
    let B := squareRootEndpoint R / A
    let q := lowWheelFrozenCofactorTopPrime y
    let d := y.2.1 / q
    q.Prime ∧
      q * d = y.2.1 ∧
      q * d ≤ B ∧
      B < q * q * d ∧
      B < R := by
  rcases Finset.mem_filter.mp hy with ⟨hyFrozen, _hsecond⟩
  let A := lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1
  let B := squareRootEndpoint R / A
  let q := lowWheelFrozenCofactorTopPrime y
  let d := y.2.1 / q
  rcases lowWheelFrozenCofactorTopPrime_data hyFrozen with
    ⟨hqPrime, hqDvd, _hpq⟩
  have hqd : q * d = y.2.1 := by
    simpa [q, d, Nat.mul_comm] using Nat.div_mul_cancel hqDvd
  have hexit := lowWheelFrozenSecondContact_source_lowerScaleExit hy
  have hcB : y.2.1 ≤ B := by
    simpa [A, B, q] using hexit.1
  have hBqc : B < q * y.2.1 := by
    simpa [A, B, q] using hexit.2.1
  have hBR : B < R := by
    simpa [A, B, q] using hexit.2.2
  have hqdB : q * d ≤ B := by
    simpa [hqd] using hcB
  have hBqqd : B < q * q * d := by
    calc
      B < q * y.2.1 := hBqc
      _ = q * (q * d) := by rw [hqd]
      _ = q * q * d := by ring
  exact ⟨hqPrime, hqd, hqdB, hBqqd, hBR⟩

end RHLean.Proof
