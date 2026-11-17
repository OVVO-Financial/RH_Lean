import «research.NATIVE_OWNER_DIAGONAL_CAPACITY_20261117»

set_option autoImplicit false
open scoped BigOperators
open RHLean.Analysis.OwnerPrefix RHLean.Proof RHLean.Proof.NativeOwnerSwapRenewal

example (R x : ℕ) (hR : 2 ≤ R) (hx : x < R ^ 2) :
    (∑ p ∈ primeOwnersUpTo R x, x / p) ≤ x - R :=
  owner_quotient_sum_le_interval R x hR hx

example (M : ℕ → ℝ) (R x : ℕ)
    (hR : 2 ≤ R) (hRx : R ≤ x) (hx : x < R ^ 2) :
    diagonalUpTo M R x ≤ ((x : ℝ) - R) * prefixAmplitude M R ^ 2 :=
  diagonal_upTo_le_capacity M R x hR hRx hx

example (R y : ℕ) (hR : 2 ≤ R) (hy : 1 ≤ y) (hyR : y < R) :
    nativeM y ^ 2 ≤ 3 * squareRootHistoricalK R * y :=
  nativeM_sq_le_three_historical hR hy hyR

example (R : ℕ) (hR : 2 ≤ R) :
    prefixAmplitude nativeM R ^ 2 ≤ 3 * squareRootHistoricalK R :=
  native_prefixAmplitude_sq_le_three_historical R hR

example (R x : ℕ) (hR : 2 ≤ R) (hRx : R ≤ x) (hx : x < R ^ 2) :
    diagonalUpTo nativeM R x ≤ 3 * ((x : ℝ) - R) * squareRootHistoricalK R :=
  native_diagonal_upTo_le_historical R x hR hRx hx

example (R : ℕ) (hR : 2 ≤ R) :
    ownerDiagonal R ≤
      3 * ((squareRootEndpoint R : ℝ) - R) * squareRootHistoricalK R :=
  native_owner_diagonal_le_capacity R hR

example (M : ℕ → ℝ) (R : ℕ) :
    diagonalUpTo M R (endpoint R) = diagonal M R :=
  diagonalUpTo_endpoint M R

example (R x : ℕ) (hR : 2 ≤ R) (hx : x < R ^ 2) :
    nativeM x = nativeSmoothUpTo R x - transportUpTo nativeM R x :=
  native_decomposition_upTo R x hR hx

example (R x : ℕ) (hR : 2 ≤ R) (hx : x < R ^ 2) :
    nativeM x ^ 2 = diagonalUpTo nativeM R x + nativeGammaUpTo R x :=
  native_energy_upTo R x hR hx

example (R : ℕ) (hR : 2 ≤ R) :
    nativeGammaUpTo R (endpoint R) = fullOwnerGamma R :=
  nativeGammaUpTo_endpoint R hR

example (R : ℕ) (hR : 2 ≤ R) (L C : ℝ)
    (hKL : squareRootHistoricalK R ≤ L) (hC : 0 ≤ C)
    (hgamma : ∀ x : ℕ, R ≤ x → x < R ^ 2 →
      nativeGammaUpTo R x ≤ C * (x : ℝ) * L) :
    squareRootHistoricalK (R ^ 2) ≤ (4 + C) * L :=
  native_historical_preservation_of_compensation R hR L C hKL hC hgamma

example (R : ℕ) (hR : 2 ≤ R) (B : ℝ) (hB : 0 ≤ B)
    (hgamma : ∀ x : ℕ, R ≤ x → x < R ^ 2 →
      nativeGammaUpTo R x ≤ B * (x : ℝ) * squareRootHistoricalK R) :
    squareRootHistoricalK (R ^ 2) ≤ (4 + B) * squareRootHistoricalK R :=
  native_historical_preservation_of_relative_compensation R hR B hB hgamma

#print owner_quotient_sum_le_interval
#print diagonal_upTo_le_capacity
#print nativeM_sq_le_three_historical
#print native_prefixAmplitude_sq_le_three_historical
#print native_diagonal_upTo_le_historical
#print native_owner_diagonal_le_capacity
#print native_decomposition_upTo
#print native_energy_upTo
#print nativeGammaUpTo_endpoint
#print native_historical_preservation_of_compensation
#print native_historical_preservation_of_relative_compensation
