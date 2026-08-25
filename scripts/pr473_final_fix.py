#!/usr/bin/env python3
"""Apply the last processed-carrier and owner-cancellation repairs for PR #473."""

from pathlib import Path


def replace_once(path: str, old: str, new: str) -> None:
    p = Path(path)
    text = p.read_text()
    count = text.count(old)
    if count == 0 and new in text:
        return
    if count != 1:
        raise SystemExit(f"expected one anchor in {path}, found {count}: {old!r}")
    p.write_text(text.replace(old, new, 1))


processed = "RHLean/Proof/SquareRootLowPrimeProcessedSeatCarrier.lean"
replace_once(
    processed,
    """        · simp [hlpf, hmu, hcR]
          push_cast
          ring
        · simp [hlpf, hmu, hcR]
          push_cast
          ring
""",
    """        · simp [hlpf, hmu, hcR]
          push_cast
          ring
        · simp [hlpf, hmu, hcR]
""",
)
replace_once(
    processed,
    """  rw [hsplit]
  unfold squareRootBornPostTailRunningLowPrimeResponse
  simp [canonicalMoebiusWeight, Complex.re_sum] <;> ring
""",
    """  rw [hsplit]
  unfold squareRootBornPostTailRunningLowPrimeResponse
  simp only [Complex.add_re, Complex.re_sum]
  simp [canonicalMoebiusWeight, Complex.mul_re]
  ring
""",
)
replace_once(
    processed,
    """  unfold squareRootLowPrimeRunningImbalanceReal
    squareRootLowPrimeRunningImbalance
  simp <;> ring
""",
    """  unfold squareRootLowPrimeRunningImbalanceReal
    squareRootLowPrimeRunningImbalance
  simp
  ring
""",
)
replace_once(
    processed,
    """  · unfold squareRootLowPrimeProcessedSeatWeightReal
    have hInt : |(-μ z.1 : ℤ)| ≤ 1 := by
      simpa using (ArithmeticFunction.abs_moebius_le_one (n := z.1))
    exact_mod_cast hInt
""",
    """  · change |(((-μ z.1 : ℤ) : ℝ))| ≤ 1
    have hInt : |(-μ z.1 : ℤ)| ≤ 1 := by
      simpa using (ArithmeticFunction.abs_moebius_le_one (n := z.1))
    exact_mod_cast hInt
""",
)

canonical = "RHLean/Proof/SquareRootLowPrimeCanonicalCreationResponseMap.lean"
replace_once(
    canonical,
    """  · have hdata := squareRootLowPrimeShallowBornSeatAtom_data hz
    have hc := Finset.mem_filter.mp hdata.1
    rcases Finset.mem_Icc.mp hc.1 with ⟨hcOne, _hcTop⟩
    exact ⟨by omega, hc.2.1, hc.2.2⟩
  · have hdata := squareRootLowPrimeShallowHighSeatAtom_data hz
    have hc := Finset.mem_filter.mp hdata.1
    rcases Finset.mem_Icc.mp hc.1 with ⟨hcOne, _hcTop⟩
    exact ⟨by omega, hc.2.1, hc.2.2⟩
""",
    """  · have hdata := squareRootLowPrimeShallowBornSeatAtom_data hz
    have hc := Finset.mem_filter.mp hdata.1
    rcases Finset.mem_Icc.mp hc.1 with ⟨hcOne, _hcTop⟩
    change 0 < z.1 ∧ canonicalLargestPrimeFactor z.1 ≤ K ∧ μ z.1 ≠ 0
    exact ⟨by omega, hc.2.1, hc.2.2⟩
  · have hdata := squareRootLowPrimeShallowHighSeatAtom_data hz
    have hc := Finset.mem_filter.mp hdata.1
    rcases Finset.mem_Icc.mp hc.1 with ⟨hcOne, _hcTop⟩
    change 0 < z.1 ∧ canonicalLargestPrimeFactor z.1 ≤ K ∧ μ z.1 ≠ 0
    exact ⟨by omega, hc.2.1, hc.2.2⟩
""",
)
replace_once(
    canonical,
    """  have hcEq :
      squareRootLowPrimeCreationStateCofactor x =
        squareRootLowPrimeCreationStateCofactor y := by
    rw [hpEq] at hprod
    exact Nat.mul_left_cancel hprod
""",
    """  have hcEq :
      squareRootLowPrimeCreationStateCofactor x =
        squareRootLowPrimeCreationStateCofactor y := by
    rw [hpEq] at hprod
    exact Nat.mul_left_cancel hpy.2.2.pos hprod
""",
)
