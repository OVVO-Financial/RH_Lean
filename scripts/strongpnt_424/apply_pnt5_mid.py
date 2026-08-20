#!/usr/bin/env python3
"""Apply the next StrongPNT PNT5 compatibility layer for Mathlib 4.24.

The replacements are taken from the already-ported PrimeNumberTheoremAnd MediumPNT
source at the pinned 4.24-compatible commit. Markers are exact and fail closed.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / ".lake" / "packages" / "StrongPNT" / "StrongPNT" / "PNT5_Strong.lean"


def replace_exact(label: str, old: str, new: str) -> None:
    text = TARGET.read_text()
    old_count = text.count(old)
    new_count = text.count(new)
    if old_count == 1:
        TARGET.write_text(text.replace(old, new, 1))
        print(f"applied PNT5_Strong.lean: {label}")
    elif old_count == 0 and new_count == 1:
        print(f"already applied PNT5_Strong.lean: {label}")
    else:
        raise SystemExit(
            f"compatibility patch mismatch for {label!r}: "
            f"old_count={old_count}, new_count={new_count}"
        )


def replace_between(label: str, start: str, end: str, replacement: str) -> None:
    text = TARGET.read_text()
    start_count = text.count(start)
    end_count = text.count(end)
    if start_count == 1 and end_count == 1:
        i = text.index(start)
        j = text.index(end, i)
        TARGET.write_text(text[:i] + replacement + text[j:])
        print(f"applied PNT5_Strong.lean: {label}")
    elif start_count == 0 and end_count == 1 and replacement in text:
        print(f"already applied PNT5_Strong.lean: {label}")
    else:
        raise SystemExit(
            f"compatibility range mismatch for {label!r}: "
            f"start_count={start_count}, end_count={end_count}"
        )


def remove_between(label: str, start: str, end: str) -> None:
    text = TARGET.read_text()
    start_count = text.count(start)
    end_count = text.count(end)
    if start_count == 1 and end_count == 1:
        i = text.index(start)
        j = text.index(end, i)
        TARGET.write_text(text[:i] + text[j:])
        print(f"removed PNT5_Strong.lean: {label}")
    elif start_count == 0 and end_count == 1:
        print(f"already removed PNT5_Strong.lean: {label}")
    else:
        raise SystemExit(
            f"compatibility range mismatch for {label!r}: "
            f"start_count={start_count}, end_count={end_count}"
        )


def main() -> None:
    replace_between(
        "finite-range splitting and initial smoothing block from 4.24 MediumPNT",
        "  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by\n",
        "  have vonBnd1 :\n",
        """  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
    rw[Nat.floor_add_one (by linarith), Nat.cast_add, Nat.cast_one]
    apply le_trans <| Nat.le_ceil X
    exact_mod_cast Nat.ceil_le_floor_add_one X

  have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := by exact Nat.floor_le (by positivity)

  rw [show ∑ x ∈ Finset.range ⌊X + 1⌋₊, Λ x =
      (∑ x ∈ Finset.range n₀, Λ x) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + ↑n₀) by
    field_simp
    simp only [add_comm _ n₀]
    rw [← Finset.sum_range_add, Nat.add_sub_of_le]
    dsimp only [n₀]
    exact Nat.ceil_le.mpr (by linarith)]

  rw [show ∑ n ∈ Finset.range n₀, Λ n * F (↑n / X) =
      ∑ n ∈ Finset.range n₀, Λ n by
    apply Finset.sum_congr rfl
    intro n hn
    obtain rfl|n_zero := eq_or_ne n 0
    · simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    · convert mul_one _
      apply smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
      simp only [Finset.mem_range, n₀] at hn
      exact Nat.lt_ceil.mp hn |>.le]
""",
    )

    remove_between(
        "helper theorems now supplied by PrimeNumberTheoremAnd.ZetaBounds",
        "theorem summable_complex_then_summable_real_part (f : ℕ → ℂ) :\n",
        "def LogDerivZetaHasBound (A C : ℝ) : Prop :=",
    )

    replace_exact(
        "continuousOn_univ API in Pull1 integrability",
        """  · apply Continuous.aestronglyMeasurable
    rw [continuous_iff_continuousOn_univ]
    intro t _
""",
        """  · apply Continuous.aestronglyMeasurable
    rw [← continuousOn_univ]
    intro t _
""",
    )


if __name__ == "__main__":
    main()
