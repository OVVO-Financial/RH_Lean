#!/usr/bin/env python3
"""Apply compatibility repairs discovered after the main StrongPNT 4.24 patch.

This stays separate from apply.py while the terminal modules are being driven through
GitHub Actions. Every replacement is exact and therefore fails closed on upstream drift.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
STRONGPNT = ROOT / ".lake" / "packages" / "StrongPNT" / "StrongPNT"


def replace_exact(path: Path, label: str, old: str, new: str) -> None:
    text = path.read_text()
    old_count = text.count(old)
    new_count = text.count(new)
    if old_count == 1:
        path.write_text(text.replace(old, new, 1))
        print(f"applied {path.name}: {label}")
    elif old_count == 0 and new_count == 1:
        print(f"already applied {path.name}: {label}")
    else:
        raise SystemExit(
            f"compatibility patch mismatch in {path.name} for {label!r}: "
            f"old_count={old_count}, new_count={new_count}"
        )


def main() -> None:
    target = STRONGPNT / "ZetaZeroFree.lean"
    replace_exact(
        target,
        "use direct zeta continuity at the punctured-limit center",
        """      use h (isClosed_singleton.isSeqClosed this (.comp (cont.continuousAt.comp (eventually_ne_nhds (by field_simp [ht₀])).mono fun and=>.intro ⟨⟩) (ToOneT0.trans (inf_le_left))))
""",
        """      have hcenter_ne : (1 : ℂ) + Complex.I * t₀ ≠ 1 := by
        intro hcenter
        apply ht₀
        have him := congrArg Complex.im hcenter
        simpa using him
      have hcont : ContinuousAt ζ (1 + Complex.I * t₀) := by
        apply DifferentiableAt.continuousAt (𝕜 := ℂ)
        convert differentiableAt_riemannZeta hcenter_ne
      have hz_tendsto :
          Tendsto (fun n ↦ ζ (↑(σ' (subseq n)) + I * ↑(t (subseq n)))) atTop
            (𝓝 (ζ (1 + I * ↑t₀))) :=
        hcont.tendsto.comp (ToOneT0.trans inf_le_left)
      exact h (isClosed_singleton.isSeqClosed this hz_tendsto)
""",
    )


if __name__ == "__main__":
    main()
