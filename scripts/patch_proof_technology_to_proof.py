from __future__ import annotations

from pathlib import Path

ROOT = Path(".")
MODULES = [
    "BlockLyapunovClosure",
    "FinitePartialMoments",
    "HeightShellGram",
    "JointGramControl",
    "OrthogonalResidual",
    "ReducedSquareClassMod40",
    "ResonantCofactorCancellation",
    "ResonantLeakage",
    "ResonantProjection",
]

INVENTORY_ROWS = [
    "\\texttt{RHLean/Analysis/HeightShellGram.lean}\n& Exact signed height-shell Gram identity with off-diagonal interactions retained.\\\\\n",
    "\\texttt{RHLean/Analysis/OrthogonalResidual.lean}\n& True orthogonal coefficient, residual orthogonality, and Pythagorean decomposition.\\\\\n",
    "\\texttt{RHLean/Analysis/ResonantProjection.lean}\n& Scale-dependent resonant projection and exact resonant/nonresonant split.\\\\\n",
]


def patch_inventory() -> None:
    path = Path("paper/LEAN_ANALYSIS_INVENTORY.tex")
    text = path.read_text()
    for row in INVENTORY_ROWS:
        if text.count(row) != 1:
            raise RuntimeError(f"expected exactly one inventory row:\n{row}")
        text = text.replace(row, "", 1)
    path.write_text(text)


def move_modules() -> None:
    for module in MODULES:
        old = Path(f"RHLean/Analysis/{module}.lean")
        new = Path(f"RHLean/Proof/{module}.lean")
        if old.exists():
            if new.exists():
                raise RuntimeError(f"destination already exists: {new}")
            new.parent.mkdir(parents=True, exist_ok=True)
            old.rename(new)
        elif not new.exists():
            raise RuntimeError(f"neither source nor destination exists for {module}")


def replace_all_paths() -> None:
    replacements: dict[str, str] = {}
    for module in MODULES:
        replacements[f"RHLean.Analysis.{module}"] = f"RHLean.Proof.{module}"
        replacements[f"RHLean/Analysis/{module}.lean"] = f"RHLean/Proof/{module}.lean"

    suffixes = {".lean", ".md", ".tex", ".sh"}
    for path in ROOT.rglob("*"):
        if not path.is_file() or path.suffix not in suffixes:
            continue
        text = path.read_text()
        updated = text
        for old, new in replacements.items():
            updated = updated.replace(old, new)
        if updated != text:
            path.write_text(updated)


def verify() -> None:
    offenders: list[str] = []
    for path in ROOT.rglob("*"):
        if not path.is_file() or path.suffix not in {".lean", ".md", ".tex", ".sh"}:
            continue
        text = path.read_text()
        for module in MODULES:
            for old in (
                f"RHLean.Analysis.{module}",
                f"RHLean/Analysis/{module}.lean",
            ):
                if old in text:
                    offenders.append(f"{path}: {old}")
    if offenders:
        raise RuntimeError("stale Analysis paths remain:\n" + "\n".join(offenders))


def main() -> None:
    patch_inventory()
    move_modules()
    replace_all_paths()
    verify()


if __name__ == "__main__":
    main()
