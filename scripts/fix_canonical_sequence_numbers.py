from pathlib import Path

path = Path("FORMALIZATION_SEQUENCE.md")
text = path.read_text()
replacements = [
    ("\n52. `RHLean.Analysis.CanonicalLowOccupancy`", "\n50. `RHLean.Analysis.CanonicalLowOccupancy`"),
    ("\n53. `RHLean.Proof.CanonicalHighSectorBridge`", "\n51. `RHLean.Proof.CanonicalHighSectorBridge`"),
]
for old, new in replacements:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)
path.write_text(text)
