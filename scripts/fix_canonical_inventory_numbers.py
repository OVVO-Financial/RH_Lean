from pathlib import Path

path = Path("FORMALIZATION_SEQUENCE.md")
text = path.read_text()
replacements = {
    "52. `RHLean.Analysis.CanonicalLowOccupancy`":
        "50. `RHLean.Analysis.CanonicalLowOccupancy`",
    "53. `RHLean.Proof.CanonicalHighSectorBridge`":
        "51. `RHLean.Proof.CanonicalHighSectorBridge`",
}
for old, new in replacements.items():
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)
path.write_text(text)
