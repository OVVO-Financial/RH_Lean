from pathlib import Path
import re

path = Path("paper/Squared_Complex_Framework_for_Square_Prefix_Mobius_Sums_Lean_Complete.tex")
text = path.read_text()
text, count = re.subn(
    r"\$\\lfloor\\Lambda\s*floor\$",
    r"$\\lfloor\\Lambda\\rfloor$",
    text,
    count=1,
)
if count != 1:
    raise RuntimeError(f"expected one malformed floor expression, found {count}")
path.write_text(text)
