#!/usr/bin/env python3
"""Insert the exact dyadic cell section into the current fixed-packet paper.

Usage:
    python paper/apply_dyadic_revision.py INPUT.tex OUTPUT.tex
"""

from __future__ import annotations

import argparse
from pathlib import Path

START = "The small-prime channels have additional deterministic structure."
END = r"\subsection{Directional signed Gram form}"
INSERT = r"\input{sections/exact_dyadic_sign_flip_cells}"
LEAN_MARKER = r"\subsection{Open input}"

LEAN_INSERT = r"""
\subsection{Dyadic compression and small-prime activation}

\begin{enumerate}[leftmargin=1.7em,itemsep=0.3em]
\item \texttt{Arithmetic/MobiusDoubling.lean}: prove
      $\mu(2a)=-\mu(a)$ for odd $a$, including the nonsquarefree zero case.
\item \texttt{Arithmetic/FourSlotCell.lean}: define the complete four-slot
      cell and prove its exact $(+,-,+,0)$ representation and scalar sum.
\item \texttt{Arithmetic/PrimeThreeActivation.lean}: prove unique divisibility
      by $3$ among the three active slots and the deterministic slot cycle.
\item \texttt{Kernel/CellPacketEquivalence.lean}: prove the exact compressed
      packet identity and the half-square boundary-energy bound $\le9M$.
\item \texttt{Bridge/CompressedFrameClosure.lean}: formulate the open
      actual-start frame estimate only for the compressed packet process and
      connect it to the uniform closure theorem.
\end{enumerate}

"""


def integrate(text: str) -> str:
    if text.count(START) != 1:
        raise SystemExit(f"expected exactly one start marker; found {text.count(START)}")
    start = text.index(START)
    if text.count(END, start) != 1:
        raise SystemExit("expected exactly one following directional-Gram marker")
    end = text.index(END, start)
    text = text[:start] + INSERT + "\n\n" + text[end:]

    if text.count(LEAN_MARKER) != 1:
        raise SystemExit(f"expected exactly one Lean marker; found {text.count(LEAN_MARKER)}")
    return text.replace(LEAN_MARKER, LEAN_INSERT + LEAN_MARKER, 1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    source = args.input.read_text(encoding="utf-8")
    revised = integrate(source)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(revised, encoding="utf-8")
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
