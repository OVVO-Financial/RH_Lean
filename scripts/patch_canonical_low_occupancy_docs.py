from __future__ import annotations

import re
from pathlib import Path


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new, 1)


def patch_sequence() -> None:
    path = Path("FORMALIZATION_SEQUENCE.md")
    text = path.read_text()
    text = replace_once(
        text,
        "The root library imports fifty-three theorem modules.",
        "The root library imports fifty-five theorem modules.",
        "sequence module count",
    )

    start = text.index("### Native canonical high-sector bridge")
    end = text.index("50. `RHLean.Proof.CanonicalHighSectorCovariance`")
    replacement = """### Native canonical high-sector analysis and bridge

49. `RHLean.Analysis.CanonicalHighSectorCore`
    - defines the unique largest-prime-factor canonical point `q_m=P⁺(m)`, `c_m=m/q_m` and signed doubled height `q_m^2-c_m^2`;
    - defines the exact square blocks, native canonical low/high increments, and cumulative square-prefix values;
    - proves exact blockwise and cumulative low/high recombination;
    - proves the complete canonical block prefix is exactly `squarePrefixMertens` at `X_n=(n+1)^2-1`;
    - defines `CanonicalLowIncrementControl` and derives the pointwise low-energy consequence of any uniform increment bound.

50. `RHLean.Analysis.CanonicalLowOccupancy`
    - proves the canonical largest-prime-factor/cofactor product identities and the exact absolute-gap height formula;
    - proves that a fixed positive absolute factor gap contributes at most one source to a square block;
    - proves low height forces `|q_m-c_m| ≤ Λ`;
    - proves the sharp nontrivial nonzero-Möbius occupancy bound `card ≤ floor Λ`;
    - isolates the single `m=1` endpoint and proves `‖canonicalLowIncrement Λ j‖ ≤ floor Λ + 1`;
    - constructs `canonicalLowIncrementControl Λ` unconditionally.

51. `RHLean.Proof.CanonicalHighSectorBridge`
    - constructs the concrete geometric partition from the analysis-layer canonical sequence;
    - defines the unresolved native statement `CanonicalHighUniformLocalBoundedStatement Λ` at scale `H N^(2+ε)`;
    - proves the native canonical high criterion is equivalent to the protected square-prefix uniform-local criterion with the proved low control inserted;
    - proves the conditional equivalence to `RiemannHypothesisStatement` from `ClassicalMertensRHCriterion`;
    - leaves only `(HS)` and the external classical Mertens↔RH theorem unproved.

"""
    text = text[:start] + replacement + text[end:]

    inventory_end = text.index("## 2. Correction history")
    prefix, suffix = text[:inventory_end], text[inventory_end:]
    for old, new in [(53, 55), (52, 54), (51, 53), (50, 52)]:
        prefix = re.sub(rf"(?m)^{old}\. `", f"{new}. `", prefix)
    text = prefix + suffix

    text = replace_once(
        text,
        "PR #60 corrects the identification of the minimal bridge. The Phase VIII/IX construction is an exact normalized all-ordered-pair/Farey transport family and remains a possible sufficient proof strategy, but it is not definitionally the paper's unique largest-prime-factor decomposition. The new native module defines one canonical point per source, proves exact recombination with `squarePrefixMertens`, and isolates `CanonicalHighUniformLocalBoundedStatement Λ` as the single analytic bridge statement. The manuscript's elementary low-increment estimate remains an explicit typed input until separately transcribed into Lean.",
        "PR #60 corrects the identification of the minimal bridge. The Phase VIII/IX construction is an exact normalized all-ordered-pair/Farey transport family and remains a possible sufficient proof strategy, but it is not definitionally the paper's unique largest-prime-factor decomposition. The native module defines one canonical point per source, proves exact recombination with `squarePrefixMertens`, and isolates `CanonicalHighUniformLocalBoundedStatement Λ` as the single analytic bridge statement. PR #72 subsequently moves the exact canonical arithmetic into the analysis layer and machine-checks the elementary low-height occupancy theorem, including the isolated `m=1` endpoint, so the low-increment control is no longer an uninstantiated premise.",
        "sequence PR60 history",
    )

    anchor = "PR #65 adds an arbitrary deterministic baseline coordinate split of the existing transport. It proves exact blockwise and cumulative recombination but deliberately does not attach prime-count interval semantics or any analytic estimate."
    addition = anchor + "\n\nPR #72 proves the manuscript's canonical low-height occupancy theorem in the analysis layer. It establishes one product per positive absolute gap, the sharp `floor Λ` count on nonzero Möbius support away from `m=1`, the uniform `floor Λ + 1` increment bound, and an unconditional `CanonicalLowIncrementControl Λ`. The canonical high-sector bridge therefore has no remaining internal low-sector hypothesis."
    text = replace_once(text, anchor, addition, "sequence PR72 history")

    old_checkpoint = """and, from `CanonicalLowIncrementControl Λ`, constructs the exact concrete partition required by the existing bridge. Consequently the compiled native chain is

```text
CanonicalHighUniformLocalBoundedStatement Λ
  ↔ SquarePrefixUniformLocalBoundedStatement
  ↔ MertensEnergyBoundedStatement
  ↔ RiemannHypothesisStatement,
```

where the last equivalence is supplied as the ordinary typed argument `ClassicalMertensRHCriterion`."""
    new_checkpoint = """and `CanonicalLowOccupancy` constructs `canonicalLowIncrementControl Λ` unconditionally from the machine-checked occupancy theorem. Consequently the compiled native chain is

```text
CanonicalHighUniformLocalBoundedStatement Λ
  ↔ SquarePrefixUniformLocalBoundedStatement
  ↔ MertensEnergyBoundedStatement
  ↔ RiemannHypothesisStatement,
```

with no remaining internal low-sector premise. The last equivalence is supplied as the ordinary typed argument `ClassicalMertensRHCriterion`; the unresolved project mathematics is exactly the native high-sector estimate `(HS)`."""
    text = replace_once(text, old_checkpoint, new_checkpoint, "sequence checkpoint")
    path.write_text(text)


def patch_checklist() -> None:
    path = Path("FORMALIZATION_CHECKLIST.md")
    text = path.read_text()
    text = replace_once(
        text,
        "- [ ] Confirm the preceding PR is green and merged; read current `main`.",
        "- [ ] Confirm the preceding dependency PR is green; read current `main` and the green head when stacking.",
        "checklist green rule",
    )
    text = replace_once(
        text,
        "- [ ] Begin the next PR only after confirming the merge on current `main`.",
        "- [ ] Begin the next dependency-bounded PR after the preceding PR is green; stack explicitly until it reaches `main`.",
        "checklist stacking rule",
    )
    old = "- [ ] **#65** — Adds the generic deterministic baseline transport approximation, exact transport error, blockwise baseline decomposition, cumulative decomposition, and square-prefix Mertens identity; no prime-count realization or analytic estimate is claimed."
    new = """- [x] **#65** — Added the generic deterministic baseline transport approximation, exact transport error, blockwise baseline decomposition, cumulative decomposition, and square-prefix Mertens identity; no prime-count realization or analytic estimate is claimed.
- [x] **#67** — Added generic finite partial moments, the exact degree-one signed-sum and absolute-mass identities, guarded balance-ratio form, and the permanent multi-route roadmap.
- [x] **#68** — Added real canonical square-block increments, exact complex-cast and cumulative Mertens bridges, and the elementary total-variation bound.
- [x] **#69** — Added the denominator-free degree-one partial-moment balance premise and proved it implies the protected pointwise and uniform-local criteria and conditionally RH.
- [ ] **#72** — Moves the canonical arithmetic core into `Analysis`, proves sharp low-height occupancy on nonzero Möbius support, isolates `m=1`, constructs unconditional low-increment control, and removes the internal low-sector hypothesis from the native high-sector bridge."""
    text = replace_once(text, old, new, "checklist ledger")
    path.write_text(text)


def patch_paper() -> None:
    path = Path("paper/Squared_Complex_Framework_for_Square_Prefix_Mobius_Sums_Lean_Complete.tex")
    text = path.read_text()
    old_abstract = "The accompanying Lean project compiles thirty-nine theorem modules covering the exact arithmetic, squared-complex geometry, modulus-$2r$ phase architecture, signed Gram identities, residual decomposition, finite certificate interface, local signed-frame theorem, and the elementary $H=1$ localization step.  The remaining analytic and realization hypotheses are exposed as ordinary typed premises; no project axiom or unconditional proof of RH is claimed."
    new_abstract = "The accompanying Lean project compiles fifty-five theorem modules covering the exact arithmetic, squared-complex geometry, modulus-$2r$ phase architecture, signed Gram identities, residual decomposition, finite certificate interface, local signed-frame theorem, square-endpoint interpolation, and the canonical low-height occupancy theorem.  The low-sector control is now constructed internally with the sharp nontrivial bound $\lfloor\Lambda\rfloor$ and the single $m=1$ endpoint correction.  The unresolved project mathematics is the native high-sector estimate; the final classical Mertens--RH equivalence remains an ordinary typed theorem argument.  No project axiom or unconditional proof of RH is claimed."
    text = replace_once(text, old_abstract, new_abstract, "paper abstract")

    old_intro = r"""\begin{theorem}[Low-height clustering and lifetime]
\label{thm:intro-low}
Let $m=cq\in B_n$ be canonical and let
\[
 Y_m=\frac{q^2-c^2}{2}.
\]
Then, for $H\ge0$,
\[
 \#\{m\in B_n:|Y_m|\le H\}
 \le\left\lfloor\frac{H}{n}\right\rfloor,
\]
and the count is zero when $H=n$.  For odd sources the bound improves to
$\lfloor H/(2n)\rfloor$.
If $Y_m>0$, the transport lifetime satisfies
\[
 L(m)\le\frac{2Y_m}{q}.
\]
Consequently, for fixed $\Lambda$, the canonical points with $|Y_m|\le\Lambda n$ have uniformly bounded block occupancy, and the transport members have uniformly bounded lifetime.
\end{theorem}"""
    new_intro = r"""\begin{theorem}[Low-height clustering and lifetime]
\label{thm:intro-low}
Let $m=cq\in B_n$ be a canonical source with $m>1$ and $\mu(m)\ne0$, and let
\[
 Y_m=\frac{q^2-c^2}{2}.
\]
Then, for $H\ge0$,
\[
 \#\{m\in B_n:m>1,\ \mu(m)\ne0,\ |Y_m|\le H\}
 \le\left\lfloor\frac{H}{n}\right\rfloor.
\]
The count is zero when $H=n$.  For odd sources the bound improves to
$\lfloor H/(2n)\rfloor$.
If $Y_m>0$, the transport lifetime satisfies
\[
 L(m)\le\frac{2Y_m}{q}.
\]
Consequently, for fixed $\Lambda$, the nontrivial M\"obius support with
$|Y_m|\le\Lambda n$ has occupancy at most $\lfloor\Lambda\rfloor$ in every
square block.  Restoring the isolated source $m=1$ gives the uniform increment
bound $\|\Delta_n^{\mathrm{low}}\|\le\lfloor\Lambda\rfloor+1$.
\end{theorem}"""
    text = replace_once(text, old_intro, new_intro, "paper intro theorem")

    anchor = "\\subsection{Parity-refined bounds}"
    formal_note = r"""\begin{remark}[Machine-checked canonical low control]
The Lean modules \texttt{RHLean.Analysis.CanonicalHighSectorCore} and
\texttt{RHLean.Analysis.CanonicalLowOccupancy} formalize the largest-prime-factor
pair, the one-product-per-positive-gap lemma, the height-to-gap implication, and
the sharp occupancy bound on nonzero M\"obius support.  They also isolate the
single $m=1$ endpoint and construct the concrete uniform control
\[
 \|\Delta_n^{\mathrm{low}}(\Lambda)\|
 \le \lfloor\Lambda\rfloor+1.
\]
Thus the low-sector input used by the canonical high-sector equivalence is no
longer an external hypothesis.  The unresolved internal statement is the
high-sector estimate itself.
\end{remark}

\subsection{Parity-refined bounds}"""
    text = replace_once(text, anchor, formal_note, "paper formalization remark")
    path.write_text(text)


def main() -> None:
    patch_sequence()
    patch_checklist()
    patch_paper()


if __name__ == "__main__":
    main()
