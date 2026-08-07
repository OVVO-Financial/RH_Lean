# Square Block Paper Export

This directory is the publication export for **A Squared-Complex Framework for Square-Prefix Möbius Sums**.

It is intentionally limited to the square-block framework. The paper is self-contained at the level of its arithmetic, geometry, lifetime refinement, and Lean-facing theorem interfaces. A later synthesis paper may compare or combine this framework with other architectures, but that material is outside this export.

## Contents

- `paper/main.tex` — publication source in the same typographic and status-reporting style as the companion block paper.
- `paper/sections/` — modular section files included by `main.tex`.
- `lean/RHLean/` — curated snapshots of the Lean modules whose mathematical content supports this paper.
- `MODULES.md` — module-by-module scope and role.

## New structural statements included in this revision

The canonical factorization of a nontrivial source is

\[
m=cq,\qquad q=P^+(m).
\]

Two different endpoint support facts are now stated separately:

1. because the canonical prime satisfies `q ≥ 2`, every canonical cofactor below `x` satisfies
   \[
   c\le \lfloor x/2\rfloor;
   \]
2. if `m ≤ x` is composite, then
   \[
   P^+(m)\le \lfloor x/2\rfloor.
   \]
   Equivalently, if `P^+(m) > floor(x/2)`, the cofactor is `c=1` and `m` itself is prime.

The revision also records the completed divisor-window estimate for the lifetime death process and isolates the remaining active survivor as the explicit signed cofactor operator

\[
Z_\Lambda(t)=-\sum_c \mu(c)\,\mathcal K_{\Lambda,t}(c).
\]

No power-saving estimate for that survivor operator is claimed as proved.

## Lean build

The copied Lean files are a **curated paper-facing snapshot**, not a second independent Lake project. Ordinary transitive scaffolding remains in the parent repository. The authoritative verification command is run at the repository root:

```powershell
lake build RHLean --wfail
```

The two new paper-facing modules introduced with this export are:

```text
RHLean.Analysis.CanonicalExtremePrimeSupport
RHLean.Analysis.SquareBlockSurvivorBridge
```

They are also copied under `export_square_block/lean/` for publication review.

## LaTeX build

From this directory:

```bash
cd export_square_block/paper
pdflatex main.tex
pdflatex main.tex
pdflatex main.tex
```

Three passes resolve the table of contents, theorem references, and page count.

## Status convention

The manuscript uses the same convention as the companion paper: theorem, proposition, lemma, and corollary labels denote proved statements from the stated definitions or standard cited results; statements labelled **Open theorem** are unresolved analytic obligations. Numerical evidence is not promoted to a theorem.

The export does not claim an unconditional proof of the Riemann Hypothesis.
