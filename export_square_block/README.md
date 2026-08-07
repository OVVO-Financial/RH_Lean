# Square-Block Möbius

**Square-Block Möbius** is the publication staging tree for **A Squared-Complex Framework for Square-Prefix Möbius Sums**.

Canonical standalone repository:

https://github.com/OVVO-Financial/square-block-mobius

Companion finite prime-wheel viewpoint:

https://github.com/OVVO-Financial/prime-wheel-mobius

The two repositories organize the Möbius problem from different finite structures. **Prime-Wheel Möbius** evolves the field prime by prime on completed wheel blocks. **Square-Block Möbius** groups integers between consecutive squares and studies how canonical Möbius sources are born, move, and disappear across square scale.

## Why square blocks?

- **Square blocks**: partitioning the integers into intervals between consecutive squares. This exposes a natural **lifetime flow**: arithmetic contributions are born, persist across a controlled range of blocks, and eventually disappear. The resulting decomposition shows that the Mertens path is essentially determined by its values at square endpoints, with only the elementary within-block interpolation cost remaining.
- **Exact square-root cutoff**: at
  \[
  X_n=(n+1)^2-1,
  \]
  a squarefree integer cannot contain two prime factors larger than `n+1`. This gives an exact one-large-prime decomposition rather than an approximation.
- **Canonical factor geometry**: every nontrivial squarefree source has a unique largest-prime factorization
  \[
  m=cq,\qquad q=P^+(m),
  \]
  and the squared-complex coordinate
  \[
  \left(\frac{c+q}{2}+i\frac{q-c}{2}\right)^2
  =m+i\frac{q^2-c^2}{2}
  \]
  records the source integer and the factor imbalance simultaneously.
- **Lifetime refinement**: the high population splits exactly into active survivors and completed deaths. The death process is controlled by a bounded-width divisor window, leaving one explicit signed survivor operator as the remaining analytic object.

## Exact square-prefix reduction

Write

\[
S_n=M(X_n),\qquad X_n=(n+1)^2-1.
\]

The square-root cutoff gives the exact decomposition

\[
\boxed{S_n=A_n-T_n.}
\]

The geometry then separates the canonical source population by signed height

\[
Y_m=\frac{q_m^2-c_m^2}{2}.
\]

For fixed `Λ > 0`, low height has uniformly bounded occupancy in each square block. Consequently the cumulative low sector is controlled without using Möbius cancellation. The unresolved cancellation can therefore be isolated in the high sector.

Following high sources through their lifetimes gives

\[
\boxed{S_t^{\mathrm{high}}(\Lambda)=Z_\Lambda(t)+D_\Lambda(t),}
\]

where the accumulated death mass `D_Λ` already satisfies the required local-energy scale. The remaining active survivor is the explicit signed cofactor operator

\[
\boxed{
Z_\Lambda(t)
=-\sum_c\mu(c)\,\mathcal K_{\Lambda,t}(c).
}
\]

This is the analytic frontier of the standalone square-block paper.

## What is proved and what remains open

The manuscript and paper-facing Lean source establish the exact arithmetic decomposition, squared-complex recovery, cofactor geometry, endpoint support laws, low-height occupancy, lifetime bookkeeping, and the divisor-window bound for completed deaths.

The remaining survivor power-saving estimate is stated explicitly as an **open theorem**. Through the square-prefix bridge and the classical Mertens criterion, this estimate has the strength required for the Riemann Hypothesis. It is **not proved** in this repository, and the repository does not claim an unconditional proof of RH.

Two endpoint support facts are kept separate:

1. because every canonical prime satisfies `q ≥ 2`, every canonical cofactor below `x` satisfies
   \[
   c\le \lfloor x/2\rfloor;
   \]
2. if `m ≤ x` is composite, then
   \[
   P^+(m)\le \lfloor x/2\rfloor.
   \]
   Equivalently, if `P^+(m) > floor(x/2)`, then `c=1` and `m` itself is prime.

## Machine-checked source

The `lean/` directory is a **curated paper-facing snapshot** of modules verified in the full Lean development. It is selected by mathematical scope rather than by transitive import closure, so the publication snapshot is not a second independent Lake project.

The authoritative verification command in the full development is:

```bash
lake build RHLean --wfail
```

The source audit also rejects unfinished proofs and project-local theorem substitutes such as `sorry`, `admit`, new axioms, and opaque constants standing in for results.

Key paper-facing modules include:

```text
RHLean.Analysis.SquarePrefixMertensBridge
RHLean.Analysis.CanonicalHighSectorCore
RHLean.Analysis.CanonicalLowOccupancy
RHLean.Analysis.CanonicalHighSectorBridge
RHLean.Analysis.CanonicalExtremePrimeSupport
RHLean.Analysis.SquareBlockDeathProcess
RHLean.Analysis.SquareBlockSurvivorBridge
```

See [`MODULES.md`](MODULES.md) for the complete curated inventory.

## Repository layout

- `paper/main.tex` — manuscript entry point.
- `paper/sections/` — modular publication source.
- `lean/RHLean/` — curated paper-facing Lean source.
- `MODULES.md` — module-by-module mathematical scope.

The contents of `export_square_block/` are intended to mirror the root of `square-block-mobius`.

## Build the paper

From the standalone repository root:

```bash
cd paper
pdflatex main.tex
pdflatex main.tex
pdflatex main.tex
```

Three passes resolve the table of contents, theorem references, and page count.

## Status convention

The manuscript uses a strict status boundary: theorem, proposition, lemma, and corollary labels denote proved statements from the stated definitions or standard cited results; statements labelled **Open theorem** are unresolved analytic obligations. Numerical evidence is diagnostic and is not promoted to theorem status.
