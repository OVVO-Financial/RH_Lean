# Square-Block Möbius

**Square-Block Möbius** develops a square-block approach to the Möbius and Mertens functions, together with a machine-checked Lean formalization of its exact arithmetic and geometric reductions.

The central idea is to group integers between consecutive squares and track how canonical Möbius sources are born, persist, and disappear as the square scale advances. This produces an exact square-endpoint description of the Mertens path and isolates the remaining cancellation problem in a concrete signed survivor operator.

The accompanying manuscript is **A Squared-Complex Framework for Square-Prefix Möbius Sums**.

## Why square blocks?

- **Square blocks**: partition the integers into intervals between consecutive squares. This exposes a natural **lifetime flow**: arithmetic contributions are born, persist across a controlled range of blocks, and eventually disappear. The resulting decomposition shows that the Mertens path is essentially determined by its values at square endpoints, with only the elementary within-block interpolation cost remaining.
- **Exact square-root cutoff**: at $X_n=(n+1)^2-1$, a squarefree integer cannot contain two prime factors larger than $n+1$. This gives an exact one-large-prime decomposition rather than an approximation.
- **Canonical factor geometry**: every nontrivial squarefree source has a unique largest-prime factorization $m=cq$, with $q=P^+(m)$. The squared-complex coordinate $\left(\frac{c+q}{2}+i\frac{q-c}{2}\right)^2=m+i\frac{q^2-c^2}{2}$ records the source integer and its factor imbalance simultaneously.
- **Lifetime refinement**: the high population splits exactly into active survivors and completed deaths. The death process is controlled by a bounded-width divisor window, leaving one explicit signed survivor operator as the remaining analytic object.

## Exact square-prefix reduction

Write

$$
S_n=M(X_n),
\qquad
X_n=(n+1)^2-1.
$$

The square-root cutoff gives the exact decomposition

$$
\boxed{S_n=A_n-T_n.}
$$

The canonical source population is then organized by signed height

$$
Y_m=\frac{q_m^2-c_m^2}{2}.
$$

For fixed $\Lambda>0$, the low-height population has uniformly bounded occupancy in each square block. Consequently, the cumulative low sector can be controlled without using Möbius cancellation. The unresolved cancellation is therefore isolated in the high sector.

Following high sources through their lifetimes gives 

$$\boxed{S_t^{\mathrm{high}}(\Lambda)=Z_\Lambda(t)+D_\Lambda(t).}$$

The accumulated death mass $D_\Lambda$ already satisfies the required local-energy scale. The remaining active survivor is the explicit signed cofactor operator 

$$\boxed{Z_\Lambda(t)=-\sum_c \mu(c)\,\mathcal K_{\Lambda,t}(c).}$$

This survivor operator is the analytic frontier of the project.

## What is proved and what remains open

The manuscript and Lean formalization establish the exact arithmetic decomposition, squared-complex recovery, cofactor geometry, endpoint support laws, low-height occupancy, lifetime bookkeeping, and the divisor-window bound for completed deaths.

The remaining power-saving estimate for the survivor operator is stated explicitly as an **open theorem**.

Through the square-prefix reduction and the classical Mertens criterion, a bound of the required strength would yield the Riemann Hypothesis. That estimate is **not proved** here, and this repository does not claim an unconditional proof of RH.

Two endpoint support facts are kept separate.

First, because every canonical prime satisfies $q\ge 2$, every canonical cofactor below $x$ satisfies

$$
c\le \left\lfloor\frac{x}{2}\right\rfloor.
$$

Second, if $m\le x$ is composite, then

$$
P^+(m)\le \left\lfloor\frac{x}{2}\right\rfloor.
$$

Equivalently, if

$$
P^+(m)>\left\lfloor\frac{x}{2}\right\rfloor,
$$

then $c=1$ and $m$ itself is prime.

## Machine-checked Lean source

The `lean/RHLean/` directory contains the Lean formalization accompanying the manuscript.

The formal source covers the square-prefix Mertens bridge, canonical high-sector decomposition, low-height occupancy, extreme-prime support, lifetime death process, and survivor reduction, together with the arithmetic and geometric lemmas required by those results.

Key modules include:

```text
RHLean.Analysis.SquarePrefixMertensBridge
RHLean.Analysis.CanonicalHighSectorCore
RHLean.Analysis.CanonicalLowOccupancy
RHLean.Analysis.CanonicalHighSectorBridge
RHLean.Analysis.CanonicalExtremePrimeSupport
RHLean.Analysis.SquareBlockDeathProcess
RHLean.Analysis.SquareBlockSurvivorBridge
````

`MODULES.md` describes the mathematical role of the included Lean modules.

The formalization maintains a strict proof boundary: unfinished proofs and theorem substitutes such as `sorry`, `admit`, added axioms, or opaque constants standing in for mathematical results are not accepted as proofs of the stated results.

## Repository layout

* `paper/squared-complex_framework.tex` — complete manuscript source.
* `lean/RHLean/` — machine-checked Lean formalization.
* `MODULES.md` — guide to the formal modules and their mathematical roles.

## Build the paper

From the repository root:

```bash
cd paper
pdflatex squared-complex_framework.tex
pdflatex squared-complex_framework.tex
pdflatex squared-complex_framework.tex
```

Multiple passes resolve the table of contents, cross-references, and final page count.

## Status convention

The manuscript maintains a strict distinction between proved results and unresolved analytic obligations.

Statements labelled **theorem**, **proposition**, **lemma**, or **corollary** are proved from the stated definitions or explicitly cited standard results.

Statements labelled **Open theorem** are unresolved.

Numerical evidence is diagnostic only and is not promoted to theorem status.

The central unresolved problem is therefore precise: prove the required power-saving estimate for the signed survivor operator

$$Z_\Lambda(t)=-\sum_c \mu(c)\,\mathcal K_{\Lambda,t}(c).$$

## License

Lean and Python source in this repository is licensed under the Apache License,
Version 2.0; see [LICENSE](LICENSE).

The manuscript under `paper/` is licensed under the Creative Commons Attribution
4.0 International License (CC BY 4.0); see [paper/LICENSE](paper/LICENSE).
