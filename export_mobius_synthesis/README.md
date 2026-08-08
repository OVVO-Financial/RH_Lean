# Möbius Synthesis

**Möbius Synthesis** combines the two standalone Möbius-cancellation tracks — square blocks and prime wheels — into a single shared analysis. It supersedes neither track: each remains a complete, independently checked argument in its own repository. This repository exists because the two coordinate systems turn out to be nested views of the same oscillating path, and that nesting lets a bound proved in one system transfer directly to the other.

Companion standalone repositories:

- Square blocks: [https://github.com/OVVO-Financial/square-block-mobius](https://github.com/OVVO-Financial/square-block-mobius)
- Prime wheels: [https://github.com/OVVO-Financial/prime-wheel-mobius](https://github.com/OVVO-Financial/prime-wheel-mobius)

## Why nest square blocks inside prime wheels?

Square blocks expose the **lifetime structure** of the Möbius field: sources are born, live, and die as the square-root cutoff advances. Prime wheels expose its **spectral structure**: the field's residue-class behavior collapses completely into classical Ramanujan sums and divisor functions. Neither coordinate system sees what the other sees.

The two are not competing descriptions of the same difficulty — they are complementary views of one object. Consecutive square-block increments are exact differences of the wheel residual sampled at square endpoints, so any finite collection of complete square blocks inherits whatever bound holds for the wheel residual, for free. Conversely, a wheel-residual bound controls every square-block residual sitting inside it. After collapsing both sides through the Ramanujan-shell identities, the residual is the same signed collection of divisor-boundary packets on both sides. That upgrades "two separately RH-equivalent statements" to "provably the same arithmetic object up to elementary boundary terms" — a real strengthening of the architecture, independent of whether the remaining estimate is ever proved.

## The shared reduction

Let $L_k$ and $U_k$ be the primorial-block endpoints, $Q_k$ the minimal wheel modulus, and $X_n=(n+1)^2-1$ the square-prefix endpoints. Define the wheel-side numerator

$$ F_k(x):=\operatorname{RawExpansionBoundary}_k(x)+\operatorname{RawRetainedBulk}_k(x)-2\operatorname{SmoothCollapsedBoundaryBulk}_k(x), $$

with the raw conductor family collapsed to genuine ternary expansion points and the smooth family collapsed while retaining the conductor-one term. The wheel residual is exactly

$$ R_k(x)=Q_k^{-1}F_k(x). $$

The square-sampling side proves that this residual, evaluated at a square-prefix endpoint inside the block, satisfies

$$ R_k(X_n)=H_{k,n}+\rho_{k,n}R_k(U_k),\qquad \rho_{k,n}=\frac{X_n-L_k}{Q_k}, $$

where $\rho_{k,n}$ is the additive zero mode and $H_{k,n}$ is the genuine nonzero square response — the object both tracks' open theorems are secretly about.

**The quantitative gain.** A strengthened Bertrand argument gives $Q_k>9y^2>6U_k$ for $y=\lfloor\sqrt{U_k}\rfloor\ge5$ (for $n=\lfloor(y+1)/2\rfloor$, Bertrand supplies a prime $p$ with $3<p\le y$, and $2,3,p$ distinct gives $\prod_{q\le y}q\ge6p>3y$). This makes the previously-strict contraction $\rho_{k,n}<1$ uniform: $\rho_{k,n}<1/6$ throughout every block. Combined with the existing terminal-tail bound $|T_{k,n_*}|^2<9(U_k+1)$, solving the self-referential relation above gives

$$ |R_k(U_k)|\le\frac65\Bigl(|H_{k,n_*}|+3\sqrt{U_k+1}\Bigr). $$

The incomplete terminal square is therefore already harmless at RH scale. This leaves exactly one object carrying the remaining difficulty.

## What is proved and what remains open

Both companion repositories independently establish, and this repository formally identifies as the same underlying difficulty:

- the exact square-block lifetime decomposition and squared-complex cofactor geometry;
- the exact prime-wheel Ramanujan-shell collapse and conductor weight calculus;
- the zero-mode elimination and the uniform $1/6$ contraction above.

The remaining target is stated once, not twice:

$$ \boxed{|H_{k,n}|\ll_\varepsilon (X_n+1)^{1/2+\varepsilon}\quad\text{uniformly for complete square samples inside every wheel.}} $$

This single estimate has both structures at once: square geometry has already removed the self-referential zero mode, and wheel geometry has already exposed the signed conductor and divisor-boundary cancellation. It is **not proved** in this repository. Through the square-prefix bridge and the classical Mertens criterion, it is equivalent to the Riemann Hypothesis. No unconditional proof of RH is claimed here or in either companion repository.

Per the current architecture freeze: no further exact decomposition should be introduced unless it directly proves the bound on $H_{k,n}$. That is where the cancellation proof has to happen.

## Machine-checked source

The `lean/` directory is a curated snapshot of the modules from the full `RH_Lean` development that this synthesis actually uses, mirrored under `export_mobius_synthesis/`. It draws on modules from both companion tracks plus the bridge theorems unique to this repository, and is kept separate from each track's own standalone export — nothing here is re-exported back into `square-block-mobius` or `prime-wheel-mobius`.

The authoritative verification command in the full development is:

```
lake build RHLean --wfail
```

Key bridge-specific modules:

```
RHLean.Arithmetic.PrimeProductLowerBound
RHLean.Analysis.SquareWheelZeroModeElimination
RHLean.Analysis.PrimeWheelRawBoundaryExpansionCollapse
```

together with the reindexed numerator identity connecting `squareWheelNonzeroSampleResponse` (the square-block side's $H_{k,n}$) to `primorialExpansionReindexedNumerator` (the prime-wheel side's $F_k$) on the minimal wheel system `primorialMinimalWheelSystem`, not the historical oversized-torus system.

See [`MODULES.md`](MODULES.md) for the complete curated inventory.

## Repository layout

- `paper/` — the synthesis manuscript, relating the square-block and prime-wheel frameworks and proving the bridge identities above.
- `lean/RHLean/` — curated bridge-specific Lean source, plus the subset of each companion track's modules the bridge depends on.
- `MODULES.md` — module-by-module mathematical scope.

## Build the paper

From the repository root:

```
cd paper
pdflatex main.tex
pdflatex main.tex
pdflatex main.tex
```

Three passes resolve the table of contents, theorem references, and page count.

## Status convention

The manuscript uses a strict status boundary: theorem, proposition, lemma, and corollary labels denote proved statements from the stated definitions or standard cited results, including identities transported from either companion repository; statements labelled **Open theorem** are unresolved analytic obligations. Numerical evidence is diagnostic and is not promoted to theorem status.
