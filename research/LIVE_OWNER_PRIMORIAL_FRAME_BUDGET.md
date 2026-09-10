# The physical owner schedule is primorial-thresholded

This note records the arithmetic behind
`RHLean/Proof/SquareRootLowPrimeLiveOwnerPrimorialFrame.lean` and states
precisely what it does and does not settle.  Numerical tables below are
route-selection evidence only; none of them is used as a theorem.

## The observation

The `4/3` cross-owner frame target of #634 was calibrated against a *global*
prime reciprocal-square budget: `sum_p 1/p^2 <= 1` over every prime owner, or
`1/2` after an odd telescope.  That budget is not the one the Go recursion
spends.

A saturated second-contact seed at root `R` (the merged #629 window) is a pair
`(q, c)` with

```text
q prime, q < R,  c squarefree,  P+(c) < q,
max R (X_R / q^2) < c <= X_R / q,   X_R = R^2 - 1.
```

The core `c` is squarefree with every prime factor below `q`, so it divides the
predecessor primorial `prod_{p < q} p`.  Since `c > R`,

```text
live owner q at root R  ==>  R < prod_{p<q} p.
```

Small owners are therefore *absent*, not merely rare.  The Lean statement is
`lowWheelFrozenSecondContactCanonicalSeeds_root_lt_predecessorPrimorial`, and
its consequences are

```text
R >= 6    ==>  every live owner is >= 7
R >= 30   ==>  every live owner is >= 11
R >= 210  ==>  every live owner is >= 13
```

with the general threshold `predecessorPrimorial Q <= R  ==>  Q < q`
(`lt_of_mem_liveOwnerCandidates`).  In particular owner `2` — whose exclusion
was an explicit open item of the factor-four target — is dead for every root at
least `2`, together with `3` and `5`.

## The dual statement: a saturated daughter is exactly zero

The same primorial governs the daughter ledger.  The Go `q`-square daughter is
the signed `q`-smooth Möbius mass below `X / q^2`.  Once
`prod_{p<q} p <= X / q^2` every `q`-smooth face is admitted, the Boolean cube is
complete, and the daughter cancels *exactly*:

```lean
squareRootLowPrimeGoWallSquareResidual_eq_zero_of_saturated :
  3 <= q -> predecessorPrimorial q <= X / (q * q) ->
    squareRootLowPrimeGoWallSquareResidual q X = 0
```

This is an exact identity, not an estimate: it is the completeness of the
truncated Boolean cube, obtained from the existing first-failure boundary
theorem `truncatedCubeAlternatingSum_eq_zero_of_no_firstFailure`.

## Quantitative consequence: the admissible frame loss

Only the product of the frame loss and the owner scale budget enters the
compiled prime-`11` recurrence
(`elevenQ2_frameLoss_budget_implies_linear`): if `A * rho <= 1` then

```text
E(X) <= (I(X) + b(X))^2,
I(X)^2 <= A * elevenWeightOneEnergyFactor * sum_{q in owners X} E(X/q^2),
b(X)^2 <= B * X
```

already give `E(X) <= (6348/143) * B * X`, with `6348/143 = 44.39...`.

The odd-owner telescope turns the primorial threshold into a budget:

```text
owners all >= 2*k+3   ==>   sum_{q in owners} 1/q^2 <= 1/(4*(k+1))
```

so the live owner schedule has budget `1/12` uniformly (`k = 2`, owners `>= 7`)
and `1/20` beyond root `30` (`k = 4`, owners `>= 11`).  Hence a frame loss of

* `12` uniformly (`liveOwnerFrame_twelve_implies_linear`),
* `20` beyond root `30` (`liveOwnerFrame_twenty_implies_linear`),
* and *any* prescribed `A`, beyond the explicit root threshold
  `predecessorPrimorial (2*k+2)` with `A <= 4*(k+1)`
  (`liveOwner_admissible_frameLoss_unbounded`),

closes the same induction.  The `4/3` figure was an artefact of the crude unit
budget, not of the physical carrier.

## Numerical evidence (filter only, not proof)

Live owner sets computed directly from the #629 inequalities.  `minlive` is the
smallest live owner and `primThresh` the smallest `q` with
`prod_{p<q} p > R`; the two agree or `minlive` is larger, as the theorem
requires.

| R | minlive | primThresh | sum 1/q^2 | sum 1/q | #live |
|---:|---:|---:|---:|---:|---:|
| 12 | 7 | 7 | 0.0204 | 0.143 | 1 |
| 25 | 7 | 7 | 0.0427 | 0.466 | 6 |
| 30 | 11 | 11 | 0.0223 | 0.323 | 5 |
| 100 | 11 | 11 | 0.0289 | 0.627 | 21 |
| 300 | 13 | 13 | 0.0220 | 0.746 | 57 |
| 1,000 | 17 | 13 | 0.0164 | 0.854 | 162 |
| 3,000 | 19 | 17 | 0.0131 | 0.941 | 422 |
| 10,000 | 19 | 17 | 0.0131 | 1.080 | 1,222 |

The observed reciprocal-square budget never exceeds `0.043`, comfortably inside
the proved `1/12`, and it decreases as the root grows.

## The purely diagonal route, and the exact distance left

The frame hypothesis can be dropped altogether if the owner weight `q` is
retained through the descent.  Weighted Cauchy–Schwarz on the owner columns —
no sign information, no cross-owner cancellation — gives

```text
I(X)^2 <= (sum_q 1/q) * sum_q q * column_q^2
```

and the weighted induction then needs only

```text
sum_{q in owners X} 1/q <= 1
```

to close with the same envelope (`elevenQ2_harmonicOwnerColumns_implies_linear`).

These columns are the exact `q`-daughters of the compiled saturated-source
identity, and the per-column bound is the *inductive* daughter energy, not a
trivial or cardinality bound.  That distinction matters: norming the
child-owner `r`-columns of the same reassembly costs a full power, as measured
in `RESEARCH_ROUTE_REGISTRY.md`.  Here the cost is only the harmonic sum.

The last column of the table is exactly this quantity.  It is `0.63` at
`R = 100`, `0.85` at `R = 1000`, `0.94` at `R = 3000`, and first exceeds `1`
between `R = 3000` and `R = 10000`; asymptotically it grows like
`log log R - log log log R`, since the live owners run from about `log R` up to
the second-contact cutoff.

So on this carrier the elementary, cancellation-free route is not off by a power
and not off by a logarithm: it is off by a double logarithm.  Any of the
following would close the gap and is the natural next target:

1. a genuine cross-owner frame bound with loss below `4*(k+1)` at root
   threshold `predecessorPrimorial (2*k+2)` — the Schur/Cotlar route, now with
   an order of magnitude more room than `4/3`;
2. a Carleson-type embedding over the live owner tree, whose measure is the
   `q^-2` owner scale rather than raw owner cardinality;
3. any saving of a double logarithm in the diagonal column bound itself.

## What is not proved

* No frame inequality is established on the reduced #643 physical packet.  All
  frame statements here remain conditional theorems with the frame estimate as
  an explicit hypothesis.
* The reduced compensated residual is still not identified with the recovered
  Mertens degree-one energy.
* The harmonic criterion is a *sufficient* condition that the physical schedule
  does not satisfy uniformly; the table above is evidence about its size, not a
  proof of any bound.
* No improved Mertens exponent and no RH closure follows from anything in this
  note.
