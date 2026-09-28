# Equal-density and PNT-density universal baseline

Status: submitted for compilation; the exact-head workflow result is authoritative.
This is a finite, unconditional quantitative baseline requested for iteration.
It does not claim an RH-scale estimate or unconditional RH.

## Objects and conventions

For integer y >= 2 and x <= y^2, the constant-density model uses the fixed
weight 1/log(y) at every integer q in (y,x]. Thus it represents uniform
spacing log(y), including each lower Mertens cofactor cutoff floor(x/q).
The unit-density reference uses weight 1.

The PNT-density model is the existing `primeSievePNTBulk y x` from
`RHLean/Analysis/PrimeSievePNTCentering.lean`, not a new approximation:

    d(q) = Li(q) - Li(q-1),
    PNTBulk(y,x) = sum_{y<q<=x} d(q) M(floor(x/q)).

The interval endpoints, integer rounding, and full signed sums are retained.
The exact prime tail and `primeSievePNTError` are also the existing objects.

## Explicit universal bounds

The module proves the following baseline statements, with compiler acceptance
checked by the dedicated warning-fatal workflow:

    |UnitBulk(y,x)| <= x (1 + log x),
    |EqualBulk(y,x)| <= 4x,
    |PNTBulk(y,x)| <= 4x.

If sqrt(x) < y, exact largest-prime reassembly also gives

    |PrimeTail(y,x)| <= x,
    Error(y,x) = PrimeTail(y,x) - PNTBulk(y,x),
    |Error(y,x)| <= 5x.

Hence the two model energies are at most 16x^2 and the error energy is at most
25x^2. At x=R^2-1, y=R these are universal quartic bounds in R, without a
numerical range, a PNT error assumption, a lower-envelope assumption, or RH.
The constants are deliberately not optimized.

## Proof sequence

1. Bound the assembled Mertens prefix by its endpoint.
2. Prove the generic signed weighted-transport harmonic envelope.
3. Use log(y)>=1/2 and H_x<=1+log(x)<=1+2log(y) to obtain constant 4.
4. Express the existing Li singleton increment as the integral over (q-1,q].
5. Bound that increment by the same frozen density 1/log(y).
6. Reassemble the actual prime tail into its single largest-prime source set
   before the endpoint norm estimate; no duplicate source charging is used.
7. Retain the exact signed error and derive its universal constant 5.
8. Square only the complete model/error amplitudes.

The real energy identity is retained explicitly:

    (model-error)^2-D = (model^2-D)-2*model*error+error^2.

## Scope of the next iteration

The finite harmonic envelope can be sharpened without changing any model
carrier. The next genuinely cancellation-sensitive improvement must bound the
signed error and its cross term, not assume monotonicity of the signed sum
under pointwise density reduction. No norm domination of actual prime signs
by a smooth signed model is asserted.

This baseline is intentionally weaker than the current CORR-4/RH target.
Its purpose is to replace an unbounded heuristic comparison with explicit
all-scale inequalities on the existing density model and its exact error.

## Compilation and preservation checklist

- [x] Read current proof contract, agent instructions, and formalization rules.
- [x] Work on a separate branch from main; leave PR #802 untouched.
- [x] Reuse the existing PNT bulk, Li convention, prime tail, and signed error.
- [x] Register the research module in an explicit warning-fatal workflow.
- [x] Preserve every existing theorem, obstruction, export, and terminal consumer.
- [x] Add compiler-log retention and named-theorem axiom inspection.
- [ ] Dedicated workflow passed on the exact final commit.
- [ ] Canonical append-only formalization ledgers updated before merge.
- [ ] Merge authorized; this branch is not automatically merged.

No local Lean toolchain was available at submission and container DNS prevents
installing it. Compilation is performed by the dedicated GitHub Actions job.
The hosted run, not these checkboxes or symbolic arithmetic, certifies Lean
elaboration. Any compiler corrections must be tested at their own final head.
